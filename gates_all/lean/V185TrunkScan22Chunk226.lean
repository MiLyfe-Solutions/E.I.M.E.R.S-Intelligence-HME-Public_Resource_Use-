import V185TrunkScan22Chunk225

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2015268 : List Nat := [2, 3, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_2015268 : Nat := 118140960795 + 2015268 * 2 ^ 59
def prefixEnd_2015268 : Nat := 4983230072969 + 3 ^ 40 * 2015268 * 2
def baseEnd_2015268 : Nat := 689867421083417658921305

theorem tailTrace_2015268 : CollatzResearch.WordTrace tailWord_2015268 prefixEnd_2015268 689867421083417658921305 := by
  unfold tailWord_2015268
  simp only [CollatzResearch.WordTrace]
  refine ⟨36751431231517845608955229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49001908308690460811940305 36751431231517845608955229)
  ·
    refine ⟨13781786711819192103358211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36751431231517845608955229 13781786711819192103358211)
    ·
      refine ⟨20672680067728788155037317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13781786711819192103358211 20672680067728788155037317)
      ·
        refine ⟨3876127512699147779069497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20672680067728788155037317 3876127512699147779069497)
        ·
          refine ⟨2907095634524360834302123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876127512699147779069497 2907095634524360834302123)
          ·
            refine ⟨4360643451786541251453185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2907095634524360834302123 4360643451786541251453185)
            ·
              refine ⟨3270482588839905938589889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360643451786541251453185 3270482588839905938589889)
              ·
                refine ⟨2452861941629929453942417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270482588839905938589889 2452861941629929453942417)
                ·
                  refine ⟨1839646456222447090456813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2452861941629929453942417 1839646456222447090456813)
                  ·
                    refine ⟨689867421083417658921305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839646456222447090456813 689867421083417658921305)
                    ·
                      rfl

theorem cell22_2015268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_2015268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015268 prefixEnd_2015268 := by exact prefixLift 2015268
  have htrace : WordTrace (prefixWord ++ tailWord_2015268) baseStart_2015268 baseEnd_2015268 := by
    simpa [prefixWord, tailWord_2015268, baseEnd_2015268] using wordTrace_append hprefix tailTrace_2015268
  have hstable : (prefixWord ++ tailWord_2015268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015268).length < 2 ^ (prefixWord ++ tailWord_2015268).sum := by decide
  have hdescent : baseEnd_2015268 < baseStart_2015268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015309 : List Nat := [1, 6, 1, 1, 1, 1, 2, 2, 7]
def baseStart_2015309 : Nat := 118140960795 + 2015309 * 2 ^ 59
def prefixEnd_2015309 : Nat := 4983230072969 + 3 ^ 40 * 2015309 * 2
def baseEnd_2015309 : Nat := 229960485407102406215393

theorem tailTrace_2015309 : CollatzResearch.WordTrace tailWord_2015309 prefixEnd_2015309 229960485407102406215393 := by
  unfold tailWord_2015309
  simp only [CollatzResearch.WordTrace]
  refine ⟨73504357855887155220152981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49002905237258103480101987 73504357855887155220152981)
  ·
    refine ⟨3445516774494710400944671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73504357855887155220152981 3445516774494710400944671)
    ·
      refine ⟨5168275161742065601417007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445516774494710400944671 5168275161742065601417007)
      ·
        refine ⟨7752412742613098402125511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168275161742065601417007 7752412742613098402125511)
        ·
          refine ⟨11628619113919647603188267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752412742613098402125511 11628619113919647603188267)
          ·
            refine ⟨17442928670879471404782401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11628619113919647603188267 17442928670879471404782401)
            ·
              refine ⟨13082196503159603553586801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17442928670879471404782401 13082196503159603553586801)
              ·
                refine ⟨9811647377369702665190101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082196503159603553586801 9811647377369702665190101)
                ·
                  refine ⟨229960485407102406215393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9811647377369702665190101 229960485407102406215393)
                  ·
                    rfl

theorem cell22_2015309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_2015309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015309 prefixEnd_2015309 := by exact prefixLift 2015309
  have htrace : WordTrace (prefixWord ++ tailWord_2015309) baseStart_2015309 baseEnd_2015309 := by
    simpa [prefixWord, tailWord_2015309, baseEnd_2015309] using wordTrace_append hprefix tailTrace_2015309
  have hstable : (prefixWord ++ tailWord_2015309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015309).length < 2 ^ (prefixWord ++ tailWord_2015309).sum := by decide
  have hdescent : baseEnd_2015309 < baseStart_2015309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015324 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2015324 : Nat := 118140960795 + 2015324 * 2 ^ 59
def prefixEnd_2015324 : Nat := 4983230072969 + 3 ^ 40 * 2015324 * 2
def baseEnd_2015324 : Nat := 689886591027852179521133

theorem tailTrace_2015324 : CollatzResearch.WordTrace tailWord_2015324 prefixEnd_2015324 689886591027852179521133 := by
  unfold tailWord_2015324
  simp only [CollatzResearch.WordTrace]
  refine ⟨36752452475416406390974513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49003269967221875187966017 36752452475416406390974513)
  ·
    refine ⟨27564339356562304793230885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36752452475416406390974513 27564339356562304793230885)
    ·
      refine ⟨5168313629355432148730791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27564339356562304793230885 5168313629355432148730791)
      ·
        refine ⟨7752470444033148223096187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168313629355432148730791 7752470444033148223096187)
        ·
          refine ⟨11628705666049722334644281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752470444033148223096187 11628705666049722334644281)
          ·
            refine ⟨8721529249537291750983211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11628705666049722334644281 8721529249537291750983211)
            ·
              refine ⟨13082293874305937626474817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8721529249537291750983211 13082293874305937626474817)
              ·
                refine ⟨9811720405729453219856113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082293874305937626474817 9811720405729453219856113)
                ·
                  refine ⟨7358790304297089914892085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9811720405729453219856113 7358790304297089914892085)
                  ·
                    refine ⟨689886591027852179521133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7358790304297089914892085 689886591027852179521133)
                    ·
                      rfl

theorem cell22_2015324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2015324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015324 prefixEnd_2015324 := by exact prefixLift 2015324
  have htrace : WordTrace (prefixWord ++ tailWord_2015324) baseStart_2015324 baseEnd_2015324 := by
    simpa [prefixWord, tailWord_2015324, baseEnd_2015324] using wordTrace_append hprefix tailTrace_2015324
  have hstable : (prefixWord ++ tailWord_2015324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015324).length < 2 ^ (prefixWord ++ tailWord_2015324).sum := by decide
  have hdescent : baseEnd_2015324 < baseStart_2015324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015356 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_2015356 : Nat := 118140960795 + 2015356 * 2 ^ 59
def prefixEnd_2015356 : Nat := 4983230072969 + 3 ^ 40 * 2015356 * 2
def baseEnd_2015356 : Nat := 689897545281814762721035

theorem tailTrace_2015356 : CollatzResearch.WordTrace tailWord_2015356 prefixEnd_2015356 689897545281814762721035 := by
  unfold tailWord_2015356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36753036043358441123556961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49004048057811254831409281 36753036043358441123556961)
  ·
    refine ⟨27564777032518830842667721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36753036043358441123556961 27564777032518830842667721)
    ·
      refine ⟨20673582774389123132000791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27564777032518830842667721 20673582774389123132000791)
      ·
        refine ⟨31010374161583684698001187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20673582774389123132000791 31010374161583684698001187)
        ·
          refine ⟨46515561242375527047001781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31010374161583684698001187 46515561242375527047001781)
          ·
            refine ⟨4360833866472705660656417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46515561242375527047001781 4360833866472705660656417)
            ·
              refine ⟨3270625399854529245492313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4360833866472705660656417 3270625399854529245492313)
              ·
                refine ⟨2452969049890896934119235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270625399854529245492313 2452969049890896934119235)
                ·
                  refine ⟨3679453574836345401178853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2452969049890896934119235 3679453574836345401178853)
                  ·
                    refine ⟨689897545281814762721035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679453574836345401178853 689897545281814762721035)
                    ·
                      rfl

theorem cell22_2015356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_2015356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015356 prefixEnd_2015356 := by exact prefixLift 2015356
  have htrace : WordTrace (prefixWord ++ tailWord_2015356) baseStart_2015356 baseEnd_2015356 := by
    simpa [prefixWord, tailWord_2015356, baseEnd_2015356] using wordTrace_append hprefix tailTrace_2015356
  have hstable : (prefixWord ++ tailWord_2015356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015356).length < 2 ^ (prefixWord ++ tailWord_2015356).sum := by decide
  have hdescent : baseEnd_2015356 < baseStart_2015356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015369 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_2015369 : Nat := 118140960795 + 2015369 * 2 ^ 59
def prefixEnd_2015369 : Nat := 4983230072969 + 3 ^ 40 * 2015369 * 2
def baseEnd_2015369 : Nat := 689901995447487062145995

theorem tailTrace_2015369 : CollatzResearch.WordTrace tailWord_2015369 prefixEnd_2015369 689901995447487062145995 := by
  unfold tailWord_2015369
  simp only [CollatzResearch.WordTrace]
  refine ⟨73506546235669785467337161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49004364157113190311558107 73506546235669785467337161)
  ·
    refine ⟨55129909676752339100502871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73506546235669785467337161 55129909676752339100502871)
    ·
      refine ⟨82694864515128508650754307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55129909676752339100502871 82694864515128508650754307)
      ·
        refine ⟨124042296772692762976131461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82694864515128508650754307 124042296772692762976131461)
        ·
          refine ⟨23257930644879893058024649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124042296772692762976131461 23257930644879893058024649)
          ·
            refine ⟨17443447983659919793518487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23257930644879893058024649 17443447983659919793518487)
            ·
              refine ⟨26165171975489879690277731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17443447983659919793518487 26165171975489879690277731)
              ·
                refine ⟨39247757963234819535416597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26165171975489879690277731 39247757963234819535416597)
                ·
                  refine ⟨1839738654526632165722653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39247757963234819535416597 1839738654526632165722653)
                  ·
                    refine ⟨689901995447487062145995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839738654526632165722653 689901995447487062145995)
                    ·
                      rfl

theorem cell22_2015369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_2015369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015369 prefixEnd_2015369 := by exact prefixLift 2015369
  have htrace : WordTrace (prefixWord ++ tailWord_2015369) baseStart_2015369 baseEnd_2015369 := by
    simpa [prefixWord, tailWord_2015369, baseEnd_2015369] using wordTrace_append hprefix tailTrace_2015369
  have hstable : (prefixWord ++ tailWord_2015369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015369).length < 2 ^ (prefixWord ++ tailWord_2015369).sum := by decide
  have hdescent : baseEnd_2015369 < baseStart_2015369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015388 : List Nat := [2, 2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_2015388 : Nat := 118140960795 + 2015388 * 2 ^ 59
def prefixEnd_2015388 : Nat := 4983230072969 + 3 ^ 40 * 2015388 * 2
def baseEnd_2015388 : Nat := 229969499845259115306979

theorem tailTrace_2015388 : CollatzResearch.WordTrace tailWord_2015388 prefixEnd_2015388 229969499845259115306979 := by
  unfold tailWord_2015388
  simp only [CollatzResearch.WordTrace]
  refine ⟨36753619611300475856139409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49004826148400634474852545 36753619611300475856139409)
  ·
    refine ⟨27565214708475356892104557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36753619611300475856139409 27565214708475356892104557)
    ·
      refine ⟨10336955515678258834539209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27565214708475356892104557 10336955515678258834539209)
      ·
        refine ⟨7752716636758694125904407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10336955515678258834539209 7752716636758694125904407)
        ·
          refine ⟨11629074955138041188856611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752716636758694125904407 11629074955138041188856611)
          ·
            refine ⟨17443612432707061783284917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629074955138041188856611 17443612432707061783284917)
            ·
              refine ⟨1635338665566287042182961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17443612432707061783284917 1635338665566287042182961)
              ·
                refine ⟨1226503999174715281637221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635338665566287042182961 1226503999174715281637221)
                ·
                  refine ⟨229969499845259115306979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226503999174715281637221 229969499845259115306979)
                  ·
                    rfl

theorem cell22_2015388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_2015388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015388 prefixEnd_2015388 := by exact prefixLift 2015388
  have htrace : WordTrace (prefixWord ++ tailWord_2015388) baseStart_2015388 baseEnd_2015388 := by
    simpa [prefixWord, tailWord_2015388, baseEnd_2015388] using wordTrace_append hprefix tailTrace_2015388
  have hstable : (prefixWord ++ tailWord_2015388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015388).length < 2 ^ (prefixWord ++ tailWord_2015388).sum := by decide
  have hdescent : baseEnd_2015388 < baseStart_2015388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015461 : List Nat := [1, 3, 1, 4, 2, 1, 2, 3, 5]
def baseStart_2015461 : Nat := 118140960795 + 2015461 * 2 ^ 59
def prefixEnd_2015461 : Nat := 4983230072969 + 3 ^ 40 * 2015461 * 2
def baseEnd_2015461 : Nat := 229977829642543162948571

theorem tailTrace_2015461 : CollatzResearch.WordTrace tailWord_2015461 prefixEnd_2015461 229977829642543162948571 := by
  unfold tailWord_2015461
  simp only [CollatzResearch.WordTrace]
  refine ⟨73509901751336485179686237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49006601167557656786457491 73509901751336485179686237)
  ·
    refine ⟨27566213156751181942382339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73509901751336485179686237 27566213156751181942382339)
    ·
      refine ⟨41349319735126772913573509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27566213156751181942382339 41349319735126772913573509)
      ·
        refine ⟨7752997450336269921295033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41349319735126772913573509 7752997450336269921295033)
        ·
          refine ⟨5814748087752202440971275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7752997450336269921295033 5814748087752202440971275)
          ·
            refine ⟨8722122131628303661456913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814748087752202440971275 8722122131628303661456913)
            ·
              refine ⟨6541591598721227746092685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8722122131628303661456913 6541591598721227746092685)
              ·
                refine ⟨2453096849520460404784757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6541591598721227746092685 2453096849520460404784757)
                ·
                  refine ⟨229977829642543162948571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2453096849520460404784757 229977829642543162948571)
                  ·
                    rfl

theorem cell22_2015461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_2015461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015461 prefixEnd_2015461 := by exact prefixLift 2015461
  have htrace : WordTrace (prefixWord ++ tailWord_2015461) baseStart_2015461 baseEnd_2015461 := by
    simpa [prefixWord, tailWord_2015461, baseEnd_2015461] using wordTrace_append hprefix tailTrace_2015461
  have hstable : (prefixWord ++ tailWord_2015461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015461).length < 2 ^ (prefixWord ++ tailWord_2015461).sum := by decide
  have hdescent : baseEnd_2015461 < baseStart_2015461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015489 : List Nat := [1, 2, 4, 1, 1, 2, 1, 2, 8]
def baseStart_2015489 : Nat := 118140960795 + 2015489 * 2 ^ 59
def prefixEnd_2015489 : Nat := 4983230072969 + 3 ^ 40 * 2015489 * 2
def baseEnd_2015489 : Nat := 229981024633282249715209

theorem tailTrace_2015489 : CollatzResearch.WordTrace tailWord_2015489 prefixEnd_2015489 229981024633282249715209 := by
  unfold tailWord_2015489
  simp only [CollatzResearch.WordTrace]
  refine ⟨73510922995235045961705521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49007281996823363974470347 73510922995235045961705521)
  ·
    refine ⟨55133192246426284471279141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73510922995235045961705521 55133192246426284471279141)
    ·
      refine ⟨10337473546204928338364839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55133192246426284471279141 10337473546204928338364839)
      ·
        refine ⟨15506210319307392507547259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10337473546204928338364839 15506210319307392507547259)
        ·
          refine ⟨23259315478961088761320889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15506210319307392507547259 23259315478961088761320889)
          ·
            refine ⟨17444486609220816570990667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23259315478961088761320889 17444486609220816570990667)
            ·
              refine ⟨26166729913831224856486001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17444486609220816570990667 26166729913831224856486001)
              ·
                refine ⟨19625047435373418642364501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26166729913831224856486001 19625047435373418642364501)
                ·
                  refine ⟨229981024633282249715209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19625047435373418642364501 229981024633282249715209)
                  ·
                    rfl

theorem cell22_2015489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_2015489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015489 prefixEnd_2015489 := by exact prefixLift 2015489
  have htrace : WordTrace (prefixWord ++ tailWord_2015489) baseStart_2015489 baseEnd_2015489 := by
    simpa [prefixWord, tailWord_2015489, baseEnd_2015489] using wordTrace_append hprefix tailTrace_2015489
  have hstable : (prefixWord ++ tailWord_2015489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015489).length < 2 ^ (prefixWord ++ tailWord_2015489).sum := by decide
  have hdescent : baseEnd_2015489 < baseStart_2015489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015491 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 1, 4]
def baseStart_2015491 : Nat := 118140960795 + 2015491 * 2 ^ 59
def prefixEnd_2015491 : Nat := 4983230072969 + 3 ^ 40 * 2015491 * 2
def baseEnd_2015491 : Nat := 689943758540719410595621

theorem tailTrace_2015491 : CollatzResearch.WordTrace tailWord_2015491 prefixEnd_2015491 689943758540719410595621 := by
  unfold tailWord_2015491
  simp only [CollatzResearch.WordTrace]
  refine ⟨73510995941227800303278327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49007330627485200202185551 73510995941227800303278327)
  ·
    refine ⟨110266493911841700454917491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73510995941227800303278327 110266493911841700454917491)
    ·
      refine ⟨165399740867762550682376237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110266493911841700454917491 165399740867762550682376237)
      ·
        refine ⟨62024902825410956505891089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165399740867762550682376237 62024902825410956505891089)
        ·
          refine ⟨46518677119058217379418317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62024902825410956505891089 46518677119058217379418317)
          ·
            refine ⟨17444503919646831517281869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46518677119058217379418317 17444503919646831517281869)
            ·
              refine ⟨6541688969867561818980701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17444503919646831517281869 6541688969867561818980701)
              ·
                refine ⟨2453133363700335682117763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6541688969867561818980701 2453133363700335682117763)
                ·
                  refine ⟨3679700045550503523176645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453133363700335682117763 3679700045550503523176645)
                  ·
                    refine ⟨689943758540719410595621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3679700045550503523176645 689943758540719410595621)
                    ·
                      rfl

theorem cell22_2015491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 4].length) (baseStart_2015491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015491 prefixEnd_2015491 := by exact prefixLift 2015491
  have htrace : WordTrace (prefixWord ++ tailWord_2015491) baseStart_2015491 baseEnd_2015491 := by
    simpa [prefixWord, tailWord_2015491, baseEnd_2015491] using wordTrace_append hprefix tailTrace_2015491
  have hstable : (prefixWord ++ tailWord_2015491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015491).length < 2 ^ (prefixWord ++ tailWord_2015491).sum := by decide
  have hdescent : baseEnd_2015491 < baseStart_2015491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015495 : List Nat := [1, 1, 4, 5, 1, 2, 1, 2, 5]
def baseStart_2015495 : Nat := 118140960795 + 2015495 * 2 ^ 59
def prefixEnd_2015495 : Nat := 4983230072969 + 3 ^ 40 * 2015495 * 2
def baseEnd_2015495 : Nat := 229981709274154911165203

theorem tailTrace_2015495 : CollatzResearch.WordTrace tailWord_2015495 prefixEnd_2015495 229981709274154911165203 := by
  unfold tailWord_2015495
  simp only [CollatzResearch.WordTrace]
  refine ⟨73511141833213308986423939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49007427888808872657615959 73511141833213308986423939)
  ·
    refine ⟨110266712749819963479635909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73511141833213308986423939 110266712749819963479635909)
    ·
      refine ⟨20675008640591243152431733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110266712749819963479635909 20675008640591243152431733)
      ·
        refine ⟨1938282060055429045540475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20675008640591243152431733 1938282060055429045540475)
        ·
          refine ⟨2907423090083143568310713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938282060055429045540475 2907423090083143568310713)
          ·
            refine ⟨2180567317562357676233035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907423090083143568310713 2180567317562357676233035)
            ·
              refine ⟨3270850976343536514349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180567317562357676233035 3270850976343536514349553)
              ·
                refine ⟨2453138232257652385762165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3270850976343536514349553 2453138232257652385762165)
                ·
                  refine ⟨229981709274154911165203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2453138232257652385762165 229981709274154911165203)
                  ·
                    rfl

theorem cell22_2015495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 2, 5].length) (baseStart_2015495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015495 prefixEnd_2015495 := by exact prefixLift 2015495
  have htrace : WordTrace (prefixWord ++ tailWord_2015495) baseStart_2015495 baseEnd_2015495 := by
    simpa [prefixWord, tailWord_2015495, baseEnd_2015495] using wordTrace_append hprefix tailTrace_2015495
  have hstable : (prefixWord ++ tailWord_2015495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015495).length < 2 ^ (prefixWord ++ tailWord_2015495).sum := by decide
  have hdescent : baseEnd_2015495 < baseStart_2015495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015521 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_2015521 : Nat := 118140960795 + 2015521 * 2 ^ 59
def prefixEnd_2015521 : Nat := 4983230072969 + 3 ^ 40 * 2015521 * 2
def baseEnd_2015521 : Nat := 689954028153809332345529

theorem tailTrace_2015521 : CollatzResearch.WordTrace tailWord_2015521 prefixEnd_2015521 689954028153809332345529 := by
  unfold tailWord_2015521
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512090131119115426870417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49008060087412743617913611 73512090131119115426870417)
  ·
    refine ⟨55134067598339336570152813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73512090131119115426870417 55134067598339336570152813)
    ·
      refine ⟨20675275349377251213807305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55134067598339336570152813 20675275349377251213807305)
      ·
        refine ⟨15506456512032938410355479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20675275349377251213807305 15506456512032938410355479)
        ·
          refine ⟨23259684768049407615533219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15506456512032938410355479 23259684768049407615533219)
          ·
            refine ⟨34889527152074111423299829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23259684768049407615533219 34889527152074111423299829)
            ·
              refine ⟨3270893170506947945934359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34889527152074111423299829 3270893170506947945934359)
              ·
                refine ⟨4906339755760421918901539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3270893170506947945934359 4906339755760421918901539)
                ·
                  refine ⟨7359509633640632878352309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906339755760421918901539 7359509633640632878352309)
                  ·
                    refine ⟨689954028153809332345529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7359509633640632878352309 689954028153809332345529)
                    ·
                      rfl

theorem cell22_2015521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_2015521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015521 prefixEnd_2015521 := by exact prefixLift 2015521
  have htrace : WordTrace (prefixWord ++ tailWord_2015521) baseStart_2015521 baseEnd_2015521 := by
    simpa [prefixWord, tailWord_2015521, baseEnd_2015521] using wordTrace_append hprefix tailTrace_2015521
  have hstable : (prefixWord ++ tailWord_2015521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015521).length < 2 ^ (prefixWord ++ tailWord_2015521).sum := by decide
  have hdescent : baseEnd_2015521 < baseStart_2015521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015540 : List Nat := [2, 5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2015540 : Nat := 118140960795 + 2015540 * 2 ^ 59
def prefixEnd_2015540 : Nat := 4983230072969 + 3 ^ 40 * 2015540 * 2
def baseEnd_2015540 : Nat := 229986844080699872040157

theorem tailTrace_2015540 : CollatzResearch.WordTrace tailWord_2015540 prefixEnd_2015540 229986844080699872040157 := by
  unfold tailWord_2015540
  simp only [CollatzResearch.WordTrace]
  refine ⟨36756391559025140835906037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49008522078700187781208049 36756391559025140835906037)
  ·
    refine ⟨3445911708658606953366191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36756391559025140835906037 3445911708658606953366191)
    ·
      refine ⟨5168867562987910430049287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445911708658606953366191 5168867562987910430049287)
      ·
        refine ⟨7753301344481865645073931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168867562987910430049287 7753301344481865645073931)
        ·
          refine ⟨11629952016722798467610897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753301344481865645073931 11629952016722798467610897)
          ·
            refine ⟨8722464012542098850708173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11629952016722798467610897 8722464012542098850708173)
            ·
              refine ⟨3270924004703287069015565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8722464012542098850708173 3270924004703287069015565)
              ·
                refine ⟨1226596501763732650880837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3270924004703287069015565 1226596501763732650880837)
                ·
                  refine ⟨229986844080699872040157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226596501763732650880837 229986844080699872040157)
                  ·
                    rfl

theorem cell22_2015540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2015540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015540 prefixEnd_2015540 := by exact prefixLift 2015540
  have htrace : WordTrace (prefixWord ++ tailWord_2015540) baseStart_2015540 baseEnd_2015540 := by
    simpa [prefixWord, tailWord_2015540, baseEnd_2015540] using wordTrace_append hprefix tailTrace_2015540
  have hstable : (prefixWord ++ tailWord_2015540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015540).length < 2 ^ (prefixWord ++ tailWord_2015540).sum := by decide
  have hdescent : baseEnd_2015540 < baseStart_2015540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015572 : List Nat := [2, 4, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_2015572 : Nat := 118140960795 + 2015572 * 2 ^ 59
def prefixEnd_2015572 : Nat := 4983230072969 + 3 ^ 40 * 2015572 * 2
def baseEnd_2015572 : Nat := 689971486496062199320373

theorem tailTrace_2015572 : CollatzResearch.WordTrace tailWord_2015572 prefixEnd_2015572 689971486496062199320373 := by
  unfold tailWord_2015572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36756975126967175568488485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49009300169289567424651313 36756975126967175568488485)
  ·
    refine ⟨6891932836306345419091591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36756975126967175568488485 6891932836306345419091591)
    ·
      refine ⟨10337899254459518128637387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6891932836306345419091591 10337899254459518128637387)
      ·
        refine ⟨15506848881689277192956081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10337899254459518128637387 15506848881689277192956081)
        ·
          refine ⟨11630136661266957894717061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15506848881689277192956081 11630136661266957894717061)
          ·
            refine ⟨2180650623987554605259449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11630136661266957894717061 2180650623987554605259449)
            ·
              refine ⟨1635487967990665953944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180650623987554605259449 1635487967990665953944587)
              ·
                refine ⟨2453231951985998930916881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635487967990665953944587 2453231951985998930916881)
                ·
                  refine ⟨1839923963989499198187661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453231951985998930916881 1839923963989499198187661)
                  ·
                    refine ⟨689971486496062199320373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839923963989499198187661 689971486496062199320373)
                    ·
                      rfl

theorem cell22_2015572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_2015572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015572 prefixEnd_2015572 := by exact prefixLift 2015572
  have htrace : WordTrace (prefixWord ++ tailWord_2015572) baseStart_2015572 baseEnd_2015572 := by
    simpa [prefixWord, tailWord_2015572, baseEnd_2015572] using wordTrace_append hprefix tailTrace_2015572
  have hstable : (prefixWord ++ tailWord_2015572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015572).length < 2 ^ (prefixWord ++ tailWord_2015572).sum := by decide
  have hdescent : baseEnd_2015572 < baseStart_2015572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015613 : List Nat := [1, 4, 1, 1, 2, 4, 2, 2, 5]
def baseStart_2015613 : Nat := 118140960795 + 2015613 * 2 ^ 59
def prefixEnd_2015613 : Nat := 4983230072969 + 3 ^ 40 * 2015613 * 2
def baseEnd_2015613 : Nat := 229995173877983919681749

theorem tailTrace_2015613 : CollatzResearch.WordTrace tailWord_2015613 prefixEnd_2015613 229995173877983919681749 := by
  unfold tailWord_2015613
  simp only [CollatzResearch.WordTrace]
  refine ⟨73515445646785815139219493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49010297097857210092812995 73515445646785815139219493)
  ·
    refine ⟨13784146058772340338603655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73515445646785815139219493 13784146058772340338603655)
    ·
      refine ⟨20676219088158510507905483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13784146058772340338603655 20676219088158510507905483)
      ·
        refine ⟨31014328632237765761858225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20676219088158510507905483 31014328632237765761858225)
        ·
          refine ⟨23260746474178324321393669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31014328632237765761858225 23260746474178324321393669)
          ·
            refine ⟨4361389963908435810261313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23260746474178324321393669 4361389963908435810261313)
            ·
              refine ⟨3271042472931326857695985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361389963908435810261313 3271042472931326857695985)
              ·
                refine ⟨2453281854698495143271989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271042472931326857695985 2453281854698495143271989)
                ·
                  refine ⟨229995173877983919681749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2453281854698495143271989 229995173877983919681749)
                  ·
                    rfl

theorem cell22_2015613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_2015613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015613 prefixEnd_2015613 := by exact prefixLift 2015613
  have htrace : WordTrace (prefixWord ++ tailWord_2015613) baseStart_2015613 baseEnd_2015613 := by
    simpa [prefixWord, tailWord_2015613, baseEnd_2015613] using wordTrace_append hprefix tailTrace_2015613
  have hstable : (prefixWord ++ tailWord_2015613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015613).length < 2 ^ (prefixWord ++ tailWord_2015613).sum := by decide
  have hdescent : baseEnd_2015613 < baseStart_2015613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015617 : List Nat := [1, 2, 4, 3, 1, 2, 1, 4, 1, 3]
def baseStart_2015617 : Nat := 118140960795 + 2015617 * 2 ^ 59
def prefixEnd_2015617 : Nat := 4983230072969 + 3 ^ 40 * 2015617 * 2
def baseEnd_2015617 : Nat := 689986890915697081945235

theorem tailTrace_2015617 : CollatzResearch.WordTrace tailWord_2015617 prefixEnd_2015617 689986890915697081945235 := by
  unfold tailWord_2015617
  simp only [CollatzResearch.WordTrace]
  refine ⟨73515591538771323822365105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49010394359180882548243403 73515591538771323822365105)
  ·
    refine ⟨55136693654078492866773829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73515591538771323822365105 55136693654078492866773829)
    ·
      refine ⟨10338130060139717412520093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55136693654078492866773829 10338130060139717412520093)
      ·
        refine ⟨3876798772552394029695035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10338130060139717412520093 3876798772552394029695035)
        ·
          refine ⟨5815198158828591044542553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876798772552394029695035 5815198158828591044542553)
          ·
            refine ⟨4361398619121443283406915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5815198158828591044542553 4361398619121443283406915)
            ·
              refine ⟨6542097928682164925110373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361398619121443283406915 6542097928682164925110373)
              ·
                refine ⟨1226643361627905923458195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6542097928682164925110373 1226643361627905923458195)
                ·
                  refine ⟨1839965042441858885187293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226643361627905923458195 1839965042441858885187293)
                  ·
                    refine ⟨689986890915697081945235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1839965042441858885187293 689986890915697081945235)
                    ·
                      rfl

theorem cell22_2015617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_2015617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015617 prefixEnd_2015617 := by exact prefixLift 2015617
  have htrace : WordTrace (prefixWord ++ tailWord_2015617) baseStart_2015617 baseEnd_2015617 := by
    simpa [prefixWord, tailWord_2015617, baseEnd_2015617] using wordTrace_append hprefix tailTrace_2015617
  have hstable : (prefixWord ++ tailWord_2015617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015617).length < 2 ^ (prefixWord ++ tailWord_2015617).sum := by decide
  have hdescent : baseEnd_2015617 < baseStart_2015617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015641 : List Nat := [1, 2, 1, 2, 1, 4, 3, 2, 6]
def baseStart_2015641 : Nat := 118140960795 + 2015641 * 2 ^ 59
def prefixEnd_2015641 : Nat := 4983230072969 + 3 ^ 40 * 2015641 * 2
def baseEnd_2015641 : Nat := 229998368868723006448387

theorem tailTrace_2015641 : CollatzResearch.WordTrace tailWord_2015641 prefixEnd_2015641 229998368868723006448387 := by
  unfold tailWord_2015641
  simp only [CollatzResearch.WordTrace]
  refine ⟨73516466890684375921238777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49010977927122917280825851 73516466890684375921238777)
  ·
    refine ⟨55137350168013281940929083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73516466890684375921238777 55137350168013281940929083)
    ·
      refine ⟨82706025252019922911393625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55137350168013281940929083 82706025252019922911393625)
      ·
        refine ⟨62029518939014942183545219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82706025252019922911393625 62029518939014942183545219)
        ·
          refine ⟨93044278408522413275317829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62029518939014942183545219 93044278408522413275317829)
          ·
            refine ⟨17445802201597952489122093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93044278408522413275317829 17445802201597952489122093)
            ·
              refine ⟨6542175825599232183420785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17445802201597952489122093 6542175825599232183420785)
              ·
                refine ⟨4906631869199424137565589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6542175825599232183420785 4906631869199424137565589)
                ·
                  refine ⟨229998368868723006448387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4906631869199424137565589 229998368868723006448387)
                  ·
                    rfl

theorem cell22_2015641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_2015641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015641 prefixEnd_2015641 := by exact prefixLift 2015641
  have htrace : WordTrace (prefixWord ++ tailWord_2015641) baseStart_2015641 baseEnd_2015641 := by
    simpa [prefixWord, tailWord_2015641, baseEnd_2015641] using wordTrace_append hprefix tailTrace_2015641
  have hstable : (prefixWord ++ tailWord_2015641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015641).length < 2 ^ (prefixWord ++ tailWord_2015641).sum := by decide
  have hdescent : baseEnd_2015641 < baseStart_2015641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015716 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_2015716 : Nat := 118140960795 + 2015716 * 2 ^ 59
def prefixEnd_2015716 : Nat := 4983230072969 + 3 ^ 40 * 2015716 * 2
def baseEnd_2015716 : Nat := 690020780638893823719931

theorem tailTrace_2015716 : CollatzResearch.WordTrace tailWord_2015716 prefixEnd_2015716 690020780638893823719931 := by
  unfold tailWord_2015716
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759601182706331865109501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49012801576941775820146001 36759601182706331865109501)
  ·
    refine ⟨13784850443514874449416063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36759601182706331865109501 13784850443514874449416063)
    ·
      refine ⟨20677275665272311674124095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13784850443514874449416063 20677275665272311674124095)
      ·
        refine ⟨31015913497908467511186143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20677275665272311674124095 31015913497908467511186143)
        ·
          refine ⟨46523870246862701266779215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31015913497908467511186143 46523870246862701266779215)
          ·
            refine ⟨69785805370294051900168823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46523870246862701266779215 69785805370294051900168823)
            ·
              refine ⟨104678708055441077850253235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69785805370294051900168823 104678708055441077850253235)
              ·
                refine ⟨157018062083161616775379853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104678708055441077850253235 157018062083161616775379853)
                ·
                  refine ⟨58881773281185606290767445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157018062083161616775379853 58881773281185606290767445)
                  ·
                    refine ⟨690020780638893823719931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58881773281185606290767445 690020780638893823719931)
                    ·
                      rfl

theorem cell22_2015716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_2015716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015716 prefixEnd_2015716 := by exact prefixLift 2015716
  have htrace : WordTrace (prefixWord ++ tailWord_2015716) baseStart_2015716 baseEnd_2015716 := by
    simpa [prefixWord, tailWord_2015716, baseEnd_2015716] using wordTrace_append hprefix tailTrace_2015716
  have hstable : (prefixWord ++ tailWord_2015716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015716).length < 2 ^ (prefixWord ++ tailWord_2015716).sum := by decide
  have hdescent : baseEnd_2015716 < baseStart_2015716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015731 : List Nat := [1, 1, 1, 2, 2, 2, 3, 3, 7]
def baseStart_2015731 : Nat := 118140960795 + 2015731 * 2 ^ 59
def prefixEnd_2015731 : Nat := 4983230072969 + 3 ^ 40 * 2015731 * 2
def baseEnd_2015731 : Nat := 230008638481812928198295

theorem tailTrace_2015731 : CollatzResearch.WordTrace tailWord_2015731 prefixEnd_2015731 230008638481812928198295 := by
  unfold tailWord_2015731
  simp only [CollatzResearch.WordTrace]
  refine ⟨73519749460358321292015047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49013166306905547528010031 73519749460358321292015047)
  ·
    refine ⟨110279624190537481938022571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73519749460358321292015047 110279624190537481938022571)
    ·
      refine ⟨165419436285806222907033857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110279624190537481938022571 165419436285806222907033857)
      ·
        refine ⟨124064577214354667180275393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165419436285806222907033857 124064577214354667180275393)
        ·
          refine ⟨93048432910766000385206545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124064577214354667180275393 93048432910766000385206545)
          ·
            refine ⟨69786324683074500288904909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93048432910766000385206545 69786324683074500288904909)
            ·
              refine ⟨26169871756152937608339341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69786324683074500288904909 26169871756152937608339341)
              ·
                refine ⟨9813701908557351603127253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26169871756152937608339341 9813701908557351603127253)
                ·
                  refine ⟨230008638481812928198295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9813701908557351603127253 230008638481812928198295)
                  ·
                    rfl

theorem cell22_2015731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_2015731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015731 prefixEnd_2015731 := by exact prefixLift 2015731
  have htrace : WordTrace (prefixWord ++ tailWord_2015731) baseStart_2015731 baseEnd_2015731 := by
    simpa [prefixWord, tailWord_2015731, baseEnd_2015731] using wordTrace_append hprefix tailTrace_2015731
  have hstable : (prefixWord ++ tailWord_2015731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015731).length < 2 ^ (prefixWord ++ tailWord_2015731).sum := by decide
  have hdescent : baseEnd_2015731 < baseStart_2015731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015786 : List Nat := [3, 1, 4, 1, 1, 4, 2, 2, 1, 3]
def baseStart_2015786 : Nat := 118140960795 + 2015786 * 2 ^ 59
def prefixEnd_2015786 : Nat := 4983230072969 + 3 ^ 40 * 2015786 * 2
def baseEnd_2015786 : Nat := 690044743069436974469717

theorem tailTrace_2015786 : CollatzResearch.WordTrace tailWord_2015786 prefixEnd_2015786 690044743069436974469717 := by
  unfold tailWord_2015786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18380438868789766421316803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49014503650106043790178141 18380438868789766421316803)
  ·
    refine ⟨27570658303184649631975205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18380438868789766421316803 27570658303184649631975205)
    ·
      refine ⟨5169498431847121805995351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27570658303184649631975205 5169498431847121805995351)
      ·
        refine ⟨7754247647770682708993027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169498431847121805995351 7754247647770682708993027)
        ·
          refine ⟨11631371471656024063489541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754247647770682708993027 11631371471656024063489541)
          ·
            refine ⟨2180882150935504511904289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11631371471656024063489541 2180882150935504511904289)
            ·
              refine ⟨1635661613201628383928217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180882150935504511904289 1635661613201628383928217)
              ·
                refine ⟨1226746209901221287946163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635661613201628383928217 1226746209901221287946163)
                ·
                  refine ⟨1840119314851831931919245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1226746209901221287946163 1840119314851831931919245)
                  ·
                    refine ⟨690044743069436974469717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840119314851831931919245 690044743069436974469717)
                    ·
                      rfl

theorem cell22_2015786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_2015786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015786 prefixEnd_2015786 := by exact prefixLift 2015786
  have htrace : WordTrace (prefixWord ++ tailWord_2015786) baseStart_2015786 baseEnd_2015786 := by
    simpa [prefixWord, tailWord_2015786, baseEnd_2015786] using wordTrace_append hprefix tailTrace_2015786
  have hstable : (prefixWord ++ tailWord_2015786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015786).length < 2 ^ (prefixWord ++ tailWord_2015786).sum := by decide
  have hdescent : baseEnd_2015786 < baseStart_2015786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015808 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_2015808 : Nat := 118140960795 + 2015808 * 2 ^ 59
def prefixEnd_2015808 : Nat := 4983230072969 + 3 ^ 40 * 2015808 * 2
def baseEnd_2015808 : Nat := 690052274119036250419649

theorem tailTrace_2015808 : CollatzResearch.WordTrace tailWord_2015808 prefixEnd_2015808 690052274119036250419649 := by
  unfold tailWord_2015808
  simp only [CollatzResearch.WordTrace]
  refine ⟨36761278940539681721284039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49015038587386242295045385 36761278940539681721284039)
  ·
    refine ⟨55141918410809522581926059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36761278940539681721284039 55141918410809522581926059)
    ·
      refine ⟨82712877616214283872889089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55141918410809522581926059 82712877616214283872889089)
      ·
        refine ⟨62034658212160712904666817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82712877616214283872889089 62034658212160712904666817)
        ·
          refine ⟨46525993659120534678500113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62034658212160712904666817 46525993659120534678500113)
          ·
            refine ⟨34894495244340401008875085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46525993659120534678500113 34894495244340401008875085)
            ·
              refine ⟨13085435716627650378328157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34894495244340401008875085 13085435716627650378328157)
              ·
                refine ⟨4907038393735368891873059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13085435716627650378328157 4907038393735368891873059)
                ·
                  refine ⟨7360557590603053337809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907038393735368891873059 7360557590603053337809589)
                  ·
                    refine ⟨690052274119036250419649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7360557590603053337809589 690052274119036250419649)
                    ·
                      rfl

theorem cell22_2015808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_2015808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015808 prefixEnd_2015808 := by exact prefixLift 2015808
  have htrace : WordTrace (prefixWord ++ tailWord_2015808) baseStart_2015808 baseEnd_2015808 := by
    simpa [prefixWord, tailWord_2015808, baseEnd_2015808] using wordTrace_append hprefix tailTrace_2015808
  have hstable : (prefixWord ++ tailWord_2015808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015808).length < 2 ^ (prefixWord ++ tailWord_2015808).sum := by decide
  have hdescent : baseEnd_2015808 < baseStart_2015808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015868 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_2015868 : Nat := 118140960795 + 2015868 * 2 ^ 59
def prefixEnd_2015868 : Nat := 4983230072969 + 3 ^ 40 * 2015868 * 2
def baseEnd_2015868 : Nat := 690072813345216093919465

theorem tailTrace_2015868 : CollatzResearch.WordTrace tailWord_2015868 prefixEnd_2015868 690072813345216093919465 := by
  unfold tailWord_2015868
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762373130430996844876129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49016497507241329126501505 36762373130430996844876129)
  ·
    refine ⟨27571779847823247633657097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36762373130430996844876129 27571779847823247633657097)
    ·
      refine ⟨20678834885867435725242823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27571779847823247633657097 20678834885867435725242823)
      ·
        refine ⟨31018252328801153587864235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20678834885867435725242823 31018252328801153587864235)
        ·
          refine ⟨46527378493201730381796353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018252328801153587864235 46527378493201730381796353)
          ·
            refine ⟨34895533869901297786347265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46527378493201730381796353 34895533869901297786347265)
            ·
              refine ⟨26171650402425973339760449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34895533869901297786347265 26171650402425973339760449)
              ·
                refine ⟨19628737801819480004820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26171650402425973339760449 19628737801819480004820337)
                ·
                  refine ⟨14721553351364610003615253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19628737801819480004820337 14721553351364610003615253)
                  ·
                    refine ⟨690072813345216093919465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14721553351364610003615253 690072813345216093919465)
                    ·
                      rfl

theorem cell22_2015868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_2015868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015868 prefixEnd_2015868 := by exact prefixLift 2015868
  have htrace : WordTrace (prefixWord ++ tailWord_2015868) baseStart_2015868 baseEnd_2015868 := by
    simpa [prefixWord, tailWord_2015868, baseEnd_2015868] using wordTrace_append hprefix tailTrace_2015868
  have hstable : (prefixWord ++ tailWord_2015868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015868).length < 2 ^ (prefixWord ++ tailWord_2015868).sum := by decide
  have hdescent : baseEnd_2015868 < baseStart_2015868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015900 : List Nat := [2, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_2015900 : Nat := 118140960795 + 2015900 * 2 ^ 59
def prefixEnd_2015900 : Nat := 4983230072969 + 3 ^ 40 * 2015900 * 2
def baseEnd_2015900 : Nat := 230027922533059559039789

theorem tailTrace_2015900 : CollatzResearch.WordTrace tailWord_2015900 prefixEnd_2015900 230027922533059559039789 := by
  unfold tailWord_2015900
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762956698373031577458577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49017275597830708769944769 36762956698373031577458577)
  ·
    refine ⟨27572217523779773683093933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36762956698373031577458577 27572217523779773683093933)
    ·
      refine ⟨10339581571417415131160225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27572217523779773683093933 10339581571417415131160225)
      ·
        refine ⟨7754686178563061348370169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10339581571417415131160225 7754686178563061348370169)
        ·
          refine ⟨5816014633922296011277627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7754686178563061348370169 5816014633922296011277627)
          ·
            refine ⟨8724021950883444016916441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816014633922296011277627 8724021950883444016916441)
            ·
              refine ⟨6543016463162583012687331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724021950883444016916441 6543016463162583012687331)
              ·
                refine ⟨9814524694743874519030997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543016463162583012687331 9814524694743874519030997)
                ·
                  refine ⟨230027922533059559039789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9814524694743874519030997 230027922533059559039789)
                  ·
                    rfl

theorem cell22_2015900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_2015900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015900 prefixEnd_2015900 := by exact prefixLift 2015900
  have htrace : WordTrace (prefixWord ++ tailWord_2015900) baseStart_2015900 baseEnd_2015900 := by
    simpa [prefixWord, tailWord_2015900, baseEnd_2015900] using wordTrace_append hprefix tailTrace_2015900
  have hstable : (prefixWord ++ tailWord_2015900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015900).length < 2 ^ (prefixWord ++ tailWord_2015900).sum := by decide
  have hdescent : baseEnd_2015900 < baseStart_2015900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015904 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 3, 3]
def baseStart_2015904 : Nat := 118140960795 + 2015904 * 2 ^ 59
def prefixEnd_2015904 : Nat := 4983230072969 + 3 ^ 40 * 2015904 * 2
def baseEnd_2015904 : Nat := 690085136880924000019355

theorem tailTrace_2015904 : CollatzResearch.WordTrace tailWord_2015904 prefixEnd_2015904 690085136880924000019355 := by
  unfold tailWord_2015904
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763029644365785919031383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49017372859154381225375177 36763029644365785919031383)
  ·
    refine ⟨55144544466548678878547075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763029644365785919031383 55144544466548678878547075)
    ·
      refine ⟨82716816699823018317820613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55144544466548678878547075 82716816699823018317820613)
      ·
        refine ⟨15509403131216815934591365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82716816699823018317820613 15509403131216815934591365)
        ·
          refine ⟨2908013087103152987735881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15509403131216815934591365 2908013087103152987735881)
          ·
            refine ⟨2181009815327364740801911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2908013087103152987735881 2181009815327364740801911)
            ·
              refine ⟨3271514722991047111202867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181009815327364740801911 3271514722991047111202867)
              ·
                refine ⟨4907272084486570666804301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271514722991047111202867 4907272084486570666804301)
                ·
                  refine ⟨1840227031682464000051613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4907272084486570666804301 1840227031682464000051613)
                  ·
                    refine ⟨690085136880924000019355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840227031682464000051613 690085136880924000019355)
                    ·
                      rfl

theorem cell22_2015904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_2015904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015904 prefixEnd_2015904 := by exact prefixLift 2015904
  have htrace : WordTrace (prefixWord ++ tailWord_2015904) baseStart_2015904 baseEnd_2015904 := by
    simpa [prefixWord, tailWord_2015904, baseEnd_2015904] using wordTrace_append hprefix tailTrace_2015904
  have hstable : (prefixWord ++ tailWord_2015904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015904).length < 2 ^ (prefixWord ++ tailWord_2015904).sum := by decide
  have hdescent : baseEnd_2015904 < baseStart_2015904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015917 : List Nat := [1, 5, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2015917 : Nat := 118140960795 + 2015917 * 2 ^ 59
def prefixEnd_2015917 : Nat := 4983230072969 + 3 ^ 40 * 2015917 * 2
def baseEnd_2015917 : Nat := 230029862348865433148105

theorem tailTrace_2015917 : CollatzResearch.WordTrace tailWord_2015917 prefixEnd_2015917 230029862348865433148105 := by
  unfold tailWord_2015917
  simp only [CollatzResearch.WordTrace]
  refine ⟨73526533437684475058286005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49017688958456316705524003 73526533437684475058286005)
  ·
    refine ⟨6893112509782919536714313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73526533437684475058286005 6893112509782919536714313)
    ·
      refine ⟨5169834382337189652535735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6893112509782919536714313 5169834382337189652535735)
      ·
        refine ⟨7754751573505784478803603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169834382337189652535735 7754751573505784478803603)
        ·
          refine ⟨11632127360258676718205405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754751573505784478803603 11632127360258676718205405)
          ·
            refine ⟨4362047760097003769327027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11632127360258676718205405 4362047760097003769327027)
            ·
              refine ⟨6543071640145505653990541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362047760097003769327027 6543071640145505653990541)
              ·
                refine ⟨2453651865054564620246453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6543071640145505653990541 2453651865054564620246453)
                ·
                  refine ⟨230029862348865433148105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2453651865054564620246453 230029862348865433148105)
                  ·
                    rfl

theorem cell22_2015917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2015917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015917 prefixEnd_2015917 := by exact prefixLift 2015917
  have htrace : WordTrace (prefixWord ++ tailWord_2015917) baseStart_2015917 baseEnd_2015917 := by
    simpa [prefixWord, tailWord_2015917, baseEnd_2015917] using wordTrace_append hprefix tailTrace_2015917
  have hstable : (prefixWord ++ tailWord_2015917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015917).length < 2 ^ (prefixWord ++ tailWord_2015917).sum := by decide
  have hdescent : baseEnd_2015917 < baseStart_2015917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015930 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_2015930 : Nat := 118140960795 + 2015930 * 2 ^ 59
def prefixEnd_2015930 : Nat := 4983230072969 + 3 ^ 40 * 2015930 * 2
def baseEnd_2015930 : Nat := 690094037212268598869275

theorem tailTrace_2015930 : CollatzResearch.WordTrace tailWord_2015930 prefixEnd_2015930 690094037212268598869275 := by
  unfold tailWord_2015930
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381751896659344569627311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49018005057758252185672829 18381751896659344569627311)
  ·
    refine ⟨27572627844989016854440967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381751896659344569627311 27572627844989016854440967)
    ·
      refine ⟨41358941767483525281661451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27572627844989016854440967 41358941767483525281661451)
      ·
        refine ⟨62038412651225287922492177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41358941767483525281661451 62038412651225287922492177)
        ·
          refine ⟨46528809488418965941869133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62038412651225287922492177 46528809488418965941869133)
          ·
            refine ⟨17448303558157112228200925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46528809488418965941869133 17448303558157112228200925)
            ·
              refine ⟨6543113834308917085575347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17448303558157112228200925 6543113834308917085575347)
              ·
                refine ⟨9814670751463375628363021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543113834308917085575347 9814670751463375628363021)
                ·
                  refine ⟨3680501531798765860636133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9814670751463375628363021 3680501531798765860636133)
                  ·
                    refine ⟨690094037212268598869275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680501531798765860636133 690094037212268598869275)
                    ·
                      rfl

theorem cell22_2015930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_2015930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015930 prefixEnd_2015930 := by exact prefixLift 2015930
  have htrace : WordTrace (prefixWord ++ tailWord_2015930) baseStart_2015930 baseEnd_2015930 := by
    simpa [prefixWord, tailWord_2015930, baseEnd_2015930] using wordTrace_append hprefix tailTrace_2015930
  have hstable : (prefixWord ++ tailWord_2015930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015930).length < 2 ^ (prefixWord ++ tailWord_2015930).sum := by decide
  have hdescent : baseEnd_2015930 < baseStart_2015930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015962 : List Nat := [3, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_2015962 : Nat := 118140960795 + 2015962 * 2 ^ 59
def prefixEnd_2015962 : Nat := 4983230072969 + 3 ^ 40 * 2015962 * 2
def baseEnd_2015962 : Nat := 230034997155410394023059

theorem tailTrace_2015962 : CollatzResearch.WordTrace tailWord_2015962 prefixEnd_2015962 230034997155410394023059 := by
  unfold tailWord_2015962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18382043680630361935918535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49018783148347631829116093 18382043680630361935918535)
  ·
    refine ⟨27573065520945542903877803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18382043680630361935918535 27573065520945542903877803)
    ·
      refine ⟨41359598281418314355816705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27573065520945542903877803 41359598281418314355816705)
      ·
        refine ⟨31019698711063735766862529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41359598281418314355816705 31019698711063735766862529)
        ·
          refine ⟨23264774033297801825146897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31019698711063735766862529 23264774033297801825146897)
          ·
            refine ⟨17448580524973351368860173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23264774033297801825146897 17448580524973351368860173)
            ·
              refine ⟨6543217696865006763322565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17448580524973351368860173 6543217696865006763322565)
              ·
                refine ⟨1226853318162188768122981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6543217696865006763322565 1226853318162188768122981)
                ·
                  refine ⟨230034997155410394023059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1226853318162188768122981 230034997155410394023059)
                  ·
                    rfl

theorem cell22_2015962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_2015962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015962 prefixEnd_2015962 := by exact prefixLift 2015962
  have htrace : WordTrace (prefixWord ++ tailWord_2015962) baseStart_2015962 baseEnd_2015962 := by
    simpa [prefixWord, tailWord_2015962, baseEnd_2015962] using wordTrace_append hprefix tailTrace_2015962
  have hstable : (prefixWord ++ tailWord_2015962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015962).length < 2 ^ (prefixWord ++ tailWord_2015962).sum := by decide
  have hdescent : baseEnd_2015962 < baseStart_2015962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2015977 : List Nat := [1, 2, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_2015977 : Nat := 118140960795 + 2015977 * 2 ^ 59
def prefixEnd_2015977 : Nat := 4983230072969 + 3 ^ 40 * 2015977 * 2
def baseEnd_2015977 : Nat := 690110126272776142944131

theorem tailTrace_2015977 : CollatzResearch.WordTrace tailWord_2015977 prefixEnd_2015977 690110126272776142944131 := by
  unfold tailWord_2015977
  simp only [CollatzResearch.WordTrace]
  refine ⟨73528721817467105305470185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49019147878311403536980123 73528721817467105305470185)
  ·
    refine ⟨55146541363100328979102639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73528721817467105305470185 55146541363100328979102639)
    ·
      refine ⟨82719812044650493468653959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55146541363100328979102639 82719812044650493468653959)
      ·
        refine ⟨124079718066975740202980939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82719812044650493468653959 124079718066975740202980939)
        ·
          refine ⟨186119577100463610304471409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124079718066975740202980939 186119577100463610304471409)
          ·
            refine ⟨139589682825347707728353557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186119577100463610304471409 139589682825347707728353557)
            ·
              refine ⟨6543266382438173799766573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139589682825347707728353557 6543266382438173799766573)
              ·
                refine ⟨2453724893414315174912465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6543266382438173799766573 2453724893414315174912465)
                ·
                  refine ⟨1840293670060736381184349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453724893414315174912465 1840293670060736381184349)
                  ·
                    refine ⟨690110126272776142944131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840293670060736381184349 690110126272776142944131)
                    ·
                      rfl

theorem cell22_2015977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_2015977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2015977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2015977 prefixEnd_2015977 := by exact prefixLift 2015977
  have htrace : WordTrace (prefixWord ++ tailWord_2015977) baseStart_2015977 baseEnd_2015977 := by
    simpa [prefixWord, tailWord_2015977, baseEnd_2015977] using wordTrace_append hprefix tailTrace_2015977
  have hstable : (prefixWord ++ tailWord_2015977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2015977).length < 2 ^ (prefixWord ++ tailWord_2015977).sum := by decide
  have hdescent : baseEnd_2015977 < baseStart_2015977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2015977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016082 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2016082 : Nat := 118140960795 + 2016082 * 2 ^ 59
def prefixEnd_2016082 : Nat := 4983230072969 + 3 ^ 40 * 2016082 * 2
def baseEnd_2016082 : Nat := 690146069918590869068809

theorem tailTrace_2016082 : CollatzResearch.WordTrace tailWord_2016082 prefixEnd_2016082 690146069918590869068809 := by
  unfold tailWord_2016082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18383137870521677059510625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49021700988057805492028333 18383137870521677059510625)
  ·
    refine ⟨13787353402891257794632969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18383137870521677059510625 13787353402891257794632969)
    ·
      refine ⟨10340515052168443345974727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13787353402891257794632969 10340515052168443345974727)
      ·
        refine ⟨15510772578252665018962091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10340515052168443345974727 15510772578252665018962091)
        ·
          refine ⟨23266158867378997528443137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15510772578252665018962091 23266158867378997528443137)
          ·
            refine ⟨17449619150534248146332353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23266158867378997528443137 17449619150534248146332353)
            ·
              refine ⟨13087214362900686109749265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17449619150534248146332353 13087214362900686109749265)
              ·
                refine ⟨9815410772175514582311949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13087214362900686109749265 9815410772175514582311949)
                ·
                  refine ⟨3680779039565817968366981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9815410772175514582311949 3680779039565817968366981)
                  ·
                    refine ⟨690146069918590869068809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680779039565817968366981 690146069918590869068809)
                    ·
                      rfl

theorem cell22_2016082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2016082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016082 prefixEnd_2016082 := by exact prefixLift 2016082
  have htrace : WordTrace (prefixWord ++ tailWord_2016082) baseStart_2016082 baseEnd_2016082 := by
    simpa [prefixWord, tailWord_2016082, baseEnd_2016082] using wordTrace_append hprefix tailTrace_2016082
  have hstable : (prefixWord ++ tailWord_2016082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016082).length < 2 ^ (prefixWord ++ tailWord_2016082).sum := by decide
  have hdescent : baseEnd_2016082 < baseStart_2016082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016099 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 1, 4]
def baseStart_2016099 : Nat := 118140960795 + 2016099 * 2 ^ 59
def prefixEnd_2016099 : Nat := 4983230072969 + 3 ^ 40 * 2016099 * 2
def baseEnd_2016099 : Nat := 690151889366008491393757

theorem tailTrace_2016099 : CollatzResearch.WordTrace tailWord_2016099 prefixEnd_2016099 690151889366008491393757 := by
  unfold tailWord_2016099
  simp only [CollatzResearch.WordTrace]
  refine ⟨73533171523025120141411351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49022114348683413427607567 73533171523025120141411351)
  ·
    refine ⟨110299757284537680212117027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73533171523025120141411351 110299757284537680212117027)
    ·
      refine ⟨165449635926806520318175541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110299757284537680212117027 165449635926806520318175541)
      ·
        refine ⟨15510903368138111279828957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165449635926806520318175541 15510903368138111279828957)
        ·
          refine ⟨5816588763051791729935859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15510903368138111279828957 5816588763051791729935859)
          ·
            refine ⟨8724883144577687594903789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816588763051791729935859 8724883144577687594903789)
            ·
              refine ⟨3271831179216632848088921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8724883144577687594903789 3271831179216632848088921)
              ·
                refine ⟨2453873384412474636066691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271831179216632848088921 2453873384412474636066691)
                ·
                  refine ⟨3680810076618711954100037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453873384412474636066691 3680810076618711954100037)
                  ·
                    refine ⟨690151889366008491393757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680810076618711954100037 690151889366008491393757)
                    ·
                      rfl

theorem cell22_2016099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 4].length) (baseStart_2016099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016099 prefixEnd_2016099 := by exact prefixLift 2016099
  have htrace : WordTrace (prefixWord ++ tailWord_2016099) baseStart_2016099 baseEnd_2016099 := by
    simpa [prefixWord, tailWord_2016099, baseEnd_2016099] using wordTrace_append hprefix tailTrace_2016099
  have hstable : (prefixWord ++ tailWord_2016099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016099).length < 2 ^ (prefixWord ++ tailWord_2016099).sum := by decide
  have hdescent : baseEnd_2016099 < baseStart_2016099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016112 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 6, 3]
def baseStart_2016112 : Nat := 118140960795 + 2016112 * 2 ^ 59
def prefixEnd_2016112 : Nat := 4983230072969 + 3 ^ 40 * 2016112 * 2
def baseEnd_2016112 : Nat := 690156339531680790818717

theorem tailTrace_2016112 : CollatzResearch.WordTrace tailWord_2016112 prefixEnd_2016112 690156339531680790818717 := by
  unfold tailWord_2016112
  simp only [CollatzResearch.WordTrace]
  refine ⟨36766822835989011680817295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49022430447985348907756393 36766822835989011680817295)
  ·
    refine ⟨55150234253983517521225943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36766822835989011680817295 55150234253983517521225943)
    ·
      refine ⟨82725351380975276281838915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55150234253983517521225943 82725351380975276281838915)
      ·
        refine ⟨124088027071462914422758373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82725351380975276281838915 124088027071462914422758373)
        ·
          refine ⟨23266505075899296454267195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124088027071462914422758373 23266505075899296454267195)
          ·
            refine ⟨34899757613848944681400793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23266505075899296454267195 34899757613848944681400793)
            ·
              refine ⟨26174818210386708511050595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34899757613848944681400793 26174818210386708511050595)
              ·
                refine ⟨39262227315580062766575893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26174818210386708511050595 39262227315580062766575893)
                ·
                  refine ⟨1840416905417815442183245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39262227315580062766575893 1840416905417815442183245)
                  ·
                    refine ⟨690156339531680790818717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840416905417815442183245 690156339531680790818717)
                    ·
                      rfl

theorem cell22_2016112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_2016112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016112 prefixEnd_2016112 := by exact prefixLift 2016112
  have htrace : WordTrace (prefixWord ++ tailWord_2016112) baseStart_2016112 baseEnd_2016112 := by
    simpa [prefixWord, tailWord_2016112, baseEnd_2016112] using wordTrace_append hprefix tailTrace_2016112
  have hstable : (prefixWord ++ tailWord_2016112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016112).length < 2 ^ (prefixWord ++ tailWord_2016112).sum := by decide
  have hdescent : baseEnd_2016112 < baseStart_2016112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016127 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_2016127 : Nat := 118140960795 + 2016127 * 2 ^ 59
def prefixEnd_2016127 : Nat := 4983230072969 + 3 ^ 40 * 2016127 * 2
def baseEnd_2016127 : Nat := 690161474338225751693671

theorem tailTrace_2016127 : CollatzResearch.WordTrace tailWord_2016127 prefixEnd_2016127 690161474338225751693671 := by
  unfold tailWord_2016127
  simp only [CollatzResearch.WordTrace]
  refine ⟨73534192766923680923430635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49022795177949120615620423 73534192766923680923430635)
  ·
    refine ⟨110301289150385521385145953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73534192766923680923430635 110301289150385521385145953)
    ·
      refine ⟨82725966862789141038859465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110301289150385521385145953 82725966862789141038859465)
      ·
        refine ⟨62044475147091855779144599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82725966862789141038859465 62044475147091855779144599)
        ·
          refine ⟨93066712720637783668716899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62044475147091855779144599 93066712720637783668716899)
          ·
            refine ⟨139600069080956675503075349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93066712720637783668716899 139600069080956675503075349)
            ·
              refine ⟨6543753238169844164206657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139600069080956675503075349 6543753238169844164206657)
              ·
                refine ⟨4907814928627383123154993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6543753238169844164206657 4907814928627383123154993)
                ·
                  refine ⟨3680861196470537342366245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907814928627383123154993 3680861196470537342366245)
                  ·
                    refine ⟨690161474338225751693671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680861196470537342366245 690161474338225751693671)
                    ·
                      rfl

theorem cell22_2016127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_2016127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016127 prefixEnd_2016127 := by exact prefixLift 2016127
  have htrace : WordTrace (prefixWord ++ tailWord_2016127) baseStart_2016127 baseEnd_2016127 := by
    simpa [prefixWord, tailWord_2016127, baseEnd_2016127] using wordTrace_append hprefix tailTrace_2016127
  have hstable : (prefixWord ++ tailWord_2016127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016127).length < 2 ^ (prefixWord ++ tailWord_2016127).sum := by decide
  have hdescent : baseEnd_2016127 < baseStart_2016127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016146 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2016146 : Nat := 118140960795 + 2016146 * 2 ^ 59
def prefixEnd_2016146 : Nat := 4983230072969 + 3 ^ 40 * 2016146 * 2
def baseEnd_2016146 : Nat := 690167978426516035468613

theorem tailTrace_2016146 : CollatzResearch.WordTrace tailWord_2016146 prefixEnd_2016146 690167978426516035468613 := by
  unfold tailWord_2016146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18383721438463711792093073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49023257169236564778914861 18383721438463711792093073)
  ·
    refine ⟨13787791078847783844069805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18383721438463711792093073 13787791078847783844069805)
    ·
      refine ⟨5170421654567918941526177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13787791078847783844069805 5170421654567918941526177)
      ·
        refine ⟨3877816240925939206144633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5170421654567918941526177 3877816240925939206144633)
        ·
          refine ⟨2908362180694454404608475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3877816240925939206144633 2908362180694454404608475)
          ·
            refine ⟨4362543271041681606912713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908362180694454404608475 4362543271041681606912713)
            ·
              refine ⟨3271907453281261205184535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4362543271041681606912713 3271907453281261205184535)
              ·
                refine ⟨4907861179921891807776803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271907453281261205184535 4907861179921891807776803)
                ·
                  refine ⟨7361791769882837711665205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907861179921891807776803 7361791769882837711665205)
                  ·
                    refine ⟨690167978426516035468613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7361791769882837711665205 690167978426516035468613)
                    ·
                      rfl

theorem cell22_2016146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2016146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016146 prefixEnd_2016146 := by exact prefixLift 2016146
  have htrace : WordTrace (prefixWord ++ tailWord_2016146) baseStart_2016146 baseEnd_2016146 := by
    simpa [prefixWord, tailWord_2016146, baseEnd_2016146] using wordTrace_append hprefix tailTrace_2016146
  have hstable : (prefixWord ++ tailWord_2016146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016146).length < 2 ^ (prefixWord ++ tailWord_2016146).sum := by decide
  have hdescent : baseEnd_2016146 < baseStart_2016146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016159 : List Nat := [1, 1, 2, 5, 2, 2, 3, 6]
def baseStart_2016159 : Nat := 118140960795 + 2016159 * 2 ^ 59
def prefixEnd_2016159 : Nat := 4983230072969 + 3 ^ 40 * 2016159 * 2
def baseEnd_2016159 : Nat := 76685825399132037210397

theorem tailTrace_2016159 : CollatzResearch.WordTrace tailWord_2016159 prefixEnd_2016159 76685825399132037210397 := by
  unfold tailWord_2016159
  simp only [CollatzResearch.WordTrace]
  refine ⟨73535359902807750388595531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49023573268538500259063687 73535359902807750388595531)
  ·
    refine ⟨110303039854211625582893297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73535359902807750388595531 110303039854211625582893297)
    ·
      refine ⟨82727279890658719187169973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110303039854211625582893297 82727279890658719187169973)
      ·
        refine ⟨7755682489749254923797185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82727279890658719187169973 7755682489749254923797185)
        ·
          refine ⟨5816761867311941192847889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7755682489749254923797185 5816761867311941192847889)
          ·
            refine ⟨4362571400483955894635917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5816761867311941192847889 4362571400483955894635917)
            ·
              refine ⟨1635964275181483460488469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4362571400483955894635917 1635964275181483460488469)
              ·
                refine ⟨76685825399132037210397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1635964275181483460488469 76685825399132037210397)
                ·
                  rfl

theorem cell22_2016159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 3, 6].length) (baseStart_2016159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016159 prefixEnd_2016159 := by exact prefixLift 2016159
  have htrace : WordTrace (prefixWord ++ tailWord_2016159) baseStart_2016159 baseEnd_2016159 := by
    simpa [prefixWord, tailWord_2016159, baseEnd_2016159] using wordTrace_append hprefix tailTrace_2016159
  have hstable : (prefixWord ++ tailWord_2016159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016159).length < 2 ^ (prefixWord ++ tailWord_2016159).sum := by decide
  have hdescent : baseEnd_2016159 < baseStart_2016159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016161 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_2016161 : Nat := 118140960795 + 2016161 * 2 ^ 59
def prefixEnd_2016161 : Nat := 4983230072969 + 3 ^ 40 * 2016161 * 2
def baseEnd_2016161 : Nat := 690173113233060996343567

theorem tailTrace_2016161 : CollatzResearch.WordTrace tailWord_2016161 prefixEnd_2016161 690173113233060996343567 := by
  unfold tailWord_2016161
  simp only [CollatzResearch.WordTrace]
  refine ⟨73535432848800504730168337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49023621899200336486778891 73535432848800504730168337)
  ·
    refine ⟨55151574636600378547626253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73535432848800504730168337 55151574636600378547626253)
    ·
      refine ⟨20681840488725141955359845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55151574636600378547626253 20681840488725141955359845)
      ·
        refine ⟨3877845091635964116629971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20681840488725141955359845 3877845091635964116629971)
        ·
          refine ⟨5816767637453946174944957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877845091635964116629971 5816767637453946174944957)
          ·
            refine ⟨2181287864045229815604359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5816767637453946174944957 2181287864045229815604359)
            ·
              refine ⟨3271931796067844723406539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181287864045229815604359 3271931796067844723406539)
              ·
                refine ⟨4907897694101767085109809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271931796067844723406539 4907897694101767085109809)
                ·
                  refine ⟨3680923270576325313832357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907897694101767085109809 3680923270576325313832357)
                  ·
                    refine ⟨690173113233060996343567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680923270576325313832357 690173113233060996343567)
                    ·
                      rfl

theorem cell22_2016161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_2016161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016161 prefixEnd_2016161 := by exact prefixLift 2016161
  have htrace : WordTrace (prefixWord ++ tailWord_2016161) baseStart_2016161 baseEnd_2016161 := by
    simpa [prefixWord, tailWord_2016161, baseEnd_2016161] using wordTrace_append hprefix tailTrace_2016161
  have hstable : (prefixWord ++ tailWord_2016161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016161).length < 2 ^ (prefixWord ++ tailWord_2016161).sum := by decide
  have hdescent : baseEnd_2016161 < baseStart_2016161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016180 : List Nat := [2, 5, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2016180 : Nat := 118140960795 + 2016180 * 2 ^ 59
def prefixEnd_2016180 : Nat := 4983230072969 + 3 ^ 40 * 2016180 * 2
def baseEnd_2016180 : Nat := 690179617321351280118509

theorem tailTrace_2016180 : CollatzResearch.WordTrace tailWord_2016180 prefixEnd_2016180 690179617321351280118509 := by
  unfold tailWord_2016180
  simp only [CollatzResearch.WordTrace]
  refine ⟨36768062917865835487554997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49024083890487780650073329 36768062917865835487554997)
  ·
    refine ⟨3447005898549922076958281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36768062917865835487554997 3447005898549922076958281)
    ·
      refine ⟨2585254423912441557718711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3447005898549922076958281 2585254423912441557718711)
      ·
        refine ⟨3877881635868662336578067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2585254423912441557718711 3877881635868662336578067)
        ·
          refine ⟨5816822453802993504867101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877881635868662336578067 5816822453802993504867101)
          ·
            refine ⟨2181308420176122564325163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5816822453802993504867101 2181308420176122564325163)
            ·
              refine ⟨3271962630264183846487745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181308420176122564325163 3271962630264183846487745)
              ·
                refine ⟨2453971972698137884865809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271962630264183846487745 2453971972698137884865809)
                ·
                  refine ⟨1840478979523603413649357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2453971972698137884865809 1840478979523603413649357)
                  ·
                    refine ⟨690179617321351280118509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840478979523603413649357 690179617321351280118509)
                    ·
                      rfl

theorem cell22_2016180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2016180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016180 prefixEnd_2016180 := by exact prefixLift 2016180
  have htrace : WordTrace (prefixWord ++ tailWord_2016180) baseStart_2016180 baseEnd_2016180 := by
    simpa [prefixWord, tailWord_2016180, baseEnd_2016180] using wordTrace_append hprefix tailTrace_2016180
  have hstable : (prefixWord ++ tailWord_2016180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016180).length < 2 ^ (prefixWord ++ tailWord_2016180).sum := by decide
  have hdescent : baseEnd_2016180 < baseStart_2016180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016232 : List Nat := [2, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_2016232 : Nat := 118140960795 + 2016232 * 2 ^ 59
def prefixEnd_2016232 : Nat := 4983230072969 + 3 ^ 40 * 2016232 * 2
def baseEnd_2016232 : Nat := 230065805994680159272783

theorem tailTrace_2016232 : CollatzResearch.WordTrace tailWord_2016232 prefixEnd_2016232 230065805994680159272783 := by
  unfold tailWord_2016232
  simp only [CollatzResearch.WordTrace]
  refine ⟨36769011215771641928001475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49025348287695522570668633 36769011215771641928001475)
  ·
    refine ⟨55153516823657462892002213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36769011215771641928001475 55153516823657462892002213)
    ·
      refine ⟨10341284404435774292250415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55153516823657462892002213 10341284404435774292250415)
      ·
        refine ⟨15511926606653661438375623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10341284404435774292250415 15511926606653661438375623)
        ·
          refine ⟨23267889909980492157563435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15511926606653661438375623 23267889909980492157563435)
          ·
            refine ⟨34901834864970738236345153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23267889909980492157563435 34901834864970738236345153)
            ·
              refine ⟨26176376148728053677258865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34901834864970738236345153 26176376148728053677258865)
              ·
                refine ⟨19632282111546040257944149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26176376148728053677258865 19632282111546040257944149)
                ·
                  refine ⟨230065805994680159272783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19632282111546040257944149 230065805994680159272783)
                  ·
                    rfl

theorem cell22_2016232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_2016232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016232 prefixEnd_2016232 := by exact prefixLift 2016232
  have htrace : WordTrace (prefixWord ++ tailWord_2016232) baseStart_2016232 baseEnd_2016232 := by
    simpa [prefixWord, tailWord_2016232, baseEnd_2016232] using wordTrace_append hprefix tailTrace_2016232
  have hstable : (prefixWord ++ tailWord_2016232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016232).length < 2 ^ (prefixWord ++ tailWord_2016232).sum := by decide
  have hdescent : baseEnd_2016232 < baseStart_2016232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016242 : List Nat := [3, 2, 1, 5, 1, 1, 3, 2, 1, 3]
def baseStart_2016242 : Nat := 118140960795 + 2016242 * 2 ^ 59
def prefixEnd_2016242 : Nat := 4983230072969 + 3 ^ 40 * 2016242 * 2
def baseEnd_2016242 : Nat := 690200841188403785068319

theorem tailTrace_2016242 : CollatzResearch.WordTrace tailWord_2016242 prefixEnd_2016242 690200841188403785068319 := by
  unfold tailWord_2016242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384596790376763890966745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49025591441004703709244653 18384596790376763890966745)
  ·
    refine ⟨13788447592782572918225059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18384596790376763890966745 13788447592782572918225059)
    ·
      refine ⟨20682671389173859377337589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13788447592782572918225059 20682671389173859377337589)
      ·
        refine ⟨1939000442735049316625399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20682671389173859377337589 1939000442735049316625399)
        ·
          refine ⟨2908500664102573974938099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939000442735049316625399 2908500664102573974938099)
          ·
            refine ⟨4362750996153860962407149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908500664102573974938099 4362750996153860962407149)
            ·
              refine ⟨1636031623557697860902681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4362750996153860962407149 1636031623557697860902681)
              ·
                refine ⟨1227023717668273395677011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636031623557697860902681 1227023717668273395677011)
                ·
                  refine ⟨1840535576502410093515517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227023717668273395677011 1840535576502410093515517)
                  ·
                    refine ⟨690200841188403785068319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840535576502410093515517 690200841188403785068319)
                    ·
                      rfl

theorem cell22_2016242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_2016242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016242 prefixEnd_2016242 := by exact prefixLift 2016242
  have htrace : WordTrace (prefixWord ++ tailWord_2016242) baseStart_2016242 baseEnd_2016242 := by
    simpa [prefixWord, tailWord_2016242, baseEnd_2016242] using wordTrace_append hprefix tailTrace_2016242
  have hstable : (prefixWord ++ tailWord_2016242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016242).length < 2 ^ (prefixWord ++ tailWord_2016242).sum := by decide
  have hdescent : baseEnd_2016242 < baseStart_2016242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016360 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2016360 : Nat := 118140960795 + 2016360 * 2 ^ 59
def prefixEnd_2016360 : Nat := 4983230072969 + 3 ^ 40 * 2016360 * 2
def baseEnd_2016360 : Nat := 690241234999890810617957

theorem tailTrace_2016360 : CollatzResearch.WordTrace tailWord_2016360 prefixEnd_2016360 690241234999890810617957 := by
  unfold tailWord_2016360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771345487539780858331267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49028460650053041144441689 36771345487539780858331267)
  ·
    refine ⟨55157018231309671287496901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36771345487539780858331267 55157018231309671287496901)
    ·
      refine ⟨10341940918370563366405669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55157018231309671287496901 10341940918370563366405669)
      ·
        refine ⟨1939113922194480631201063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10341940918370563366405669 1939113922194480631201063)
        ·
          refine ⟨2908670883291720946801595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939113922194480631201063 2908670883291720946801595)
          ·
            refine ⟨4363006324937581420202393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908670883291720946801595 4363006324937581420202393)
            ·
              refine ⟨3272254743703186065151795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363006324937581420202393 3272254743703186065151795)
              ·
                refine ⟨4908382115554779097727693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272254743703186065151795 4908382115554779097727693)
                ·
                  refine ⟨1840643293333042161647885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4908382115554779097727693 1840643293333042161647885)
                  ·
                    refine ⟨690241234999890810617957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840643293333042161647885 690241234999890810617957)
                    ·
                      rfl

theorem cell22_2016360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2016360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016360 prefixEnd_2016360 := by exact prefixLift 2016360
  have htrace : WordTrace (prefixWord ++ tailWord_2016360) baseStart_2016360 baseEnd_2016360 := by
    simpa [prefixWord, tailWord_2016360, baseEnd_2016360] using wordTrace_append hprefix tailTrace_2016360
  have hstable : (prefixWord ++ tailWord_2016360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016360).length < 2 ^ (prefixWord ++ tailWord_2016360).sum := by decide
  have hdescent : baseEnd_2016360 < baseStart_2016360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016369 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2016369 : Nat := 118140960795 + 2016369 * 2 ^ 59
def prefixEnd_2016369 : Nat := 4983230072969 + 3 ^ 40 * 2016369 * 2
def baseEnd_2016369 : Nat := 690244315883817787142929

theorem tailTrace_2016369 : CollatzResearch.WordTrace tailWord_2016369 prefixEnd_2016369 690244315883817787142929 := by
  unfold tailWord_2016369
  simp only [CollatzResearch.WordTrace]
  refine ⟨73543019232046956253740161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49028679488031304169160107 73543019232046956253740161)
  ·
    refine ⟨55157264424035217190305121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73543019232046956253740161 55157264424035217190305121)
    ·
      refine ⟨41367948318026412892728841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55157264424035217190305121 41367948318026412892728841)
      ·
        refine ⟨31025961238519809669546631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41367948318026412892728841 31025961238519809669546631)
        ·
          refine ⟨46538941857779714504319947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31025961238519809669546631 46538941857779714504319947)
          ·
            refine ⟨69808412786669571756479921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46538941857779714504319947 69808412786669571756479921)
            ·
              refine ⟨52356309590002178817359941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69808412786669571756479921 52356309590002178817359941)
              ·
                refine ⟨9816808048125408528254989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52356309590002178817359941 9816808048125408528254989)
                ·
                  refine ⟨3681303018047028198095621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9816808048125408528254989 3681303018047028198095621)
                  ·
                    refine ⟨690244315883817787142929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681303018047028198095621 690244315883817787142929)
                    ·
                      rfl

theorem cell22_2016369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2016369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016369 prefixEnd_2016369 := by exact prefixLift 2016369
  have htrace : WordTrace (prefixWord ++ tailWord_2016369) baseStart_2016369 baseEnd_2016369 := by
    simpa [prefixWord, tailWord_2016369, baseEnd_2016369] using wordTrace_append hprefix tailTrace_2016369
  have hstable : (prefixWord ++ tailWord_2016369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016369).length < 2 ^ (prefixWord ++ tailWord_2016369).sum := by decide
  have hdescent : baseEnd_2016369 < baseStart_2016369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016384 : List Nat := [2, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_2016384 : Nat := 118140960795 + 2016384 * 2 ^ 59
def prefixEnd_2016384 : Nat := 4983230072969 + 3 ^ 40 * 2016384 * 2
def baseEnd_2016384 : Nat := 230083150230120916005961

theorem tailTrace_2016384 : CollatzResearch.WordTrace tailWord_2016384 prefixEnd_2016384 230083150230120916005961 := by
  unfold tailWord_2016384
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771783163496306907768103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49029044217995075877024137 36771783163496306907768103)
  ·
    refine ⟨55157674745244460361652155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36771783163496306907768103 55157674745244460361652155)
    ·
      refine ⟨82736512117866690542478233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55157674745244460361652155 82736512117866690542478233)
      ·
        refine ⟨62052384088400017906858675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82736512117866690542478233 62052384088400017906858675)
        ·
          refine ⟨93078576132600026860288013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62052384088400017906858675 93078576132600026860288013)
          ·
            refine ⟨34904466049725010072608005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93078576132600026860288013 34904466049725010072608005)
            ·
              refine ⟨6544587384323439388614001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34904466049725010072608005 6544587384323439388614001)
              ·
                refine ⟨4908440538242579541460501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544587384323439388614001 4908440538242579541460501)
                ·
                  refine ⟨230083150230120916005961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4908440538242579541460501 230083150230120916005961)
                  ·
                    rfl

theorem cell22_2016384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_2016384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016384 prefixEnd_2016384 := by exact prefixLift 2016384
  have htrace : WordTrace (prefixWord ++ tailWord_2016384) baseStart_2016384 baseEnd_2016384 := by
    simpa [prefixWord, tailWord_2016384, baseEnd_2016384] using wordTrace_append hprefix tailTrace_2016384
  have hstable : (prefixWord ++ tailWord_2016384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016384).length < 2 ^ (prefixWord ++ tailWord_2016384).sum := by decide
  have hdescent : baseEnd_2016384 < baseStart_2016384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016416 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_2016416 : Nat := 118140960795 + 2016416 * 2 ^ 59
def prefixEnd_2016416 : Nat := 4983230072969 + 3 ^ 40 * 2016416 * 2
def baseEnd_2016416 : Nat := 690260404944325331217785

theorem tailTrace_2016416 : CollatzResearch.WordTrace tailWord_2016416 prefixEnd_2016416 690260404944325331217785 := by
  unfold tailWord_2016416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772366731438341640350551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49029822308584455520467401 36772366731438341640350551)
  ·
    refine ⟨55158550097157512460525827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36772366731438341640350551 55158550097157512460525827)
    ·
      refine ⟨82737825145736268690788741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55158550097157512460525827 82737825145736268690788741)
      ·
        refine ⟨15513342214825550379522889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82737825145736268690788741 15513342214825550379522889)
        ·
          refine ⟨11635006661119162784642167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15513342214825550379522889 11635006661119162784642167)
          ·
            refine ⟨17452509991678744176963251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635006661119162784642167 17452509991678744176963251)
            ·
              refine ⟨26178764987518116265444877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17452509991678744176963251 26178764987518116265444877)
              ·
                refine ⟨9817036870319293599541829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26178764987518116265444877 9817036870319293599541829)
                ·
                  refine ⟨1840694413184867549914093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9817036870319293599541829 1840694413184867549914093)
                  ·
                    refine ⟨690260404944325331217785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840694413184867549914093 690260404944325331217785)
                    ·
                      rfl

theorem cell22_2016416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_2016416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016416 prefixEnd_2016416 := by exact prefixLift 2016416
  have htrace : WordTrace (prefixWord ++ tailWord_2016416) baseStart_2016416 baseEnd_2016416 := by
    simpa [prefixWord, tailWord_2016416, baseEnd_2016416] using wordTrace_append hprefix tailTrace_2016416
  have hstable : (prefixWord ++ tailWord_2016416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016416).length < 2 ^ (prefixWord ++ tailWord_2016416).sum := by decide
  have hdescent : baseEnd_2016416 < baseStart_2016416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016446 : List Nat := [4, 2, 1, 1, 3, 1, 2, 8]
def baseStart_2016446 : Nat := 118140960795 + 2016446 * 2 ^ 59
def prefixEnd_2016446 : Nat := 4983230072969 + 3 ^ 40 * 2016446 * 2
def baseEnd_2016446 : Nat := 76696741617490583663077

theorem tailTrace_2016446 : CollatzResearch.WordTrace tailWord_2016446 prefixEnd_2016446 76696741617490583663077 := by
  unfold tailWord_2016446
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193228456595999800536649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49030551768511998936195461 9193228456595999800536649)
  ·
    refine ⟨6894921342446999850402487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9193228456595999800536649 6894921342446999850402487)
    ·
      refine ⟨10342382013670499775603731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894921342446999850402487 10342382013670499775603731)
      ·
        refine ⟨15513573020505749663405597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10342382013670499775603731 15513573020505749663405597)
        ·
          refine ⟨5817589882689656123777099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15513573020505749663405597 5817589882689656123777099)
          ·
            refine ⟨8726384824034484185665649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817589882689656123777099 8726384824034484185665649)
            ·
              refine ⟨6544788618025863139249237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726384824034484185665649 6544788618025863139249237)
              ·
                refine ⟨76696741617490583663077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6544788618025863139249237 76696741617490583663077)
                ·
                  rfl

theorem cell22_2016446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_2016446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016446 prefixEnd_2016446 := by exact prefixLift 2016446
  have htrace : WordTrace (prefixWord ++ tailWord_2016446) baseStart_2016446 baseEnd_2016446 := by
    simpa [prefixWord, tailWord_2016446, baseEnd_2016446] using wordTrace_append hprefix tailTrace_2016446
  have hstable : (prefixWord ++ tailWord_2016446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016446).length < 2 ^ (prefixWord ++ tailWord_2016446).sum := by decide
  have hdescent : baseEnd_2016446 < baseStart_2016446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016448 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_2016448 : Nat := 118140960795 + 2016448 * 2 ^ 59
def prefixEnd_2016448 : Nat := 4983230072969 + 3 ^ 40 * 2016448 * 2
def baseEnd_2016448 : Nat := 690271359198287914417687

theorem tailTrace_2016448 : CollatzResearch.WordTrace tailWord_2016448 prefixEnd_2016448 690271359198287914417687 := by
  unfold tailWord_2016448
  simp only [CollatzResearch.WordTrace]
  refine ⟨36772950299380376372932999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49030600399173835163910665 36772950299380376372932999)
  ·
    refine ⟨55159425449070564559399499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36772950299380376372932999 55159425449070564559399499)
    ·
      refine ⟨82739138173605846839099249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55159425449070564559399499 82739138173605846839099249)
      ·
        refine ⟨62054353630204385129324437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82739138173605846839099249 62054353630204385129324437)
        ·
          refine ⟨2908797826415830552937083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62054353630204385129324437 2908797826415830552937083)
          ·
            refine ⟨4363196739623745829405625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908797826415830552937083 4363196739623745829405625)
            ·
              refine ⟨3272397554717809372054219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363196739623745829405625 3272397554717809372054219)
              ·
                refine ⟨4908596332076714058081329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272397554717809372054219 4908596332076714058081329)
                ·
                  refine ⟨3681447249057535543560997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908596332076714058081329 3681447249057535543560997)
                  ·
                    refine ⟨690271359198287914417687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681447249057535543560997 690271359198287914417687)
                    ·
                      rfl

theorem cell22_2016448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_2016448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016448 prefixEnd_2016448 := by exact prefixLift 2016448
  have htrace : WordTrace (prefixWord ++ tailWord_2016448) baseStart_2016448 baseEnd_2016448 := by
    simpa [prefixWord, tailWord_2016448, baseEnd_2016448] using wordTrace_append hprefix tailTrace_2016448
  have hstable : (prefixWord ++ tailWord_2016448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016448).length < 2 ^ (prefixWord ++ tailWord_2016448).sum := by decide
  have hdescent : baseEnd_2016448 < baseStart_2016448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016491 : List Nat := [1, 1, 1, 1, 2, 6, 2, 3, 5]
def baseStart_2016491 : Nat := 118140960795 + 2016491 * 2 ^ 59
def prefixEnd_2016491 : Nat := 4983230072969 + 3 ^ 40 * 2016491 * 2
def baseEnd_2016491 : Nat := 230095359659016711864185

theorem tailTrace_2016491 : CollatzResearch.WordTrace tailWord_2016491 prefixEnd_2016491 230095359659016711864185 := by
  unfold tailWord_2016491
  simp only [CollatzResearch.WordTrace]
  refine ⟨73547468937604971089681327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49031645958403314059787551 73547468937604971089681327)
  ·
    refine ⟨110321203406407456634521991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73547468937604971089681327 110321203406407456634521991)
    ·
      refine ⟨165481805109611184951782987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110321203406407456634521991 165481805109611184951782987)
      ·
        refine ⟨248222707664416777427674481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165481805109611184951782987 248222707664416777427674481)
        ·
          refine ⟨186167030748312583070755861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248222707664416777427674481 186167030748312583070755861)
          ·
            refine ⟨8726579566327152331441681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186167030748312583070755861 8726579566327152331441681)
            ·
              refine ⟨6544934674745364248581261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726579566327152331441681 6544934674745364248581261)
              ·
                refine ⟨2454350503029511593217973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6544934674745364248581261 2454350503029511593217973)
                ·
                  refine ⟨230095359659016711864185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454350503029511593217973 230095359659016711864185)
                  ·
                    rfl

theorem cell22_2016491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3, 5].length) (baseStart_2016491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016491 prefixEnd_2016491 := by exact prefixLift 2016491
  have htrace : WordTrace (prefixWord ++ tailWord_2016491) baseStart_2016491 baseEnd_2016491 := by
    simpa [prefixWord, tailWord_2016491, baseEnd_2016491] using wordTrace_append hprefix tailTrace_2016491
  have hstable : (prefixWord ++ tailWord_2016491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016491).length < 2 ^ (prefixWord ++ tailWord_2016491).sum := by decide
  have hdescent : baseEnd_2016491 < baseStart_2016491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016536 : List Nat := [2, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_2016536 : Nat := 118140960795 + 2016536 * 2 ^ 59
def prefixEnd_2016536 : Nat := 4983230072969 + 3 ^ 40 * 2016536 * 2
def baseEnd_2016536 : Nat := 230100494465561672739139

theorem tailTrace_2016536 : CollatzResearch.WordTrace tailWord_2016536 prefixEnd_2016536 230100494465561672739139 := by
  unfold tailWord_2016536
  simp only [CollatzResearch.WordTrace]
  refine ⟨36774555111220971887534731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49032740148294629183379641 36774555111220971887534731)
  ·
    refine ⟨55161832666831457831302097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36774555111220971887534731 55161832666831457831302097)
    ·
      refine ⟨41371374500123593373476573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55161832666831457831302097 41371374500123593373476573)
      ·
        refine ⟨15514265437546347515053715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41371374500123593373476573 15514265437546347515053715)
        ·
          refine ⟨23271398156319521272580573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514265437546347515053715 23271398156319521272580573)
          ·
            refine ⟨8726774308619820477217715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23271398156319521272580573 8726774308619820477217715)
            ·
              refine ⟨13090161462929730715826573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726774308619820477217715 13090161462929730715826573)
              ·
                refine ⟨4908810548598649018434965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13090161462929730715826573 4908810548598649018434965)
                ·
                  refine ⟨230100494465561672739139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4908810548598649018434965 230100494465561672739139)
                  ·
                    rfl

theorem cell22_2016536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_2016536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016536 prefixEnd_2016536 := by exact prefixLift 2016536
  have htrace : WordTrace (prefixWord ++ tailWord_2016536) baseStart_2016536 baseEnd_2016536 := by
    simpa [prefixWord, tailWord_2016536, baseEnd_2016536] using wordTrace_append hprefix tailTrace_2016536
  have hstable : (prefixWord ++ tailWord_2016536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016536).length < 2 ^ (prefixWord ++ tailWord_2016536).sum := by decide
  have hdescent : baseEnd_2016536 < baseStart_2016536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016583 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_2016583 : Nat := 118140960795 + 2016583 * 2 ^ 59
def prefixEnd_2016583 : Nat := 4983230072969 + 3 ^ 40 * 2016583 * 2
def baseEnd_2016583 : Nat := 690317572457192562292273

theorem tailTrace_2016583 : CollatzResearch.WordTrace tailWord_2016583 prefixEnd_2016583 690317572457192562292273 := by
  unfold tailWord_2016583
  simp only [CollatzResearch.WordTrace]
  refine ⟨73550824453271670802030403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49033882968847780534686935 73550824453271670802030403)
  ·
    refine ⟨110326236679907506203045605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73550824453271670802030403 110326236679907506203045605)
    ·
      refine ⟨20686169377482657413071051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110326236679907506203045605 20686169377482657413071051)
      ·
        refine ⟨31029254066223986119606577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20686169377482657413071051 31029254066223986119606577)
        ·
          refine ⟨23271940549667989589704933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31029254066223986119606577 23271940549667989589704933)
          ·
            refine ⟨4363488853062748048069675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23271940549667989589704933 4363488853062748048069675)
            ·
              refine ⟨6545233279594122072104513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363488853062748048069675 6545233279594122072104513)
              ·
                refine ⟨4908924959695591554078385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545233279594122072104513 4908924959695591554078385)
                ·
                  refine ⟨3681693719771693665558789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908924959695591554078385 3681693719771693665558789)
                  ·
                    refine ⟨690317572457192562292273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681693719771693665558789 690317572457192562292273)
                    ·
                      rfl

theorem cell22_2016583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_2016583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016583 prefixEnd_2016583 := by exact prefixLift 2016583
  have htrace : WordTrace (prefixWord ++ tailWord_2016583) baseStart_2016583 baseEnd_2016583 := by
    simpa [prefixWord, tailWord_2016583, baseEnd_2016583] using wordTrace_append hprefix tailTrace_2016583
  have hstable : (prefixWord ++ tailWord_2016583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016583).length < 2 ^ (prefixWord ++ tailWord_2016583).sum := by decide
  have hdescent : baseEnd_2016583 < baseStart_2016583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016613 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_2016613 : Nat := 118140960795 + 2016613 * 2 ^ 59
def prefixEnd_2016613 : Nat := 4983230072969 + 3 ^ 40 * 2016613 * 2
def baseEnd_2016613 : Nat := 690327842070282484042181

theorem tailTrace_2016613 : CollatzResearch.WordTrace tailWord_2016613 prefixEnd_2016613 690327842070282484042181 := by
  unfold tailWord_2016613
  simp only [CollatzResearch.WordTrace]
  refine ⟨73551918643162985925622493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49034612428775323950414995 73551918643162985925622493)
  ·
    refine ⟨27581969491186119722108435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73551918643162985925622493 27581969491186119722108435)
    ·
      refine ⟨41372954236779179583162653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27581969491186119722108435 41372954236779179583162653)
      ·
        refine ⟨15514857838792192343685995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41372954236779179583162653 15514857838792192343685995)
        ·
          refine ⟨23272286758188288515528993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514857838792192343685995 23272286758188288515528993)
          ·
            refine ⟨17454215068641216386646745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23272286758188288515528993 17454215068641216386646745)
            ·
              refine ⟨13090661301480912289985059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17454215068641216386646745 13090661301480912289985059)
              ·
                refine ⟨19635991952221368434977589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13090661301480912289985059 19635991952221368434977589)
                ·
                  refine ⟨1840874245520753290779149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19635991952221368434977589 1840874245520753290779149)
                  ·
                    refine ⟨690327842070282484042181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840874245520753290779149 690327842070282484042181)
                    ·
                      rfl

theorem cell22_2016613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_2016613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016613 prefixEnd_2016613 := by exact prefixLift 2016613
  have htrace : WordTrace (prefixWord ++ tailWord_2016613) baseStart_2016613 baseEnd_2016613 := by
    simpa [prefixWord, tailWord_2016613, baseEnd_2016613] using wordTrace_append hprefix tailTrace_2016613
  have hstable : (prefixWord ++ tailWord_2016613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016613).length < 2 ^ (prefixWord ++ tailWord_2016613).sum := by decide
  have hdescent : baseEnd_2016613 < baseStart_2016613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016638 : List Nat := [4, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_2016638 : Nat := 118140960795 + 2016638 * 2 ^ 59
def prefixEnd_2016638 : Nat := 4983230072969 + 3 ^ 40 * 2016638 * 2
def baseEnd_2016638 : Nat := 230112133360396917389035

theorem tailTrace_2016638 : CollatzResearch.WordTrace tailWord_2016638 prefixEnd_2016638 230112133360396917389035 := by
  unfold tailWord_2016638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194103808509051899410321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49035220312048276796855045 9194103808509051899410321)
  ·
    refine ⟨6895577856381788924557741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9194103808509051899410321 6895577856381788924557741)
    ·
      refine ⟨2585841696143170846709153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6895577856381788924557741 2585841696143170846709153)
      ·
        refine ⟨1939381272107378135031865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585841696143170846709153 1939381272107378135031865)
        ·
          refine ⟨1454535954080533601273899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939381272107378135031865 1454535954080533601273899)
          ·
            refine ⟨2181803931120800401910849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454535954080533601273899 2181803931120800401910849)
            ·
              refine ⟨1636352948340600301433137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181803931120800401910849 1636352948340600301433137)
              ·
                refine ⟨1227264711255450226074853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636352948340600301433137 1227264711255450226074853)
                ·
                  refine ⟨230112133360396917389035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227264711255450226074853 230112133360396917389035)
                  ·
                    rfl

theorem cell22_2016638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_2016638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016638 prefixEnd_2016638 := by exact prefixLift 2016638
  have htrace : WordTrace (prefixWord ++ tailWord_2016638) baseStart_2016638 baseEnd_2016638 := by
    simpa [prefixWord, tailWord_2016638, baseEnd_2016638] using wordTrace_append hprefix tailTrace_2016638
  have hstable : (prefixWord ++ tailWord_2016638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016638).length < 2 ^ (prefixWord ++ tailWord_2016638).sum := by decide
  have hdescent : baseEnd_2016638 < baseStart_2016638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016643 : List Nat := [1, 1, 1, 3, 5, 1, 1, 4, 5]
def baseStart_2016643 : Nat := 118140960795 + 2016643 * 2 ^ 59
def prefixEnd_2016643 : Nat := 4983230072969 + 3 ^ 40 * 2016643 * 2
def baseEnd_2016643 : Nat := 230112703894457468597363

theorem tailTrace_2016643 : CollatzResearch.WordTrace tailWord_2016643 prefixEnd_2016643 230112703894457468597363 := by
  unfold tailWord_2016643
  simp only [CollatzResearch.WordTrace]
  refine ⟨73553012833054301049214583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49035341888702867366143055 73553012833054301049214583)
  ·
    refine ⟨110329519249581451573821875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73553012833054301049214583 110329519249581451573821875)
    ·
      refine ⟨165494278874372177360732813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110329519249581451573821875 165494278874372177360732813)
      ·
        refine ⟨62060354577889566510274805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165494278874372177360732813 62060354577889566510274805)
        ·
          refine ⟨5818158241677146860338263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62060354577889566510274805 5818158241677146860338263)
          ·
            refine ⟨8727237362515720290507395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818158241677146860338263 8727237362515720290507395)
            ·
              refine ⟨13090856043773580435761093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8727237362515720290507395 13090856043773580435761093)
              ·
                refine ⟨2454535508207546331705205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13090856043773580435761093 2454535508207546331705205)
                ·
                  refine ⟨230112703894457468597363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454535508207546331705205 230112703894457468597363)
                  ·
                    rfl

theorem cell22_2016643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 5].length) (baseStart_2016643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016643 prefixEnd_2016643 := by exact prefixLift 2016643
  have htrace : WordTrace (prefixWord ++ tailWord_2016643) baseStart_2016643 baseEnd_2016643 := by
    simpa [prefixWord, tailWord_2016643, baseEnd_2016643] using wordTrace_append hprefix tailTrace_2016643
  have hstable : (prefixWord ++ tailWord_2016643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016643).length < 2 ^ (prefixWord ++ tailWord_2016643).sum := by decide
  have hdescent : baseEnd_2016643 < baseStart_2016643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016647 : List Nat := [1, 1, 4, 2, 2, 3, 1, 4, 1, 3]
def baseStart_2016647 : Nat := 118140960795 + 2016647 * 2 ^ 59
def prefixEnd_2016647 : Nat := 4983230072969 + 3 ^ 40 * 2016647 * 2
def baseEnd_2016647 : Nat := 690339480965117728692077

theorem tailTrace_2016647 : CollatzResearch.WordTrace tailWord_2016647 prefixEnd_2016647 690339480965117728692077 := by
  unfold tailWord_2016647
  simp only [CollatzResearch.WordTrace]
  refine ⟨73553158725039809732360195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49035439150026539821573463 73553158725039809732360195)
  ·
    refine ⟨110329738087559714598540293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73553158725039809732360195 110329738087559714598540293)
    ·
      refine ⟨20686825891417446487226305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110329738087559714598540293 20686825891417446487226305)
      ·
        refine ⟨15515119418563084865419729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20686825891417446487226305 15515119418563084865419729)
        ·
          refine ⟨11636339563922313649064797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15515119418563084865419729 11636339563922313649064797)
          ·
            refine ⟨4363627336470867618399299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11636339563922313649064797 4363627336470867618399299)
            ·
              refine ⟨6545441004706301427598949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363627336470867618399299 6545441004706301427598949)
              ·
                refine ⟨1227270188382431517674803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6545441004706301427598949 1227270188382431517674803)
                ·
                  refine ⟨1840905282573647276512205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227270188382431517674803 1840905282573647276512205)
                  ·
                    refine ⟨690339480965117728692077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1840905282573647276512205 690339480965117728692077)
                    ·
                      rfl

theorem cell22_2016647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_2016647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016647 prefixEnd_2016647 := by exact prefixLift 2016647
  have htrace : WordTrace (prefixWord ++ tailWord_2016647) baseStart_2016647 baseEnd_2016647 := by
    simpa [prefixWord, tailWord_2016647, baseEnd_2016647] using wordTrace_append hprefix tailTrace_2016647
  have hstable : (prefixWord ++ tailWord_2016647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016647).length < 2 ^ (prefixWord ++ tailWord_2016647).sum := by decide
  have hdescent : baseEnd_2016647 < baseStart_2016647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016660 : List Nat := [2, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_2016660 : Nat := 118140960795 + 2016660 * 2 ^ 59
def prefixEnd_2016660 : Nat := 4983230072969 + 3 ^ 40 * 2016660 * 2
def baseEnd_2016660 : Nat := 230114643710263342705679

theorem tailTrace_2016660 : CollatzResearch.WordTrace tailWord_2016660 prefixEnd_2016660 230114643710263342705679 := by
  unfold tailWord_2016660
  simp only [CollatzResearch.WordTrace]
  refine ⟨36776816436996356476291717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49035755249328475301722289 36776816436996356476291717)
  ·
    refine ⟨6895653081936816839304697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36776816436996356476291717 6895653081936816839304697)
    ·
      refine ⟨5171739811452612629478523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6895653081936816839304697 5171739811452612629478523)
      ·
        refine ⟨7757609717178918944217785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171739811452612629478523 7757609717178918944217785)
        ·
          refine ⟨5818207287884189208163339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7757609717178918944217785 5818207287884189208163339)
          ·
            refine ⟨8727310931826283812245009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818207287884189208163339 8727310931826283812245009)
            ·
              refine ⟨6545483198869712859183757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727310931826283812245009 6545483198869712859183757)
              ·
                refine ⟨2454556199576142322193909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6545483198869712859183757 2454556199576142322193909)
                ·
                  refine ⟨230114643710263342705679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2454556199576142322193909 230114643710263342705679)
                  ·
                    rfl

theorem cell22_2016660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_2016660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016660 prefixEnd_2016660 := by exact prefixLift 2016660
  have htrace : WordTrace (prefixWord ++ tailWord_2016660) baseStart_2016660 baseEnd_2016660 := by
    simpa [prefixWord, tailWord_2016660, baseEnd_2016660] using wordTrace_append hprefix tailTrace_2016660
  have hstable : (prefixWord ++ tailWord_2016660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016660).length < 2 ^ (prefixWord ++ tailWord_2016660).sum := by decide
  have hdescent : baseEnd_2016660 < baseStart_2016660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016718 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2016718 : Nat := 118140960795 + 2016718 * 2 ^ 59
def prefixEnd_2016718 : Nat := 4983230072969 + 3 ^ 40 * 2016718 * 2
def baseEnd_2016718 : Nat := 690363785716097210166859

theorem tailTrace_2016718 : CollatzResearch.WordTrace tailWord_2016718 prefixEnd_2016718 690363785716097210166859 := by
  unfold tailWord_2016718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194468538472823607274351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49037165538521725905463205 9194468538472823607274351)
  ·
    refine ⟨13791702807709235410911527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9194468538472823607274351 13791702807709235410911527)
    ·
      refine ⟨20687554211563853116367291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13791702807709235410911527 20687554211563853116367291)
      ·
        refine ⟨31031331317345779674550937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20687554211563853116367291 31031331317345779674550937)
        ·
          refine ⟨23273498488009334755913203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31031331317345779674550937 23273498488009334755913203)
          ·
            refine ⟨34910247732014002133869805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23273498488009334755913203 34910247732014002133869805)
            ·
              refine ⟨13091342899505250800201177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34910247732014002133869805 13091342899505250800201177)
              ·
                refine ⟨9818507174628938100150883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091342899505250800201177 9818507174628938100150883)
                ·
                  refine ⟨14727760761943407150226325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818507174628938100150883 14727760761943407150226325)
                  ·
                    refine ⟨690363785716097210166859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14727760761943407150226325 690363785716097210166859)
                    ·
                      rfl

theorem cell22_2016718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2016718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016718 prefixEnd_2016718 := by exact prefixLift 2016718
  have htrace : WordTrace (prefixWord ++ tailWord_2016718) baseStart_2016718 baseEnd_2016718 := by
    simpa [prefixWord, tailWord_2016718, baseEnd_2016718] using wordTrace_append hprefix tailTrace_2016718
  have hstable : (prefixWord ++ tailWord_2016718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016718).length < 2 ^ (prefixWord ++ tailWord_2016718).sum := by decide
  have hdescent : baseEnd_2016718 < baseStart_2016718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016810 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2016810 : Nat := 118140960795 + 2016810 * 2 ^ 59
def prefixEnd_2016810 : Nat := 4983230072969 + 3 ^ 40 * 2016810 * 2
def baseEnd_2016810 : Nat := 690395279196239636866577

theorem tailTrace_2016810 : CollatzResearch.WordTrace tailWord_2016810 prefixEnd_2016810 690395279196239636866577 := by
  unfold tailWord_2016810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18389775955862322142635971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49039402548966192380362589 18389775955862322142635971)
  ·
    refine ⟨27584663933793483213953957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18389775955862322142635971 27584663933793483213953957)
    ·
      refine ⟨5172124487586278102616367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27584663933793483213953957 5172124487586278102616367)
      ·
        refine ⟨7758186731379417153924551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172124487586278102616367 7758186731379417153924551)
        ·
          refine ⟨11637280097069125730886827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758186731379417153924551 11637280097069125730886827)
          ·
            refine ⟨17455920145603688596330241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637280097069125730886827 17455920145603688596330241)
            ·
              refine ⟨13091940109202766447247681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17455920145603688596330241 13091940109202766447247681)
              ·
                refine ⟨9818955081902074835435761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091940109202766447247681 9818955081902074835435761)
                ·
                  refine ⟨7364216311426556126576821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818955081902074835435761 7364216311426556126576821)
                  ·
                    refine ⟨690395279196239636866577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7364216311426556126576821 690395279196239636866577)
                    ·
                      rfl

theorem cell22_2016810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2016810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016810 prefixEnd_2016810 := by exact prefixLift 2016810
  have htrace : WordTrace (prefixWord ++ tailWord_2016810) baseStart_2016810 baseEnd_2016810 := by
    simpa [prefixWord, tailWord_2016810, baseEnd_2016810] using wordTrace_append hprefix tailTrace_2016810
  have hstable : (prefixWord ++ tailWord_2016810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016810).length < 2 ^ (prefixWord ++ tailWord_2016810).sum := by decide
  have hdescent : baseEnd_2016810 < baseStart_2016810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016825 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_2016825 : Nat := 118140960795 + 2016825 * 2 ^ 59
def prefixEnd_2016825 : Nat := 4983230072969 + 3 ^ 40 * 2016825 * 2
def baseEnd_2016825 : Nat := 690400414002784597741531

theorem tailTrace_2016825 : CollatzResearch.WordTrace tailWord_2016825 prefixEnd_2016825 690400414002784597741531 := by
  unfold tailWord_2016825
  simp only [CollatzResearch.WordTrace]
  refine ⟨73559650918394946132339929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49039767278929964088226619 73559650918394946132339929)
  ·
    refine ⟨55169738188796209599254947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73559650918394946132339929 55169738188796209599254947)
    ·
      refine ⟨82754607283194314398882421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55169738188796209599254947 82754607283194314398882421)
      ·
        refine ⟨7758244432799466974895227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82754607283194314398882421 7758244432799466974895227)
        ·
          refine ⟨11637366649199200462342841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758244432799466974895227 11637366649199200462342841)
          ·
            refine ⟨8728024986899400346757131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11637366649199200462342841 8728024986899400346757131)
            ·
              refine ⟨13092037480349100520135697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728024986899400346757131 13092037480349100520135697)
              ·
                refine ⟨9819028110261825390101773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092037480349100520135697 9819028110261825390101773)
                ·
                  refine ⟨3682135541348184521288165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9819028110261825390101773 3682135541348184521288165)
                  ·
                    refine ⟨690400414002784597741531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3682135541348184521288165 690400414002784597741531)
                    ·
                      rfl

theorem cell22_2016825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_2016825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016825 prefixEnd_2016825 := by exact prefixLift 2016825
  have htrace : WordTrace (prefixWord ++ tailWord_2016825) baseStart_2016825 baseEnd_2016825 := by
    simpa [prefixWord, tailWord_2016825, baseEnd_2016825] using wordTrace_append hprefix tailTrace_2016825
  have hstable : (prefixWord ++ tailWord_2016825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016825).length < 2 ^ (prefixWord ++ tailWord_2016825).sum := by decide
  have hdescent : baseEnd_2016825 < baseStart_2016825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016855 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_2016855 : Nat := 118140960795 + 2016855 * 2 ^ 59
def prefixEnd_2016855 : Nat := 4983230072969 + 3 ^ 40 * 2016855 * 2
def baseEnd_2016855 : Nat := 690410683615874519491439

theorem tailTrace_2016855 : CollatzResearch.WordTrace tailWord_2016855 prefixEnd_2016855 690410683615874519491439 := by
  unfold tailWord_2016855
  simp only [CollatzResearch.WordTrace]
  refine ⟨73560745108286261255932019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49040496738857507503954679 73560745108286261255932019)
  ·
    refine ⟨110341117662429391883898029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73560745108286261255932019 110341117662429391883898029)
    ·
      refine ⟨41377919123411021956461761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110341117662429391883898029 41377919123411021956461761)
      ·
        refine ⟨31033439342558266467346321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41377919123411021956461761 31033439342558266467346321)
        ·
          refine ⟨23275079506918699850509741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31033439342558266467346321 23275079506918699850509741)
          ·
            refine ⟨8728154815094512443941153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23275079506918699850509741 8728154815094512443941153)
            ·
              refine ⟨6546116111320884332955865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728154815094512443941153 6546116111320884332955865)
              ·
                refine ⟨4909587083490663249716899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546116111320884332955865 4909587083490663249716899)
                ·
                  refine ⟨7364380625235994874575349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909587083490663249716899 7364380625235994874575349)
                  ·
                    refine ⟨690410683615874519491439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7364380625235994874575349 690410683615874519491439)
                    ·
                      rfl

theorem cell22_2016855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_2016855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016855 prefixEnd_2016855 := by exact prefixLift 2016855
  have htrace : WordTrace (prefixWord ++ tailWord_2016855) baseStart_2016855 baseEnd_2016855 := by
    simpa [prefixWord, tailWord_2016855, baseEnd_2016855] using wordTrace_append hprefix tailTrace_2016855
  have hstable : (prefixWord ++ tailWord_2016855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016855).length < 2 ^ (prefixWord ++ tailWord_2016855).sum := by decide
  have hdescent : baseEnd_2016855 < baseStart_2016855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016889 : List Nat := [1, 2, 1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_2016889 : Nat := 118140960795 + 2016889 * 2 ^ 59
def prefixEnd_2016889 : Nat := 4983230072969 + 3 ^ 40 * 2016889 * 2
def baseEnd_2016889 : Nat := 690422322510709764141335

theorem tailTrace_2016889 : CollatzResearch.WordTrace tailWord_2016889 prefixEnd_2016889 690422322510709764141335 := by
  unfold tailWord_2016889
  simp only [CollatzResearch.WordTrace]
  refine ⟨73561985190163085062669721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49041323460108723375113147 73561985190163085062669721)
  ·
    refine ⟨55171488892622313797002291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73561985190163085062669721 55171488892622313797002291)
    ·
      refine ⟨82757233338933470695503437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55171488892622313797002291 82757233338933470695503437)
      ·
        refine ⟨31033962502100051510813789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82757233338933470695503437 31033962502100051510813789)
        ·
          refine ⟨11637735938287519316555171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31033962502100051510813789 11637735938287519316555171)
          ·
            refine ⟨17456603907431278974832757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637735938287519316555171 17456603907431278974832757)
            ·
              refine ⟨1636556616321682403890571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17456603907431278974832757 1636556616321682403890571)
              ·
                refine ⟨2454834924482523605835857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636556616321682403890571 2454834924482523605835857)
                ·
                  refine ⟨1841126193361892704376893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2454834924482523605835857 1841126193361892704376893)
                  ·
                    refine ⟨690422322510709764141335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841126193361892704376893 690422322510709764141335)
                    ·
                      rfl

theorem cell22_2016889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_2016889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016889 prefixEnd_2016889 := by exact prefixLift 2016889
  have htrace : WordTrace (prefixWord ++ tailWord_2016889) baseStart_2016889 baseEnd_2016889 := by
    simpa [prefixWord, tailWord_2016889, baseEnd_2016889] using wordTrace_append hprefix tailTrace_2016889
  have hstable : (prefixWord ++ tailWord_2016889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016889).length < 2 ^ (prefixWord ++ tailWord_2016889).sum := by decide
  have hdescent : baseEnd_2016889 < baseStart_2016889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2016936 : List Nat := [2, 1, 7, 1, 1, 1, 2, 7]
def baseStart_2016936 : Nat := 118140960795 + 2016936 * 2 ^ 59
def prefixEnd_2016936 : Nat := 4983230072969 + 3 ^ 40 * 2016936 * 2
def baseEnd_2016936 : Nat := 76715379063468589801799

theorem tailTrace_2016936 : CollatzResearch.WordTrace tailWord_2016936 prefixEnd_2016936 76715379063468589801799 := by
  unfold tailWord_2016936
  simp only [CollatzResearch.WordTrace]
  refine ⟨36781849710496406044815331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49042466280661874726420441 36781849710496406044815331)
  ·
    refine ⟨55172774565744609067222997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36781849710496406044815331 55172774565744609067222997)
    ·
      refine ⟨1293111903884639275013039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55172774565744609067222997 1293111903884639275013039)
      ·
        refine ⟨1939667855826958912519559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293111903884639275013039 1939667855826958912519559)
        ·
          refine ⟨2909501783740438368779339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939667855826958912519559 2909501783740438368779339)
          ·
            refine ⟨4364252675610657553169009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909501783740438368779339 4364252675610657553169009)
            ·
              refine ⟨3273189506707993164876757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364252675610657553169009 3273189506707993164876757)
              ·
                refine ⟨76715379063468589801799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3273189506707993164876757 76715379063468589801799)
                ·
                  rfl

theorem cell22_2016936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_2016936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2016936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2016936 prefixEnd_2016936 := by exact prefixLift 2016936
  have htrace : WordTrace (prefixWord ++ tailWord_2016936) baseStart_2016936 baseEnd_2016936 := by
    simpa [prefixWord, tailWord_2016936, baseEnd_2016936] using wordTrace_append hprefix tailTrace_2016936
  have hstable : (prefixWord ++ tailWord_2016936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2016936).length < 2 ^ (prefixWord ++ tailWord_2016936).sum := by decide
  have hdescent : baseEnd_2016936 < baseStart_2016936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2016936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017007 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 1, 5]
def baseStart_2017007 : Nat := 118140960795 + 2017007 * 2 ^ 59
def prefixEnd_2017007 : Nat := 4983230072969 + 3 ^ 40 * 2017007 * 2
def baseEnd_2017007 : Nat := 690462716322196789690973

theorem tailTrace_2017007 : CollatzResearch.WordTrace tailWord_2017007 prefixEnd_2017007 690462716322196789690973 := by
  unfold tailWord_2017007
  simp only [CollatzResearch.WordTrace]
  refine ⟨73566289003735591215465275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49044192669157060810310183 73566289003735591215465275)
  ·
    refine ⟨110349433505603386823197913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73566289003735591215465275 110349433505603386823197913)
    ·
      refine ⟨82762075129202540117398435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110349433505603386823197913 82762075129202540117398435)
      ·
        refine ⟨124143112693803810176097653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82762075129202540117398435 124143112693803810176097653)
        ·
          refine ⟨11638416815044107204009155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124143112693803810176097653 11638416815044107204009155)
          ·
            refine ⟨17457625222566160806013733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638416815044107204009155 17457625222566160806013733)
            ·
              refine ⟨3273304729231155151127575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17457625222566160806013733 3273304729231155151127575)
              ·
                refine ⟨4909957093846732726691363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273304729231155151127575 4909957093846732726691363)
                ·
                  refine ⟨7364935640770099090037045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909957093846732726691363 7364935640770099090037045)
                  ·
                    refine ⟨690462716322196789690973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7364935640770099090037045 690462716322196789690973)
                    ·
                      rfl

theorem cell22_2017007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_2017007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017007 prefixEnd_2017007 := by exact prefixLift 2017007
  have htrace : WordTrace (prefixWord ++ tailWord_2017007) baseStart_2017007 baseEnd_2017007 := by
    simpa [prefixWord, tailWord_2017007, baseEnd_2017007] using wordTrace_append hprefix tailTrace_2017007
  have hstable : (prefixWord ++ tailWord_2017007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017007).length < 2 ^ (prefixWord ++ tailWord_2017007).sum := by decide
  have hdescent : baseEnd_2017007 < baseStart_2017007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017026 : List Nat := [3, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2017026 : Nat := 118140960795 + 2017026 * 2 ^ 59
def prefixEnd_2017026 : Nat := 4983230072969 + 3 ^ 40 * 2017026 * 2
def baseEnd_2017026 : Nat := 230156406803495691155305

theorem tailTrace_2017026 : CollatzResearch.WordTrace tailWord_2017026 prefixEnd_2017026 230156406803495691155305 := by
  unfold tailWord_2017026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18391745497666689365101733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49044654660444504973604621 18391745497666689365101733)
  ·
    refine ⟨3448452280812504255956575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18391745497666689365101733 3448452280812504255956575)
    ·
      refine ⟨5172678421218756383934863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448452280812504255956575 5172678421218756383934863)
      ·
        refine ⟨7759017631828134575902295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172678421218756383934863 7759017631828134575902295)
        ·
          refine ⟨11638526447742201863853443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759017631828134575902295 11638526447742201863853443)
          ·
            refine ⟨17457789671613302795780165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638526447742201863853443 17457789671613302795780165)
            ·
              refine ⟨3273335563427494274208781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17457789671613302795780165 3273335563427494274208781)
              ·
                refine ⟨1227500836285310352828293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3273335563427494274208781 1227500836285310352828293)
                ·
                  refine ⟨230156406803495691155305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227500836285310352828293 230156406803495691155305)
                  ·
                    rfl

theorem cell22_2017026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2017026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017026 prefixEnd_2017026 := by exact prefixLift 2017026
  have htrace : WordTrace (prefixWord ++ tailWord_2017026) baseStart_2017026 baseEnd_2017026 := by
    simpa [prefixWord, tailWord_2017026, baseEnd_2017026] using wordTrace_append hprefix tailTrace_2017026
  have hstable : (prefixWord ++ tailWord_2017026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017026).length < 2 ^ (prefixWord ++ tailWord_2017026).sum := by decide
  have hdescent : baseEnd_2017026 < baseStart_2017026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017065 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 11]
def baseStart_2017065 : Nat := 118140960795 + 2017065 * 2 ^ 59
def prefixEnd_2017065 : Nat := 4983230072969 + 3 ^ 40 * 2017065 * 2
def baseEnd_2017065 : Nat := 230160856969167990580265

theorem tailTrace_2017065 : CollatzResearch.WordTrace tailWord_2017065 prefixEnd_2017065 230160856969167990580265 := by
  unfold tailWord_2017065
  simp only [CollatzResearch.WordTrace]
  refine ⟨73568404437525467121076649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49045602958350311414051099 73568404437525467121076649)
  ·
    refine ⟨55176303328144100340807487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73568404437525467121076649 55176303328144100340807487)
    ·
      refine ⟨82764454992216150511211231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55176303328144100340807487 82764454992216150511211231)
      ·
        refine ⟨124146682488324225766816847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82764454992216150511211231 124146682488324225766816847)
        ·
          refine ⟨186220023732486338650225271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124146682488324225766816847 186220023732486338650225271)
          ·
            refine ⟨279330035598729507975337907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186220023732486338650225271 279330035598729507975337907)
            ·
              refine ⟨418995053398094261963006861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279330035598729507975337907 418995053398094261963006861)
              ·
                refine ⟨157123145024285348236127573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418995053398094261963006861 157123145024285348236127573)
                ·
                  refine ⟨230160856969167990580265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 157123145024285348236127573 230160856969167990580265)
                  ·
                    rfl

theorem cell22_2017065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_2017065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017065 prefixEnd_2017065 := by exact prefixLift 2017065
  have htrace : WordTrace (prefixWord ++ tailWord_2017065) baseStart_2017065 baseEnd_2017065 := by
    simpa [prefixWord, tailWord_2017065, baseEnd_2017065] using wordTrace_append hprefix tailTrace_2017065
  have hstable : (prefixWord ++ tailWord_2017065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017065).length < 2 ^ (prefixWord ++ tailWord_2017065).sum := by decide
  have hdescent : baseEnd_2017065 < baseStart_2017065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017082 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_2017082 : Nat := 118140960795 + 2017082 * 2 ^ 59
def prefixEnd_2017082 : Nat := 4983230072969 + 3 ^ 40 * 2017082 * 2
def baseEnd_2017082 : Nat := 230162796784973864688581

theorem tailTrace_2017082 : CollatzResearch.WordTrace tailWord_2017082 prefixEnd_2017082 230162796784973864688581 := by
  unfold tailWord_2017082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392256119615969756111375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49046016318975919349630333 18392256119615969756111375)
  ·
    refine ⟨27588384179423954634167063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18392256119615969756111375 27588384179423954634167063)
    ·
      refine ⟨41382576269135931951250595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27588384179423954634167063 41382576269135931951250595)
      ·
        refine ⟨62073864403703897926875893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41382576269135931951250595 62073864403703897926875893)
        ·
          refine ⟨5819424787847240430644615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62073864403703897926875893 5819424787847240430644615)
          ·
            refine ⟨8729137181770860645966923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819424787847240430644615 8729137181770860645966923)
            ·
              refine ⟨13093705772656290968950385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729137181770860645966923 13093705772656290968950385)
              ·
                refine ⟨9820279329492218226712789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093705772656290968950385 9820279329492218226712789)
                ·
                  refine ⟨230162796784973864688581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9820279329492218226712789 230162796784973864688581)
                  ·
                    rfl

theorem cell22_2017082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_2017082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017082 prefixEnd_2017082 := by exact prefixLift 2017082
  have htrace : WordTrace (prefixWord ++ tailWord_2017082) baseStart_2017082 baseEnd_2017082 := by
    simpa [prefixWord, tailWord_2017082, baseEnd_2017082] using wordTrace_append hprefix tailTrace_2017082
  have hstable : (prefixWord ++ tailWord_2017082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017082).length < 2 ^ (prefixWord ++ tailWord_2017082).sum := by decide
  have hdescent : baseEnd_2017082 < baseStart_2017082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017116 : List Nat := [2, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_2017116 : Nat := 118140960795 + 2017116 * 2 ^ 59
def prefixEnd_2017116 : Nat := 4983230072969 + 3 ^ 40 * 2017116 * 2
def baseEnd_2017116 : Nat := 230166676416585612905213

theorem tailTrace_2017116 : CollatzResearch.WordTrace tailWord_2017116 prefixEnd_2017116 230166676416585612905213 := by
  unfold tailWord_2017116
  simp only [CollatzResearch.WordTrace]
  refine ⟨36785132280170351415591601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49046843040227135220788801 36785132280170351415591601)
  ·
    refine ⟨27588849210127763561693701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36785132280170351415591601 27588849210127763561693701)
    ·
      refine ⟨5172909226898955667817569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27588849210127763561693701 5172909226898955667817569)
      ·
        refine ⟨3879681920174216750863177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5172909226898955667817569 3879681920174216750863177)
        ·
          refine ⟨2909761440130662563147383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3879681920174216750863177 2909761440130662563147383)
          ·
            refine ⟨4364642160195993844721075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909761440130662563147383 4364642160195993844721075)
            ·
              refine ⟨6546963240293990767081613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364642160195993844721075 6546963240293990767081613)
              ·
                refine ⟨2455111215110246537655605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6546963240293990767081613 2455111215110246537655605)
                ·
                  refine ⟨230166676416585612905213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455111215110246537655605 230166676416585612905213)
                  ·
                    rfl

theorem cell22_2017116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_2017116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017116 prefixEnd_2017116 := by exact prefixLift 2017116
  have htrace : WordTrace (prefixWord ++ tailWord_2017116) baseStart_2017116 baseEnd_2017116 := by
    simpa [prefixWord, tailWord_2017116, baseEnd_2017116] using wordTrace_append hprefix tailTrace_2017116
  have hstable : (prefixWord ++ tailWord_2017116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017116).length < 2 ^ (prefixWord ++ tailWord_2017116).sum := by decide
  have hdescent : baseEnd_2017116 < baseStart_2017116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017127 : List Nat := [1, 1, 5, 1, 2, 1, 2, 1, 8]
def baseStart_2017127 : Nat := 118140960795 + 2017127 * 2 ^ 59
def prefixEnd_2017127 : Nat := 4983230072969 + 3 ^ 40 * 2017127 * 2
def baseEnd_2017127 : Nat := 230167931591518825563535

theorem tailTrace_2017127 : CollatzResearch.WordTrace tailWord_2017127 prefixEnd_2017127 230167931591518825563535 := by
  unfold tailWord_2017127
  simp only [CollatzResearch.WordTrace]
  refine ⟨73570665763300851709833635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49047110508867234473222423 73570665763300851709833635)
  ·
    refine ⟨110355998644951277564750453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73570665763300851709833635 110355998644951277564750453)
    ·
      refine ⟨10345874872964182271695355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110355998644951277564750453 10345874872964182271695355)
      ·
        refine ⟨15518812309446273407543033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345874872964182271695355 15518812309446273407543033)
        ·
          refine ⟨11639109232084705055657275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15518812309446273407543033 11639109232084705055657275)
          ·
            refine ⟨17458663848127057583485913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639109232084705055657275 17458663848127057583485913)
            ·
              refine ⟨13093997886095293187614435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17458663848127057583485913 13093997886095293187614435)
              ·
                refine ⟨19640996829142939781421653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13093997886095293187614435 19640996829142939781421653)
                ·
                  refine ⟨230167931591518825563535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19640996829142939781421653 230167931591518825563535)
                  ·
                    rfl

theorem cell22_2017127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_2017127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017127 prefixEnd_2017127 := by exact prefixLift 2017127
  have htrace : WordTrace (prefixWord ++ tailWord_2017127) baseStart_2017127 baseEnd_2017127 := by
    simpa [prefixWord, tailWord_2017127, baseEnd_2017127] using wordTrace_append hprefix tailTrace_2017127
  have hstable : (prefixWord ++ tailWord_2017127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017127).length < 2 ^ (prefixWord ++ tailWord_2017127).sum := by decide
  have hdescent : baseEnd_2017127 < baseStart_2017127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017191 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2017191 : Nat := 118140960795 + 2017191 * 2 ^ 59
def prefixEnd_2017191 : Nat := 4983230072969 + 3 ^ 40 * 2017191 * 2
def baseEnd_2017191 : Nat := 690525703282481643090409

theorem tailTrace_2017191 : CollatzResearch.WordTrace tailWord_2017191 prefixEnd_2017191 690525703282481643090409 := by
  unfold tailWord_2017191
  simp only [CollatzResearch.WordTrace]
  refine ⟨73573000035068990640163427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49048666690045993760108951 73573000035068990640163427)
  ·
    refine ⟨110359500052603485960245141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73573000035068990640163427 110359500052603485960245141)
    ·
      refine ⟨5173101564965788404386491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110359500052603485960245141 5173101564965788404386491)
      ·
        refine ⟨7759652347448682606579737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173101564965788404386491 7759652347448682606579737)
        ·
          refine ⟨5819739260586511954934803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7759652347448682606579737 5819739260586511954934803)
          ·
            refine ⟨8729608890879767932402205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819739260586511954934803 8729608890879767932402205)
            ·
              refine ⟨3273603334079912974650827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8729608890879767932402205 3273603334079912974650827)
              ·
                refine ⟨4910405001119869461976241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273603334079912974650827 4910405001119869461976241)
                ·
                  refine ⟨3682803750839902096482181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910405001119869461976241 3682803750839902096482181)
                  ·
                    refine ⟨690525703282481643090409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3682803750839902096482181 690525703282481643090409)
                    ·
                      rfl

theorem cell22_2017191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2017191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017191 prefixEnd_2017191 := by exact prefixLift 2017191
  have htrace : WordTrace (prefixWord ++ tailWord_2017191) baseStart_2017191 baseEnd_2017191 := by
    simpa [prefixWord, tailWord_2017191, baseEnd_2017191] using wordTrace_append hprefix tailTrace_2017191
  have hstable : (prefixWord ++ tailWord_2017191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017191).length < 2 ^ (prefixWord ++ tailWord_2017191).sum := by decide
  have hdescent : baseEnd_2017191 < baseStart_2017191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017328 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_2017328 : Nat := 118140960795 + 2017328 * 2 ^ 59
def prefixEnd_2017328 : Nat := 4983230072969 + 3 ^ 40 * 2017328 * 2
def baseEnd_2017328 : Nat := 690572601182258952414989

theorem tailTrace_2017328 : CollatzResearch.WordTrace tailWord_2017328 prefixEnd_2017328 690572601182258952414989 := by
  unfold tailWord_2017328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36788998417786331518950319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49051997890381775358600425 36788998417786331518950319)
  ·
    refine ⟨55183497626679497278425479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36788998417786331518950319 55183497626679497278425479)
    ·
      refine ⟨82775246440019245917638219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55183497626679497278425479 82775246440019245917638219)
      ·
        refine ⟨124162869660028868876457329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82775246440019245917638219 124162869660028868876457329)
        ·
          refine ⟨93122152245021651657342997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124162869660028868876457329 93122152245021651657342997)
          ·
            refine ⟨4365100886485389921437953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93122152245021651657342997 4365100886485389921437953)
            ·
              refine ⟨3273825664864042441078465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365100886485389921437953 3273825664864042441078465)
              ·
                refine ⟨2455369248648031830808849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273825664864042441078465 2455369248648031830808849)
                ·
                  refine ⟨1841526936486023873106637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455369248648031830808849 1841526936486023873106637)
                  ·
                    refine ⟨690572601182258952414989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841526936486023873106637 690572601182258952414989)
                    ·
                      rfl

theorem cell22_2017328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_2017328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017328 prefixEnd_2017328 := by exact prefixLift 2017328
  have htrace : WordTrace (prefixWord ++ tailWord_2017328) baseStart_2017328 baseEnd_2017328 := by
    simpa [prefixWord, tailWord_2017328, baseEnd_2017328] using wordTrace_append hprefix tailTrace_2017328
  have hstable : (prefixWord ++ tailWord_2017328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017328).length < 2 ^ (prefixWord ++ tailWord_2017328).sum := by decide
  have hdescent : baseEnd_2017328 < baseStart_2017328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017330 : List Nat := [3, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_2017330 : Nat := 118140960795 + 2017330 * 2 ^ 59
def prefixEnd_2017330 : Nat := 4983230072969 + 3 ^ 40 * 2017330 * 2
def baseEnd_2017330 : Nat := 230191095274377204621661

theorem tailTrace_2017330 : CollatzResearch.WordTrace tailWord_2017330 prefixEnd_2017330 230191095274377204621661 := by
  unfold tailWord_2017330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394517445391354344868361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49052046521043611586315629 18394517445391354344868361)
  ·
    refine ⟨13795888084043515758651271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18394517445391354344868361 13795888084043515758651271)
    ·
      refine ⟨20693832126065273637976907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13795888084043515758651271 20693832126065273637976907)
      ·
        refine ⟨31040748189097910456965361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20693832126065273637976907 31040748189097910456965361)
        ·
          refine ⟨23280561141823432842724021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31040748189097910456965361 23280561141823432842724021)
          ·
            refine ⟨2182552607045946829005377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23280561141823432842724021 2182552607045946829005377)
            ·
              refine ⟨1636914455284460121754033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182552607045946829005377 1636914455284460121754033)
              ·
                refine ⟨1227685841463345091315525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636914455284460121754033 1227685841463345091315525)
                ·
                  refine ⟨230191095274377204621661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227685841463345091315525 230191095274377204621661)
                  ·
                    rfl

theorem cell22_2017330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_2017330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017330 prefixEnd_2017330 := by exact prefixLift 2017330
  have htrace : WordTrace (prefixWord ++ tailWord_2017330) baseStart_2017330 baseEnd_2017330 := by
    simpa [prefixWord, tailWord_2017330, baseEnd_2017330] using wordTrace_append hprefix tailTrace_2017330
  have hstable : (prefixWord ++ tailWord_2017330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017330).length < 2 ^ (prefixWord ++ tailWord_2017330).sum := by decide
  have hdescent : baseEnd_2017330 < baseStart_2017330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017354 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2017354 : Nat := 118140960795 + 2017354 * 2 ^ 59
def prefixEnd_2017354 : Nat := 4983230072969 + 3 ^ 40 * 2017354 * 2
def baseEnd_2017354 : Nat := 690581501513603551264909

theorem tailTrace_2017354 : CollatzResearch.WordTrace tailWord_2017354 prefixEnd_2017354 690581501513603551264909 := by
  unfold tailWord_2017354
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394736283369617369586779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49052630088985646318898077 18394736283369617369586779)
  ·
    refine ⟨27592104425054426054380169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18394736283369617369586779 27592104425054426054380169)
    ·
      refine ⟨20694078318790819540785127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27592104425054426054380169 20694078318790819540785127)
      ·
        refine ⟨31041117478186229311177691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20694078318790819540785127 31041117478186229311177691)
        ·
          refine ⟨46561676217279343966766537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31041117478186229311177691 46561676217279343966766537)
          ·
            refine ⟨34921257162959507975074903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46561676217279343966766537 34921257162959507975074903)
            ·
              refine ⟨52381885744439261962612355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34921257162959507975074903 52381885744439261962612355)
              ·
                refine ⟨78572828616658892943918533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52381885744439261962612355 78572828616658892943918533)
                ·
                  refine ⟨14732405365623542426984725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78572828616658892943918533 14732405365623542426984725)
                  ·
                    refine ⟨690581501513603551264909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14732405365623542426984725 690581501513603551264909)
                    ·
                      rfl

theorem cell22_2017354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2017354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017354 prefixEnd_2017354 := by exact prefixLift 2017354
  have htrace : WordTrace (prefixWord ++ tailWord_2017354) baseStart_2017354 baseEnd_2017354 := by
    simpa [prefixWord, tailWord_2017354, baseEnd_2017354] using wordTrace_append hprefix tailTrace_2017354
  have hstable : (prefixWord ++ tailWord_2017354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017354).length < 2 ^ (prefixWord ++ tailWord_2017354).sum := by decide
  have hdescent : baseEnd_2017354 < baseStart_2017354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017356 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 5, 3]
def baseStart_2017356 : Nat := 118140960795 + 2017356 * 2 ^ 59
def prefixEnd_2017356 : Nat := 4983230072969 + 3 ^ 40 * 2017356 * 2
def baseEnd_2017356 : Nat := 690582186154476212714903

theorem tailTrace_2017356 : CollatzResearch.WordTrace tailWord_2017356 prefixEnd_2017356 690582186154476212714903 := by
  unfold tailWord_2017356
  simp only [CollatzResearch.WordTrace]
  refine ⟨36789509039735611909959961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49052678719647482546613281 36789509039735611909959961)
  ·
    refine ⟨27592131779801708932469971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36789509039735611909959961 27592131779801708932469971)
    ·
      refine ⟨41388197669702563398704957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27592131779801708932469971 41388197669702563398704957)
      ·
        refine ⟨15520574126138461274514359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41388197669702563398704957 15520574126138461274514359)
        ·
          refine ⟨23280861189207691911771539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15520574126138461274514359 23280861189207691911771539)
          ·
            refine ⟨34921291783811537867657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23280861189207691911771539 34921291783811537867657309)
            ·
              refine ⟨13095484418929326700371491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34921291783811537867657309 13095484418929326700371491)
              ·
                refine ⟨19643226628393990050557237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13095484418929326700371491 19643226628393990050557237)
                ·
                  refine ⟨1841552496411936567239741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19643226628393990050557237 1841552496411936567239741)
                  ·
                    refine ⟨690582186154476212714903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841552496411936567239741 690582186154476212714903)
                    ·
                      rfl

theorem cell22_2017356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_2017356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017356 prefixEnd_2017356 := by exact prefixLift 2017356
  have htrace : WordTrace (prefixWord ++ tailWord_2017356) baseStart_2017356 baseEnd_2017356 := by
    simpa [prefixWord, tailWord_2017356, baseEnd_2017356] using wordTrace_append hprefix tailTrace_2017356
  have hstable : (prefixWord ++ tailWord_2017356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017356).length < 2 ^ (prefixWord ++ tailWord_2017356).sum := by decide
  have hdescent : baseEnd_2017356 < baseStart_2017356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017369 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 7]
def baseStart_2017369 : Nat := 118140960795 + 2017369 * 2 ^ 59
def prefixEnd_2017369 : Nat := 4983230072969 + 3 ^ 40 * 2017369 * 2
def baseEnd_2017369 : Nat := 230195545440049504046621

theorem tailTrace_2017369 : CollatzResearch.WordTrace tailWord_2017369 prefixEnd_2017369 230195545440049504046621 := by
  unfold tailWord_2017369
  simp only [CollatzResearch.WordTrace]
  refine ⟨73579492228424127040143161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49052994818949418026762107 73579492228424127040143161)
  ·
    refine ⟨55184619171318095280107371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73579492228424127040143161 55184619171318095280107371)
    ·
      refine ⟨82776928756977142920161057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55184619171318095280107371 82776928756977142920161057)
      ·
        refine ⟨62082696567732857190120793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82776928756977142920161057 62082696567732857190120793)
        ·
          refine ⟨46562022425799642892590595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62082696567732857190120793 46562022425799642892590595)
          ·
            refine ⟨69843033638699464338885893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46562022425799642892590595 69843033638699464338885893)
            ·
              refine ⟨13095568807256149563541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69843033638699464338885893 13095568807256149563541105)
              ·
                refine ⟨9821676605442112172655829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13095568807256149563541105 9821676605442112172655829)
                ·
                  refine ⟨230195545440049504046621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9821676605442112172655829 230195545440049504046621)
                  ·
                    rfl

theorem cell22_2017369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_2017369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017369 prefixEnd_2017369 := by exact prefixLift 2017369
  have htrace : WordTrace (prefixWord ++ tailWord_2017369) baseStart_2017369 baseEnd_2017369 := by
    simpa [prefixWord, tailWord_2017369, baseEnd_2017369] using wordTrace_append hprefix tailTrace_2017369
  have hstable : (prefixWord ++ tailWord_2017369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017369).length < 2 ^ (prefixWord ++ tailWord_2017369).sum := by decide
  have hdescent : baseEnd_2017369 < baseStart_2017369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017390 : List Nat := [4, 1, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2017390 : Nat := 118140960795 + 2017390 * 2 ^ 59
def prefixEnd_2017390 : Nat := 4983230072969 + 3 ^ 40 * 2017390 * 2
def baseEnd_2017390 : Nat := 690593825049311457364799

theorem tailTrace_2017390 : CollatzResearch.WordTrace tailWord_2017390 prefixEnd_2017390 690593825049311457364799 := by
  unfold tailWord_2017390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197532270168505953332203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49053505440898698417771749 9197532270168505953332203)
  ·
    refine ⟨13796298405252758929998305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197532270168505953332203 13796298405252758929998305)
    ·
      refine ⟨10347223803939569197498729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13796298405252758929998305 10347223803939569197498729)
      ·
        refine ⟨7760417852954676898124047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10347223803939569197498729 7760417852954676898124047)
        ·
          refine ⟨11640626779432015347186071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760417852954676898124047 11640626779432015347186071)
          ·
            refine ⟨17460940169148023020779107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640626779432015347186071 17460940169148023020779107)
            ·
              refine ⟨26191410253722034531168661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17460940169148023020779107 26191410253722034531168661)
              ·
                refine ⟨1227722355643220368648531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26191410253722034531168661 1227722355643220368648531)
                ·
                  refine ⟨1841583533464830552972797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227722355643220368648531 1841583533464830552972797)
                  ·
                    refine ⟨690593825049311457364799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841583533464830552972797 690593825049311457364799)
                    ·
                      rfl

theorem cell22_2017390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2017390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017390 prefixEnd_2017390 := by exact prefixLift 2017390
  have htrace : WordTrace (prefixWord ++ tailWord_2017390) baseStart_2017390 baseEnd_2017390 := by
    simpa [prefixWord, tailWord_2017390, baseEnd_2017390] using wordTrace_append hprefix tailTrace_2017390
  have hstable : (prefixWord ++ tailWord_2017390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017390).length < 2 ^ (prefixWord ++ tailWord_2017390).sum := by decide
  have hdescent : baseEnd_2017390 < baseStart_2017390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017401 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_2017401 : Nat := 118140960795 + 2017401 * 2 ^ 59
def prefixEnd_2017401 : Nat := 4983230072969 + 3 ^ 40 * 2017401 * 2
def baseEnd_2017401 : Nat := 690597590574111095339765

theorem tailTrace_2017401 : CollatzResearch.WordTrace tailWord_2017401 prefixEnd_2017401 690597590574111095339765 := by
  unfold tailWord_2017401
  simp only [CollatzResearch.WordTrace]
  refine ⟨73580659364308196505308057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49053772909538797670205371 73580659364308196505308057)
  ·
    refine ⟨55185494523231147378981043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73580659364308196505308057 55185494523231147378981043)
    ·
      refine ⟨82778241784846721068471565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55185494523231147378981043 82778241784846721068471565)
      ·
        refine ⟨31041840669317520400676837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82778241784846721068471565 31041840669317520400676837)
        ·
          refine ⟨5820345125497035075126907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31041840669317520400676837 5820345125497035075126907)
          ·
            refine ⟨8730517688245552612690361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820345125497035075126907 8730517688245552612690361)
            ·
              refine ⟨6547888266184164459517771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8730517688245552612690361 6547888266184164459517771)
              ·
                refine ⟨9821832399276246689276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547888266184164459517771 9821832399276246689276657)
                ·
                  refine ⟨7366374299457185016957493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9821832399276246689276657 7366374299457185016957493)
                  ·
                    refine ⟨690597590574111095339765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7366374299457185016957493 690597590574111095339765)
                    ·
                      rfl

theorem cell22_2017401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_2017401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017401 prefixEnd_2017401 := by exact prefixLift 2017401
  have htrace : WordTrace (prefixWord ++ tailWord_2017401) baseStart_2017401 baseEnd_2017401 := by
    simpa [prefixWord, tailWord_2017401, baseEnd_2017401] using wordTrace_append hprefix tailTrace_2017401
  have hstable : (prefixWord ++ tailWord_2017401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017401).length < 2 ^ (prefixWord ++ tailWord_2017401).sum := by decide
  have hdescent : baseEnd_2017401 < baseStart_2017401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017454 : List Nat := [4, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_2017454 : Nat := 118140960795 + 2017454 * 2 ^ 59
def prefixEnd_2017454 : Nat := 4983230072969 + 3 ^ 40 * 2017454 * 2
def baseEnd_2017454 : Nat := 230205244519078874588201

theorem tailTrace_2017454 : CollatzResearch.WordTrace tailWord_2017454 prefixEnd_2017454 230205244519078874588201 := by
  unfold tailWord_2017454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197824054139523319623427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49055061622077457704658277 9197824054139523319623427)
  ·
    refine ⟨13796736081209284979435141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197824054139523319623427 13796736081209284979435141)
    ·
      refine ⟨2586888015226740933644089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13796736081209284979435141 2586888015226740933644089)
      ·
        refine ⟨1940166011420055700233067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586888015226740933644089 1940166011420055700233067)
        ·
          refine ⟨2910249017130083550349601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1940166011420055700233067 2910249017130083550349601)
          ·
            refine ⟨2182686762847562662762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2910249017130083550349601 2182686762847562662762201)
            ·
              refine ⟨1637015072135671997071651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182686762847562662762201 1637015072135671997071651)
              ·
                refine ⟨2455522608203507995607477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637015072135671997071651 2455522608203507995607477)
                ·
                  refine ⟨230205244519078874588201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455522608203507995607477 230205244519078874588201)
                  ·
                    rfl

theorem cell22_2017454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_2017454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017454 prefixEnd_2017454 := by exact prefixLift 2017454
  have htrace : WordTrace (prefixWord ++ tailWord_2017454) baseStart_2017454 baseEnd_2017454 := by
    simpa [prefixWord, tailWord_2017454, baseEnd_2017454] using wordTrace_append hprefix tailTrace_2017454
  have hstable : (prefixWord ++ tailWord_2017454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017454).length < 2 ^ (prefixWord ++ tailWord_2017454).sum := by decide
  have hdescent : baseEnd_2017454 < baseStart_2017454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017493 : List Nat := [1, 3, 2, 4, 3, 9]
def baseStart_2017493 : Nat := 118140960795 + 2017493 * 2 ^ 59
def prefixEnd_2017493 : Nat := 4983230072969 + 3 ^ 40 * 2017493 * 2
def baseEnd_2017493 : Nat := 8526284988324117556043

theorem tailTrace_2017493 : CollatzResearch.WordTrace tailWord_2017493 prefixEnd_2017493 8526284988324117556043 := by
  unfold tailWord_2017493
  simp only [CollatzResearch.WordTrace]
  refine ⟨73584014879974896217657133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49056009919983264145104755 73584014879974896217657133)
  ·
    refine ⟨27594005579990586081621425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73584014879974896217657133 27594005579990586081621425)
    ·
      refine ⟨20695504184992939561216069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27594005579990586081621425 20695504184992939561216069)
      ·
        refine ⟨3880407034686176167728013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20695504184992939561216069 3880407034686176167728013)
        ·
          refine ⟨1455152638007316062898005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3880407034686176167728013 1455152638007316062898005)
          ·
            refine ⟨8526284988324117556043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1455152638007316062898005 8526284988324117556043)
            ·
              rfl

theorem cell22_2017493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 9].length) (baseStart_2017493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017493 prefixEnd_2017493 := by exact prefixLift 2017493
  have htrace : WordTrace (prefixWord ++ tailWord_2017493) baseStart_2017493 baseEnd_2017493 := by
    simpa [prefixWord, tailWord_2017493, baseEnd_2017493] using wordTrace_append hprefix tailTrace_2017493
  have hstable : (prefixWord ++ tailWord_2017493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017493).length < 2 ^ (prefixWord ++ tailWord_2017493).sum := by decide
  have hdescent : baseEnd_2017493 < baseStart_2017493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017508 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_2017508 : Nat := 118140960795 + 2017508 * 2 ^ 59
def prefixEnd_2017508 : Nat := 4983230072969 + 3 ^ 40 * 2017508 * 2
def baseEnd_2017508 : Nat := 690634218860798482914437

theorem tailTrace_2017508 : CollatzResearch.WordTrace tailWord_2017508 prefixEnd_2017508 690634218860798482914437 := by
  unfold tailWord_2017508
  simp only [CollatzResearch.WordTrace]
  refine ⟨36792280987460276889726589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49056374649947035852968785 36792280987460276889726589)
  ·
    refine ⟨13797105370297603833647471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36792280987460276889726589 13797105370297603833647471)
    ·
      refine ⟨20695658055446405750471207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13797105370297603833647471 20695658055446405750471207)
      ·
        refine ⟨31043487083169608625706811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20695658055446405750471207 31043487083169608625706811)
        ·
          refine ⟨46565230624754412938560217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31043487083169608625706811 46565230624754412938560217)
          ·
            refine ⟨34923922968565809703920163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46565230624754412938560217 34923922968565809703920163)
            ·
              refine ⟨52385884452848714555880245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34923922968565809703920163 52385884452848714555880245)
              ·
                refine ⟨4911176667454566989613773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52385884452848714555880245 4911176667454566989613773)
                ·
                  refine ⟨1841691250295462621105165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4911176667454566989613773 1841691250295462621105165)
                  ·
                    refine ⟨690634218860798482914437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841691250295462621105165 690634218860798482914437)
                    ·
                      rfl

theorem cell22_2017508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_2017508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017508 prefixEnd_2017508 := by exact prefixLift 2017508
  have htrace : WordTrace (prefixWord ++ tailWord_2017508) baseStart_2017508 baseEnd_2017508 := by
    simpa [prefixWord, tailWord_2017508, baseEnd_2017508] using wordTrace_append hprefix tailTrace_2017508
  have hstable : (prefixWord ++ tailWord_2017508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017508).length < 2 ^ (prefixWord ++ tailWord_2017508).sum := by decide
  have hdescent : baseEnd_2017508 < baseStart_2017508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017617 : List Nat := [1, 2, 2, 1, 4, 3, 3, 2, 4]
def baseStart_2017617 : Nat := 118140960795 + 2017617 * 2 ^ 59
def prefixEnd_2017617 : Nat := 4983230072969 + 3 ^ 40 * 2017617 * 2
def baseEnd_2017617 : Nat := 230223843929452843979701

theorem tailTrace_2017617 : CollatzResearch.WordTrace tailWord_2017617 prefixEnd_2017617 230223843929452843979701 := by
  unfold tailWord_2017617
  simp only [CollatzResearch.WordTrace]
  refine ⟨73588537531525665395171105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49059025021017110263447403 73588537531525665395171105)
  ·
    refine ⟨55191403148644249046378329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73588537531525665395171105 55191403148644249046378329)
    ·
      refine ⟨41393552361483186784783747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55191403148644249046378329 41393552361483186784783747)
      ·
        refine ⟨62090328542224780177175621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41393552361483186784783747 62090328542224780177175621)
        ·
          refine ⟨11641936601667146283220429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62090328542224780177175621 11641936601667146283220429)
          ·
            refine ⟨4365726225625179856207661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11641936601667146283220429 4365726225625179856207661)
            ·
              refine ⟨1637147334609442446077873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4365726225625179856207661 1637147334609442446077873)
              ·
                refine ⟨1227860500957081834558405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637147334609442446077873 1227860500957081834558405)
                ·
                  refine ⟨230223843929452843979701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227860500957081834558405 230223843929452843979701)
                  ·
                    rfl

theorem cell22_2017617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_2017617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017617 prefixEnd_2017617 := by exact prefixLift 2017617
  have htrace : WordTrace (prefixWord ++ tailWord_2017617) baseStart_2017617 baseEnd_2017617 := by
    simpa [prefixWord, tailWord_2017617, baseEnd_2017617] using wordTrace_append hprefix tailTrace_2017617
  have hstable : (prefixWord ++ tailWord_2017617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017617).length < 2 ^ (prefixWord ++ tailWord_2017617).sum := by decide
  have hdescent : baseEnd_2017617 < baseStart_2017617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017632 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 2, 3]
def baseStart_2017632 : Nat := 118140960795 + 2017632 * 2 ^ 59
def prefixEnd_2017632 : Nat := 4983230072969 + 3 ^ 40 * 2017632 * 2
def baseEnd_2017632 : Nat := 690676666594903492814057

theorem tailTrace_2017632 : CollatzResearch.WordTrace tailWord_2017632 prefixEnd_2017632 690676666594903492814057 := by
  unfold tailWord_2017632
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794542313235661478483575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49059389750980881971311433 36794542313235661478483575)
  ·
    refine ⟨55191813469853492217725363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36794542313235661478483575 55191813469853492217725363)
    ·
      refine ⟨82787720204780238326588045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55191813469853492217725363 82787720204780238326588045)
      ·
        refine ⟨31045395076792589372470517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82787720204780238326588045 31045395076792589372470517)
        ·
          refine ⟨2910505788449305253669111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31045395076792589372470517 2910505788449305253669111)
          ·
            refine ⟨4365758682673957880503667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910505788449305253669111 4365758682673957880503667)
            ·
              refine ⟨6548638024010936820755501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365758682673957880503667 6548638024010936820755501)
              ·
                refine ⟨2455739259004101307783313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6548638024010936820755501 2455739259004101307783313)
                ·
                  refine ⟨1841804444253075980837485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455739259004101307783313 1841804444253075980837485)
                  ·
                    refine ⟨690676666594903492814057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841804444253075980837485 690676666594903492814057)
                    ·
                      rfl

theorem cell22_2017632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_2017632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017632 prefixEnd_2017632 := by exact prefixLift 2017632
  have htrace : WordTrace (prefixWord ++ tailWord_2017632) baseStart_2017632 baseEnd_2017632 := by
    simpa [prefixWord, tailWord_2017632, baseEnd_2017632] using wordTrace_append hprefix tailTrace_2017632
  have hstable : (prefixWord ++ tailWord_2017632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017632).length < 2 ^ (prefixWord ++ tailWord_2017632).sum := by decide
  have hdescent : baseEnd_2017632 < baseStart_2017632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017666 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2017666 : Nat := 118140960795 + 2017666 * 2 ^ 59
def prefixEnd_2017666 : Nat := 4983230072969 + 3 ^ 40 * 2017666 * 2
def baseEnd_2017666 : Nat := 690688305489738737463953

theorem tailTrace_2017666 : CollatzResearch.WordTrace tailWord_2017666 prefixEnd_2017666 690688305489738737463953 := by
  unfold tailWord_2017666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397581177087036690926213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49060216472232097842469901 18397581177087036690926213)
  ·
    refine ⟨3449546470703819379548665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18397581177087036690926213 3449546470703819379548665)
    ·
      refine ⟨2587159853027864534661499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3449546470703819379548665 2587159853027864534661499)
      ·
        refine ⟨3880739779541796801992249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587159853027864534661499 3880739779541796801992249)
        ·
          refine ⟨2910554834656347601494187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3880739779541796801992249 2910554834656347601494187)
          ·
            refine ⟨4365832251984521402241281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910554834656347601494187 4365832251984521402241281)
            ·
              refine ⟨3274374188988391051680961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365832251984521402241281 3274374188988391051680961)
              ·
                refine ⟨2455780641741293288760721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274374188988391051680961 2455780641741293288760721)
                ·
                  refine ⟨1841835481305969966570541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2455780641741293288760721 1841835481305969966570541)
                  ·
                    refine ⟨690688305489738737463953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841835481305969966570541 690688305489738737463953)
                    ·
                      rfl

theorem cell22_2017666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2017666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017666 prefixEnd_2017666 := by exact prefixLift 2017666
  have htrace : WordTrace (prefixWord ++ tailWord_2017666) baseStart_2017666 baseEnd_2017666 := by
    simpa [prefixWord, tailWord_2017666, baseEnd_2017666] using wordTrace_append hprefix tailTrace_2017666
  have hstable : (prefixWord ++ tailWord_2017666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017666).length < 2 ^ (prefixWord ++ tailWord_2017666).sum := by decide
  have hdescent : baseEnd_2017666 < baseStart_2017666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017690 : List Nat := [3, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_2017690 : Nat := 118140960795 + 2017690 * 2 ^ 59
def prefixEnd_2017690 : Nat := 4983230072969 + 3 ^ 40 * 2017690 * 2
def baseEnd_2017690 : Nat := 230232173726736891621293

theorem tailTrace_2017690 : CollatzResearch.WordTrace tailWord_2017690 prefixEnd_2017690 230232173726736891621293 := by
  unfold tailWord_2017690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397800015065299715644631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49060800040174132575052349 18397800015065299715644631)
  ·
    refine ⟨27596700022597949573466947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18397800015065299715644631 27596700022597949573466947)
    ·
      refine ⟨41395050033896924360200421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27596700022597949573466947 41395050033896924360200421)
      ·
        refine ⟨7761571881355673317537579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41395050033896924360200421 7761571881355673317537579)
        ·
          refine ⟨11642357822033509976306369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761571881355673317537579 11642357822033509976306369)
          ·
            refine ⟨8731768366525132482229777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11642357822033509976306369 8731768366525132482229777)
            ·
              refine ⟨6548826274893849361672333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8731768366525132482229777 6548826274893849361672333)
              ·
                refine ⟨2455809853085193510627125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6548826274893849361672333 2455809853085193510627125)
                ·
                  refine ⟨230232173726736891621293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455809853085193510627125 230232173726736891621293)
                  ·
                    rfl

theorem cell22_2017690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_2017690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017690 prefixEnd_2017690 := by exact prefixLift 2017690
  have htrace : WordTrace (prefixWord ++ tailWord_2017690) baseStart_2017690 baseEnd_2017690 := by
    simpa [prefixWord, tailWord_2017690, baseEnd_2017690] using wordTrace_append hprefix tailTrace_2017690
  have hstable : (prefixWord ++ tailWord_2017690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017690).length < 2 ^ (prefixWord ++ tailWord_2017690).sum := by decide
  have hdescent : baseEnd_2017690 < baseStart_2017690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017694 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2017694 : Nat := 118140960795 + 2017694 * 2 ^ 59
def prefixEnd_2017694 : Nat := 4983230072969 + 3 ^ 40 * 2017694 * 2
def baseEnd_2017694 : Nat := 690697890461955997763867

theorem tailTrace_2017694 : CollatzResearch.WordTrace tailWord_2017694 prefixEnd_2017694 690697890461955997763867 := by
  unfold tailWord_2017694
  simp only [CollatzResearch.WordTrace]
  refine ⟨9198918244030838443215517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49060897301497805030482757 9198918244030838443215517)
  ·
    refine ⟨3449594341511564416205819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9198918244030838443215517 3449594341511564416205819)
    ·
      refine ⟨5174391512267346624308729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449594341511564416205819 5174391512267346624308729)
      ·
        refine ⟨3880793634200509968231547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5174391512267346624308729 3880793634200509968231547)
        ·
          refine ⟨5821190451300764952347321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880793634200509968231547 5821190451300764952347321)
          ·
            refine ⟨4365892838475573714260491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821190451300764952347321 4365892838475573714260491)
            ·
              refine ⟨6548839257713360571390737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365892838475573714260491 6548839257713360571390737)
              ·
                refine ⟨4911629443285020428543053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6548839257713360571390737 4911629443285020428543053)
                ·
                  refine ⟨1841861041231882660703645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4911629443285020428543053 1841861041231882660703645)
                  ·
                    refine ⟨690697890461955997763867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1841861041231882660703645 690697890461955997763867)
                    ·
                      rfl

theorem cell22_2017694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2017694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017694 prefixEnd_2017694 := by exact prefixLift 2017694
  have htrace : WordTrace (prefixWord ++ tailWord_2017694) baseStart_2017694 baseEnd_2017694 := by
    simpa [prefixWord, tailWord_2017694, baseEnd_2017694] using wordTrace_append hprefix tailTrace_2017694
  have hstable : (prefixWord ++ tailWord_2017694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017694).length < 2 ^ (prefixWord ++ tailWord_2017694).sum := by decide
  have hdescent : baseEnd_2017694 < baseStart_2017694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017735 : List Nat := [1, 1, 4, 1, 1, 5, 2, 1, 6]
def baseStart_2017735 : Nat := 118140960795 + 2017735 * 2 ^ 59
def prefixEnd_2017735 : Nat := 4983230072969 + 3 ^ 40 * 2017735 * 2
def baseEnd_2017735 : Nat := 230237308533281852496247

theorem tailTrace_2017735 : CollatzResearch.WordTrace tailWord_2017735 prefixEnd_2017735 230237308533281852496247 := by
  unfold tailWord_2017735
  simp only [CollatzResearch.WordTrace]
  refine ⟨73592841345098171547966659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49061894230065447698644439 73592841345098171547966659)
  ·
    refine ⟨110389262017647257321949989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73592841345098171547966659 110389262017647257321949989)
    ·
      refine ⟨20697986628308860747865623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110389262017647257321949989 20697986628308860747865623)
      ·
        refine ⟨31046979942463291121798435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20697986628308860747865623 31046979942463291121798435)
        ·
          refine ⟨46570469913694936682697653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31046979942463291121798435 46570469913694936682697653)
          ·
            refine ⟨4365981554408900314002905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46570469913694936682697653 4365981554408900314002905)
            ·
              refine ⟨3274486165806675235502179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365981554408900314002905 3274486165806675235502179)
              ·
                refine ⟨4911729248710012853253269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274486165806675235502179 4911729248710012853253269)
                ·
                  refine ⟨230237308533281852496247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4911729248710012853253269 230237308533281852496247)
                  ·
                    rfl

theorem cell22_2017735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 1, 6].length) (baseStart_2017735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017735 prefixEnd_2017735 := by exact prefixLift 2017735
  have htrace : WordTrace (prefixWord ++ tailWord_2017735) baseStart_2017735 baseEnd_2017735 := by
    simpa [prefixWord, tailWord_2017735, baseEnd_2017735] using wordTrace_append hprefix tailTrace_2017735
  have hstable : (prefixWord ++ tailWord_2017735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017735).length < 2 ^ (prefixWord ++ tailWord_2017735).sum := by decide
  have hdescent : baseEnd_2017735 < baseStart_2017735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017782 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2017782 : Nat := 118140960795 + 2017782 * 2 ^ 59
def prefixEnd_2017782 : Nat := 4983230072969 + 3 ^ 40 * 2017782 * 2
def baseEnd_2017782 : Nat := 690728014660353101563597

theorem tailTrace_2017782 : CollatzResearch.WordTrace tailWord_2017782 prefixEnd_2017782 690728014660353101563597 := by
  unfold tailWord_2017782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599659723495493660932975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49063037050618599049951733 4599659723495493660932975)
  ·
    refine ⟨6899489585243240491399463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4599659723495493660932975 6899489585243240491399463)
    ·
      refine ⟨10349234377864860737099195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6899489585243240491399463 10349234377864860737099195)
      ·
        refine ⟨15523851566797291105648793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10349234377864860737099195 15523851566797291105648793)
        ·
          refine ⟨11642888675097968329236595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15523851566797291105648793 11642888675097968329236595)
          ·
            refine ⟨17464333012646952493854893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11642888675097968329236595 17464333012646952493854893)
            ·
              refine ⟨6549124879742607185195585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17464333012646952493854893 6549124879742607185195585)
              ·
                refine ⟨4911843659806955388896689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549124879742607185195585 4911843659806955388896689)
                ·
                  refine ⟨3683882744855216541672517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911843659806955388896689 3683882744855216541672517)
                  ·
                    refine ⟨690728014660353101563597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3683882744855216541672517 690728014660353101563597)
                    ·
                      rfl

theorem cell22_2017782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2017782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017782 prefixEnd_2017782 := by exact prefixLift 2017782
  have htrace : WordTrace (prefixWord ++ tailWord_2017782) baseStart_2017782 baseEnd_2017782 := by
    simpa [prefixWord, tailWord_2017782, baseEnd_2017782] using wordTrace_append hprefix tailTrace_2017782
  have hstable : (prefixWord ++ tailWord_2017782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017782).length < 2 ^ (prefixWord ++ tailWord_2017782).sum := by decide
  have hdescent : baseEnd_2017782 < baseStart_2017782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017837 : List Nat := [1, 5, 4, 1, 2, 1, 2, 2, 4]
def baseStart_2017837 : Nat := 118140960795 + 2017837 * 2 ^ 59
def prefixEnd_2017837 : Nat := 4983230072969 + 3 ^ 40 * 2017837 * 2
def baseEnd_2017837 : Nat := 230248947428117097146143

theorem tailTrace_2017837 : CollatzResearch.WordTrace tailWord_2017837 prefixEnd_2017837 230248947428117097146143 := by
  unfold tailWord_2017837
  simp only [CollatzResearch.WordTrace]
  refine ⟨73596561590728642968179765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49064374393819095312119843 73596561590728642968179765)
  ·
    refine ⟨6899677649130810278266853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73596561590728642968179765 6899677649130810278266853)
    ·
      refine ⟨1293689559212026927175035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6899677649130810278266853 1293689559212026927175035)
      ·
        refine ⟨1940534338818040390762553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293689559212026927175035 1940534338818040390762553)
        ·
          refine ⟨1455400754113530293071915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940534338818040390762553 1455400754113530293071915)
          ·
            refine ⟨2183101131170295439607873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455400754113530293071915 2183101131170295439607873)
            ·
              refine ⟨1637325848377721579705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183101131170295439607873 1637325848377721579705905)
              ·
                refine ⟨1227994386283291184779429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637325848377721579705905 1227994386283291184779429)
                ·
                  refine ⟨230248947428117097146143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1227994386283291184779429 230248947428117097146143)
                  ·
                    rfl

theorem cell22_2017837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_2017837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017837 prefixEnd_2017837 := by exact prefixLift 2017837
  have htrace : WordTrace (prefixWord ++ tailWord_2017837) baseStart_2017837 baseEnd_2017837 := by
    simpa [prefixWord, tailWord_2017837, baseEnd_2017837] using wordTrace_append hprefix tailTrace_2017837
  have hstable : (prefixWord ++ tailWord_2017837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017837).length < 2 ^ (prefixWord ++ tailWord_2017837).sum := by decide
  have hdescent : baseEnd_2017837 < baseStart_2017837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017855 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_2017855 : Nat := 118140960795 + 2017855 * 2 ^ 59
def prefixEnd_2017855 : Nat := 4983230072969 + 3 ^ 40 * 2017855 * 2
def baseEnd_2017855 : Nat := 690753004052205244488373

theorem tailTrace_2017855 : CollatzResearch.WordTrace tailWord_2017855 prefixEnd_2017855 690753004052205244488373 := by
  unfold tailWord_2017855
  simp only [CollatzResearch.WordTrace]
  refine ⟨73597218104663432042335019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49064812069775621361556679 73597218104663432042335019)
  ·
    refine ⟨110395827156995148063502529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73597218104663432042335019 110395827156995148063502529)
    ·
      refine ⟨82796870367746361047626897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110395827156995148063502529 82796870367746361047626897)
      ·
        refine ⟨62097652775809770785720173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82796870367746361047626897 62097652775809770785720173)
        ·
          refine ⟨23286619790928664044645065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62097652775809770785720173 23286619790928664044645065)
          ·
            refine ⟨17464964843196498033483799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23286619790928664044645065 17464964843196498033483799)
            ·
              refine ⟨26197447264794747050225699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17464964843196498033483799 26197447264794747050225699)
              ·
                refine ⟨39296170897192120575338549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26197447264794747050225699 39296170897192120575338549)
                ·
                  refine ⟨3684016021611761303937989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39296170897192120575338549 3684016021611761303937989)
                  ·
                    refine ⟨690753004052205244488373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684016021611761303937989 690753004052205244488373)
                    ·
                      rfl

theorem cell22_2017855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_2017855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017855 prefixEnd_2017855 := by exact prefixLift 2017855
  have htrace : WordTrace (prefixWord ++ tailWord_2017855) baseStart_2017855 baseEnd_2017855 := by
    simpa [prefixWord, tailWord_2017855, baseEnd_2017855] using wordTrace_append hprefix tailTrace_2017855
  have hstable : (prefixWord ++ tailWord_2017855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017855).length < 2 ^ (prefixWord ++ tailWord_2017855).sum := by decide
  have hdescent : baseEnd_2017855 < baseStart_2017855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017857 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2017857 : Nat := 118140960795 + 2017857 * 2 ^ 59
def prefixEnd_2017857 : Nat := 4983230072969 + 3 ^ 40 * 2017857 * 2
def baseEnd_2017857 : Nat := 690753688693077905938367

theorem tailTrace_2017857 : CollatzResearch.WordTrace tailWord_2017857 prefixEnd_2017857 690753688693077905938367 := by
  unfold tailWord_2017857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73597291050656186383907825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49064860700437457589271883 73597291050656186383907825)
  ·
    refine ⟨55197968287992139787930869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73597291050656186383907825 55197968287992139787930869)
    ·
      refine ⟨5174809526999263105118519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55197968287992139787930869 5174809526999263105118519)
      ·
        refine ⟨7762214290498894657677779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174809526999263105118519 7762214290498894657677779)
        ·
          refine ⟨11643321435748341986516669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7762214290498894657677779 11643321435748341986516669)
          ·
            refine ⟨4366245538405628244943751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11643321435748341986516669 4366245538405628244943751)
            ·
              refine ⟨6549368307608442367415627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366245538405628244943751 6549368307608442367415627)
              ·
                refine ⟨9824052461412663551123441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549368307608442367415627 9824052461412663551123441)
                ·
                  refine ⟨7368039346059497663342581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9824052461412663551123441 7368039346059497663342581)
                  ·
                    refine ⟨690753688693077905938367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7368039346059497663342581 690753688693077905938367)
                    ·
                      rfl

theorem cell22_2017857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2017857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017857 prefixEnd_2017857 := by exact prefixLift 2017857
  have htrace : WordTrace (prefixWord ++ tailWord_2017857) baseStart_2017857 baseEnd_2017857 := by
    simpa [prefixWord, tailWord_2017857, baseEnd_2017857] using wordTrace_append hprefix tailTrace_2017857
  have hstable : (prefixWord ++ tailWord_2017857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017857).length < 2 ^ (prefixWord ++ tailWord_2017857).sum := by decide
  have hdescent : baseEnd_2017857 < baseStart_2017857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017870 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2017870 : Nat := 118140960795 + 2017870 * 2 ^ 59
def prefixEnd_2017870 : Nat := 4983230072969 + 3 ^ 40 * 2017870 * 2
def baseEnd_2017870 : Nat := 230252712952916735121109

theorem tailTrace_2017870 : CollatzResearch.WordTrace tailWord_2017870 prefixEnd_2017870 230252712952916735121109 := by
  unfold tailWord_2017870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199720649951136200516383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49065176799739393069420709 9199720649951136200516383)
  ·
    refine ⟨13799580974926704300774575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9199720649951136200516383 13799580974926704300774575)
    ·
      refine ⟨20699371462390056451161863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799580974926704300774575 20699371462390056451161863)
      ·
        refine ⟨31049057193585084676742795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699371462390056451161863 31049057193585084676742795)
        ·
          refine ⟨46573585790377627015114193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31049057193585084676742795 46573585790377627015114193)
          ·
            refine ⟨34930189342783220261335645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46573585790377627015114193 34930189342783220261335645)
            ·
              refine ⟨13098821003543707598000867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34930189342783220261335645 13098821003543707598000867)
              ·
                refine ⟨19648231505315561397001301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13098821003543707598000867 19648231505315561397001301)
                ·
                  refine ⟨230252712952916735121109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19648231505315561397001301 230252712952916735121109)
                  ·
                    rfl

theorem cell22_2017870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2017870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017870 prefixEnd_2017870 := by exact prefixLift 2017870
  have htrace : WordTrace (prefixWord ++ tailWord_2017870) baseStart_2017870 baseEnd_2017870 := by
    simpa [prefixWord, tailWord_2017870, baseEnd_2017870] using wordTrace_append hprefix tailTrace_2017870
  have hstable : (prefixWord ++ tailWord_2017870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017870).length < 2 ^ (prefixWord ++ tailWord_2017870).sum := by decide
  have hdescent : baseEnd_2017870 < baseStart_2017870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2017889 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_2017889 : Nat := 118140960795 + 2017889 * 2 ^ 59
def prefixEnd_2017889 : Nat := 4983230072969 + 3 ^ 40 * 2017889 * 2
def baseEnd_2017889 : Nat := 690764642947040489138269

theorem tailTrace_2017889 : CollatzResearch.WordTrace tailWord_2017889 prefixEnd_2017889 690764642947040489138269 := by
  unfold tailWord_2017889
  simp only [CollatzResearch.WordTrace]
  refine ⟨73598458186540255849072721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49065638791026837232715147 73598458186540255849072721)
  ·
    refine ⟨55198843639905191886804541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73598458186540255849072721 55198843639905191886804541)
    ·
      refine ⟨20699566364964446957551703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55198843639905191886804541 20699566364964446957551703)
      ·
        refine ⟨31049349547446670436327555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20699566364964446957551703 31049349547446670436327555)
        ·
          refine ⟨46574024321170005654491333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31049349547446670436327555 46574024321170005654491333)
          ·
            refine ⟨8732629560219376060217125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46574024321170005654491333 8732629560219376060217125)
            ·
              refine ⟨1637368042541133011290711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8732629560219376060217125 1637368042541133011290711)
              ·
                refine ⟨2456052063811699516936067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637368042541133011290711 2456052063811699516936067)
                ·
                  refine ⟨3684078095717549275404101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456052063811699516936067 3684078095717549275404101)
                  ·
                    refine ⟨690764642947040489138269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684078095717549275404101 690764642947040489138269)
                    ·
                      rfl

theorem cell22_2017889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_2017889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2017889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2017889 prefixEnd_2017889 := by exact prefixLift 2017889
  have htrace : WordTrace (prefixWord ++ tailWord_2017889) baseStart_2017889 baseEnd_2017889 := by
    simpa [prefixWord, tailWord_2017889, baseEnd_2017889] using wordTrace_append hprefix tailTrace_2017889
  have hstable : (prefixWord ++ tailWord_2017889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2017889).length < 2 ^ (prefixWord ++ tailWord_2017889).sum := by decide
  have hdescent : baseEnd_2017889 < baseStart_2017889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2017889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018056 : List Nat := [2, 1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_2018056 : Nat := 118140960795 + 2018056 * 2 ^ 59
def prefixEnd_2018056 : Nat := 4983230072969 + 3 ^ 40 * 2018056 * 2
def baseEnd_2018056 : Nat := 230273936819969240070919

theorem tailTrace_2018056 : CollatzResearch.WordTrace tailWord_2018056 prefixEnd_2018056 230273936819969240070919 := by
  unfold tailWord_2018056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36802274588467621685201011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49069699451290162246934681 36802274588467621685201011)
  ·
    refine ⟨55203411882701432527801517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36802274588467621685201011 55203411882701432527801517)
    ·
      refine ⟨20701279456013037197925569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55203411882701432527801517 20701279456013037197925569)
      ·
        refine ⟨15525959592009777898444177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20701279456013037197925569 15525959592009777898444177)
        ·
          refine ⟨11644469694007333423833133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15525959592009777898444177 11644469694007333423833133)
          ·
            refine ⟨4366676135252750033937425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11644469694007333423833133 4366676135252750033937425)
            ·
              refine ⟨3275007101439562525453069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366676135252750033937425 3275007101439562525453069)
              ·
                refine ⟨1228127663039835947044901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3275007101439562525453069 1228127663039835947044901)
                ·
                  refine ⟨230273936819969240070919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1228127663039835947044901 230273936819969240070919)
                  ·
                    rfl

theorem cell22_2018056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_2018056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018056 prefixEnd_2018056 := by exact prefixLift 2018056
  have htrace : WordTrace (prefixWord ++ tailWord_2018056) baseStart_2018056 baseEnd_2018056 := by
    simpa [prefixWord, tailWord_2018056, baseEnd_2018056] using wordTrace_append hprefix tailTrace_2018056
  have hstable : (prefixWord ++ tailWord_2018056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018056).length < 2 ^ (prefixWord ++ tailWord_2018056).sum := by decide
  have hdescent : baseEnd_2018056 < baseStart_2018056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018071 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 4, 3]
def baseStart_2018071 : Nat := 118140960795 + 2018071 * 2 ^ 59
def prefixEnd_2018071 : Nat := 4983230072969 + 3 ^ 40 * 2018071 * 2
def baseEnd_2018071 : Nat := 690826945266452681087711

theorem tailTrace_2018071 : CollatzResearch.WordTrace tailWord_2018071 prefixEnd_2018071 690826945266452681087711 := by
  unfold tailWord_2018071
  simp only [CollatzResearch.WordTrace]
  refine ⟨73605096271880900932198067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49070064181253933954798711 73605096271880900932198067)
  ·
    refine ⟨110407644407821351398297101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73605096271880900932198067 110407644407821351398297101)
    ·
      refine ⟨41402866652933006774361413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110407644407821351398297101 41402866652933006774361413)
      ·
        refine ⟨7763037497424938770192765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41402866652933006774361413 7763037497424938770192765)
        ·
          refine ⟨2911139061534352038822287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7763037497424938770192765 2911139061534352038822287)
          ·
            refine ⟨4366708592301528058233431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911139061534352038822287 4366708592301528058233431)
            ·
              refine ⟨6550062888452292087350147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366708592301528058233431 6550062888452292087350147)
              ·
                refine ⟨9825094332678438131025221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6550062888452292087350147 9825094332678438131025221)
                ·
                  refine ⟨1842205187377207149567229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9825094332678438131025221 1842205187377207149567229)
                  ·
                    refine ⟨690826945266452681087711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842205187377207149567229 690826945266452681087711)
                    ·
                      rfl

theorem cell22_2018071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 3].length) (baseStart_2018071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018071 prefixEnd_2018071 := by exact prefixLift 2018071
  have htrace : WordTrace (prefixWord ++ tailWord_2018071) baseStart_2018071 baseEnd_2018071 := by
    simpa [prefixWord, tailWord_2018071, baseEnd_2018071] using wordTrace_append hprefix tailTrace_2018071
  have hstable : (prefixWord ++ tailWord_2018071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018071).length < 2 ^ (prefixWord ++ tailWord_2018071).sum := by decide
  have hdescent : baseEnd_2018071 < baseStart_2018071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018088 : List Nat := [2, 1, 5, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2018088 : Nat := 118140960795 + 2018088 * 2 ^ 59
def prefixEnd_2018088 : Nat := 4983230072969 + 3 ^ 40 * 2018088 * 2
def baseEnd_2018088 : Nat := 690832764713870303412659

theorem tailTrace_2018088 : CollatzResearch.WordTrace tailWord_2018088 prefixEnd_2018088 690832764713870303412659 := by
  unfold tailWord_2018088
  simp only [CollatzResearch.WordTrace]
  refine ⟨36802858156409656417783459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49070477541879541890377945 36802858156409656417783459)
  ·
    refine ⟨55204287234614484626675189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36802858156409656417783459 55204287234614484626675189)
    ·
      refine ⟨5175401928245107933750799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55204287234614484626675189 5175401928245107933750799)
      ·
        refine ⟨7763102892367661900626199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175401928245107933750799 7763102892367661900626199)
        ·
          refine ⟨11644654338551492850939299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7763102892367661900626199 11644654338551492850939299)
          ·
            refine ⟨17466981507827239276408949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644654338551492850939299 17466981507827239276408949)
            ·
              refine ⟨1637529516358803682163339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17466981507827239276408949 1637529516358803682163339)
              ·
                refine ⟨2456294274538205523245009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637529516358803682163339 2456294274538205523245009)
                ·
                  refine ⟨1842220705903654142433757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456294274538205523245009 1842220705903654142433757)
                  ·
                    refine ⟨690832764713870303412659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842220705903654142433757 690832764713870303412659)
                    ·
                      rfl

theorem cell22_2018088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2018088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018088 prefixEnd_2018088 := by exact prefixLift 2018088
  have htrace : WordTrace (prefixWord ++ tailWord_2018088) baseStart_2018088 baseEnd_2018088 := by
    simpa [prefixWord, tailWord_2018088, baseEnd_2018088] using wordTrace_append hprefix tailTrace_2018088
  have hstable : (prefixWord ++ tailWord_2018088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018088).length < 2 ^ (prefixWord ++ tailWord_2018088).sum := by decide
  have hdescent : baseEnd_2018088 < baseStart_2018088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018101 : List Nat := [1, 3, 3, 1, 3, 3, 2, 6]
def baseStart_2018101 : Nat := 118140960795 + 2018101 * 2 ^ 59
def prefixEnd_2018101 : Nat := 4983230072969 + 3 ^ 40 * 2018101 * 2
def baseEnd_2018101 : Nat := 76759690542171400315291

theorem tailTrace_2018101 : CollatzResearch.WordTrace tailWord_2018101 prefixEnd_2018101 76759690542171400315291 := by
  unfold tailWord_2018101
  simp only [CollatzResearch.WordTrace]
  refine ⟨73606190461772216055790157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49070793641181477370526771 73606190461772216055790157)
  ·
    refine ⟨27602321423164581020921309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73606190461772216055790157 27602321423164581020921309)
    ·
      refine ⟨10350870533686717882845491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27602321423164581020921309 10350870533686717882845491)
      ·
        refine ⟨15526305800530076824268237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10350870533686717882845491 15526305800530076824268237)
        ·
          refine ⟨5822364675198778809100589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15526305800530076824268237 5822364675198778809100589)
          ·
            refine ⟨2183386753199542053412721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5822364675198778809100589 2183386753199542053412721)
            ·
              refine ⟨1637540064899656540059541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183386753199542053412721 1637540064899656540059541)
              ·
                refine ⟨76759690542171400315291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1637540064899656540059541 76759690542171400315291)
                ·
                  rfl

theorem cell22_2018101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 6].length) (baseStart_2018101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018101 prefixEnd_2018101 := by exact prefixLift 2018101
  have htrace : WordTrace (prefixWord ++ tailWord_2018101) baseStart_2018101 baseEnd_2018101 := by
    simpa [prefixWord, tailWord_2018101, baseEnd_2018101] using wordTrace_append hprefix tailTrace_2018101
  have hstable : (prefixWord ++ tailWord_2018101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018101).length < 2 ^ (prefixWord ++ tailWord_2018101).sum := by decide
  have hdescent : baseEnd_2018101 < baseStart_2018101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018118 : List Nat := [6, 1, 1, 2, 2, 2, 8]
def baseStart_2018118 : Nat := 118140960795 + 2018118 * 2 ^ 59
def prefixEnd_2018118 : Nat := 4983230072969 + 3 ^ 40 * 2018118 * 2
def baseEnd_2018118 : Nat := 25586779049146675006021

theorem tailTrace_2018118 : CollatzResearch.WordTrace tailWord_2018118 prefixEnd_2018118 25586779049146675006021 := by
  unfold tailWord_2018118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300212828209707123723719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49071207001807085306106005 2300212828209707123723719)
  ·
    refine ⟨3450319242314560685585579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300212828209707123723719 3450319242314560685585579)
    ·
      refine ⟨5175478863471841028378369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450319242314560685585579 5175478863471841028378369)
      ·
        refine ⟨3881609147603880771283777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175478863471841028378369 3881609147603880771283777)
        ·
          refine ⟨2911206860702910578462833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881609147603880771283777 2911206860702910578462833)
          ·
            refine ⟨2183405145527182933847125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911206860702910578462833 2183405145527182933847125)
            ·
              refine ⟨25586779049146675006021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2183405145527182933847125 25586779049146675006021)
              ·
                rfl

theorem cell22_2018118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 8].length) (baseStart_2018118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018118 prefixEnd_2018118 := by exact prefixLift 2018118
  have htrace : WordTrace (prefixWord ++ tailWord_2018118) baseStart_2018118 baseEnd_2018118 := by
    simpa [prefixWord, tailWord_2018118, baseEnd_2018118] using wordTrace_append hprefix tailTrace_2018118
  have hstable : (prefixWord ++ tailWord_2018118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018118).length < 2 ^ (prefixWord ++ tailWord_2018118).sum := by decide
  have hdescent : baseEnd_2018118 < baseStart_2018118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018251 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 3, 3]
def baseStart_2018251 : Nat := 118140960795 + 2018251 * 2 ^ 59
def prefixEnd_2018251 : Nat := 4983230072969 + 3 ^ 40 * 2018251 * 2
def baseEnd_2018251 : Nat := 690888562944992211587159

theorem tailTrace_2018251 : CollatzResearch.WordTrace tailWord_2018251 prefixEnd_2018251 690888562944992211587159 := by
  unfold tailWord_2018251
  simp only [CollatzResearch.WordTrace]
  refine ⟨73611661411228791673750607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49074440940819194449167071 73611661411228791673750607)
  ·
    refine ⟨110417492116843187510625911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73611661411228791673750607 110417492116843187510625911)
    ·
      refine ⟨165626238175264781265938867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110417492116843187510625911 165626238175264781265938867)
      ·
        refine ⟨248439357262897171898908301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165626238175264781265938867 248439357262897171898908301)
        ·
          refine ⟨93164758973586439462090613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248439357262897171898908301 93164758973586439462090613)
          ·
            refine ⟨8734196153773728699570995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93164758973586439462090613 8734196153773728699570995)
            ·
              refine ⟨13101294230660593049356493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734196153773728699570995 13101294230660593049356493)
              ·
                refine ⟨4912985336497722393508685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13101294230660593049356493 4912985336497722393508685)
                ·
                  refine ⟨1842369501186645897565757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4912985336497722393508685 1842369501186645897565757)
                  ·
                    refine ⟨690888562944992211587159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842369501186645897565757 690888562944992211587159)
                    ·
                      rfl

theorem cell22_2018251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 3].length) (baseStart_2018251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018251 prefixEnd_2018251 := by exact prefixLift 2018251
  have htrace : WordTrace (prefixWord ++ tailWord_2018251) baseStart_2018251 baseEnd_2018251 := by
    simpa [prefixWord, tailWord_2018251, baseEnd_2018251] using wordTrace_append hprefix tailTrace_2018251
  have hstable : (prefixWord ++ tailWord_2018251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018251).length < 2 ^ (prefixWord ++ tailWord_2018251).sum := by decide
  have hdescent : baseEnd_2018251 < baseStart_2018251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018302 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2018302 : Nat := 118140960795 + 2018302 * 2 ^ 59
def prefixEnd_2018302 : Nat := 4983230072969 + 3 ^ 40 * 2018302 * 2
def baseEnd_2018302 : Nat := 690906021287245078562003

theorem tailTrace_2018302 : CollatzResearch.WordTrace tailWord_2018302 prefixEnd_2018302 690906021287245078562003 := by
  unfold tailWord_2018302
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201690191755503422982145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49075681022696018255904773 9201690191755503422982145)
  ·
    refine ⟨6901267643816627567236609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9201690191755503422982145 6901267643816627567236609)
    ·
      refine ⟨5175950732862470675427457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6901267643816627567236609 5175950732862470675427457)
      ·
        refine ⟨3881963049646853006570593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5175950732862470675427457 3881963049646853006570593)
        ·
          refine ⟨2911472287235139754927945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881963049646853006570593 2911472287235139754927945)
          ·
            refine ⟨2183604215426354816195959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911472287235139754927945 2183604215426354816195959)
            ·
              refine ⟨3275406323139532224293939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183604215426354816195959 3275406323139532224293939)
              ·
                refine ⟨4913109484709298336440909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275406323139532224293939 4913109484709298336440909)
                ·
                  refine ⟨1842416056765986876165341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4913109484709298336440909 1842416056765986876165341)
                  ·
                    refine ⟨690906021287245078562003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842416056765986876165341 690906021287245078562003)
                    ·
                      rfl

theorem cell22_2018302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2018302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018302 prefixEnd_2018302 := by exact prefixLift 2018302
  have htrace : WordTrace (prefixWord ++ tailWord_2018302) baseStart_2018302 baseEnd_2018302 := by
    simpa [prefixWord, tailWord_2018302, baseEnd_2018302] using wordTrace_append hprefix tailTrace_2018302
  have hstable : (prefixWord ++ tailWord_2018302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018302).length < 2 ^ (prefixWord ++ tailWord_2018302).sum := by decide
  have hdescent : baseEnd_2018302 < baseStart_2018302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018311 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2018311 : Nat := 118140960795 + 2018311 * 2 ^ 59
def prefixEnd_2018311 : Nat := 4983230072969 + 3 ^ 40 * 2018311 * 2
def baseEnd_2018311 : Nat := 690909102171172055086975

theorem tailTrace_2018311 : CollatzResearch.WordTrace tailWord_2018311 prefixEnd_2018311 690909102171172055086975 := by
  unfold tailWord_2018311
  simp only [CollatzResearch.WordTrace]
  refine ⟨73613849791011421920934787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49075899860674281280623191 73613849791011421920934787)
  ·
    refine ⟨110420774686517132881402181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73613849791011421920934787 110420774686517132881402181)
    ·
      refine ⟨20703895253721962415262909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110420774686517132881402181 20703895253721962415262909)
      ·
        refine ⟨7763960720145735905723591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20703895253721962415262909 7763960720145735905723591)
        ·
          refine ⟨11645941080218603858585387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7763960720145735905723591 11645941080218603858585387)
          ·
            refine ⟨17468911620327905787878081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11645941080218603858585387 17468911620327905787878081)
            ·
              refine ⟨13101683715245929340908561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17468911620327905787878081 13101683715245929340908561)
              ·
                refine ⟨9826262786434447005681421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13101683715245929340908561 9826262786434447005681421)
                ·
                  refine ⟨3684848544912917627130533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9826262786434447005681421 3684848544912917627130533)
                  ·
                    refine ⟨690909102171172055086975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684848544912917627130533 690909102171172055086975)
                    ·
                      rfl

theorem cell22_2018311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2018311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018311 prefixEnd_2018311 := by exact prefixLift 2018311
  have htrace : WordTrace (prefixWord ++ tailWord_2018311) baseStart_2018311 baseEnd_2018311 := by
    simpa [prefixWord, tailWord_2018311, baseEnd_2018311] using wordTrace_append hprefix tailTrace_2018311
  have hstable : (prefixWord ++ tailWord_2018311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018311).length < 2 ^ (prefixWord ++ tailWord_2018311).sum := by decide
  have hdescent : baseEnd_2018311 < baseStart_2018311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018328 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_2018328 : Nat := 118140960795 + 2018328 * 2 ^ 59
def prefixEnd_2018328 : Nat := 4983230072969 + 3 ^ 40 * 2018328 * 2
def baseEnd_2018328 : Nat := 690914921618589677411923

theorem tailTrace_2018328 : CollatzResearch.WordTrace tailWord_2018328 prefixEnd_2018328 690914921618589677411923 := by
  unfold tailWord_2018328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807234915974916912151819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49076313221299889216202425 36807234915974916912151819)
  ·
    refine ⟨55210852373962375368227729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36807234915974916912151819 55210852373962375368227729)
    ·
      refine ⟨41408139280471781526170797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55210852373962375368227729 41408139280471781526170797)
      ·
        refine ⟨15528052230176918072314049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41408139280471781526170797 15528052230176918072314049)
        ·
          refine ⟨11646039172632688554235537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15528052230176918072314049 11646039172632688554235537)
          ·
            refine ⟨8734529379474516415676653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11646039172632688554235537 8734529379474516415676653)
            ·
              refine ⟨3275448517302943655878745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8734529379474516415676653 3275448517302943655878745)
              ·
                refine ⟨2456586387977207741909059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275448517302943655878745 2456586387977207741909059)
                ·
                  refine ⟨3684879581965811612863589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456586387977207741909059 3684879581965811612863589)
                  ·
                    refine ⟨690914921618589677411923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684879581965811612863589 690914921618589677411923)
                    ·
                      rfl

theorem cell22_2018328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_2018328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018328 prefixEnd_2018328 := by exact prefixLift 2018328
  have htrace : WordTrace (prefixWord ++ tailWord_2018328) baseStart_2018328 baseEnd_2018328 := by
    simpa [prefixWord, tailWord_2018328, baseEnd_2018328] using wordTrace_append hprefix tailTrace_2018328
  have hstable : (prefixWord ++ tailWord_2018328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018328).length < 2 ^ (prefixWord ++ tailWord_2018328).sum := by decide
  have hdescent : baseEnd_2018328 < baseStart_2018328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018341 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_2018341 : Nat := 118140960795 + 2018341 * 2 ^ 59
def prefixEnd_2018341 : Nat := 4983230072969 + 3 ^ 40 * 2018341 * 2
def baseEnd_2018341 : Nat := 690919371784261976836883

theorem tailTrace_2018341 : CollatzResearch.WordTrace tailWord_2018341 prefixEnd_2018341 690919371784261976836883 := by
  unfold tailWord_2018341
  simp only [CollatzResearch.WordTrace]
  refine ⟨73614943980902737044526877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49076629320601824696351251 73614943980902737044526877)
  ·
    refine ⟨27605603992838526391697579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73614943980902737044526877 27605603992838526391697579)
    ·
      refine ⟨41408405989257789587546369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27605603992838526391697579 41408405989257789587546369)
      ·
        refine ⟨31056304491943342190659777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41408405989257789587546369 31056304491943342190659777)
        ·
          refine ⟨23292228368957506642994833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31056304491943342190659777 23292228368957506642994833)
          ·
            refine ⟨17469171276718129982246125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23292228368957506642994833 17469171276718129982246125)
            ·
              refine ⟨6550939228769298743342297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17469171276718129982246125 6550939228769298743342297)
              ·
                refine ⟨4913204421576974057506723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550939228769298743342297 4913204421576974057506723)
                ·
                  refine ⟨7369806632365461086260085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913204421576974057506723 7369806632365461086260085)
                  ·
                    refine ⟨690919371784261976836883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7369806632365461086260085 690919371784261976836883)
                    ·
                      rfl

theorem cell22_2018341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_2018341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018341 prefixEnd_2018341 := by exact prefixLift 2018341
  have htrace : WordTrace (prefixWord ++ tailWord_2018341) baseStart_2018341 baseEnd_2018341 := by
    simpa [prefixWord, tailWord_2018341, baseEnd_2018341] using wordTrace_append hprefix tailTrace_2018341
  have hstable : (prefixWord ++ tailWord_2018341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018341).length < 2 ^ (prefixWord ++ tailWord_2018341).sum := by decide
  have hdescent : baseEnd_2018341 < baseStart_2018341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018360 : List Nat := [2, 1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_2018360 : Nat := 118140960795 + 2018360 * 2 ^ 59
def prefixEnd_2018360 : Nat := 4983230072969 + 3 ^ 40 * 2018360 * 2
def baseEnd_2018360 : Nat := 230308625290850753537275

theorem tailTrace_2018360 : CollatzResearch.WordTrace tailWord_2018360 prefixEnd_2018360 230308625290850753537275 := by
  unfold tailWord_2018360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807818483916951644734267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49077091311889268859645689 36807818483916951644734267)
  ·
    refine ⟨55211727725875427467101401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36807818483916951644734267 55211727725875427467101401)
    ·
      refine ⟨41408795794406570600326051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55211727725875427467101401 41408795794406570600326051)
      ·
        refine ⟨62113193691609855900489077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41408795794406570600326051 62113193691609855900489077)
        ·
          refine ⟨5823111908588423990670851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62113193691609855900489077 5823111908588423990670851)
          ·
            refine ⟨8734667862882635986006277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823111908588423990670851 8734667862882635986006277)
            ·
              refine ⟨1637750224290494247376177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8734667862882635986006277 1637750224290494247376177)
              ·
                refine ⟨1228312668217870685532133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637750224290494247376177 1228312668217870685532133)
                ·
                  refine ⟨230308625290850753537275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1228312668217870685532133 230308625290850753537275)
                  ·
                    rfl

theorem cell22_2018360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_2018360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018360 prefixEnd_2018360 := by exact prefixLift 2018360
  have htrace : WordTrace (prefixWord ++ tailWord_2018360) baseStart_2018360 baseEnd_2018360 := by
    simpa [prefixWord, tailWord_2018360, baseEnd_2018360] using wordTrace_append hprefix tailTrace_2018360
  have hstable : (prefixWord ++ tailWord_2018360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018360).length < 2 ^ (prefixWord ++ tailWord_2018360).sum := by decide
  have hdescent : baseEnd_2018360 < baseStart_2018360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018416 : List Nat := [2, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_2018416 : Nat := 118140960795 + 2018416 * 2 ^ 59
def prefixEnd_2018416 : Nat := 4983230072969 + 3 ^ 40 * 2018416 * 2
def baseEnd_2018416 : Nat := 230315015272328927070551

theorem tailTrace_2018416 : CollatzResearch.WordTrace tailWord_2018416 prefixEnd_2018416 230315015272328927070551 := by
  unfold tailWord_2018416
  simp only [CollatzResearch.WordTrace]
  refine ⟨36808839727815512426753551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49078452970420683235671401 36808839727815512426753551)
  ·
    refine ⟨55213259591723268640130327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36808839727815512426753551 55213259591723268640130327)
    ·
      refine ⟨82819889387584902960195491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55213259591723268640130327 82819889387584902960195491)
      ·
        refine ⟨124229834081377354440293237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82819889387584902960195491 124229834081377354440293237)
        ·
          refine ⟨11646546945129126978777491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124229834081377354440293237 11646546945129126978777491)
          ·
            refine ⟨17469820417693690468166237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11646546945129126978777491 17469820417693690468166237)
            ·
              refine ⟨6551182656635133925562339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17469820417693690468166237 6551182656635133925562339)
              ·
                refine ⟨9826773984952700888343509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551182656635133925562339 9826773984952700888343509)
                ·
                  refine ⟨230315015272328927070551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9826773984952700888343509 230315015272328927070551)
                  ·
                    rfl

theorem cell22_2018416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_2018416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018416 prefixEnd_2018416 := by exact prefixLift 2018416
  have htrace : WordTrace (prefixWord ++ tailWord_2018416) baseStart_2018416 baseEnd_2018416 := by
    simpa [prefixWord, tailWord_2018416, baseEnd_2018416] using wordTrace_append hprefix tailTrace_2018416
  have hstable : (prefixWord ++ tailWord_2018416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018416).length < 2 ^ (prefixWord ++ tailWord_2018416).sum := by decide
  have hdescent : baseEnd_2018416 < baseStart_2018416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018476 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_2018476 : Nat := 118140960795 + 2018476 * 2 ^ 59
def prefixEnd_2018476 : Nat := 4983230072969 + 3 ^ 40 * 2018476 * 2
def baseEnd_2018476 : Nat := 690965585043166624711469

theorem tailTrace_2018476 : CollatzResearch.WordTrace tailWord_2018476 prefixEnd_2018476 690965585043166624711469 := by
  unfold tailWord_2018476
  simp only [CollatzResearch.WordTrace]
  refine ⟨36809933917706827550345641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49079911890275770067127521 36809933917706827550345641)
  ·
    refine ⟨27607450438280120662759231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36809933917706827550345641 27607450438280120662759231)
    ·
      refine ⟨41411175657420180994138847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27607450438280120662759231 41411175657420180994138847)
      ·
        refine ⟨62116763486130271491208271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41411175657420180994138847 62116763486130271491208271)
        ·
          refine ⟨93175145229195407236812407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62116763486130271491208271 93175145229195407236812407)
          ·
            refine ⟨139762717843793110855218611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93175145229195407236812407 139762717843793110855218611)
            ·
              refine ⟨209644076765689666282827917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139762717843793110855218611 209644076765689666282827917)
              ·
                refine ⟨78616528787133624856060469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209644076765689666282827917 78616528787133624856060469)
                ·
                  refine ⟨7370299573793777330255669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78616528787133624856060469 7370299573793777330255669)
                  ·
                    refine ⟨690965585043166624711469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7370299573793777330255669 690965585043166624711469)
                    ·
                      rfl

theorem cell22_2018476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_2018476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018476 prefixEnd_2018476 := by exact prefixLift 2018476
  have htrace : WordTrace (prefixWord ++ tailWord_2018476) baseStart_2018476 baseEnd_2018476 := by
    simpa [prefixWord, tailWord_2018476, baseEnd_2018476] using wordTrace_append hprefix tailTrace_2018476
  have hstable : (prefixWord ++ tailWord_2018476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018476).length < 2 ^ (prefixWord ++ tailWord_2018476).sum := by decide
  have hdescent : baseEnd_2018476 < baseStart_2018476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018491 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_2018491 : Nat := 118140960795 + 2018491 * 2 ^ 59
def prefixEnd_2018491 : Nat := 4983230072969 + 3 ^ 40 * 2018491 * 2
def baseEnd_2018491 : Nat := 690970719849711585586423

theorem tailTrace_2018491 : CollatzResearch.WordTrace tailWord_2018491 prefixEnd_2018491 690970719849711585586423 := by
  unfold tailWord_2018491
  simp only [CollatzResearch.WordTrace]
  refine ⟨73620414930359312662487327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49080276620239541774991551 73620414930359312662487327)
  ·
    refine ⟨110430622395538968993730991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73620414930359312662487327 110430622395538968993730991)
    ·
      refine ⟨165645933593308453490596487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110430622395538968993730991 165645933593308453490596487)
      ·
        refine ⟨248468900389962680235894731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165645933593308453490596487 248468900389962680235894731)
        ·
          refine ⟨372703350584944020353842097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248468900389962680235894731 372703350584944020353842097)
          ·
            refine ⟨279527512938708015265381573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372703350584944020353842097 279527512938708015265381573)
            ·
              refine ⟨52411408676007752862259045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279527512938708015265381573 52411408676007752862259045)
              ·
                refine ⟨9827139126751453661673571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52411408676007752862259045 9827139126751453661673571)
                ·
                  refine ⟨14740708690127180492510357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827139126751453661673571 14740708690127180492510357)
                  ·
                    refine ⟨690970719849711585586423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14740708690127180492510357 690970719849711585586423)
                    ·
                      rfl

theorem cell22_2018491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_2018491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018491 prefixEnd_2018491 := by exact prefixLift 2018491
  have htrace : WordTrace (prefixWord ++ tailWord_2018491) baseStart_2018491 baseEnd_2018491 := by
    simpa [prefixWord, tailWord_2018491, baseEnd_2018491] using wordTrace_append hprefix tailTrace_2018491
  have hstable : (prefixWord ++ tailWord_2018491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018491).length < 2 ^ (prefixWord ++ tailWord_2018491).sum := by decide
  have hdescent : baseEnd_2018491 < baseStart_2018491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018497 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2018497 : Nat := 118140960795 + 2018497 * 2 ^ 59
def prefixEnd_2018497 : Nat := 4983230072969 + 3 ^ 40 * 2018497 * 2
def baseEnd_2018497 : Nat := 690972773772329569936405

theorem tailTrace_2018497 : CollatzResearch.WordTrace tailWord_2018497 prefixEnd_2018497 690972773772329569936405 := by
  unfold tailWord_2018497
  simp only [CollatzResearch.WordTrace]
  refine ⟨73620633768337575687205745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49080422512225050458137163 73620633768337575687205745)
  ·
    refine ⟨55215475326253181765404309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73620633768337575687205745 55215475326253181765404309)
    ·
      refine ⟨2588225405918117895253327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55215475326253181765404309 2588225405918117895253327)
      ·
        refine ⟨3882338108877176842879991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588225405918117895253327 3882338108877176842879991)
        ·
          refine ⟨5823507163315765264319987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882338108877176842879991 5823507163315765264319987)
          ·
            refine ⟨8735260744973647896479981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823507163315765264319987 8735260744973647896479981)
            ·
              refine ⟨3275722779365117961179993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8735260744973647896479981 3275722779365117961179993)
              ·
                refine ⟨2456792084523838470884995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275722779365117961179993 2456792084523838470884995)
                ·
                  refine ⟨3685188126785757706327493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456792084523838470884995 3685188126785757706327493)
                  ·
                    refine ⟨690972773772329569936405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685188126785757706327493 690972773772329569936405)
                    ·
                      rfl

theorem cell22_2018497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2018497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018497 prefixEnd_2018497 := by exact prefixLift 2018497
  have htrace : WordTrace (prefixWord ++ tailWord_2018497) baseStart_2018497 baseEnd_2018497 := by
    simpa [prefixWord, tailWord_2018497, baseEnd_2018497] using wordTrace_append hprefix tailTrace_2018497
  have hstable : (prefixWord ++ tailWord_2018497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018497).length < 2 ^ (prefixWord ++ tailWord_2018497).sum := by decide
  have hdescent : baseEnd_2018497 < baseStart_2018497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018510 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2018510 : Nat := 118140960795 + 2018510 * 2 ^ 59
def prefixEnd_2018510 : Nat := 4983230072969 + 3 ^ 40 * 2018510 * 2
def baseEnd_2018510 : Nat := 690977223938001869361365

theorem tailTrace_2018510 : CollatzResearch.WordTrace tailWord_2018510 prefixEnd_2018510 690977223938001869361365 := by
  unfold tailWord_2018510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202638489661309863428623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49080738611526985938285989 9202638489661309863428623)
  ·
    refine ⟨13803957734491964795142935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9202638489661309863428623 13803957734491964795142935)
    ·
      refine ⟨20705936601737947192714403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13803957734491964795142935 20705936601737947192714403)
      ·
        refine ⟨31058904902606920789071605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20705936601737947192714403 31058904902606920789071605)
        ·
          refine ⟨2911772334619398823975463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31058904902606920789071605 2911772334619398823975463)
          ·
            refine ⟨4367658501929098235963195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911772334619398823975463 4367658501929098235963195)
            ·
              refine ⟨6551487752893647353944793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367658501929098235963195 6551487752893647353944793)
              ·
                refine ⟨4913615814670235515458595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551487752893647353944793 4913615814670235515458595)
                ·
                  refine ⟨7370423722005353273187893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913615814670235515458595 7370423722005353273187893)
                  ·
                    refine ⟨690977223938001869361365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7370423722005353273187893 690977223938001869361365)
                    ·
                      rfl

theorem cell22_2018510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2018510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018510 prefixEnd_2018510 := by exact prefixLift 2018510
  have htrace : WordTrace (prefixWord ++ tailWord_2018510) baseStart_2018510 baseEnd_2018510 := by
    simpa [prefixWord, tailWord_2018510, baseEnd_2018510] using wordTrace_append hprefix tailTrace_2018510
  have hstable : (prefixWord ++ tailWord_2018510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018510).length < 2 ^ (prefixWord ++ tailWord_2018510).sum := by decide
  have hdescent : baseEnd_2018510 < baseStart_2018510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018572 : List Nat := [2, 2, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_2018572 : Nat := 118140960795 + 2018572 * 2 ^ 59
def prefixEnd_2018572 : Nat := 4983230072969 + 3 ^ 40 * 2018572 * 2
def baseEnd_2018572 : Nat := 690998447805054374311175

theorem tailTrace_2018572 : CollatzResearch.WordTrace tailWord_2018572 prefixEnd_2018572 690998447805054374311175 := by
  unfold tailWord_2018572
  simp only [CollatzResearch.WordTrace]
  refine ⟨36811684621532931748092985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49082246162043908997457313 36811684621532931748092985)
  ·
    refine ⟨27608763466149698811069739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36811684621532931748092985 27608763466149698811069739)
    ·
      refine ⟨41413145199224548216604609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27608763466149698811069739 41413145199224548216604609)
      ·
        refine ⟨31059858899418411162453457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41413145199224548216604609 31059858899418411162453457)
        ·
          refine ⟨23294894174563808371840093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31059858899418411162453457 23294894174563808371840093)
          ·
            refine ⟨8735585315461428139440035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23294894174563808371840093 8735585315461428139440035)
            ·
              refine ⟨13103377973192142209160053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735585315461428139440035 13103377973192142209160053)
              ·
                refine ⟨1228441684986763332108755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13103377973192142209160053 1228441684986763332108755)
                ·
                  refine ⟨1842662527480144998163133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228441684986763332108755 1842662527480144998163133)
                  ·
                    refine ⟨690998447805054374311175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842662527480144998163133 690998447805054374311175)
                    ·
                      rfl

theorem cell22_2018572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_2018572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018572 prefixEnd_2018572 := by exact prefixLift 2018572
  have htrace : WordTrace (prefixWord ++ tailWord_2018572) baseStart_2018572 baseEnd_2018572 := by
    simpa [prefixWord, tailWord_2018572, baseEnd_2018572] using wordTrace_append hprefix tailTrace_2018572
  have hstable : (prefixWord ++ tailWord_2018572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018572).length < 2 ^ (prefixWord ++ tailWord_2018572).sum := by decide
  have hdescent : baseEnd_2018572 < baseStart_2018572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018578 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2018578 : Nat := 118140960795 + 2018578 * 2 ^ 59
def prefixEnd_2018578 : Nat := 4983230072969 + 3 ^ 40 * 2018578 * 2
def baseEnd_2018578 : Nat := 691000501727672358661157

theorem tailTrace_2018578 : CollatzResearch.WordTrace tailWord_2018578 prefixEnd_2018578 691000501727672358661157 := by
  unfold tailWord_2018578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405897020261031630226097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49082392054029417680602925 18405897020261031630226097)
  ·
    refine ⟨13804422765195773722669573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18405897020261031630226097 13804422765195773722669573)
    ·
      refine ⟨2588329268474207573000545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13804422765195773722669573 2588329268474207573000545)
      ·
        refine ⟨1941246951355655679750409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2588329268474207573000545 1941246951355655679750409)
        ·
          refine ⟨1455935213516741759812807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941246951355655679750409 1455935213516741759812807)
          ·
            refine ⟨2183902820275112639719211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455935213516741759812807 2183902820275112639719211)
            ·
              refine ⟨3275854230412668959578817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183902820275112639719211 3275854230412668959578817)
              ·
                refine ⟨2456890672809501719684113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275854230412668959578817 2456890672809501719684113)
                ·
                  refine ⟨1842668004607126289763085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2456890672809501719684113 1842668004607126289763085)
                  ·
                    refine ⟨691000501727672358661157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842668004607126289763085 691000501727672358661157)
                    ·
                      rfl

theorem cell22_2018578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2018578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018578 prefixEnd_2018578 := by exact prefixLift 2018578
  have htrace : WordTrace (prefixWord ++ tailWord_2018578) baseStart_2018578 baseEnd_2018578 := by
    simpa [prefixWord, tailWord_2018578, baseEnd_2018578] using wordTrace_append hprefix tailTrace_2018578
  have hstable : (prefixWord ++ tailWord_2018578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018578).length < 2 ^ (prefixWord ++ tailWord_2018578).sum := by decide
  have hdescent : baseEnd_2018578 < baseStart_2018578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018583 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2018583 : Nat := 118140960795 + 2018583 * 2 ^ 59
def prefixEnd_2018583 : Nat := 4983230072969 + 3 ^ 40 * 2018583 * 2
def baseEnd_2018583 : Nat := 691002213329854012286141

theorem tailTrace_2018583 : CollatzResearch.WordTrace tailWord_2018583 prefixEnd_2018583 691002213329854012286141 := by
  unfold tailWord_2018583
  simp only [CollatzResearch.WordTrace]
  refine ⟨73623770446026012374836403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49082513630684008249890935 73623770446026012374836403)
  ·
    refine ⟨110435655669039018562254605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73623770446026012374836403 110435655669039018562254605)
    ·
      refine ⟨41413370875889631960845477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110435655669039018562254605 41413370875889631960845477)
      ·
        refine ⟨7765007039229305992658527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41413370875889631960845477 7765007039229305992658527)
        ·
          refine ⟨11647510558843958988987791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765007039229305992658527 11647510558843958988987791)
          ·
            refine ⟨17471265838265938483481687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647510558843958988987791 17471265838265938483481687)
            ·
              refine ⟨26206898757398907725222531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17471265838265938483481687 26206898757398907725222531)
              ·
                refine ⟨39310348136098361587833797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26206898757398907725222531 39310348136098361587833797)
                ·
                  refine ⟨7370690275518442797718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39310348136098361587833797 7370690275518442797718837)
                  ·
                    refine ⟨691002213329854012286141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7370690275518442797718837 691002213329854012286141)
                    ·
                      rfl

theorem cell22_2018583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2018583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018583 prefixEnd_2018583 := by exact prefixLift 2018583
  have htrace : WordTrace (prefixWord ++ tailWord_2018583) baseStart_2018583 baseEnd_2018583 := by
    simpa [prefixWord, tailWord_2018583, baseEnd_2018583] using wordTrace_append hprefix tailTrace_2018583
  have hstable : (prefixWord ++ tailWord_2018583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018583).length < 2 ^ (prefixWord ++ tailWord_2018583).sum := by decide
  have hdescent : baseEnd_2018583 < baseStart_2018583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018589 : List Nat := [1, 4, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2018589 : Nat := 118140960795 + 2018589 * 2 ^ 59
def prefixEnd_2018589 : Nat := 4983230072969 + 3 ^ 40 * 2018589 * 2
def baseEnd_2018589 : Nat := 691004267252471996636123

theorem tailTrace_2018589 : CollatzResearch.WordTrace tailWord_2018589 prefixEnd_2018589 691004267252471996636123 := by
  unfold tailWord_2018589
  simp only [CollatzResearch.WordTrace]
  refine ⟨73623989284004275399554821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49082659522669516933036547 73623989284004275399554821)
  ·
    refine ⟨13804497990750801637416529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73623989284004275399554821 13804497990750801637416529)
    ·
      refine ⟨10353373493063101228062397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13804497990750801637416529 10353373493063101228062397)
      ·
        refine ⟨3882515059898662960523399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10353373493063101228062397 3882515059898662960523399)
        ·
          refine ⟨5823772589847994440785099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882515059898662960523399 5823772589847994440785099)
          ·
            refine ⟨8735658884771991661177649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823772589847994440785099 8735658884771991661177649)
            ·
              refine ⟨6551744163578993745883237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735658884771991661177649 6551744163578993745883237)
              ·
                refine ⟨1228452030671061327353107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6551744163578993745883237 1228452030671061327353107)
                ·
                  refine ⟨1842678046006591991029661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228452030671061327353107 1842678046006591991029661)
                  ·
                    refine ⟨691004267252471996636123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842678046006591991029661 691004267252471996636123)
                    ·
                      rfl

theorem cell22_2018589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2018589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018589 prefixEnd_2018589 := by exact prefixLift 2018589
  have htrace : WordTrace (prefixWord ++ tailWord_2018589) baseStart_2018589 baseEnd_2018589 := by
    simpa [prefixWord, tailWord_2018589, baseEnd_2018589] using wordTrace_append hprefix tailTrace_2018589
  have hstable : (prefixWord ++ tailWord_2018589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018589).length < 2 ^ (prefixWord ++ tailWord_2018589).sum := by decide
  have hdescent : baseEnd_2018589 < baseStart_2018589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018600 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2018600 : Nat := 118140960795 + 2018600 * 2 ^ 59
def prefixEnd_2018600 : Nat := 4983230072969 + 3 ^ 40 * 2018600 * 2
def baseEnd_2018600 : Nat := 691008032777271634611089

theorem tailTrace_2018600 : CollatzResearch.WordTrace tailWord_2018600 prefixEnd_2018600 691008032777271634611089 := by
  unfold tailWord_2018600
  simp only [CollatzResearch.WordTrace]
  refine ⟨36812195243482212139102627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49082926991309616185470169 36812195243482212139102627)
  ·
    refine ⟨55218292865223318208653941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36812195243482212139102627 55218292865223318208653941)
    ·
      refine ⟨5176714956114686082061307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55218292865223318208653941 5176714956114686082061307)
      ·
        refine ⟨7765072434172029123091961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5176714956114686082061307 7765072434172029123091961)
        ·
          refine ⟨5823804325629021842318971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7765072434172029123091961 5823804325629021842318971)
          ·
            refine ⟨8735706488443532763478457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823804325629021842318971 8735706488443532763478457)
            ·
              refine ⟨6551779866332649572608843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735706488443532763478457 6551779866332649572608843)
              ·
                refine ⟨9827669799498974358913265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551779866332649572608843 9827669799498974358913265)
                ·
                  refine ⟨7370752349624230769184949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827669799498974358913265 7370752349624230769184949)
                  ·
                    refine ⟨691008032777271634611089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7370752349624230769184949 691008032777271634611089)
                    ·
                      rfl

theorem cell22_2018600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2018600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018600 prefixEnd_2018600 := by exact prefixLift 2018600
  have htrace : WordTrace (prefixWord ++ tailWord_2018600) baseStart_2018600 baseEnd_2018600 := by
    simpa [prefixWord, tailWord_2018600, baseEnd_2018600] using wordTrace_append hprefix tailTrace_2018600
  have hstable : (prefixWord ++ tailWord_2018600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018600).length < 2 ^ (prefixWord ++ tailWord_2018600).sum := by decide
  have hdescent : baseEnd_2018600 < baseStart_2018600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018653 : List Nat := [1, 4, 5, 1, 1, 2, 2, 1, 5]
def baseStart_2018653 : Nat := 118140960795 + 2018653 * 2 ^ 59
def prefixEnd_2018653 : Nat := 4983230072969 + 3 ^ 40 * 2018653 * 2
def baseEnd_2018653 : Nat := 230342058586799054345309

theorem tailTrace_2018653 : CollatzResearch.WordTrace tailWord_2018653 prefixEnd_2018653 230342058586799054345309 := by
  unfold tailWord_2018653
  simp only [CollatzResearch.WordTrace]
  refine ⟨73626323555772414329884613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49084215703848276219923075 73626323555772414329884613)
  ·
    refine ⟨13804935666707327686853365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73626323555772414329884613 13804935666707327686853365)
    ·
      refine ⟨1294212718753811970642503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13804935666707327686853365 1294212718753811970642503)
      ·
        refine ⟨1941319078130717955963755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294212718753811970642503 1941319078130717955963755)
        ·
          refine ⟨2911978617196076933945633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941319078130717955963755 2911978617196076933945633)
          ·
            refine ⟨2183983962897057700459225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911978617196076933945633 2183983962897057700459225)
            ·
              refine ⟨1637987972172793275344419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2183983962897057700459225 1637987972172793275344419)
              ·
                refine ⟨2456981958259189913016629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637987972172793275344419 2456981958259189913016629)
                ·
                  refine ⟨230342058586799054345309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2456981958259189913016629 230342058586799054345309)
                  ·
                    rfl

theorem cell22_2018653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_2018653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018653 prefixEnd_2018653 := by exact prefixLift 2018653
  have htrace : WordTrace (prefixWord ++ tailWord_2018653) baseStart_2018653 baseEnd_2018653 := by
    simpa [prefixWord, tailWord_2018653, baseEnd_2018653] using wordTrace_append hprefix tailTrace_2018653
  have hstable : (prefixWord ++ tailWord_2018653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018653).length < 2 ^ (prefixWord ++ tailWord_2018653).sum := by decide
  have hdescent : baseEnd_2018653 < baseStart_2018653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018666 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 1, 4]
def baseStart_2018666 : Nat := 118140960795 + 2018666 * 2 ^ 59
def prefixEnd_2018666 : Nat := 4983230072969 + 3 ^ 40 * 2018666 * 2
def baseEnd_2018666 : Nat := 691030625926069462460887

theorem tailTrace_2018666 : CollatzResearch.WordTrace tailWord_2018666 prefixEnd_2018666 691030625926069462460887 := by
  unfold tailWord_2018666
  simp only [CollatzResearch.WordTrace]
  refine ⟨18406699426181329387526963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49084531803150211700071901 18406699426181329387526963)
  ·
    refine ⟨27610049139271994081290445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18406699426181329387526963 27610049139271994081290445)
    ·
      refine ⟨10353768427226997780483917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27610049139271994081290445 10353768427226997780483917)
      ·
        refine ⟨3882663160210124167681469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10353768427226997780483917 3882663160210124167681469)
        ·
          refine ⟨1455998685078796562880551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3882663160210124167681469 1455998685078796562880551)
          ·
            refine ⟨2183998027618194844320827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455998685078796562880551 2183998027618194844320827)
            ·
              refine ⟨3275997041427292266481241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183998027618194844320827 3275997041427292266481241)
              ·
                refine ⟨2456997781070469199860931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275997041427292266481241 2456997781070469199860931)
                ·
                  refine ⟨3685496671605703799791397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456997781070469199860931 3685496671605703799791397)
                  ·
                    refine ⟨691030625926069462460887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685496671605703799791397 691030625926069462460887)
                    ·
                      rfl

theorem cell22_2018666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_2018666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018666 prefixEnd_2018666 := by exact prefixLift 2018666
  have htrace : WordTrace (prefixWord ++ tailWord_2018666) baseStart_2018666 baseEnd_2018666 := by
    simpa [prefixWord, tailWord_2018666, baseEnd_2018666] using wordTrace_append hprefix tailTrace_2018666
  have hstable : (prefixWord ++ tailWord_2018666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018666).length < 2 ^ (prefixWord ++ tailWord_2018666).sum := by decide
  have hdescent : baseEnd_2018666 < baseStart_2018666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018673 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2018673 : Nat := 118140960795 + 2018673 * 2 ^ 59
def prefixEnd_2018673 : Nat := 4983230072969 + 3 ^ 40 * 2018673 * 2
def baseEnd_2018673 : Nat := 691033022169123777535865

theorem tailTrace_2018673 : CollatzResearch.WordTrace tailWord_2018673 prefixEnd_2018673 691033022169123777535865 := by
  unfold tailWord_2018673
  simp only [CollatzResearch.WordTrace]
  refine ⟨73627053015699957745612673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49084702010466638497075115 73627053015699957745612673)
  ·
    refine ⟨55220289761774968309209505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73627053015699957745612673 55220289761774968309209505)
    ·
      refine ⟨41415217321331226231907129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55220289761774968309209505 41415217321331226231907129)
      ·
        refine ⟨31061412990998419673930347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41415217321331226231907129 31061412990998419673930347)
        ·
          refine ⟨46592119486497629510895521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31061412990998419673930347 46592119486497629510895521)
          ·
            refine ⟨34944089614873222133171641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46592119486497629510895521 34944089614873222133171641)
            ·
              refine ⟨26208067211154916599878731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34944089614873222133171641 26208067211154916599878731)
              ·
                refine ⟨39312100816732374899818097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26208067211154916599878731 39312100816732374899818097)
                ·
                  refine ⟨29484075612549281174863573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39312100816732374899818097 29484075612549281174863573)
                  ·
                    refine ⟨691033022169123777535865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29484075612549281174863573 691033022169123777535865)
                    ·
                      rfl

theorem cell22_2018673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2018673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018673 prefixEnd_2018673 := by exact prefixLift 2018673
  have htrace : WordTrace (prefixWord ++ tailWord_2018673) baseStart_2018673 baseEnd_2018673 := by
    simpa [prefixWord, tailWord_2018673, baseEnd_2018673] using wordTrace_append hprefix tailTrace_2018673
  have hstable : (prefixWord ++ tailWord_2018673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018673).length < 2 ^ (prefixWord ++ tailWord_2018673).sum := by decide
  have hdescent : baseEnd_2018673 < baseStart_2018673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018688 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 4, 6]
def baseStart_2018688 : Nat := 118140960795 + 2018688 * 2 ^ 59
def prefixEnd_2018688 : Nat := 4983230072969 + 3 ^ 40 * 2018688 * 2
def baseEnd_2018688 : Nat := 691038156975668738410819

theorem tailTrace_2018688 : CollatzResearch.WordTrace tailWord_2018688 prefixEnd_2018688 691038156975668738410819 := by
  unfold tailWord_2018688
  simp only [CollatzResearch.WordTrace]
  refine ⟨36813800055322807653704359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49085066740430410204939145 36813800055322807653704359)
  ·
    refine ⟨55220700082984211480556539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36813800055322807653704359 55220700082984211480556539)
    ·
      refine ⟨82831050124476317220834809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55220700082984211480556539 82831050124476317220834809)
      ·
        refine ⟨62123287593357237915626107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82831050124476317220834809 62123287593357237915626107)
        ·
          refine ⟨93184931390035856873439161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62123287593357237915626107 93184931390035856873439161)
          ·
            refine ⟨69888698542526892655079371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93184931390035856873439161 69888698542526892655079371)
            ·
              refine ⟨104833047813790338982619057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69888698542526892655079371 104833047813790338982619057)
              ·
                refine ⟨78624785860342754236964293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104833047813790338982619057 78624785860342754236964293)
                ·
                  refine ⟨14742147348814266419430805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78624785860342754236964293 14742147348814266419430805)
                  ·
                    refine ⟨691038156975668738410819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14742147348814266419430805 691038156975668738410819)
                    ·
                      rfl

theorem cell22_2018688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_2018688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018688 prefixEnd_2018688 := by exact prefixLift 2018688
  have htrace : WordTrace (prefixWord ++ tailWord_2018688) baseStart_2018688 baseEnd_2018688 := by
    simpa [prefixWord, tailWord_2018688, baseEnd_2018688] using wordTrace_append hprefix tailTrace_2018688
  have hstable : (prefixWord ++ tailWord_2018688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018688).length < 2 ^ (prefixWord ++ tailWord_2018688).sum := by decide
  have hdescent : baseEnd_2018688 < baseStart_2018688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018720 : List Nat := [2, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_2018720 : Nat := 118140960795 + 2018720 * 2 ^ 59
def prefixEnd_2018720 : Nat := 4983230072969 + 3 ^ 40 * 2018720 * 2
def baseEnd_2018720 : Nat := 230349703743210440536907

theorem tailTrace_2018720 : CollatzResearch.WordTrace tailWord_2018720 prefixEnd_2018720 230349703743210440536907 := by
  unfold tailWord_2018720
  simp only [CollatzResearch.WordTrace]
  refine ⟨36814383623264842386286807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49085844831019789848382409 36814383623264842386286807)
  ·
    refine ⟨55221575434897263579430211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36814383623264842386286807 55221575434897263579430211)
    ·
      refine ⟨82832363152345895369145317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55221575434897263579430211 82832363152345895369145317)
      ·
        refine ⟨15531068091064855381714747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82832363152345895369145317 15531068091064855381714747)
        ·
          refine ⟨23296602136597283072572121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15531068091064855381714747 23296602136597283072572121)
          ·
            refine ⟨17472451602447962304429091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23296602136597283072572121 17472451602447962304429091)
            ·
              refine ⟨26208677403671943456643637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17472451602447962304429091 26208677403671943456643637)
              ·
                refine ⟨2457063506594244699060341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26208677403671943456643637 2457063506594244699060341)
                ·
                  refine ⟨230349703743210440536907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457063506594244699060341 230349703743210440536907)
                  ·
                    rfl

theorem cell22_2018720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_2018720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018720 prefixEnd_2018720 := by exact prefixLift 2018720
  have htrace : WordTrace (prefixWord ++ tailWord_2018720) baseStart_2018720 baseEnd_2018720 := by
    simpa [prefixWord, tailWord_2018720, baseEnd_2018720] using wordTrace_append hprefix tailTrace_2018720
  have hstable : (prefixWord ++ tailWord_2018720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018720).length < 2 ^ (prefixWord ++ tailWord_2018720).sum := by decide
  have hdescent : baseEnd_2018720 < baseStart_2018720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018741 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_2018741 : Nat := 118140960795 + 2018741 * 2 ^ 59
def prefixEnd_2018741 : Nat := 4983230072969 + 3 ^ 40 * 2018741 * 2
def baseEnd_2018741 : Nat := 691056299958794266835657

theorem tailTrace_2018741 : CollatzResearch.WordTrace tailWord_2018741 prefixEnd_2018741 691056299958794266835657 := by
  unfold tailWord_2018741
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629533179453605359088077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49086355452969070239392051 73629533179453605359088077)
  ·
    refine ⟨27611074942295102009658029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73629533179453605359088077 27611074942295102009658029)
    ·
      refine ⟨10354153103360663253621761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27611074942295102009658029 10354153103360663253621761)
      ·
        refine ⟨7765614827520497440216321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10354153103360663253621761 7765614827520497440216321)
        ·
          refine ⟨5824211120640373080162241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7765614827520497440216321 5824211120640373080162241)
          ·
            refine ⟨4368158340480279810121681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824211120640373080162241 4368158340480279810121681)
            ·
              refine ⟨3276118755360209857591261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368158340480279810121681 3276118755360209857591261)
              ·
                refine ⟨1228544533260078696596723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3276118755360209857591261 1228544533260078696596723)
                ·
                  refine ⟨1842816799890118044895085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228544533260078696596723 1842816799890118044895085)
                  ·
                    refine ⟨691056299958794266835657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842816799890118044895085 691056299958794266835657)
                    ·
                      rfl

theorem cell22_2018741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_2018741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018741 prefixEnd_2018741 := by exact prefixLift 2018741
  have htrace : WordTrace (prefixWord ++ tailWord_2018741) baseStart_2018741 baseEnd_2018741 := by
    simpa [prefixWord, tailWord_2018741, baseEnd_2018741] using wordTrace_append hprefix tailTrace_2018741
  have hstable : (prefixWord ++ tailWord_2018741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018741).length < 2 ^ (prefixWord ++ tailWord_2018741).sum := by decide
  have hdescent : baseEnd_2018741 < baseStart_2018741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018822 : List Nat := [6, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2018822 : Nat := 118140960795 + 2018822 * 2 ^ 59
def prefixEnd_2018822 : Nat := 4983230072969 + 3 ^ 40 * 2018822 * 2
def baseEnd_2018822 : Nat := 230361342638045685186803

theorem tailTrace_2018822 : CollatzResearch.WordTrace tailWord_2018822 prefixEnd_2018822 230361342638045685186803 := by
  unfold tailWord_2018822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301015234130004881024585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49088324994773437461857813 2301015234130004881024585)
  ·
    refine ⟨1725761425597503660768439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2301015234130004881024585 1725761425597503660768439)
    ·
      refine ⟨2588642138396255491152659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725761425597503660768439 2588642138396255491152659)
      ·
        refine ⟨3882963207594383236728989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588642138396255491152659 3882963207594383236728989)
        ·
          refine ⟨1456111202847893713773371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3882963207594383236728989 1456111202847893713773371)
          ·
            refine ⟨2184166804271840570660057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456111202847893713773371 2184166804271840570660057)
            ·
              refine ⟨1638125103203880427995043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184166804271840570660057 1638125103203880427995043)
              ·
                refine ⟨2457187654805820641992565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638125103203880427995043 2457187654805820641992565)
                ·
                  refine ⟨230361342638045685186803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457187654805820641992565 230361342638045685186803)
                  ·
                    rfl

theorem cell22_2018822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2018822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018822 prefixEnd_2018822 := by exact prefixLift 2018822
  have htrace : WordTrace (prefixWord ++ tailWord_2018822) baseStart_2018822 baseEnd_2018822 := by
    simpa [prefixWord, tailWord_2018822, baseEnd_2018822] using wordTrace_append hprefix tailTrace_2018822
  have hstable : (prefixWord ++ tailWord_2018822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018822).length < 2 ^ (prefixWord ++ tailWord_2018822).sum := by decide
  have hdescent : baseEnd_2018822 < baseStart_2018822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018827 : List Nat := [1, 1, 1, 1, 8, 1, 2, 7]
def baseStart_2018827 : Nat := 118140960795 + 2018827 * 2 ^ 59
def prefixEnd_2018827 : Nat := 4983230072969 + 3 ^ 40 * 2018827 * 2
def baseEnd_2018827 : Nat := 76787304390702078798377

theorem tailTrace_2018827 : CollatzResearch.WordTrace tailWord_2018827 prefixEnd_2018827 76787304390702078798377 := by
  unfold tailWord_2018827
  simp only [CollatzResearch.WordTrace]
  refine ⟨73632669857142042046718735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49088446571428028031145823 73632669857142042046718735)
  ·
    refine ⟨110449004785713063070078103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73632669857142042046718735 110449004785713063070078103)
    ·
      refine ⟨165673507178569594605117155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110449004785713063070078103 165673507178569594605117155)
      ·
        refine ⟨248510260767854391907675733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165673507178569594605117155 248510260767854391907675733)
        ·
          refine ⟨2912229618373293655168075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 248510260767854391907675733 2912229618373293655168075)
          ·
            refine ⟨4368344427559940482752113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912229618373293655168075 4368344427559940482752113)
            ·
              refine ⟨3276258320669955362064085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368344427559940482752113 3276258320669955362064085)
              ·
                refine ⟨76787304390702078798377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3276258320669955362064085 76787304390702078798377)
                ·
                  rfl

theorem cell22_2018827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 2, 7].length) (baseStart_2018827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018827 prefixEnd_2018827 := by exact prefixLift 2018827
  have htrace : WordTrace (prefixWord ++ tailWord_2018827) baseStart_2018827 baseEnd_2018827 := by
    simpa [prefixWord, tailWord_2018827, baseEnd_2018827] using wordTrace_append hprefix tailTrace_2018827
  have hstable : (prefixWord ++ tailWord_2018827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018827).length < 2 ^ (prefixWord ++ tailWord_2018827).sum := by decide
  have hdescent : baseEnd_2018827 < baseStart_2018827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018842 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_2018842 : Nat := 118140960795 + 2018842 * 2 ^ 59
def prefixEnd_2018842 : Nat := 4983230072969 + 3 ^ 40 * 2018842 * 2
def baseEnd_2018842 : Nat := 691090874322863670060347

theorem tailTrace_2018842 : CollatzResearch.WordTrace tailWord_2018842 prefixEnd_2018842 691090874322863670060347 := by
  unfold tailWord_2018842
  simp only [CollatzResearch.WordTrace]
  refine ⟨18408304238021924902128695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49088811301391799739009853 18408304238021924902128695)
  ·
    refine ⟨27612456357032887353193043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18408304238021924902128695 27612456357032887353193043)
    ·
      refine ⟨41418684535549331029789565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27612456357032887353193043 41418684535549331029789565)
      ·
        refine ⟨15532006700830999136171087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41418684535549331029789565 15532006700830999136171087)
        ·
          refine ⟨23298010051246498704256631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15532006700830999136171087 23298010051246498704256631)
          ·
            refine ⟨34947015076869748056384947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23298010051246498704256631 34947015076869748056384947)
            ·
              refine ⟨52420522615304622084577421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34947015076869748056384947 52420522615304622084577421)
              ·
                refine ⟨19657695980739233281716533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52420522615304622084577421 19657695980739233281716533)
                ·
                  refine ⟨1842908998194303120160925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19657695980739233281716533 1842908998194303120160925)
                  ·
                    refine ⟨691090874322863670060347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842908998194303120160925 691090874322863670060347)
                    ·
                      rfl

theorem cell22_2018842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_2018842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018842 prefixEnd_2018842 := by exact prefixLift 2018842
  have htrace : WordTrace (prefixWord ++ tailWord_2018842) baseStart_2018842 baseEnd_2018842 := by
    simpa [prefixWord, tailWord_2018842, baseEnd_2018842] using wordTrace_append hprefix tailTrace_2018842
  have hstable : (prefixWord ++ tailWord_2018842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018842).length < 2 ^ (prefixWord ++ tailWord_2018842).sum := by decide
  have hdescent : baseEnd_2018842 < baseStart_2018842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018872 : List Nat := [2, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_2018872 : Nat := 118140960795 + 2018872 * 2 ^ 59
def prefixEnd_2018872 : Nat := 4983230072969 + 3 ^ 40 * 2018872 * 2
def baseEnd_2018872 : Nat := 230367047978651197270085

theorem tailTrace_2018872 : CollatzResearch.WordTrace tailWord_2018872 prefixEnd_2018872 230367047978651197270085 := by
  unfold tailWord_2018872
  simp only [CollatzResearch.WordTrace]
  refine ⟨36817155570989507366053435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49089540761319343154737913 36817155570989507366053435)
  ·
    refine ⟨55225733356484261049080153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36817155570989507366053435 55225733356484261049080153)
    ·
      refine ⟨41419300017363195786810115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55225733356484261049080153 41419300017363195786810115)
      ·
        refine ⟨62128950026044793680215173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41419300017363195786810115 62128950026044793680215173)
        ·
          refine ⟨11649178129883398815040345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62128950026044793680215173 11649178129883398815040345)
          ·
            refine ⟨8736883597412549111280259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11649178129883398815040345 8736883597412549111280259)
            ·
              refine ⟨13105325396118823666920389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736883597412549111280259 13105325396118823666920389)
              ·
                refine ⟨2457248511772279437547573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13105325396118823666920389 2457248511772279437547573)
                ·
                  refine ⟨230367047978651197270085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457248511772279437547573 230367047978651197270085)
                  ·
                    rfl

theorem cell22_2018872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_2018872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018872 prefixEnd_2018872 := by exact prefixLift 2018872
  have htrace : WordTrace (prefixWord ++ tailWord_2018872) baseStart_2018872 baseEnd_2018872 := by
    simpa [prefixWord, tailWord_2018872, baseEnd_2018872] using wordTrace_append hprefix tailTrace_2018872
  have hstable : (prefixWord ++ tailWord_2018872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018872).length < 2 ^ (prefixWord ++ tailWord_2018872).sum := by decide
  have hdescent : baseEnd_2018872 < baseStart_2018872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2018934 : List Nat := [5, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_2018934 : Nat := 118140960795 + 2018934 * 2 ^ 59
def prefixEnd_2018934 : Nat := 4983230072969 + 3 ^ 40 * 2018934 * 2
def baseEnd_2018934 : Nat := 230374122601002032253355

theorem tailTrace_2018934 : CollatzResearch.WordTrace tailWord_2018934 prefixEnd_2018934 230374122601002032253355 := by
  unfold tailWord_2018934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602285779234649957553991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49091048311836266213909237 4602285779234649957553991)
  ·
    refine ⟨6903428668851974936330987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602285779234649957553991 6903428668851974936330987)
    ·
      refine ⟨10355143003277962404496481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903428668851974936330987 10355143003277962404496481)
      ·
        refine ⟨7766357252458471803372361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10355143003277962404496481 7766357252458471803372361)
        ·
          refine ⟨5824767939343853852529271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7766357252458471803372361 5824767939343853852529271)
          ·
            refine ⟨8737151909015780778793907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824767939343853852529271 8737151909015780778793907)
            ·
              refine ⟨13105727863523671168190861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8737151909015780778793907 13105727863523671168190861)
              ·
                refine ⟨4914647948821376688071573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13105727863523671168190861 4914647948821376688071573)
                ·
                  refine ⟨230374122601002032253355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4914647948821376688071573 230374122601002032253355)
                  ·
                    rfl

theorem cell22_2018934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_2018934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2018934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2018934 prefixEnd_2018934 := by exact prefixLift 2018934
  have htrace : WordTrace (prefixWord ++ tailWord_2018934) baseStart_2018934 baseEnd_2018934 := by
    simpa [prefixWord, tailWord_2018934, baseEnd_2018934] using wordTrace_append hprefix tailTrace_2018934
  have hstable : (prefixWord ++ tailWord_2018934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2018934).length < 2 ^ (prefixWord ++ tailWord_2018934).sum := by decide
  have hdescent : baseEnd_2018934 < baseStart_2018934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2018934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019041 : List Nat := [1, 2, 3, 1, 5, 1, 2, 2, 5]
def baseStart_2019041 : Nat := 118140960795 + 2019041 * 2 ^ 59
def prefixEnd_2019041 : Nat := 4983230072969 + 3 ^ 40 * 2019041 * 2
def baseEnd_2019041 : Nat := 230386332029897828111579

theorem tailTrace_2019041 : CollatzResearch.WordTrace tailWord_2019041 prefixEnd_2019041 230386332029897828111579 := by
  unfold tailWord_2019041
  simp only [CollatzResearch.WordTrace]
  refine ⟨73640475078366756595008977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49093650052244504396672651 73640475078366756595008977)
  ·
    refine ⟨55230356308775067446256733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73640475078366756595008977 55230356308775067446256733)
    ·
      refine ⟨20711383615790650292346275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55230356308775067446256733 20711383615790650292346275)
      ·
        refine ⟨31067075423685975438519413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20711383615790650292346275 31067075423685975438519413)
        ·
          refine ⟨2912538320970560197361195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31067075423685975438519413 2912538320970560197361195)
          ·
            refine ⟨4368807481455840296041793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912538320970560197361195 4368807481455840296041793)
            ·
              refine ⟨3276605611091880222031345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368807481455840296041793 3276605611091880222031345)
              ·
                refine ⟨2457454208318910166523509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276605611091880222031345 2457454208318910166523509)
                ·
                  refine ⟨230386332029897828111579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457454208318910166523509 230386332029897828111579)
                  ·
                    rfl

theorem cell22_2019041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_2019041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019041 prefixEnd_2019041 := by exact prefixLift 2019041
  have htrace : WordTrace (prefixWord ++ tailWord_2019041) baseStart_2019041 baseEnd_2019041 := by
    simpa [prefixWord, tailWord_2019041, baseEnd_2019041] using wordTrace_append hprefix tailTrace_2019041
  have hstable : (prefixWord ++ tailWord_2019041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019041).length < 2 ^ (prefixWord ++ tailWord_2019041).sum := by decide
  have hdescent : baseEnd_2019041 < baseStart_2019041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019054 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2019054 : Nat := 118140960795 + 2019054 * 2 ^ 59
def prefixEnd_2019054 : Nat := 4983230072969 + 3 ^ 40 * 2019054 * 2
def baseEnd_2019054 : Nat := 691163446255365783759697

theorem tailTrace_2019054 : CollatzResearch.WordTrace tailWord_2019054 prefixEnd_2019054 691163446255365783759697 := by
  unfold tailWord_2019054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205118653414957476904027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49093966151546439876821477 9205118653414957476904027)
  ·
    refine ⟨13807677980122436215356041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9205118653414957476904027 13807677980122436215356041)
    ·
      refine ⟨10355758485091827161517031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13807677980122436215356041 10355758485091827161517031)
      ·
        refine ⟨15533637727637740742275547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10355758485091827161517031 15533637727637740742275547)
        ·
          refine ⟨23300456591456611113413321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533637727637740742275547 23300456591456611113413321)
          ·
            refine ⟨17475342443592458335059991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23300456591456611113413321 17475342443592458335059991)
            ·
              refine ⟨26213013665388687502589987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17475342443592458335059991 26213013665388687502589987)
              ·
                refine ⟨39319520498083031253884981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26213013665388687502589987 39319520498083031253884981)
                ·
                  refine ⟨3686205046695284180051717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39319520498083031253884981 3686205046695284180051717)
                  ·
                    refine ⟨691163446255365783759697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686205046695284180051717 691163446255365783759697)
                    ·
                      rfl

theorem cell22_2019054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2019054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019054 prefixEnd_2019054 := by exact prefixLift 2019054
  have htrace : WordTrace (prefixWord ++ tailWord_2019054) baseStart_2019054 baseEnd_2019054 := by
    simpa [prefixWord, tailWord_2019054, baseEnd_2019054] using wordTrace_append hprefix tailTrace_2019054
  have hstable : (prefixWord ++ tailWord_2019054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019054).length < 2 ^ (prefixWord ++ tailWord_2019054).sum := by decide
  have hdescent : baseEnd_2019054 < baseStart_2019054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019084 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_2019084 : Nat := 118140960795 + 2019084 * 2 ^ 59
def prefixEnd_2019084 : Nat := 4983230072969 + 3 ^ 40 * 2019084 * 2
def baseEnd_2019084 : Nat := 691173715868455705509605

theorem tailTrace_2019084 : CollatzResearch.WordTrace tailWord_2019084 prefixEnd_2019084 691173715868455705509605 := by
  unfold tailWord_2019084
  simp only [CollatzResearch.WordTrace]
  refine ⟨36821021708605487469412153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49094695611473983292549537 36821021708605487469412153)
  ·
    refine ⟨27615766281454115602059115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36821021708605487469412153 27615766281454115602059115)
    ·
      refine ⟨41423649422181173403088673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27615766281454115602059115 41423649422181173403088673)
      ·
        refine ⟨31067737066635880052316505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41423649422181173403088673 31067737066635880052316505)
        ·
          refine ⟨23300802799976910039237379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31067737066635880052316505 23300802799976910039237379)
          ·
            refine ⟨34951204199965365058856069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23300802799976910039237379 34951204199965365058856069)
            ·
              refine ⟨6553350787493505948535513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34951204199965365058856069 6553350787493505948535513)
              ·
                refine ⟨4915013090620129461401635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553350787493505948535513 4915013090620129461401635)
                ·
                  refine ⟨7372519635930194192102453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915013090620129461401635 7372519635930194192102453)
                  ·
                    refine ⟨691173715868455705509605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7372519635930194192102453 691173715868455705509605)
                    ·
                      rfl

theorem cell22_2019084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_2019084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019084 prefixEnd_2019084 := by exact prefixLift 2019084
  have htrace : WordTrace (prefixWord ++ tailWord_2019084) baseStart_2019084 baseEnd_2019084 := by
    simpa [prefixWord, tailWord_2019084, baseEnd_2019084] using wordTrace_append hprefix tailTrace_2019084
  have hstable : (prefixWord ++ tailWord_2019084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019084).length < 2 ^ (prefixWord ++ tailWord_2019084).sum := by decide
  have hdescent : baseEnd_2019084 < baseStart_2019084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019086 : List Nat := [4, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_2019086 : Nat := 118140960795 + 2019086 * 2 ^ 59
def prefixEnd_2019086 : Nat := 4983230072969 + 3 ^ 40 * 2019086 * 2
def baseEnd_2019086 : Nat := 230391466836442788986533

theorem tailTrace_2019086 : CollatzResearch.WordTrace tailWord_2019086 prefixEnd_2019086 230391466836442788986533 := by
  unfold tailWord_2019086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205264545400466160049639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49094744242135819520264741 9205264545400466160049639)
  ·
    refine ⟨13807896818100699240074459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9205264545400466160049639 13807896818100699240074459)
    ·
      refine ⟨20711845227151048860111689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13807896818100699240074459 20711845227151048860111689)
      ·
        refine ⟨15533883920363286645083767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20711845227151048860111689 15533883920363286645083767)
        ·
          refine ⟨23300825880544929967625651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533883920363286645083767 23300825880544929967625651)
          ·
            refine ⟨34951238820817394951438477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23300825880544929967625651 34951238820817394951438477)
            ·
              refine ⟨13106714557806523106789429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34951238820817394951438477 13106714557806523106789429)
              ·
                refine ⟨1228754489794361541261509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13106714557806523106789429 1228754489794361541261509)
                ·
                  refine ⟨230391466836442788986533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1228754489794361541261509 230391466836442788986533)
                  ·
                    rfl

theorem cell22_2019086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_2019086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019086 prefixEnd_2019086 := by exact prefixLift 2019086
  have htrace : WordTrace (prefixWord ++ tailWord_2019086) baseStart_2019086 baseEnd_2019086 := by
    simpa [prefixWord, tailWord_2019086, baseEnd_2019086] using wordTrace_append hprefix tailTrace_2019086
  have hstable : (prefixWord ++ tailWord_2019086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019086).length < 2 ^ (prefixWord ++ tailWord_2019086).sum := by decide
  have hdescent : baseEnd_2019086 < baseStart_2019086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019092 : List Nat := [2, 4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_2019092 : Nat := 118140960795 + 2019092 * 2 ^ 59
def prefixEnd_2019092 : Nat := 4983230072969 + 3 ^ 40 * 2019092 * 2
def baseEnd_2019092 : Nat := 230392151477315450436527

theorem tailTrace_2019092 : CollatzResearch.WordTrace tailWord_2019092 prefixEnd_2019092 230392151477315450436527 := by
  unfold tailWord_2019092
  simp only [CollatzResearch.WordTrace]
  refine ⟨36821167600590996152557765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49094890134121328203410353 36821167600590996152557765)
  ·
    refine ⟨6903968925110811778604581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36821167600590996152557765 6903968925110811778604581)
    ·
      refine ⟨1294494173458277208488359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6903968925110811778604581 1294494173458277208488359)
      ·
        refine ⟨1941741260187415812732539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294494173458277208488359 1941741260187415812732539)
        ·
          refine ⟨2912611890281123719098809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941741260187415812732539 2912611890281123719098809)
          ·
            refine ⟨2184458917710842789324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912611890281123719098809 2184458917710842789324107)
            ·
              refine ⟨3276688376566264183986161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184458917710842789324107 3276688376566264183986161)
              ·
                refine ⟨2457516282424698137989621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276688376566264183986161 2457516282424698137989621)
                ·
                  refine ⟨230392151477315450436527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457516282424698137989621 230392151477315450436527)
                  ·
                    rfl

theorem cell22_2019092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_2019092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019092 prefixEnd_2019092 := by exact prefixLift 2019092
  have htrace : WordTrace (prefixWord ++ tailWord_2019092) baseStart_2019092 baseEnd_2019092 := by
    simpa [prefixWord, tailWord_2019092, baseEnd_2019092] using wordTrace_append hprefix tailTrace_2019092
  have hstable : (prefixWord ++ tailWord_2019092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019092).length < 2 ^ (prefixWord ++ tailWord_2019092).sum := by decide
  have hdescent : baseEnd_2019092 < baseStart_2019092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019176 : List Nat := [2, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_2019176 : Nat := 118140960795 + 2019176 * 2 ^ 59
def prefixEnd_2019176 : Nat := 4983230072969 + 3 ^ 40 * 2019176 * 2
def baseEnd_2019176 : Nat := 230401736449532710736441

theorem tailTrace_2019176 : CollatzResearch.WordTrace tailWord_2019176 prefixEnd_2019176 230401736449532710736441 := by
  unfold tailWord_2019176
  simp only [CollatzResearch.WordTrace]
  refine ⟨36822699466438837325586691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49096932621918449767448921 36822699466438837325586691)
  ·
    refine ⟨55234049199658255988380037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36822699466438837325586691 55234049199658255988380037)
    ·
      refine ⟨10356384224935922997821257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55234049199658255988380037 10356384224935922997821257)
      ·
        refine ⟨7767288168701942248365943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10356384224935922997821257 7767288168701942248365943)
        ·
          refine ⟨11650932253052913372548915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767288168701942248365943 11650932253052913372548915)
          ·
            refine ⟨17476398379579370058823373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650932253052913372548915 17476398379579370058823373)
            ·
              refine ⟨6553649392342263772058765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17476398379579370058823373 6553649392342263772058765)
              ·
                refine ⟨2457618522128348914522037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6553649392342263772058765 2457618522128348914522037)
                ·
                  refine ⟨230401736449532710736441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457618522128348914522037 230401736449532710736441)
                  ·
                    rfl

theorem cell22_2019176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_2019176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019176 prefixEnd_2019176 := by exact prefixLift 2019176
  have htrace : WordTrace (prefixWord ++ tailWord_2019176) baseStart_2019176 baseEnd_2019176 := by
    simpa [prefixWord, tailWord_2019176, baseEnd_2019176] using wordTrace_append hprefix tailTrace_2019176
  have hstable : (prefixWord ++ tailWord_2019176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019176).length < 2 ^ (prefixWord ++ tailWord_2019176).sum := by decide
  have hdescent : baseEnd_2019176 < baseStart_2019176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019236 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_2019236 : Nat := 118140960795 + 2019236 * 2 ^ 59
def prefixEnd_2019236 : Nat := 4983230072969 + 3 ^ 40 * 2019236 * 2
def baseEnd_2019236 : Nat := 691225748574777975709139

theorem tailTrace_2019236 : CollatzResearch.WordTrace tailWord_2019236 prefixEnd_2019236 691225748574777975709139 := by
  unfold tailWord_2019236
  simp only [CollatzResearch.WordTrace]
  refine ⟨36823793656330152449178781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49098391541773536598905041 36823793656330152449178781)
  ·
    refine ⟨13808922621123807168442043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36823793656330152449178781 13808922621123807168442043)
    ·
      refine ⟨20713383931685710752663065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13808922621123807168442043 20713383931685710752663065)
      ·
        refine ⟨15535037948764283064497299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20713383931685710752663065 15535037948764283064497299)
        ·
          refine ⟨23302556923146424596745949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15535037948764283064497299 23302556923146424596745949)
          ·
            refine ⟨8738458846179909223779731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23302556923146424596745949 8738458846179909223779731)
            ·
              refine ⟨13107688269269863835669597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738458846179909223779731 13107688269269863835669597)
              ·
                refine ⟨4915383100976198938376099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13107688269269863835669597 4915383100976198938376099)
                ·
                  refine ⟨7373074651464298407564149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915383100976198938376099 7373074651464298407564149)
                  ·
                    refine ⟨691225748574777975709139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7373074651464298407564149 691225748574777975709139)
                    ·
                      rfl

theorem cell22_2019236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_2019236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019236 prefixEnd_2019236 := by exact prefixLift 2019236
  have htrace : WordTrace (prefixWord ++ tailWord_2019236) baseStart_2019236 baseEnd_2019236 := by
    simpa [prefixWord, tailWord_2019236, baseEnd_2019236] using wordTrace_append hprefix tailTrace_2019236
  have hstable : (prefixWord ++ tailWord_2019236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019236).length < 2 ^ (prefixWord ++ tailWord_2019236).sum := by decide
  have hdescent : baseEnd_2019236 < baseStart_2019236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019334 : List Nat := [6, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2019334 : Nat := 118140960795 + 2019334 * 2 ^ 59
def prefixEnd_2019334 : Nat := 4983230072969 + 3 ^ 40 * 2019334 * 2
def baseEnd_2019334 : Nat := 76806588441948709639871

theorem tailTrace_2019334 : CollatzResearch.WordTrace tailWord_2019334 prefixEnd_2019334 76806588441948709639871 := by
  unfold tailWord_2019334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301598802072039613607033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49100774444203511756950037 2301598802072039613607033)
  ·
    refine ⟨1726199101554029710205275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2301598802072039613607033 1726199101554029710205275)
    ·
      refine ⟨2589298652331044565307913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726199101554029710205275 2589298652331044565307913)
      ·
        refine ⟨1941973989248283423980935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2589298652331044565307913 1941973989248283423980935)
        ·
          refine ⟨2912960983872425135971403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941973989248283423980935 2912960983872425135971403)
          ·
            refine ⟨4369441475808637703957105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912960983872425135971403 4369441475808637703957105)
            ·
              refine ⟨3277081106856478277967829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4369441475808637703957105 3277081106856478277967829)
              ·
                refine ⟨76806588441948709639871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3277081106856478277967829 76806588441948709639871)
                ·
                  rfl

theorem cell22_2019334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2019334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019334 prefixEnd_2019334 := by exact prefixLift 2019334
  have htrace : WordTrace (prefixWord ++ tailWord_2019334) baseStart_2019334 baseEnd_2019334 := by
    simpa [prefixWord, tailWord_2019334, baseEnd_2019334] using wordTrace_append hprefix tailTrace_2019334
  have hstable : (prefixWord ++ tailWord_2019334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019334).length < 2 ^ (prefixWord ++ tailWord_2019334).sum := by decide
  have hdescent : baseEnd_2019334 < baseStart_2019334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019386 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_2019386 : Nat := 118140960795 + 2019386 * 2 ^ 59
def prefixEnd_2019386 : Nat := 4983230072969 + 3 ^ 40 * 2019386 * 2
def baseEnd_2019386 : Nat := 691277096640227584458679

theorem tailTrace_2019386 : CollatzResearch.WordTrace tailWord_2019386 prefixEnd_2019386 691277096640227584458679 := by
  unfold tailWord_2019386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413264565529220129079503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49102038841411253677545341 18413264565529220129079503)
  ·
    refine ⟨27619896848293830193619255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413264565529220129079503 27619896848293830193619255)
    ·
      refine ⟨41429845272440745290428883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27619896848293830193619255 41429845272440745290428883)
      ·
        refine ⟨62144767908661117935643325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41429845272440745290428883 62144767908661117935643325)
        ·
          refine ⟨23304287965747919225866247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62144767908661117935643325 23304287965747919225866247)
          ·
            refine ⟨34956431948621878838799371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23304287965747919225866247 34956431948621878838799371)
            ·
              refine ⟨52434647922932818258199057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34956431948621878838799371 52434647922932818258199057)
              ·
                refine ⟨39325985942199613693649293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52434647922932818258199057 39325985942199613693649293)
                ·
                  refine ⟨14747244728324855135118485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39325985942199613693649293 14747244728324855135118485)
                  ·
                    refine ⟨691277096640227584458679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14747244728324855135118485 691277096640227584458679)
                    ·
                      rfl

theorem cell22_2019386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_2019386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019386 prefixEnd_2019386 := by exact prefixLift 2019386
  have htrace : WordTrace (prefixWord ++ tailWord_2019386) baseStart_2019386 baseEnd_2019386 := by
    simpa [prefixWord, tailWord_2019386, baseEnd_2019386] using wordTrace_append hprefix tailTrace_2019386
  have hstable : (prefixWord ++ tailWord_2019386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019386).length < 2 ^ (prefixWord ++ tailWord_2019386).sum := by decide
  have hdescent : baseEnd_2019386 < baseStart_2019386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019405 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2019405 : Nat := 118140960795 + 2019405 * 2 ^ 59
def prefixEnd_2019405 : Nat := 4983230072969 + 3 ^ 40 * 2019405 * 2
def baseEnd_2019405 : Nat := 691283600728517868233621

theorem tailTrace_2019405 : CollatzResearch.WordTrace tailWord_2019405 prefixEnd_2019405 691283600728517868233621 := by
  unfold tailWord_2019405
  simp only [CollatzResearch.WordTrace]
  refine ⟨73653751249048046761259669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49102500832698697840839779 73653751249048046761259669)
  ·
    refine ⟨3452519589799127191934047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73653751249048046761259669 3452519589799127191934047)
    ·
      refine ⟨5178779384698690787901071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3452519589799127191934047 5178779384698690787901071)
      ·
        refine ⟨7768169077048036181851607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178779384698690787901071 7768169077048036181851607)
        ·
          refine ⟨11652253615572054272777411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768169077048036181851607 11652253615572054272777411)
          ·
            refine ⟨17478380423358081409166117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652253615572054272777411 17478380423358081409166117)
            ·
              refine ⟨3277196329379640264218647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17478380423358081409166117 3277196329379640264218647)
              ·
                refine ⟨4915794494069460396327971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277196329379640264218647 4915794494069460396327971)
                ·
                  refine ⟨7373691741104190594491957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915794494069460396327971 7373691741104190594491957)
                  ·
                    refine ⟨691283600728517868233621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7373691741104190594491957 691283600728517868233621)
                    ·
                      rfl

theorem cell22_2019405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2019405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019405 prefixEnd_2019405 := by exact prefixLift 2019405
  have htrace : WordTrace (prefixWord ++ tailWord_2019405) baseStart_2019405 baseEnd_2019405 := by
    simpa [prefixWord, tailWord_2019405, baseEnd_2019405] using wordTrace_append hprefix tailTrace_2019405
  have hstable : (prefixWord ++ tailWord_2019405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019405).length < 2 ^ (prefixWord ++ tailWord_2019405).sum := by decide
  have hdescent : baseEnd_2019405 < baseStart_2019405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019418 : List Nat := [3, 1, 1, 2, 1, 1, 7, 6]
def baseStart_2019418 : Nat := 118140960795 + 2019418 * 2 ^ 59
def prefixEnd_2019418 : Nat := 4983230072969 + 3 ^ 40 * 2019418 * 2
def baseEnd_2019418 : Nat := 76809783432687796406509

theorem tailTrace_2019418 : CollatzResearch.WordTrace tailWord_2019418 prefixEnd_2019418 76809783432687796406509 := by
  unfold tailWord_2019418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413556349500237495370727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49102816932000633320988605 18413556349500237495370727)
  ·
    refine ⟨27620334524250356243056091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413556349500237495370727 27620334524250356243056091)
    ·
      refine ⟨41430501786375534364584137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27620334524250356243056091 41430501786375534364584137)
      ·
        refine ⟨31072876339781650773438103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41430501786375534364584137 31072876339781650773438103)
        ·
          refine ⟨46609314509672476160157155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31072876339781650773438103 46609314509672476160157155)
          ·
            refine ⟨69913971764508714240235733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46609314509672476160157155 69913971764508714240235733)
            ·
              refine ⟨1638608713230672990005525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69913971764508714240235733 1638608713230672990005525)
              ·
                refine ⟨76809783432687796406509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1638608713230672990005525 76809783432687796406509)
                ·
                  rfl

theorem cell22_2019418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_2019418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019418 prefixEnd_2019418 := by exact prefixLift 2019418
  have htrace : WordTrace (prefixWord ++ tailWord_2019418) baseStart_2019418 baseEnd_2019418 := by
    simpa [prefixWord, tailWord_2019418, baseEnd_2019418] using wordTrace_append hprefix tailTrace_2019418
  have hstable : (prefixWord ++ tailWord_2019418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019418).length < 2 ^ (prefixWord ++ tailWord_2019418).sum := by decide
  have hdescent : baseEnd_2019418 < baseStart_2019418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019420 : List Nat := [2, 2, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2019420 : Nat := 118140960795 + 2019420 * 2 ^ 59
def prefixEnd_2019420 : Nat := 4983230072969 + 3 ^ 40 * 2019420 * 2
def baseEnd_2019420 : Nat := 691288735535062829108575

theorem tailTrace_2019420 : CollatzResearch.WordTrace tailWord_2019420 prefixEnd_2019420 691288735535062829108575 := by
  unfold tailWord_2019420
  simp only [CollatzResearch.WordTrace]
  refine ⟨36827149171996852161527857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49102865562662469548703809 36827149171996852161527857)
  ·
    refine ⟨27620361878997639121145893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36827149171996852161527857 27620361878997639121145893)
    ·
      refine ⟨5178817852312057335214855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27620361878997639121145893 5178817852312057335214855)
      ·
        refine ⟨7768226778468086002822283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178817852312057335214855 7768226778468086002822283)
        ·
          refine ⟨11652340167702129004233425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768226778468086002822283 11652340167702129004233425)
          ·
            refine ⟨8739255125776596753175069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11652340167702129004233425 8739255125776596753175069)
            ·
              refine ⟨3277220672166223782440651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8739255125776596753175069 3277220672166223782440651)
              ·
                refine ⟨4915831008249335673660977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277220672166223782440651 4915831008249335673660977)
                ·
                  refine ⟨3686873256187001755245733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915831008249335673660977 3686873256187001755245733)
                  ·
                    refine ⟨691288735535062829108575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686873256187001755245733 691288735535062829108575)
                    ·
                      rfl

theorem cell22_2019420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2019420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019420 prefixEnd_2019420 := by exact prefixLift 2019420
  have htrace : WordTrace (prefixWord ++ tailWord_2019420) baseStart_2019420 baseEnd_2019420 := by
    simpa [prefixWord, tailWord_2019420, baseEnd_2019420] using wordTrace_append hprefix tailTrace_2019420
  have hstable : (prefixWord ++ tailWord_2019420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019420).length < 2 ^ (prefixWord ++ tailWord_2019420).sum := by decide
  have hdescent : baseEnd_2019420 < baseStart_2019420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019426 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_2019426 : Nat := 118140960795 + 2019426 * 2 ^ 59
def prefixEnd_2019426 : Nat := 4983230072969 + 3 ^ 40 * 2019426 * 2
def baseEnd_2019426 : Nat := 691290789457680813458557

theorem tailTrace_2019426 : CollatzResearch.WordTrace tailWord_2019426 prefixEnd_2019426 691290789457680813458557 := by
  unfold tailWord_2019426
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413629295492991836943533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49103011454647978231849421 18413629295492991836943533)
  ·
    refine ⟨6905110985809871938853825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18413629295492991836943533 6905110985809871938853825)
    ·
      refine ⟨5178833239357403954140369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6905110985809871938853825 5178833239357403954140369)
      ·
        refine ⟨3884124929518052965605277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5178833239357403954140369 3884124929518052965605277)
        ·
          refine ⟨1456546848569269862101979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3884124929518052965605277 1456546848569269862101979)
          ·
            refine ⟨2184820272853904793152969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456546848569269862101979 2184820272853904793152969)
            ·
              refine ⟨1638615204640428594864727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184820272853904793152969 1638615204640428594864727)
              ·
                refine ⟨2457922806960642892297091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638615204640428594864727 2457922806960642892297091)
                ·
                  refine ⟨3686884210440964338445637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457922806960642892297091 3686884210440964338445637)
                  ·
                    refine ⟨691290789457680813458557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686884210440964338445637 691290789457680813458557)
                    ·
                      rfl

theorem cell22_2019426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_2019426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019426 prefixEnd_2019426 := by exact prefixLift 2019426
  have htrace : WordTrace (prefixWord ++ tailWord_2019426) baseStart_2019426 baseEnd_2019426 := by
    simpa [prefixWord, tailWord_2019426, baseEnd_2019426] using wordTrace_append hprefix tailTrace_2019426
  have hstable : (prefixWord ++ tailWord_2019426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019426).length < 2 ^ (prefixWord ++ tailWord_2019426).sum := by decide
  have hdescent : baseEnd_2019426 < baseStart_2019426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019433 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_2019433 : Nat := 118140960795 + 2019433 * 2 ^ 59
def prefixEnd_2019433 : Nat := 4983230072969 + 3 ^ 40 * 2019433 * 2
def baseEnd_2019433 : Nat := 691293185700735128533535

theorem tailTrace_2019433 : CollatzResearch.WordTrace tailWord_2019433 prefixEnd_2019433 691293185700735128533535 := by
  unfold tailWord_2019433
  simp only [CollatzResearch.WordTrace]
  refine ⟨73654772492946607543278953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49103181661964405028852635 73654772492946607543278953)
  ·
    refine ⟨55241079369709955657459215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73654772492946607543278953 55241079369709955657459215)
    ·
      refine ⟨82861619054564933486188823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55241079369709955657459215 82861619054564933486188823)
      ·
        refine ⟨124292428581847400229283235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82861619054564933486188823 124292428581847400229283235)
        ·
          refine ⟨186438642872771100343924853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124292428581847400229283235 186438642872771100343924853)
          ·
            refine ⟨17478622769322290657242955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186438642872771100343924853 17478622769322290657242955)
            ·
              refine ⟨26217934153983435985864433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17478622769322290657242955 26217934153983435985864433)
              ·
                refine ⟨19663450615487576989398325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26217934153983435985864433 19663450615487576989398325)
                ·
                  refine ⟨1843448495201960342756093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19663450615487576989398325 1843448495201960342756093)
                  ·
                    refine ⟨691293185700735128533535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843448495201960342756093 691293185700735128533535)
                    ·
                      rfl

theorem cell22_2019433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_2019433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019433 prefixEnd_2019433 := by exact prefixLift 2019433
  have htrace : WordTrace (prefixWord ++ tailWord_2019433) baseStart_2019433 baseEnd_2019433 := by
    simpa [prefixWord, tailWord_2019433, baseEnd_2019433] using wordTrace_append hprefix tailTrace_2019433
  have hstable : (prefixWord ++ tailWord_2019433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019433).length < 2 ^ (prefixWord ++ tailWord_2019433).sum := by decide
  have hdescent : baseEnd_2019433 < baseStart_2019433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019463 : List Nat := [1, 1, 4, 2, 1, 1, 2, 5, 5]
def baseStart_2019463 : Nat := 118140960795 + 2019463 * 2 ^ 59
def prefixEnd_2019463 : Nat := 4983230072969 + 3 ^ 40 * 2019463 * 2
def baseEnd_2019463 : Nat := 230434485104608350094481

theorem tailTrace_2019463 : CollatzResearch.WordTrace tailWord_2019463 prefixEnd_2019463 230434485104608350094481 := by
  unfold tailWord_2019463
  simp only [CollatzResearch.WordTrace]
  refine ⟨73655866682837922666871043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49103911121891948444580695 73655866682837922666871043)
  ·
    refine ⟨110483800024256884000306565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73655866682837922666871043 110483800024256884000306565)
    ·
      refine ⟨20715712504548165750057481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110483800024256884000306565 20715712504548165750057481)
      ·
        refine ⟨15536784378411124312543111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20715712504548165750057481 15536784378411124312543111)
        ·
          refine ⟨23305176567616686468814667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15536784378411124312543111 23305176567616686468814667)
          ·
            refine ⟨34957764851425029703222001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23305176567616686468814667 34957764851425029703222001)
            ·
              refine ⟨26218323638568772277416501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34957764851425029703222001 26218323638568772277416501)
              ·
                refine ⟨2457967841115822401007797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26218323638568772277416501 2457967841115822401007797)
                ·
                  refine ⟨230434485104608350094481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457967841115822401007797 230434485104608350094481)
                  ·
                    rfl

theorem cell22_2019463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 5, 5].length) (baseStart_2019463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019463 prefixEnd_2019463 := by exact prefixLift 2019463
  have htrace : WordTrace (prefixWord ++ tailWord_2019463) baseStart_2019463 baseEnd_2019463 := by
    simpa [prefixWord, tailWord_2019463, baseEnd_2019463] using wordTrace_append hprefix tailTrace_2019463
  have hstable : (prefixWord ++ tailWord_2019463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019463).length < 2 ^ (prefixWord ++ tailWord_2019463).sum := by decide
  have hdescent : baseEnd_2019463 < baseStart_2019463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019501 : List Nat := [1, 5, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_2019501 : Nat := 118140960795 + 2019501 * 2 ^ 59
def prefixEnd_2019501 : Nat := 4983230072969 + 3 ^ 40 * 2019501 * 2
def baseEnd_2019501 : Nat := 691316463490405617833327

theorem tailTrace_2019501 : CollatzResearch.WordTrace tailWord_2019501 prefixEnd_2019501 691316463490405617833327 := by
  unfold tailWord_2019501
  simp only [CollatzResearch.WordTrace]
  refine ⟨73657252656700255156754357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49104835104466836771169571 73657252656700255156754357)
  ·
    refine ⟨6905367436565648920945721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73657252656700255156754357 6905367436565648920945721)
    ·
      refine ⟨5179025577424236690709291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6905367436565648920945721 5179025577424236690709291)
      ·
        refine ⟨7768538366136355036063937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179025577424236690709291 7768538366136355036063937)
        ·
          refine ⟨5826403774602266277047953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7768538366136355036063937 5826403774602266277047953)
          ·
            refine ⟨4369802830951699707785965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5826403774602266277047953 4369802830951699707785965)
            ·
              refine ⟨1638676061606887390419737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4369802830951699707785965 1638676061606887390419737)
              ·
                refine ⟨1229007046205165542814803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638676061606887390419737 1229007046205165542814803)
                ·
                  refine ⟨1843510569307748314222205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229007046205165542814803 1843510569307748314222205)
                  ·
                    refine ⟨691316463490405617833327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843510569307748314222205 691316463490405617833327)
                    ·
                      rfl

theorem cell22_2019501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_2019501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019501 prefixEnd_2019501 := by exact prefixLift 2019501
  have htrace : WordTrace (prefixWord ++ tailWord_2019501) baseStart_2019501 baseEnd_2019501 := by
    simpa [prefixWord, tailWord_2019501, baseEnd_2019501] using wordTrace_append hprefix tailTrace_2019501
  have hstable : (prefixWord ++ tailWord_2019501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019501).length < 2 ^ (prefixWord ++ tailWord_2019501).sum := by decide
  have hdescent : baseEnd_2019501 < baseStart_2019501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019557 : List Nat := [1, 3, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_2019557 : Nat := 118140960795 + 2019557 * 2 ^ 59
def prefixEnd_2019557 : Nat := 4983230072969 + 3 ^ 40 * 2019557 * 2
def baseEnd_2019557 : Nat := 691335633434840138433155

theorem tailTrace_2019557 : CollatzResearch.WordTrace tailWord_2019557 prefixEnd_2019557 691335633434840138433155 := by
  unfold tailWord_2019557
  simp only [CollatzResearch.WordTrace]
  refine ⟨73659295144497376720792925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49106196762998251147195283 73659295144497376720792925)
  ·
    refine ⟨27622235679186516270297347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73659295144497376720792925 27622235679186516270297347)
    ·
      refine ⟨41433353518779774405446021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27622235679186516270297347 41433353518779774405446021)
      ·
        refine ⟨7768753784771207701021129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41433353518779774405446021 7768753784771207701021129)
        ·
          refine ⟨5826565338578405775765847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7768753784771207701021129 5826565338578405775765847)
          ·
            refine ⟨8739848007867608663648771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826565338578405775765847 8739848007867608663648771)
            ·
              refine ⟨13109772011801412995473157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739848007867608663648771 13109772011801412995473157)
              ·
                refine ⟨2458082252212764936651217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13109772011801412995473157 2458082252212764936651217)
                ·
                  refine ⟨1843561689159573702488413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2458082252212764936651217 1843561689159573702488413)
                  ·
                    refine ⟨691335633434840138433155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843561689159573702488413 691335633434840138433155)
                    ·
                      rfl

theorem cell22_2019557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_2019557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019557 prefixEnd_2019557 := by exact prefixLift 2019557
  have htrace : WordTrace (prefixWord ++ tailWord_2019557) baseStart_2019557 baseEnd_2019557 := by
    simpa [prefixWord, tailWord_2019557, baseEnd_2019557] using wordTrace_append hprefix tailTrace_2019557
  have hstable : (prefixWord ++ tailWord_2019557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019557).length < 2 ^ (prefixWord ++ tailWord_2019557).sum := by decide
  have hdescent : baseEnd_2019557 < baseStart_2019557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019559 : List Nat := [1, 1, 5, 3, 1, 1, 4, 2, 4]
def baseStart_2019559 : Nat := 118140960795 + 2019559 * 2 ^ 59
def prefixEnd_2019559 : Nat := 4983230072969 + 3 ^ 40 * 2019559 * 2
def baseEnd_2019559 : Nat := 230445439358570933294383

theorem tailTrace_2019559 : CollatzResearch.WordTrace tailWord_2019559 prefixEnd_2019559 230445439358570933294383 := by
  unfold tailWord_2019559
  simp only [CollatzResearch.WordTrace]
  refine ⟨73659368090490131062365731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49106245393660087374910487 73659368090490131062365731)
  ·
    refine ⟨110489052135735196593548597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73659368090490131062365731 110489052135735196593548597)
    ·
      refine ⟨10358348637725174680645181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110489052135735196593548597 10358348637725174680645181)
      ·
        refine ⟨3884380739146940505241943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10358348637725174680645181 3884380739146940505241943)
        ·
          refine ⟨5826571108720410757862915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884380739146940505241943 5826571108720410757862915)
          ·
            refine ⟨8739856663080616136794373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826571108720410757862915 8739856663080616136794373)
            ·
              refine ⟨1638723124327615525648945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8739856663080616136794373 1638723124327615525648945)
              ·
                refine ⟨1229042343245711644236709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638723124327615525648945 1229042343245711644236709)
                ·
                  refine ⟨230445439358570933294383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229042343245711644236709 230445439358570933294383)
                  ·
                    rfl

theorem cell22_2019559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 4].length) (baseStart_2019559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019559 prefixEnd_2019559 := by exact prefixLift 2019559
  have htrace : WordTrace (prefixWord ++ tailWord_2019559) baseStart_2019559 baseEnd_2019559 := by
    simpa [prefixWord, tailWord_2019559, baseEnd_2019559] using wordTrace_append hprefix tailTrace_2019559
  have hstable : (prefixWord ++ tailWord_2019559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019559).length < 2 ^ (prefixWord ++ tailWord_2019559).sum := by decide
  have hdescent : baseEnd_2019559 < baseStart_2019559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019570 : List Nat := [3, 2, 1, 3, 2, 1, 3, 7]
def baseStart_2019570 : Nat := 118140960795 + 2019570 * 2 ^ 59
def prefixEnd_2019570 : Nat := 4983230072969 + 3 ^ 40 * 2019570 * 2
def baseEnd_2019570 : Nat := 76815564844501381984235

theorem tailTrace_2019570 : CollatzResearch.WordTrace tailWord_2019570 prefixEnd_2019570 76815564844501381984235 := by
  unfold tailWord_2019570
  simp only [CollatzResearch.WordTrace]
  refine ⟨18414942323362569985254041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49106512862300186627344109 18414942323362569985254041)
  ·
    refine ⟨13811206742521927488940531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18414942323362569985254041 13811206742521927488940531)
    ·
      refine ⟨20716810113782891233410797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13811206742521927488940531 20716810113782891233410797)
      ·
        refine ⟨7768803792668584212529049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20716810113782891233410797 7768803792668584212529049)
        ·
          refine ⟨5826602844501438159396787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7768803792668584212529049 5826602844501438159396787)
          ·
            refine ⟨8739904266752157239095181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826602844501438159396787 8739904266752157239095181)
            ·
              refine ⟨3277464100032058964660693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8739904266752157239095181 3277464100032058964660693)
              ·
                refine ⟨76815564844501381984235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3277464100032058964660693 76815564844501381984235)
                ·
                  rfl

theorem cell22_2019570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_2019570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019570 prefixEnd_2019570 := by exact prefixLift 2019570
  have htrace : WordTrace (prefixWord ++ tailWord_2019570) baseStart_2019570 baseEnd_2019570 := by
    simpa [prefixWord, tailWord_2019570, baseEnd_2019570] using wordTrace_append hprefix tailTrace_2019570
  have hstable : (prefixWord ++ tailWord_2019570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019570).length < 2 ^ (prefixWord ++ tailWord_2019570).sum := by decide
  have hdescent : baseEnd_2019570 < baseStart_2019570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019583 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_2019583 : Nat := 118140960795 + 2019583 * 2 ^ 59
def prefixEnd_2019583 : Nat := 4983230072969 + 3 ^ 40 * 2019583 * 2
def baseEnd_2019583 : Nat := 691344533766184737283075

theorem tailTrace_2019583 : CollatzResearch.WordTrace tailWord_2019583 prefixEnd_2019583 691344533766184737283075 := by
  unfold tailWord_2019583
  simp only [CollatzResearch.WordTrace]
  refine ⟨73660243442403183161239403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49106828961602122107492935 73660243442403183161239403)
  ·
    refine ⟨110490365163604774741859105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73660243442403183161239403 110490365163604774741859105)
    ·
      refine ⟨82867773872703581056394329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110490365163604774741859105 82867773872703581056394329)
      ·
        refine ⟨62150830404527685792295747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82867773872703581056394329 62150830404527685792295747)
        ·
          refine ⟨93226245606791528688443621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62150830404527685792295747 93226245606791528688443621)
          ·
            refine ⟨17479921051273411629083179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93226245606791528688443621 17479921051273411629083179)
            ·
              refine ⟨26219881576910117443624769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17479921051273411629083179 26219881576910117443624769)
              ·
                refine ⟨19664911182682588082718577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26219881576910117443624769 19664911182682588082718577)
                ·
                  refine ⟨14748683387011941062038933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19664911182682588082718577 14748683387011941062038933)
                  ·
                    refine ⟨691344533766184737283075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14748683387011941062038933 691344533766184737283075)
                    ·
                      rfl

theorem cell22_2019583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_2019583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019583 prefixEnd_2019583 := by exact prefixLift 2019583
  have htrace : WordTrace (prefixWord ++ tailWord_2019583) baseStart_2019583 baseEnd_2019583 := by
    simpa [prefixWord, tailWord_2019583, baseEnd_2019583] using wordTrace_append hprefix tailTrace_2019583
  have hstable : (prefixWord ++ tailWord_2019583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019583).length < 2 ^ (prefixWord ++ tailWord_2019583).sum := by decide
  have hdescent : baseEnd_2019583 < baseStart_2019583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019615 : List Nat := [1, 1, 2, 4, 3, 2, 1, 1, 7]
def baseStart_2019615 : Nat := 118140960795 + 2019615 * 2 ^ 59
def prefixEnd_2019615 : Nat := 4983230072969 + 3 ^ 40 * 2019615 * 2
def baseEnd_2019615 : Nat := 230451829340049106827659

theorem tailTrace_2019615 : CollatzResearch.WordTrace tailWord_2019615 prefixEnd_2019615 230451829340049106827659 := by
  unfold tailWord_2019615
  simp only [CollatzResearch.WordTrace]
  refine ⟨73661410578287252626404299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49107607052191501750936199 73661410578287252626404299)
  ·
    refine ⟨110492115867430878939606449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73661410578287252626404299 110492115867430878939606449)
    ·
      refine ⟨82869086900573159204704837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110492115867430878939606449 82869086900573159204704837)
      ·
        refine ⟨15537953793857467350882157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82869086900573159204704837 15537953793857467350882157)
        ·
          refine ⟨5826732672696550256580809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15537953793857467350882157 5826732672696550256580809)
          ·
            refine ⟨4370049504522412692435607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5826732672696550256580809 4370049504522412692435607)
            ·
              refine ⟨6555074256783619038653411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370049504522412692435607 6555074256783619038653411)
              ·
                refine ⟨9832611385175428557980117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6555074256783619038653411 9832611385175428557980117)
                ·
                  refine ⟨230451829340049106827659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9832611385175428557980117 230451829340049106827659)
                  ·
                    rfl

theorem cell22_2019615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_2019615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019615 prefixEnd_2019615 := by exact prefixLift 2019615
  have htrace : WordTrace (prefixWord ++ tailWord_2019615) baseStart_2019615 baseEnd_2019615 := by
    simpa [prefixWord, tailWord_2019615, baseEnd_2019615] using wordTrace_append hprefix tailTrace_2019615
  have hstable : (prefixWord ++ tailWord_2019615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019615).length < 2 ^ (prefixWord ++ tailWord_2019615).sum := by decide
  have hdescent : baseEnd_2019615 < baseStart_2019615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019707 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 2, 4]
def baseStart_2019707 : Nat := 118140960795 + 2019707 * 2 ^ 59
def prefixEnd_2019707 : Nat := 4983230072969 + 3 ^ 40 * 2019707 * 2
def baseEnd_2019707 : Nat := 691386981500289747182695

theorem tailTrace_2019707 : CollatzResearch.WordTrace tailWord_2019707 prefixEnd_2019707 691386981500289747182695 := by
  unfold tailWord_2019707
  simp only [CollatzResearch.WordTrace]
  refine ⟨73664766093953952338753375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49109844062635968225835583 73664766093953952338753375)
  ·
    refine ⟨110497149140930928508130063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73664766093953952338753375 110497149140930928508130063)
    ·
      refine ⟨165745723711396392762195095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110497149140930928508130063 165745723711396392762195095)
      ·
        refine ⟨248618585567094589143292643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165745723711396392762195095 248618585567094589143292643)
        ·
          refine ⟨372927878350641883714938965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248618585567094589143292643 372927878350641883714938965)
          ·
            refine ⟨4370248574421584574784441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 372927878350641883714938965 4370248574421584574784441)
            ·
              refine ⟨3277686430816188431088331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370248574421584574784441 3277686430816188431088331)
              ·
                refine ⟨4916529646224282646632497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3277686430816188431088331 4916529646224282646632497)
                ·
                  refine ⟨3687397234668211984974373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4916529646224282646632497 3687397234668211984974373)
                  ·
                    refine ⟨691386981500289747182695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687397234668211984974373 691386981500289747182695)
                    ·
                      rfl

theorem cell22_2019707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_2019707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019707 prefixEnd_2019707 := by exact prefixLift 2019707
  have htrace : WordTrace (prefixWord ++ tailWord_2019707) baseStart_2019707 baseEnd_2019707 := by
    simpa [prefixWord, tailWord_2019707, baseEnd_2019707] using wordTrace_append hprefix tailTrace_2019707
  have hstable : (prefixWord ++ tailWord_2019707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019707).length < 2 ^ (prefixWord ++ tailWord_2019707).sum := by decide
  have hdescent : baseEnd_2019707 < baseStart_2019707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019722 : List Nat := [3, 1, 2, 5, 1, 10]
def baseStart_2019722 : Nat := 118140960795 + 2019722 * 2 ^ 59
def prefixEnd_2019722 : Nat := 4983230072969 + 3 ^ 40 * 2019722 * 2
def baseEnd_2019722 : Nat := 8535705139590551951329

theorem tailTrace_2019722 : CollatzResearch.WordTrace tailWord_2019722 prefixEnd_2019722 8535705139590551951329 := by
  unfold tailWord_2019722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18416328297224902475137355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49110208792599739933699613 18416328297224902475137355)
  ·
    refine ⟨27624492445837353712706033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18416328297224902475137355 27624492445837353712706033)
    ·
      refine ⟨20718369334378015284529525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27624492445837353712706033 20718369334378015284529525)
      ·
        refine ⟨1942347125097938932924643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20718369334378015284529525 1942347125097938932924643)
        ·
          refine ⟨2913520687646908399386965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942347125097938932924643 2913520687646908399386965)
          ·
            refine ⟨8535705139590551951329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2913520687646908399386965 8535705139590551951329)
            ·
              rfl

theorem cell22_2019722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 10].length) (baseStart_2019722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019722 prefixEnd_2019722 := by exact prefixLift 2019722
  have htrace : WordTrace (prefixWord ++ tailWord_2019722) baseStart_2019722 baseEnd_2019722 := by
    simpa [prefixWord, tailWord_2019722, baseEnd_2019722] using wordTrace_append hprefix tailTrace_2019722
  have hstable : (prefixWord ++ tailWord_2019722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019722).length < 2 ^ (prefixWord ++ tailWord_2019722).sum := by decide
  have hdescent : baseEnd_2019722 < baseStart_2019722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019726 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_2019726 : Nat := 118140960795 + 2019726 * 2 ^ 59
def prefixEnd_2019726 : Nat := 4983230072969 + 3 ^ 40 * 2019726 * 2
def baseEnd_2019726 : Nat := 691393485588580030957637

theorem tailTrace_2019726 : CollatzResearch.WordTrace tailWord_2019726 prefixEnd_2019726 691393485588580030957637 := by
  unfold tailWord_2019726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208182385110639822961879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49110306053923412389130021 9208182385110639822961879)
  ·
    refine ⟨13812273577665959734442819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9208182385110639822961879 13812273577665959734442819)
    ·
      refine ⟨20718410366498939601664229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13812273577665959734442819 20718410366498939601664229)
      ·
        refine ⟨3884701943718551175312043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20718410366498939601664229 3884701943718551175312043)
        ·
          refine ⟨5827052915577826762968065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884701943718551175312043 5827052915577826762968065)
          ·
            refine ⟨4370289686683370072226049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827052915577826762968065 4370289686683370072226049)
            ·
              refine ⟨3277717265012527554169537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370289686683370072226049 3277717265012527554169537)
              ·
                refine ⟨2458287948759395665627153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277717265012527554169537 2458287948759395665627153)
                ·
                  refine ⟨1843715961569546749220365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2458287948759395665627153 1843715961569546749220365)
                  ·
                    refine ⟨691393485588580030957637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843715961569546749220365 691393485588580030957637)
                    ·
                      rfl

theorem cell22_2019726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_2019726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019726 prefixEnd_2019726 := by exact prefixLift 2019726
  have htrace : WordTrace (prefixWord ++ tailWord_2019726) baseStart_2019726 baseEnd_2019726 := by
    simpa [prefixWord, tailWord_2019726, baseEnd_2019726] using wordTrace_append hprefix tailTrace_2019726
  have hstable : (prefixWord ++ tailWord_2019726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019726).length < 2 ^ (prefixWord ++ tailWord_2019726).sum := by decide
  have hdescent : baseEnd_2019726 < baseStart_2019726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019735 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2019735 : Nat := 118140960795 + 2019735 * 2 ^ 59
def prefixEnd_2019735 : Nat := 4983230072969 + 3 ^ 40 * 2019735 * 2
def baseEnd_2019735 : Nat := 691396566472507007482609

theorem tailTrace_2019735 : CollatzResearch.WordTrace tailWord_2019735 prefixEnd_2019735 691396566472507007482609 := by
  unfold tailWord_2019735
  simp only [CollatzResearch.WordTrace]
  refine ⟨73665787337852513120772659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49110524891901675413848439 73665787337852513120772659)
  ·
    refine ⟨110498681006778769681158989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73665787337852513120772659 110498681006778769681158989)
    ·
      refine ⟨41437005377542038630434621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110498681006778769681158989 41437005377542038630434621)
      ·
        refine ⟨15538877016578264486412983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41437005377542038630434621 15538877016578264486412983)
        ·
          refine ⟨23308315524867396729619475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15538877016578264486412983 23308315524867396729619475)
          ·
            refine ⟨34962473287301095094429213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23308315524867396729619475 34962473287301095094429213)
            ·
              refine ⟨13110927482737910660410955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34962473287301095094429213 13110927482737910660410955)
              ·
                refine ⟨19666391224106865990616433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110927482737910660410955 19666391224106865990616433)
                ·
                  refine ⟨14749793418080149492962325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19666391224106865990616433 14749793418080149492962325)
                  ·
                    refine ⟨691396566472507007482609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14749793418080149492962325 691396566472507007482609)
                    ·
                      rfl

theorem cell22_2019735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2019735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019735 prefixEnd_2019735 := by exact prefixLift 2019735
  have htrace : WordTrace (prefixWord ++ tailWord_2019735) baseStart_2019735 baseEnd_2019735 := by
    simpa [prefixWord, tailWord_2019735, baseEnd_2019735] using wordTrace_append hprefix tailTrace_2019735
  have hstable : (prefixWord ++ tailWord_2019735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019735).length < 2 ^ (prefixWord ++ tailWord_2019735).sum := by decide
  have hdescent : baseEnd_2019735 < baseStart_2019735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019737 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_2019737 : Nat := 118140960795 + 2019737 * 2 ^ 59
def prefixEnd_2019737 : Nat := 4983230072969 + 3 ^ 40 * 2019737 * 2
def baseEnd_2019737 : Nat := 691397251113379668932603

theorem tailTrace_2019737 : CollatzResearch.WordTrace tailWord_2019737 prefixEnd_2019737 691397251113379668932603 := by
  unfold tailWord_2019737
  simp only [CollatzResearch.WordTrace]
  refine ⟨73665860283845267462345465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49110573522563511641563643 73665860283845267462345465)
  ·
    refine ⟨55249395212883950596759099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73665860283845267462345465 55249395212883950596759099)
    ·
      refine ⟨82874092819325925895138649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55249395212883950596759099 82874092819325925895138649)
      ·
        refine ⟨62155569614494444421353987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82874092819325925895138649 62155569614494444421353987)
        ·
          refine ⟨93233354421741666632030981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62155569614494444421353987 93233354421741666632030981)
          ·
            refine ⟨17481253954076562493505809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93233354421741666632030981 17481253954076562493505809)
            ·
              refine ⟨13110940465557421870129357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17481253954076562493505809 13110940465557421870129357)
              ·
                refine ⟨4916602674584033201298509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13110940465557421870129357 4916602674584033201298509)
                ·
                  refine ⟨1843726002969012450486941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4916602674584033201298509 1843726002969012450486941)
                  ·
                    refine ⟨691397251113379668932603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843726002969012450486941 691397251113379668932603)
                    ·
                      rfl

theorem cell22_2019737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_2019737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019737 prefixEnd_2019737 := by exact prefixLift 2019737
  have htrace : WordTrace (prefixWord ++ tailWord_2019737) baseStart_2019737 baseEnd_2019737 := by
    simpa [prefixWord, tailWord_2019737, baseEnd_2019737] using wordTrace_append hprefix tailTrace_2019737
  have hstable : (prefixWord ++ tailWord_2019737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019737).length < 2 ^ (prefixWord ++ tailWord_2019737).sum := by decide
  have hdescent : baseEnd_2019737 < baseStart_2019737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019777 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2019777 : Nat := 118140960795 + 2019777 * 2 ^ 59
def prefixEnd_2019777 : Nat := 4983230072969 + 3 ^ 40 * 2019777 * 2
def baseEnd_2019777 : Nat := 691410943930832897932481

theorem tailTrace_2019777 : CollatzResearch.WordTrace tailWord_2019777 prefixEnd_2019777 691410943930832897932481 := by
  unfold tailWord_2019777
  simp only [CollatzResearch.WordTrace]
  refine ⟨73667319203700354293801585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49111546135800236195867723 73667319203700354293801585)
  ·
    refine ⟨55250489402775265720351189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73667319203700354293801585 55250489402775265720351189)
    ·
      refine ⟨1294933345377545290320731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55250489402775265720351189 1294933345377545290320731)
      ·
        refine ⟨1942400018066317935481097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294933345377545290320731 1942400018066317935481097)
        ·
          refine ⟨1456800013549738451610823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942400018066317935481097 1456800013549738451610823)
          ·
            refine ⟨2185200020324607677416235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456800013549738451610823 2185200020324607677416235)
            ·
              refine ⟨3277800030486911516124353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185200020324607677416235 3277800030486911516124353)
              ·
                refine ⟨2458350022865183637093265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277800030486911516124353 2458350022865183637093265)
                ·
                  refine ⟨1843762517148887727819949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2458350022865183637093265 1843762517148887727819949)
                  ·
                    refine ⟨691410943930832897932481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843762517148887727819949 691410943930832897932481)
                    ·
                      rfl

theorem cell22_2019777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2019777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019777 prefixEnd_2019777 := by exact prefixLift 2019777
  have htrace : WordTrace (prefixWord ++ tailWord_2019777) baseStart_2019777 baseEnd_2019777 := by
    simpa [prefixWord, tailWord_2019777, baseEnd_2019777] using wordTrace_append hprefix tailTrace_2019777
  have hstable : (prefixWord ++ tailWord_2019777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019777).length < 2 ^ (prefixWord ++ tailWord_2019777).sum := by decide
  have hdescent : baseEnd_2019777 < baseStart_2019777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019784 : List Nat := [2, 1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_2019784 : Nat := 118140960795 + 2019784 * 2 ^ 59
def prefixEnd_2019784 : Nat := 4983230072969 + 3 ^ 40 * 2019784 * 2
def baseEnd_2019784 : Nat := 230471113391295737669153

theorem tailTrace_2019784 : CollatzResearch.WordTrace tailWord_2019784 prefixEnd_2019784 230471113391295737669153 := by
  unfold tailWord_2019784
  simp only [CollatzResearch.WordTrace]
  refine ⟨36833787257337497244653203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49111716343116662992870937 36833787257337497244653203)
  ·
    refine ⟨55250680886006245866979805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36833787257337497244653203 55250680886006245866979805)
    ·
      refine ⟨20719005332252342200117427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55250680886006245866979805 20719005332252342200117427)
      ·
        refine ⟨31078507998378513300176141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20719005332252342200117427 31078507998378513300176141)
        ·
          refine ⟨11654440499391942487566053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31078507998378513300176141 11654440499391942487566053)
          ·
            refine ⟨2185207593635989216418635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11654440499391942487566053 2185207593635989216418635)
            ·
              refine ⟨3277811390453983824627953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185207593635989216418635 3277811390453983824627953)
              ·
                refine ⟨2458358542840487868470965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277811390453983824627953 2458358542840487868470965)
                ·
                  refine ⟨230471113391295737669153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2458358542840487868470965 230471113391295737669153)
                  ·
                    rfl

theorem cell22_2019784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_2019784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019784 prefixEnd_2019784 := by exact prefixLift 2019784
  have htrace : WordTrace (prefixWord ++ tailWord_2019784) baseStart_2019784 baseEnd_2019784 := by
    simpa [prefixWord, tailWord_2019784, baseEnd_2019784] using wordTrace_append hprefix tailTrace_2019784
  have hstable : (prefixWord ++ tailWord_2019784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019784).length < 2 ^ (prefixWord ++ tailWord_2019784).sum := by decide
  have hdescent : baseEnd_2019784 < baseStart_2019784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019827 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 6, 3]
def baseStart_2019827 : Nat := 118140960795 + 2019827 * 2 ^ 59
def prefixEnd_2019827 : Nat := 4983230072969 + 3 ^ 40 * 2019827 * 2
def baseEnd_2019827 : Nat := 691428059952649434182327

theorem tailTrace_2019827 : CollatzResearch.WordTrace tailWord_2019827 prefixEnd_2019827 691428059952649434182327 := by
  unfold tailWord_2019827
  simp only [CollatzResearch.WordTrace]
  refine ⟨73669142853519212833121735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49112761902346141888747823 73669142853519212833121735)
  ·
    refine ⟨110503714280278819249682603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73669142853519212833121735 110503714280278819249682603)
    ·
      refine ⟨165755571420418228874523905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110503714280278819249682603 165755571420418228874523905)
      ·
        refine ⟨124316678565313671655892929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165755571420418228874523905 124316678565313671655892929)
        ·
          refine ⟨93237508923985253741919697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124316678565313671655892929 93237508923985253741919697)
          ·
            refine ⟨69928131692988940306439773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93237508923985253741919697 69928131692988940306439773)
            ·
              refine ⟨26223049384870852614914915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69928131692988940306439773 26223049384870852614914915)
              ·
                refine ⟨39334574077306278922372373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26223049384870852614914915 39334574077306278922372373)
                ·
                  refine ⟨1843808159873731824486205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39334574077306278922372373 1843808159873731824486205)
                  ·
                    refine ⟨691428059952649434182327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843808159873731824486205 691428059952649434182327)
                    ·
                      rfl

theorem cell22_2019827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 3].length) (baseStart_2019827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019827 prefixEnd_2019827 := by exact prefixLift 2019827
  have htrace : WordTrace (prefixWord ++ tailWord_2019827) baseStart_2019827 baseEnd_2019827 := by
    simpa [prefixWord, tailWord_2019827, baseEnd_2019827] using wordTrace_append hprefix tailTrace_2019827
  have hstable : (prefixWord ++ tailWord_2019827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019827).length < 2 ^ (prefixWord ++ tailWord_2019827).sum := by decide
  have hdescent : baseEnd_2019827 < baseStart_2019827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2019996 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_2019996 : Nat := 118140960795 + 2019996 * 2 ^ 59
def prefixEnd_2019996 : Nat := 4983230072969 + 3 ^ 40 * 2019996 * 2
def baseEnd_2019996 : Nat := 691485912106389326706809

theorem tailTrace_2019996 : CollatzResearch.WordTrace tailWord_2019996 prefixEnd_2019996 691485912106389326706809 := by
  unfold tailWord_2019996
  simp only [CollatzResearch.WordTrace]
  refine ⟨36837653394953477348011921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49116871193271303130682561 36837653394953477348011921)
  ·
    refine ⟨27628240046215108011008941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36837653394953477348011921 27628240046215108011008941)
    ·
      refine ⟨10360590017330665504128353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27628240046215108011008941 10360590017330665504128353)
      ·
        refine ⟨7770442512997999128096265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10360590017330665504128353 7770442512997999128096265)
        ·
          refine ⟨5827831884748499346072199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7770442512997999128096265 5827831884748499346072199)
          ·
            refine ⟨8741747827122749019108299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827831884748499346072199 8741747827122749019108299)
            ·
              refine ⟨13112621740684123528662449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741747827122749019108299 13112621740684123528662449)
              ·
                refine ⟨9834466305513092646496837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13112621740684123528662449 9834466305513092646496837)
                ·
                  refine ⟨1843962432283704871218157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9834466305513092646496837 1843962432283704871218157)
                  ·
                    refine ⟨691485912106389326706809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1843962432283704871218157 691485912106389326706809)
                    ·
                      rfl

theorem cell22_2019996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_2019996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2019996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2019996 prefixEnd_2019996 := by exact prefixLift 2019996
  have htrace : WordTrace (prefixWord ++ tailWord_2019996) baseStart_2019996 baseEnd_2019996 := by
    simpa [prefixWord, tailWord_2019996, baseEnd_2019996] using wordTrace_append hprefix tailTrace_2019996
  have hstable : (prefixWord ++ tailWord_2019996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2019996).length < 2 ^ (prefixWord ++ tailWord_2019996).sum := by decide
  have hdescent : baseEnd_2019996 < baseStart_2019996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2019996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020045 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2020045 : Nat := 118140960795 + 2020045 * 2 ^ 59
def prefixEnd_2020045 : Nat := 4983230072969 + 3 ^ 40 * 2020045 * 2
def baseEnd_2020045 : Nat := 691502685807769532231659

theorem tailTrace_2020045 : CollatzResearch.WordTrace tailWord_2020045 prefixEnd_2020045 691502685807769532231659 := by
  unfold tailWord_2020045
  simp only [CollatzResearch.WordTrace]
  refine ⟨73677093966729436064557589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49118062644486290709705059 73677093966729436064557589)
  ·
    refine ⟨3453613779690442315526137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73677093966729436064557589 3453613779690442315526137)
    ·
      refine ⟨2590210334767831736644603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453613779690442315526137 2590210334767831736644603)
      ·
        refine ⟨3885315502151747604966905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590210334767831736644603 3885315502151747604966905)
        ·
          refine ⟨2913986626613810703725179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3885315502151747604966905 2913986626613810703725179)
          ·
            refine ⟨4370979939920716055587769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2913986626613810703725179 4370979939920716055587769)
            ·
              refine ⟨3278234954940537041690827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370979939920716055587769 3278234954940537041690827)
              ·
                refine ⟨4917352432410805562536241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278234954940537041690827 4917352432410805562536241)
                ·
                  refine ⟨3688014324308104171902181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4917352432410805562536241 3688014324308104171902181)
                  ·
                    refine ⟨691502685807769532231659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688014324308104171902181 691502685807769532231659)
                    ·
                      rfl

theorem cell22_2020045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2020045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020045 prefixEnd_2020045 := by exact prefixLift 2020045
  have htrace : WordTrace (prefixWord ++ tailWord_2020045) baseStart_2020045 baseEnd_2020045 := by
    simpa [prefixWord, tailWord_2020045, baseEnd_2020045] using wordTrace_append hprefix tailTrace_2020045
  have hstable : (prefixWord ++ tailWord_2020045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020045).length < 2 ^ (prefixWord ++ tailWord_2020045).sum := by decide
  have hdescent : baseEnd_2020045 < baseStart_2020045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020058 : List Nat := [3, 1, 1, 2, 2, 2, 2, 5, 1, 3]
def baseStart_2020058 : Nat := 118140960795 + 2020058 * 2 ^ 59
def prefixEnd_2020058 : Nat := 4983230072969 + 3 ^ 40 * 2020058 * 2
def baseEnd_2020058 : Nat := 691507135973441831656619

theorem tailTrace_2020058 : CollatzResearch.WordTrace tailWord_2020058 prefixEnd_2020058 691507135973441831656619 := by
  unfold tailWord_2020058
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419392028920584821195207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49118378743788226189853885 18419392028920584821195207)
  ·
    refine ⟨27629088043380877231792811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18419392028920584821195207 27629088043380877231792811)
    ·
      refine ⟨41443632065071315847689217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27629088043380877231792811 41443632065071315847689217)
      ·
        refine ⟨31082724048803486885766913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41443632065071315847689217 31082724048803486885766913)
        ·
          refine ⟨23312043036602615164325185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31082724048803486885766913 23312043036602615164325185)
          ·
            refine ⟨17484032277451961373243889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23312043036602615164325185 17484032277451961373243889)
            ·
              refine ⟨13113024208088971029932917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17484032277451961373243889 13113024208088971029932917)
              ·
                refine ⟨1229346019508341034056211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13113024208088971029932917 1229346019508341034056211)
                ·
                  refine ⟨1844019029262511551084317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229346019508341034056211 1844019029262511551084317)
                  ·
                    refine ⟨691507135973441831656619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844019029262511551084317 691507135973441831656619)
                    ·
                      rfl

theorem cell22_2020058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_2020058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020058 prefixEnd_2020058 := by exact prefixLift 2020058
  have htrace : WordTrace (prefixWord ++ tailWord_2020058) baseStart_2020058 baseEnd_2020058 := by
    simpa [prefixWord, tailWord_2020058, baseEnd_2020058] using wordTrace_append hprefix tailTrace_2020058
  have hstable : (prefixWord ++ tailWord_2020058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020058).length < 2 ^ (prefixWord ++ tailWord_2020058).sum := by decide
  have hdescent : baseEnd_2020058 < baseStart_2020058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020086 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2020086 : Nat := 118140960795 + 2020086 * 2 ^ 59
def prefixEnd_2020086 : Nat := 4983230072969 + 3 ^ 40 * 2020086 * 2
def baseEnd_2020086 : Nat := 691516720945659091956533

theorem tailTrace_2020086 : CollatzResearch.WordTrace tailWord_2020086 prefixEnd_2020086 691516720945659091956533 := by
  unfold tailWord_2020086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604911834973806254175007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49119059573053933377866741 4604911834973806254175007)
  ·
    refine ⟨6907367752460709381262511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4604911834973806254175007 6907367752460709381262511)
    ·
      refine ⟨10361051628691064071893767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907367752460709381262511 10361051628691064071893767)
      ·
        refine ⟨15541577443036596107840651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361051628691064071893767 15541577443036596107840651)
        ·
          refine ⟨23312366164554894161760977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15541577443036596107840651 23312366164554894161760977)
          ·
            refine ⟨17484274623416170621320733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23312366164554894161760977 17484274623416170621320733)
            ·
              refine ⟨6556602983781063982995275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17484274623416170621320733 6556602983781063982995275)
              ·
                refine ⟨9834904475671595974492913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6556602983781063982995275 9834904475671595974492913)
                ·
                  refine ⟨7376178356753696980869685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9834904475671595974492913 7376178356753696980869685)
                  ·
                    refine ⟨691516720945659091956533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7376178356753696980869685 691516720945659091956533)
                    ·
                      rfl

theorem cell22_2020086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2020086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020086 prefixEnd_2020086 := by exact prefixLift 2020086
  have htrace : WordTrace (prefixWord ++ tailWord_2020086) baseStart_2020086 baseEnd_2020086 := by
    simpa [prefixWord, tailWord_2020086, baseEnd_2020086] using wordTrace_append hprefix tailTrace_2020086
  have hstable : (prefixWord ++ tailWord_2020086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020086).length < 2 ^ (prefixWord ++ tailWord_2020086).sum := by decide
  have hdescent : baseEnd_2020086 < baseStart_2020086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020176 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 5, 3]
def baseStart_2020176 : Nat := 118140960795 + 2020176 * 2 ^ 59
def prefixEnd_2020176 : Nat := 4983230072969 + 3 ^ 40 * 2020176 * 2
def baseEnd_2020176 : Nat := 691547529784928857206257

theorem tailTrace_2020176 : CollatzResearch.WordTrace tailWord_2020176 prefixEnd_2020176 691547529784928857206257 := by
  unfold tailWord_2020176
  simp only [CollatzResearch.WordTrace]
  refine ⟨36840935964627422718788191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49121247952836563625050921 36840935964627422718788191)
  ·
    refine ⟨55261403946941134078182287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36840935964627422718788191 55261403946941134078182287)
    ·
      refine ⟨82892105920411701117273431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55261403946941134078182287 82892105920411701117273431)
      ·
        refine ⟨124338158880617551675910147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82892105920411701117273431 124338158880617551675910147)
        ·
          refine ⟨186507238320926327513865221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124338158880617551675910147 186507238320926327513865221)
          ·
            refine ⟨34970107185173686408849729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186507238320926327513865221 34970107185173686408849729)
            ·
              refine ⟨26227580388880264806637297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34970107185173686408849729 26227580388880264806637297)
              ·
                refine ⟨19670685291660198604977973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26227580388880264806637297 19670685291660198604977973)
                ·
                  refine ⟨1844126746093143619216685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19670685291660198604977973 1844126746093143619216685)
                  ·
                    refine ⟨691547529784928857206257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844126746093143619216685 691547529784928857206257)
                    ·
                      rfl

theorem cell22_2020176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_2020176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020176 prefixEnd_2020176 := by exact prefixLift 2020176
  have htrace : WordTrace (prefixWord ++ tailWord_2020176) baseStart_2020176 baseEnd_2020176 := by
    simpa [prefixWord, tailWord_2020176, baseEnd_2020176] using wordTrace_append hprefix tailTrace_2020176
  have hstable : (prefixWord ++ tailWord_2020176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020176).length < 2 ^ (prefixWord ++ tailWord_2020176).sum := by decide
  have hdescent : baseEnd_2020176 < baseStart_2020176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020278 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2020278 : Nat := 118140960795 + 2020278 * 2 ^ 59
def prefixEnd_2020278 : Nat := 4983230072969 + 3 ^ 40 * 2020278 * 2
def baseEnd_2020278 : Nat := 691582446469434591155945

theorem tailTrace_2020278 : CollatzResearch.WordTrace tailWord_2020278 prefixEnd_2020278 691582446469434591155945 := by
  unfold tailWord_2020278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605349510930332303611843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49123728116590211238526325 4605349510930332303611843)
  ·
    refine ⟨6908024266395498455417765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4605349510930332303611843 6908024266395498455417765)
    ·
      refine ⟨1295254549949155960390831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6908024266395498455417765 1295254549949155960390831)
      ·
        refine ⟨1942881824923733940586247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295254549949155960390831 1942881824923733940586247)
        ·
          refine ⟨2914322737385600910879371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942881824923733940586247 2914322737385600910879371)
          ·
            refine ⟨4371484106078401366319057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914322737385600910879371 4371484106078401366319057)
            ·
              refine ⟨3278613079558801024739293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371484106078401366319057 3278613079558801024739293)
              ·
                refine ⟨1229479904834550384277235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3278613079558801024739293 1229479904834550384277235)
                ·
                  refine ⟨1844219857251825576415853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229479904834550384277235 1844219857251825576415853)
                  ·
                    refine ⟨691582446469434591155945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844219857251825576415853 691582446469434591155945)
                    ·
                      rfl

theorem cell22_2020278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2020278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020278 prefixEnd_2020278 := by exact prefixLift 2020278
  have htrace : WordTrace (prefixWord ++ tailWord_2020278) baseStart_2020278 baseEnd_2020278 := by
    simpa [prefixWord, tailWord_2020278, baseEnd_2020278] using wordTrace_append hprefix tailTrace_2020278
  have hstable : (prefixWord ++ tailWord_2020278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020278).length < 2 ^ (prefixWord ++ tailWord_2020278).sum := by decide
  have hdescent : baseEnd_2020278 < baseStart_2020278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020330 : List Nat := [3, 1, 3, 1, 2, 4, 2, 6]
def baseStart_2020330 : Nat := 118140960795 + 2020330 * 2 ^ 59
def prefixEnd_2020330 : Nat := 4983230072969 + 3 ^ 40 * 2020330 * 2
def baseEnd_2020330 : Nat := 76844471903569309872865

theorem tailTrace_2020330 : CollatzResearch.WordTrace tailWord_2020330 prefixEnd_2020330 76844471903569309872865 := by
  unfold tailWord_2020330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421872192674232434670611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49124992513797953159121629 18421872192674232434670611)
  ·
    refine ⟨27632808289011348652005917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18421872192674232434670611 27632808289011348652005917)
    ·
      refine ⟨10362303108379255744502219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27632808289011348652005917 10362303108379255744502219)
      ·
        refine ⟨15543454662568883616753329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10362303108379255744502219 15543454662568883616753329)
        ·
          refine ⟨11657590996926662712564997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15543454662568883616753329 11657590996926662712564997)
          ·
            refine ⟨2185798311923749258605937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11657590996926662712564997 2185798311923749258605937)
            ·
              refine ⟨1639348733942811943954453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185798311923749258605937 1639348733942811943954453)
              ·
                refine ⟨76844471903569309872865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1639348733942811943954453 76844471903569309872865)
                ·
                  rfl

theorem cell22_2020330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_2020330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020330 prefixEnd_2020330 := by exact prefixLift 2020330
  have htrace : WordTrace (prefixWord ++ tailWord_2020330) baseStart_2020330 baseEnd_2020330 := by
    simpa [prefixWord, tailWord_2020330, baseEnd_2020330] using wordTrace_append hprefix tailTrace_2020330
  have hstable : (prefixWord ++ tailWord_2020330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020330).length < 2 ^ (prefixWord ++ tailWord_2020330).sum := by decide
  have hdescent : baseEnd_2020330 < baseStart_2020330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020362 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_2020362 : Nat := 118140960795 + 2020362 * 2 ^ 59
def prefixEnd_2020362 : Nat := 4983230072969 + 3 ^ 40 * 2020362 * 2
def baseEnd_2020362 : Nat := 691611201386086372055687

theorem tailTrace_2020362 : CollatzResearch.WordTrace tailWord_2020362 prefixEnd_2020362 691611201386086372055687 := by
  unfold tailWord_2020362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18422163976645249800961835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49125770604387332802564893 18422163976645249800961835)
  ·
    refine ⟨27633245964967874701442753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18422163976645249800961835 27633245964967874701442753)
    ·
      refine ⟨20724934473725906026082065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27633245964967874701442753 20724934473725906026082065)
      ·
        refine ⟨15543700855294429519561549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724934473725906026082065 15543700855294429519561549)
        ·
          refine ⟨5828887820735411069835581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15543700855294429519561549 5828887820735411069835581)
          ·
            refine ⟨2185832932775779151188343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5828887820735411069835581 2185832932775779151188343)
            ·
              refine ⟨3278749399163668726782515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185832932775779151188343 3278749399163668726782515)
              ·
                refine ⟨4918124098745503090173773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3278749399163668726782515 4918124098745503090173773)
                ·
                  refine ⟨1844296537029563658815165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4918124098745503090173773 1844296537029563658815165)
                  ·
                    refine ⟨691611201386086372055687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844296537029563658815165 691611201386086372055687)
                    ·
                      rfl

theorem cell22_2020362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_2020362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020362 prefixEnd_2020362 := by exact prefixLift 2020362
  have htrace : WordTrace (prefixWord ++ tailWord_2020362) baseStart_2020362 baseEnd_2020362 := by
    simpa [prefixWord, tailWord_2020362, baseEnd_2020362] using wordTrace_append hprefix tailTrace_2020362
  have hstable : (prefixWord ++ tailWord_2020362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020362).length < 2 ^ (prefixWord ++ tailWord_2020362).sum := by decide
  have hdescent : baseEnd_2020362 < baseStart_2020362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020371 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_2020371 : Nat := 118140960795 + 2020371 * 2 ^ 59
def prefixEnd_2020371 : Nat := 4983230072969 + 3 ^ 40 * 2020371 * 2
def baseEnd_2020371 : Nat := 691614282270013348580659

theorem tailTrace_2020371 : CollatzResearch.WordTrace tailWord_2020371 prefixEnd_2020371 691614282270013348580659 := by
  unfold tailWord_2020371
  simp only [CollatzResearch.WordTrace]
  refine ⟨73688984163548393740924967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49125989442365595827283311 73688984163548393740924967)
  ·
    refine ⟨110533476245322590611387451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73688984163548393740924967 110533476245322590611387451)
    ·
      refine ⟨165800214367983885917081177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110533476245322590611387451 165800214367983885917081177)
      ·
        refine ⟨124350160775987914437810883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165800214367983885917081177 124350160775987914437810883)
        ·
          refine ⟨186525241163981871656716325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124350160775987914437810883 186525241163981871656716325)
          ·
            refine ⟨34973482718246600935634311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186525241163981871656716325 34973482718246600935634311)
            ·
              refine ⟨52460224077369901403451467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34973482718246600935634311 52460224077369901403451467)
              ·
                refine ⟨78690336116054852105177201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52460224077369901403451467 78690336116054852105177201)
                ·
                  refine ⟨59017752087041139078882901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78690336116054852105177201 59017752087041139078882901)
                  ·
                    refine ⟨691614282270013348580659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59017752087041139078882901 691614282270013348580659)
                    ·
                      rfl

theorem cell22_2020371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_2020371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020371 prefixEnd_2020371 := by exact prefixLift 2020371
  have htrace : WordTrace (prefixWord ++ tailWord_2020371) baseStart_2020371 baseEnd_2020371 := by
    simpa [prefixWord, tailWord_2020371, baseEnd_2020371] using wordTrace_append hprefix tailTrace_2020371
  have hstable : (prefixWord ++ tailWord_2020371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020371).length < 2 ^ (prefixWord ++ tailWord_2020371).sum := by decide
  have hdescent : baseEnd_2020371 < baseStart_2020371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020375 : List Nat := [1, 1, 3, 5, 1, 2, 1, 3, 5]
def baseStart_2020375 : Nat := 118140960795 + 2020375 * 2 ^ 59
def prefixEnd_2020375 : Nat := 4983230072969 + 3 ^ 40 * 2020375 * 2
def baseEnd_2020375 : Nat := 230538550517252890493549

theorem tailTrace_2020375 : CollatzResearch.WordTrace tailWord_2020375 prefixEnd_2020375 230538550517252890493549 := by
  unfold tailWord_2020375
  simp only [CollatzResearch.WordTrace]
  refine ⟨73689130055533902424070579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49126086703689268282713719 73689130055533902424070579)
  ·
    refine ⟨110533695083300853636105869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73689130055533902424070579 110533695083300853636105869)
    ·
      refine ⟨41450135656237820113539701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110533695083300853636105869 41450135656237820113539701)
      ·
        refine ⟨3885950217772295635644347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41450135656237820113539701 3885950217772295635644347)
        ·
          refine ⟨5828925326658443453466521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885950217772295635644347 5828925326658443453466521)
          ·
            refine ⟨4371693994993832590099891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5828925326658443453466521 4371693994993832590099891)
            ·
              refine ⟨6557540992490748885149837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371693994993832590099891 6557540992490748885149837)
              ·
                refine ⟨2459077872184030831931189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6557540992490748885149837 2459077872184030831931189)
                ·
                  refine ⟨230538550517252890493549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2459077872184030831931189 230538550517252890493549)
                  ·
                    rfl

theorem cell22_2020375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 3, 5].length) (baseStart_2020375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020375 prefixEnd_2020375 := by exact prefixLift 2020375
  have htrace : WordTrace (prefixWord ++ tailWord_2020375) baseStart_2020375 baseEnd_2020375 := by
    simpa [prefixWord, tailWord_2020375, baseEnd_2020375] using wordTrace_append hprefix tailTrace_2020375
  have hstable : (prefixWord ++ tailWord_2020375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020375).length < 2 ^ (prefixWord ++ tailWord_2020375).sum := by decide
  have hdescent : baseEnd_2020375 < baseStart_2020375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020422 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2020422 : Nat := 118140960795 + 2020422 * 2 ^ 59
def prefixEnd_2020422 : Nat := 4983230072969 + 3 ^ 40 * 2020422 * 2
def baseEnd_2020422 : Nat := 691631740612266215555503

theorem tailTrace_2020422 : CollatzResearch.WordTrace tailWord_2020422 prefixEnd_2020422 691631740612266215555503 := by
  unfold tailWord_2020422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302838883948863420344735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49127229524242419634021013 2302838883948863420344735)
  ·
    refine ⟨3454258325923295130517103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302838883948863420344735 3454258325923295130517103)
    ·
      refine ⟨5181387488884942695775655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454258325923295130517103 5181387488884942695775655)
      ·
        refine ⟨7772081233327414043663483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181387488884942695775655 7772081233327414043663483)
        ·
          refine ⟨11658121849991121065495225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772081233327414043663483 11658121849991121065495225)
          ·
            refine ⟨8743591387493340799121419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11658121849991121065495225 8743591387493340799121419)
            ·
              refine ⟨13115387081240011198682129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8743591387493340799121419 13115387081240011198682129)
              ·
                refine ⟨9836540310930008399011597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13115387081240011198682129 9836540310930008399011597)
                ·
                  refine ⟨3688702616598753149629349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9836540310930008399011597 3688702616598753149629349)
                  ·
                    refine ⟨691631740612266215555503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688702616598753149629349 691631740612266215555503)
                    ·
                      rfl

theorem cell22_2020422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2020422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020422 prefixEnd_2020422 := by exact prefixLift 2020422
  have htrace : WordTrace (prefixWord ++ tailWord_2020422) baseStart_2020422 baseEnd_2020422 := by
    simpa [prefixWord, tailWord_2020422, baseEnd_2020422] using wordTrace_append hprefix tailTrace_2020422
  have hstable : (prefixWord ++ tailWord_2020422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020422).length < 2 ^ (prefixWord ++ tailWord_2020422).sum := by decide
  have hdescent : baseEnd_2020422 < baseStart_2020422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020433 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_2020433 : Nat := 118140960795 + 2020433 * 2 ^ 59
def prefixEnd_2020433 : Nat := 4983230072969 + 3 ^ 40 * 2020433 * 2
def baseEnd_2020433 : Nat := 691635506137065853530469

theorem tailTrace_2020433 : CollatzResearch.WordTrace tailWord_2020433 prefixEnd_2020433 691635506137065853530469 := by
  unfold tailWord_2020433
  simp only [CollatzResearch.WordTrace]
  refine ⟨73691245489323778329681953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49127496992882518886454635 73691245489323778329681953)
  ·
    refine ⟨55268434116992833747261465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73691245489323778329681953 55268434116992833747261465)
    ·
      refine ⟨41451325587744625310446099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55268434116992833747261465 41451325587744625310446099)
      ·
        refine ⟨62176988381616937965669149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41451325587744625310446099 62176988381616937965669149)
        ·
          refine ⟨23316370643106351737125931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62176988381616937965669149 23316370643106351737125931)
          ·
            refine ⟨34974555964659527605688897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23316370643106351737125931 34974555964659527605688897)
            ·
              refine ⟨26230916973494645704266673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34974555964659527605688897 26230916973494645704266673)
              ·
                refine ⟨19673187730120984278200005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26230916973494645704266673 19673187730120984278200005)
                ·
                  refine ⟨3688722699397684552162501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19673187730120984278200005 3688722699397684552162501)
                  ·
                    refine ⟨691635506137065853530469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688722699397684552162501 691635506137065853530469)
                    ·
                      rfl

theorem cell22_2020433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_2020433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020433 prefixEnd_2020433 := by exact prefixLift 2020433
  have htrace : WordTrace (prefixWord ++ tailWord_2020433) baseStart_2020433 baseEnd_2020433 := by
    simpa [prefixWord, tailWord_2020433, baseEnd_2020433] using wordTrace_append hprefix tailTrace_2020433
  have hstable : (prefixWord ++ tailWord_2020433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020433).length < 2 ^ (prefixWord ++ tailWord_2020433).sum := by decide
  have hdescent : baseEnd_2020433 < baseStart_2020433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020456 : List Nat := [2, 1, 4, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2020456 : Nat := 118140960795 + 2020456 * 2 ^ 59
def prefixEnd_2020456 : Nat := 4983230072969 + 3 ^ 40 * 2020456 * 2
def baseEnd_2020456 : Nat := 691643379507101460205399

theorem tailTrace_2020456 : CollatzResearch.WordTrace tailWord_2020456 prefixEnd_2020456 691643379507101460205399 := by
  unfold tailWord_2020456
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846042184120226628884611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49128056245493635505179481 36846042184120226628884611)
  ·
    refine ⟨55269063276180339943326917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36846042184120226628884611 55269063276180339943326917)
    ·
      refine ⟨10362949364283813739373797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55269063276180339943326917 10362949364283813739373797)
      ·
        refine ⟨1943053005803215076132587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10362949364283813739373797 1943053005803215076132587)
        ·
          refine ⟨2914579508704822614198881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943053005803215076132587 2914579508704822614198881)
          ·
            refine ⟨2185934631528616960649161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914579508704822614198881 2185934631528616960649161)
            ·
              refine ⟨1639450973646462720486871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185934631528616960649161 1639450973646462720486871)
              ·
                refine ⟨2459176460469694080730307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639450973646462720486871 2459176460469694080730307)
                ·
                  refine ⟨3688764690704541121095461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2459176460469694080730307 3688764690704541121095461)
                  ·
                    refine ⟨691643379507101460205399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3688764690704541121095461 691643379507101460205399)
                    ·
                      rfl

theorem cell22_2020456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2020456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020456 prefixEnd_2020456 := by exact prefixLift 2020456
  have htrace : WordTrace (prefixWord ++ tailWord_2020456) baseStart_2020456 baseEnd_2020456 := by
    simpa [prefixWord, tailWord_2020456, baseEnd_2020456] using wordTrace_append hprefix tailTrace_2020456
  have hstable : (prefixWord ++ tailWord_2020456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020456).length < 2 ^ (prefixWord ++ tailWord_2020456).sum := by decide
  have hdescent : baseEnd_2020456 < baseStart_2020456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020469 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2020469 : Nat := 118140960795 + 2020469 * 2 ^ 59
def prefixEnd_2020469 : Nat := 4983230072969 + 3 ^ 40 * 2020469 * 2
def baseEnd_2020469 : Nat := 691647829672773759630359

theorem tailTrace_2020469 : CollatzResearch.WordTrace tailWord_2020469 prefixEnd_2020469 691647829672773759630359 := by
  unfold tailWord_2020469
  simp only [CollatzResearch.WordTrace]
  refine ⟨73692558517193356477992461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49128372344795570985328307 73692558517193356477992461)
  ·
    refine ⟨27634709443947508679247173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73692558517193356477992461 27634709443947508679247173)
    ·
      refine ⟨5181508020740157877358845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27634709443947508679247173 5181508020740157877358845)
      ·
        refine ⟨1943065507777559204009567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5181508020740157877358845 1943065507777559204009567)
        ·
          refine ⟨2914598261666338806014351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943065507777559204009567 2914598261666338806014351)
          ·
            refine ⟨4371897392499508209021527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914598261666338806014351 4371897392499508209021527)
            ·
              refine ⟨6557846088749262313532291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4371897392499508209021527 6557846088749262313532291)
              ·
                refine ⟨9836769133123893470298437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6557846088749262313532291 9836769133123893470298437)
                ·
                  refine ⟨1844394212460730025680957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9836769133123893470298437 1844394212460730025680957)
                  ·
                    refine ⟨691647829672773759630359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844394212460730025680957 691647829672773759630359)
                    ·
                      rfl

theorem cell22_2020469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2020469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020469 prefixEnd_2020469 := by exact prefixLift 2020469
  have htrace : WordTrace (prefixWord ++ tailWord_2020469) baseStart_2020469 baseEnd_2020469 := by
    simpa [prefixWord, tailWord_2020469, baseEnd_2020469] using wordTrace_append hprefix tailTrace_2020469
  have hstable : (prefixWord ++ tailWord_2020469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020469).length < 2 ^ (prefixWord ++ tailWord_2020469).sum := by decide
  have hdescent : baseEnd_2020469 < baseStart_2020469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020480 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 3, 3]
def baseStart_2020480 : Nat := 118140960795 + 2020480 * 2 ^ 59
def prefixEnd_2020480 : Nat := 4983230072969 + 3 ^ 40 * 2020480 * 2
def baseEnd_2020480 : Nat := 691651595197573397605325

theorem tailTrace_2020480 : CollatzResearch.WordTrace tailWord_2020480 prefixEnd_2020480 691651595197573397605325 := by
  unfold tailWord_2020480
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846479860076752678321447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49128639813435670237761929 36846479860076752678321447)
  ·
    refine ⟨55269719790115129017482171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36846479860076752678321447 55269719790115129017482171)
    ·
      refine ⟨82904579685172693526223257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55269719790115129017482171 82904579685172693526223257)
      ·
        refine ⟨62178434763879520144667443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82904579685172693526223257 62178434763879520144667443)
        ·
          refine ⟨93267652145819280217001165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62178434763879520144667443 93267652145819280217001165)
          ·
            refine ⟨34975369554682230081375437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93267652145819280217001165 34975369554682230081375437)
            ·
              refine ⟨13115763583005836280515789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34975369554682230081375437 13115763583005836280515789)
              ·
                refine ⟨4918411343627188605193421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13115763583005836280515789 4918411343627188605193421)
                ·
                  refine ⟨1844404253860195726947533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4918411343627188605193421 1844404253860195726947533)
                  ·
                    refine ⟨691651595197573397605325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844404253860195726947533 691651595197573397605325)
                    ·
                      rfl

theorem cell22_2020480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_2020480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020480 prefixEnd_2020480 := by exact prefixLift 2020480
  have htrace : WordTrace (prefixWord ++ tailWord_2020480) baseStart_2020480 baseEnd_2020480 := by
    simpa [prefixWord, tailWord_2020480, baseEnd_2020480] using wordTrace_append hprefix tailTrace_2020480
  have hstable : (prefixWord ++ tailWord_2020480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020480).length < 2 ^ (prefixWord ++ tailWord_2020480).sum := by decide
  have hdescent : baseEnd_2020480 < baseStart_2020480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020544 : List Nat := [2, 1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_2020544 : Nat := 118140960795 + 2020544 * 2 ^ 59
def prefixEnd_2020544 : Nat := 4983230072969 + 3 ^ 40 * 2020544 * 2
def baseEnd_2020544 : Nat := 230557834568499521335043

theorem tailTrace_2020544 : CollatzResearch.WordTrace tailWord_2020544 prefixEnd_2020544 230557834568499521335043 := by
  unfold tailWord_2020544
  simp only [CollatzResearch.WordTrace]
  refine ⟨36847646995960822143486343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49130195994614429524648457 36847646995960822143486343)
  ·
    refine ⟨55271470493941233215229515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36847646995960822143486343 55271470493941233215229515)
    ·
      refine ⟨82907205740911849822844273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55271470493941233215229515 82907205740911849822844273)
      ·
        refine ⟨62180404305683887367133205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82907205740911849822844273 62180404305683887367133205)
        ·
          refine ⟨2914706451828932220334369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62180404305683887367133205 2914706451828932220334369)
          ·
            refine ⟨2186029838871699165250777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2914706451828932220334369 2186029838871699165250777)
            ·
              refine ⟨1639522379153774373938083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186029838871699165250777 1639522379153774373938083)
              ·
                refine ⟨2459283568730661560907125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639522379153774373938083 2459283568730661560907125)
                ·
                  refine ⟨230557834568499521335043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2459283568730661560907125 230557834568499521335043)
                  ·
                    rfl

theorem cell22_2020544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_2020544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020544 prefixEnd_2020544 := by exact prefixLift 2020544
  have htrace : WordTrace (prefixWord ++ tailWord_2020544) baseStart_2020544 baseEnd_2020544 := by
    simpa [prefixWord, tailWord_2020544, baseEnd_2020544] using wordTrace_append hprefix tailTrace_2020544
  have hstable : (prefixWord ++ tailWord_2020544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020544).length < 2 ^ (prefixWord ++ tailWord_2020544).sum := by decide
  have hdescent : baseEnd_2020544 < baseStart_2020544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020587 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 2, 3]
def baseStart_2020587 : Nat := 118140960795 + 2020587 * 2 ^ 59
def prefixEnd_2020587 : Nat := 4983230072969 + 3 ^ 40 * 2020587 * 2
def baseEnd_2020587 : Nat := 691688223484260785179997

theorem tailTrace_2020587 : CollatzResearch.WordTrace tailWord_2020587 prefixEnd_2020587 691688223484260785179997 := by
  unfold tailWord_2020587
  simp only [CollatzResearch.WordTrace]
  refine ⟨73696862330765862630788015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49131241553843908420525343 73696862330765862630788015)
  ·
    refine ⟨110545293496148793946182023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73696862330765862630788015 110545293496148793946182023)
    ·
      refine ⟨165817940244223190919273035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110545293496148793946182023 165817940244223190919273035)
      ·
        refine ⟨248726910366334786378909553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165817940244223190919273035 248726910366334786378909553)
        ·
          refine ⟨186545182774751089784182165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248726910366334786378909553 186545182774751089784182165)
          ·
            refine ⟨8744305442566457333633539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186545182774751089784182165 8744305442566457333633539)
            ·
              refine ⟨13116458163849686000450309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744305442566457333633539 13116458163849686000450309)
              ·
                refine ⟨2459335905721816125084433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13116458163849686000450309 2459335905721816125084433)
                ·
                  refine ⟨1844501929291362093813325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459335905721816125084433 1844501929291362093813325)
                  ·
                    refine ⟨691688223484260785179997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844501929291362093813325 691688223484260785179997)
                    ·
                      rfl

theorem cell22_2020587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 3].length) (baseStart_2020587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020587 prefixEnd_2020587 := by exact prefixLift 2020587
  have htrace : WordTrace (prefixWord ++ tailWord_2020587) baseStart_2020587 baseEnd_2020587 := by
    simpa [prefixWord, tailWord_2020587, baseEnd_2020587] using wordTrace_append hprefix tailTrace_2020587
  have hstable : (prefixWord ++ tailWord_2020587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020587).length < 2 ^ (prefixWord ++ tailWord_2020587).sum := by decide
  have hdescent : baseEnd_2020587 < baseStart_2020587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020589 : List Nat := [1, 5, 1, 2, 2, 2, 1, 4, 4]
def baseStart_2020589 : Nat := 118140960795 + 2020589 * 2 ^ 59
def prefixEnd_2020589 : Nat := 4983230072969 + 3 ^ 40 * 2020589 * 2
def baseEnd_2020589 : Nat := 230562969375044482209997

theorem tailTrace_2020589 : CollatzResearch.WordTrace tailWord_2020589 prefixEnd_2020589 230562969375044482209997 := by
  unfold tailWord_2020589
  simp only [CollatzResearch.WordTrace]
  refine ⟨73696935276758616972360821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49131290184505744648240547 73696935276758616972360821)
  ·
    refine ⟨6909087682196120341158827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73696935276758616972360821 6909087682196120341158827)
    ·
      refine ⟨10363631523294180511738241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909087682196120341158827 10363631523294180511738241)
      ·
        refine ⟨7772723642470635383803681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10363631523294180511738241 7772723642470635383803681)
        ·
          refine ⟨5829542731852976537852761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7772723642470635383803681 5829542731852976537852761)
          ·
            refine ⟨4372157048889732403389571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5829542731852976537852761 4372157048889732403389571)
            ·
              refine ⟨6558235573334598605084357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4372157048889732403389571 6558235573334598605084357)
              ·
                refine ⟨1229669170000237238453317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6558235573334598605084357 1229669170000237238453317)
                ·
                  refine ⟨230562969375044482209997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229669170000237238453317 230562969375044482209997)
                  ·
                    rfl

theorem cell22_2020589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_2020589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020589 prefixEnd_2020589 := by exact prefixLift 2020589
  have htrace : WordTrace (prefixWord ++ tailWord_2020589) baseStart_2020589 baseEnd_2020589 := by
    simpa [prefixWord, tailWord_2020589, baseEnd_2020589] using wordTrace_append hprefix tailTrace_2020589
  have hstable : (prefixWord ++ tailWord_2020589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020589).length < 2 ^ (prefixWord ++ tailWord_2020589).sum := by decide
  have hdescent : baseEnd_2020589 < baseStart_2020589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020707 : List Nat := [1, 1, 1, 5, 2, 2, 3, 1, 6]
def baseStart_2020707 : Nat := 118140960795 + 2020707 * 2 ^ 59
def prefixEnd_2020707 : Nat := 4983230072969 + 3 ^ 40 * 2020707 * 2
def baseEnd_2020707 : Nat := 230576433978873490726543

theorem tailTrace_2020707 : CollatzResearch.WordTrace tailWord_2020707 prefixEnd_2020707 230576433978873490726543 := by
  unfold tailWord_2020707
  simp only [CollatzResearch.WordTrace]
  refine ⟨73701239090331123125156375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49134159393554082083437583 73701239090331123125156375)
  ·
    refine ⟨110551858635496684687734563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73701239090331123125156375 110551858635496684687734563)
    ·
      refine ⟨165827787953245027031601845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110551858635496684687734563 165827787953245027031601845)
      ·
        refine ⟨15546355120616721284212673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165827787953245027031601845 15546355120616721284212673)
        ·
          refine ⟨11659766340462540963159505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15546355120616721284212673 11659766340462540963159505)
          ·
            refine ⟨8744824755346905722369629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11659766340462540963159505 8744824755346905722369629)
            ·
              refine ⟨3279309283255089645888611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8744824755346905722369629 3279309283255089645888611)
              ·
                refine ⟨4918963924882634468832917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279309283255089645888611 4918963924882634468832917)
                ·
                  refine ⟨230576433978873490726543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4918963924882634468832917 230576433978873490726543)
                  ·
                    rfl

theorem cell22_2020707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 6].length) (baseStart_2020707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020707 prefixEnd_2020707 := by exact prefixLift 2020707
  have htrace : WordTrace (prefixWord ++ tailWord_2020707) baseStart_2020707 baseEnd_2020707 := by
    simpa [prefixWord, tailWord_2020707, baseEnd_2020707] using wordTrace_append hprefix tailTrace_2020707
  have hstable : (prefixWord ++ tailWord_2020707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020707).length < 2 ^ (prefixWord ++ tailWord_2020707).sum := by decide
  have hdescent : baseEnd_2020707 < baseStart_2020707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020722 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_2020722 : Nat := 118140960795 + 2020722 * 2 ^ 59
def prefixEnd_2020722 : Nat := 4983230072969 + 3 ^ 40 * 2020722 * 2
def baseEnd_2020722 : Nat := 691734436743165433054583

theorem tailTrace_2020722 : CollatzResearch.WordTrace tailWord_2020722 prefixEnd_2020722 691734436743165433054583 := by
  unfold tailWord_2020722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425446546319195171738105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49134524123517853791301613 18425446546319195171738105)
  ·
    refine ⟨13819084909739396378803579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18425446546319195171738105 13819084909739396378803579)
    ·
      refine ⟨20728627364609094568205369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819084909739396378803579 20728627364609094568205369)
      ·
        refine ⟨15546470523456820926154027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20728627364609094568205369 15546470523456820926154027)
        ·
          refine ⟨23319705785185231389231041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15546470523456820926154027 23319705785185231389231041)
          ·
            refine ⟨17489779338888923541923281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23319705785185231389231041 17489779338888923541923281)
            ·
              refine ⟨13117334504166692656442461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17489779338888923541923281 13117334504166692656442461)
              ·
                refine ⟨4919000439062509746165923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13117334504166692656442461 4919000439062509746165923)
                ·
                  refine ⟨7378500658593764619248885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919000439062509746165923 7378500658593764619248885)
                  ·
                    refine ⟨691734436743165433054583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7378500658593764619248885 691734436743165433054583)
                    ·
                      rfl

theorem cell22_2020722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_2020722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020722 prefixEnd_2020722 := by exact prefixLift 2020722
  have htrace : WordTrace (prefixWord ++ tailWord_2020722) baseStart_2020722 baseEnd_2020722 := by
    simpa [prefixWord, tailWord_2020722, baseEnd_2020722] using wordTrace_append hprefix tailTrace_2020722
  have hstable : (prefixWord ++ tailWord_2020722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020722).length < 2 ^ (prefixWord ++ tailWord_2020722).sum := by decide
  have hdescent : baseEnd_2020722 < baseStart_2020722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020756 : List Nat := [2, 4, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2020756 : Nat := 118140960795 + 2020756 * 2 ^ 59
def prefixEnd_2020756 : Nat := 4983230072969 + 3 ^ 40 * 2020756 * 2
def baseEnd_2020756 : Nat := 691746075638000677704479

theorem tailTrace_2020756 : CollatzResearch.WordTrace tailWord_2020756 prefixEnd_2020756 691746075638000677704479 := by
  unfold tailWord_2020756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36851513133576802246845061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49135350844769069662460081 36851513133576802246845061)
  ·
    refine ⟨6909658712545650421283449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36851513133576802246845061 6909658712545650421283449)
    ·
      refine ⟨5182244034409237815962587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6909658712545650421283449 5182244034409237815962587)
      ·
        refine ⟨7773366051613856723943881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182244034409237815962587 7773366051613856723943881)
        ·
          refine ⟨5830024538710392542957911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7773366051613856723943881 5830024538710392542957911)
          ·
            refine ⟨8745036808065588814436867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830024538710392542957911 8745036808065588814436867)
            ·
              refine ⟨13117555212098383221655301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8745036808065588814436867 13117555212098383221655301)
              ·
                refine ⟨2459541602268446854060369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13117555212098383221655301 2459541602268446854060369)
                ·
                  refine ⟨1844656201701335140545277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459541602268446854060369 1844656201701335140545277)
                  ·
                    refine ⟨691746075638000677704479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844656201701335140545277 691746075638000677704479)
                    ·
                      rfl

theorem cell22_2020756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2020756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020756 prefixEnd_2020756 := by exact prefixLift 2020756
  have htrace : WordTrace (prefixWord ++ tailWord_2020756) baseStart_2020756 baseEnd_2020756 := by
    simpa [prefixWord, tailWord_2020756, baseEnd_2020756] using wordTrace_append hprefix tailTrace_2020756
  have hstable : (prefixWord ++ tailWord_2020756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020756).length < 2 ^ (prefixWord ++ tailWord_2020756).sum := by decide
  have hdescent : baseEnd_2020756 < baseStart_2020756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020797 : List Nat := [1, 4, 1, 2, 2, 1, 2, 2, 7]
def baseStart_2020797 : Nat := 118140960795 + 2020797 * 2 ^ 59
def prefixEnd_2020797 : Nat := 4983230072969 + 3 ^ 40 * 2020797 * 2
def baseEnd_2020797 : Nat := 230586703591963412476451

theorem tailTrace_2020797 : CollatzResearch.WordTrace tailWord_2020797 prefixEnd_2020797 230586703591963412476451 := by
  unfold tailWord_2020797
  simp only [CollatzResearch.WordTrace]
  refine ⟨73704521660005068495932645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49136347773336712330621763 73704521660005068495932645)
  ·
    refine ⟨13819597811250950342987371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73704521660005068495932645 13819597811250950342987371)
    ·
      refine ⟨20729396716876425514481057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819597811250950342987371 20729396716876425514481057)
      ·
        refine ⟨15547047537657319135860793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20729396716876425514481057 15547047537657319135860793)
        ·
          refine ⟨11660285653242989351895595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15547047537657319135860793 11660285653242989351895595)
          ·
            refine ⟨17490428479864484027843393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660285653242989351895595 17490428479864484027843393)
            ·
              refine ⟨13117821359898363020882545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17490428479864484027843393 13117821359898363020882545)
              ·
                refine ⟨9838366019923772265661909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13117821359898363020882545 9838366019923772265661909)
                ·
                  refine ⟨230586703591963412476451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9838366019923772265661909 230586703591963412476451)
                  ·
                    rfl

theorem cell22_2020797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_2020797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020797 prefixEnd_2020797 := by exact prefixLift 2020797
  have htrace : WordTrace (prefixWord ++ tailWord_2020797) baseStart_2020797 baseEnd_2020797 := by
    simpa [prefixWord, tailWord_2020797, baseEnd_2020797] using wordTrace_append hprefix tailTrace_2020797
  have hstable : (prefixWord ++ tailWord_2020797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020797).length < 2 ^ (prefixWord ++ tailWord_2020797).sum := by decide
  have hdescent : baseEnd_2020797 < baseStart_2020797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020814 : List Nat := [4, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2020814 : Nat := 118140960795 + 2020814 * 2 ^ 59
def prefixEnd_2020814 : Nat := 4983230072969 + 3 ^ 40 * 2020814 * 2
def baseEnd_2020814 : Nat := 230588643407769286584767

theorem tailTrace_2020814 : CollatzResearch.WordTrace tailWord_2020814 prefixEnd_2020814 230588643407769286584767 := by
  unfold tailWord_2020814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213142712617935049912687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49136761133962320266200997 9213142712617935049912687)
  ·
    refine ⟨13819714068926902574869031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9213142712617935049912687 13819714068926902574869031)
    ·
      refine ⟨20729571103390353862303547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819714068926902574869031 20729571103390353862303547)
      ·
        refine ⟨31094356655085530793455321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729571103390353862303547 31094356655085530793455321)
        ·
          refine ⟨23320767491314148095091491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31094356655085530793455321 23320767491314148095091491)
          ·
            refine ⟨34981151236971222142637237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23320767491314148095091491 34981151236971222142637237)
            ·
              refine ⟨3279482928466052075872241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34981151236971222142637237 3279482928466052075872241)
              ·
                refine ⟨2459612196349539056904181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279482928466052075872241 2459612196349539056904181)
                ·
                  refine ⟨230588643407769286584767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2459612196349539056904181 230588643407769286584767)
                  ·
                    rfl

theorem cell22_2020814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2020814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020814 prefixEnd_2020814 := by exact prefixLift 2020814
  have htrace : WordTrace (prefixWord ++ tailWord_2020814) baseStart_2020814 baseEnd_2020814 := by
    simpa [prefixWord, tailWord_2020814, baseEnd_2020814] using wordTrace_append hprefix tailTrace_2020814
  have hstable : (prefixWord ++ tailWord_2020814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020814).length < 2 ^ (prefixWord ++ tailWord_2020814).sum := by decide
  have hdescent : baseEnd_2020814 < baseStart_2020814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020829 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2020829 : Nat := 118140960795 + 2020829 * 2 ^ 59
def prefixEnd_2020829 : Nat := 4983230072969 + 3 ^ 40 * 2020829 * 2
def baseEnd_2020829 : Nat := 691771065029852820629255

theorem tailTrace_2020829 : CollatzResearch.WordTrace tailWord_2020829 prefixEnd_2020829 691771065029852820629255 := by
  unfold tailWord_2020829
  simp only [CollatzResearch.WordTrace]
  refine ⟨73705688795889137961097541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49137125863926091974065027 73705688795889137961097541)
  ·
    refine ⟨13819816649229213367705789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73705688795889137961097541 13819816649229213367705789)
    ·
      refine ⟨5182431243460955012889671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13819816649229213367705789 5182431243460955012889671)
      ·
        refine ⟨7773646865191432519334507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182431243460955012889671 7773646865191432519334507)
        ·
          refine ⟨11660470297787148779001761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773646865191432519334507 11660470297787148779001761)
          ·
            refine ⟨8745352723340361584251321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11660470297787148779001761 8745352723340361584251321)
            ·
              refine ⟨6559014542505271188188491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8745352723340361584251321 6559014542505271188188491)
              ·
                refine ⟨9838521813757906782282737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559014542505271188188491 9838521813757906782282737)
                ·
                  refine ⟨7378891360318430086712053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9838521813757906782282737 7378891360318430086712053)
                  ·
                    refine ⟨691771065029852820629255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7378891360318430086712053 691771065029852820629255)
                    ·
                      rfl

theorem cell22_2020829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2020829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020829 prefixEnd_2020829 := by exact prefixLift 2020829
  have htrace : WordTrace (prefixWord ++ tailWord_2020829) baseStart_2020829 baseEnd_2020829 := by
    simpa [prefixWord, tailWord_2020829, baseEnd_2020829] using wordTrace_append hprefix tailTrace_2020829
  have hstable : (prefixWord ++ tailWord_2020829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020829).length < 2 ^ (prefixWord ++ tailWord_2020829).sum := by decide
  have hdescent : baseEnd_2020829 < baseStart_2020829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020857 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_2020857 : Nat := 118140960795 + 2020857 * 2 ^ 59
def prefixEnd_2020857 : Nat := 4983230072969 + 3 ^ 40 * 2020857 * 2
def baseEnd_2020857 : Nat := 691780650002070080929169

theorem tailTrace_2020857 : CollatzResearch.WordTrace tailWord_2020857 prefixEnd_2020857 691780650002070080929169 := by
  unfold tailWord_2020857
  simp only [CollatzResearch.WordTrace]
  refine ⟨73706710039787698743116825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49137806693191799162077883 73706710039787698743116825)
  ·
    refine ⟨55280032529840774057337619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73706710039787698743116825 55280032529840774057337619)
    ·
      refine ⟨82920048794761161086006429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55280032529840774057337619 82920048794761161086006429)
      ·
        refine ⟨31095018298035435407252411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82920048794761161086006429 31095018298035435407252411)
        ·
          refine ⟨46642527447053153110878617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31095018298035435407252411 46642527447053153110878617)
          ·
            refine ⟨34981895585289864833158963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46642527447053153110878617 34981895585289864833158963)
            ·
              refine ⟨52472843377934797249738445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34981895585289864833158963 52472843377934797249738445)
              ·
                refine ⟨19677316266725548968651917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52472843377934797249738445 19677316266725548968651917)
                ·
                  refine ⟨7378993600022080863244469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19677316266725548968651917 7378993600022080863244469)
                  ·
                    refine ⟨691780650002070080929169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7378993600022080863244469 691780650002070080929169)
                    ·
                      rfl

theorem cell22_2020857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_2020857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020857 prefixEnd_2020857 := by exact prefixLift 2020857
  have htrace : WordTrace (prefixWord ++ tailWord_2020857) baseStart_2020857 baseEnd_2020857 := by
    simpa [prefixWord, tailWord_2020857, baseEnd_2020857] using wordTrace_append hprefix tailTrace_2020857
  have hstable : (prefixWord ++ tailWord_2020857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020857).length < 2 ^ (prefixWord ++ tailWord_2020857).sum := by decide
  have hdescent : baseEnd_2020857 < baseStart_2020857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020876 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_2020876 : Nat := 118140960795 + 2020876 * 2 ^ 59
def prefixEnd_2020876 : Nat := 4983230072969 + 3 ^ 40 * 2020876 * 2
def baseEnd_2020876 : Nat := 230595718030120121568037

theorem tailTrace_2020876 : CollatzResearch.WordTrace tailWord_2020876 prefixEnd_2020876 230595718030120121568037 := by
  unfold tailWord_2020876
  simp only [CollatzResearch.WordTrace]
  refine ⟨36853701513359432494029241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49138268684479243325372321 36853701513359432494029241)
  ·
    refine ⟨27640276135019574370521931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36853701513359432494029241 27640276135019574370521931)
    ·
      refine ⟨41460414202529361555782897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27640276135019574370521931 41460414202529361555782897)
      ·
        refine ⟨31095310651897021166837173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41460414202529361555782897 31095310651897021166837173)
        ·
          refine ⟨2915185373615345734390985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31095310651897021166837173 2915185373615345734390985)
          ·
            refine ⟨2186389030211509300793239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915185373615345734390985 2186389030211509300793239)
            ·
              refine ⟨3279583545317263951189859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186389030211509300793239 3279583545317263951189859)
              ·
                refine ⟨4919375317975895926784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279583545317263951189859 4919375317975895926784789)
                ·
                  refine ⟨230595718030120121568037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4919375317975895926784789 230595718030120121568037)
                  ·
                    rfl

theorem cell22_2020876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_2020876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020876 prefixEnd_2020876 := by exact prefixLift 2020876
  have htrace : WordTrace (prefixWord ++ tailWord_2020876) baseStart_2020876 baseEnd_2020876 := by
    simpa [prefixWord, tailWord_2020876, baseEnd_2020876] using wordTrace_append hprefix tailTrace_2020876
  have hstable : (prefixWord ++ tailWord_2020876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020876).length < 2 ^ (prefixWord ++ tailWord_2020876).sum := by decide
  have hdescent : baseEnd_2020876 < baseStart_2020876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020906 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2020906 : Nat := 118140960795 + 2020906 * 2 ^ 59
def prefixEnd_2020906 : Nat := 4983230072969 + 3 ^ 40 * 2020906 * 2
def baseEnd_2020906 : Nat := 691797423703450286454019

theorem tailTrace_2020906 : CollatzResearch.WordTrace tailWord_2020906 prefixEnd_2020906 691797423703450286454019 := by
  unfold tailWord_2020906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427124304152545027912643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49138998144406786741100381 18427124304152545027912643)
  ·
    refine ⟨27640686456228817541868965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18427124304152545027912643 27640686456228817541868965)
    ·
      refine ⟨5182628710542903289100431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27640686456228817541868965 5182628710542903289100431)
      ·
        refine ⟨7773943065814354933650647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182628710542903289100431 7773943065814354933650647)
        ·
          refine ⟨11660914598721532400475971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773943065814354933650647 11660914598721532400475971)
          ·
            refine ⟨17491371898082298600713957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11660914598721532400475971 17491371898082298600713957)
            ·
              refine ⟨3279632230890430987633867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17491371898082298600713957 3279632230890430987633867)
              ·
                refine ⟨4919448346335646481450801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279632230890430987633867 4919448346335646481450801)
                ·
                  refine ⟨3689586259751734861088101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919448346335646481450801 3689586259751734861088101)
                  ·
                    refine ⟨691797423703450286454019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689586259751734861088101 691797423703450286454019)
                    ·
                      rfl

theorem cell22_2020906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2020906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020906 prefixEnd_2020906 := by exact prefixLift 2020906
  have htrace : WordTrace (prefixWord ++ tailWord_2020906) baseStart_2020906 baseEnd_2020906 := by
    simpa [prefixWord, tailWord_2020906, baseEnd_2020906] using wordTrace_append hprefix tailTrace_2020906
  have hstable : (prefixWord ++ tailWord_2020906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020906).length < 2 ^ (prefixWord ++ tailWord_2020906).sum := by decide
  have hdescent : baseEnd_2020906 < baseStart_2020906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020957 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2020957 : Nat := 118140960795 + 2020957 * 2 ^ 59
def prefixEnd_2020957 : Nat := 4983230072969 + 3 ^ 40 * 2020957 * 2
def baseEnd_2020957 : Nat := 691814882045703153428863

theorem tailTrace_2020957 : CollatzResearch.WordTrace tailWord_2020957 prefixEnd_2020957 691814882045703153428863 := by
  unfold tailWord_2020957
  simp only [CollatzResearch.WordTrace]
  refine ⟨73710357339425415821757125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49140238226283610547838083 73710357339425415821757125)
  ·
    refine ⟨13820692001142265466579461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73710357339425415821757125 13820692001142265466579461)
    ·
      refine ⟨2591379750214174774983649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13820692001142265466579461 2591379750214174774983649)
      ·
        refine ⟨1943534812660631081237737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2591379750214174774983649 1943534812660631081237737)
        ·
          refine ⟨1457651109495473310928303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1943534812660631081237737 1457651109495473310928303)
          ·
            refine ⟨2186476664243209966392455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457651109495473310928303 2186476664243209966392455)
            ·
              refine ⟨3279714996364814949588683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186476664243209966392455 3279714996364814949588683)
              ·
                refine ⟨4919572494547222424383025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279714996364814949588683 4919572494547222424383025)
                ·
                  refine ⟨3689679370910416818287269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4919572494547222424383025 3689679370910416818287269)
                  ·
                    refine ⟨691814882045703153428863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689679370910416818287269 691814882045703153428863)
                    ·
                      rfl

theorem cell22_2020957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2020957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020957 prefixEnd_2020957 := by exact prefixLift 2020957
  have htrace : WordTrace (prefixWord ++ tailWord_2020957) baseStart_2020957 baseEnd_2020957 := by
    simpa [prefixWord, tailWord_2020957, baseEnd_2020957] using wordTrace_append hprefix tailTrace_2020957
  have hstable : (prefixWord ++ tailWord_2020957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020957).length < 2 ^ (prefixWord ++ tailWord_2020957).sum := by decide
  have hdescent : baseEnd_2020957 < baseStart_2020957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020970 : List Nat := [3, 1, 3, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2020970 : Nat := 118140960795 + 2020970 * 2 ^ 59
def prefixEnd_2020970 : Nat := 4983230072969 + 3 ^ 40 * 2020970 * 2
def baseEnd_2020970 : Nat := 691819332211375452853823

theorem tailTrace_2020970 : CollatzResearch.WordTrace tailWord_2020970 prefixEnd_2020970 691819332211375452853823 := by
  unfold tailWord_2020970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427707872094579760495091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49140554325585546027986909 18427707872094579760495091)
  ·
    refine ⟨27641561808141869640742637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18427707872094579760495091 27641561808141869640742637)
    ·
      refine ⟨10365585678053201115278489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27641561808141869640742637 10365585678053201115278489)
      ·
        refine ⟨7774189258539900836458867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10365585678053201115278489 7774189258539900836458867)
        ·
          refine ⟨11661283887809851254688301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774189258539900836458867 11661283887809851254688301)
          ·
            refine ⟨4372981457928694220508113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11661283887809851254688301 4372981457928694220508113)
            ·
              refine ⟨3279736093446520665381085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372981457928694220508113 3279736093446520665381085)
              ·
                refine ⟨1229901035042445249517907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279736093446520665381085 1229901035042445249517907)
                ·
                  refine ⟨1844851552563667874276861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229901035042445249517907 1844851552563667874276861)
                  ·
                    refine ⟨691819332211375452853823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844851552563667874276861 691819332211375452853823)
                    ·
                      rfl

theorem cell22_2020970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2020970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020970 prefixEnd_2020970 := by exact prefixLift 2020970
  have htrace : WordTrace (prefixWord ++ tailWord_2020970) baseStart_2020970 baseEnd_2020970 := by
    simpa [prefixWord, tailWord_2020970, baseEnd_2020970] using wordTrace_append hprefix tailTrace_2020970
  have hstable : (prefixWord ++ tailWord_2020970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020970).length < 2 ^ (prefixWord ++ tailWord_2020970).sum := by decide
  have hdescent : baseEnd_2020970 < baseStart_2020970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2020981 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2020981 : Nat := 118140960795 + 2020981 * 2 ^ 59
def prefixEnd_2020981 : Nat := 4983230072969 + 3 ^ 40 * 2020981 * 2
def baseEnd_2020981 : Nat := 691823097736175090828789

theorem tailTrace_2020981 : CollatzResearch.WordTrace tailWord_2020981 prefixEnd_2020981 691823097736175090828789 := by
  unfold tailWord_2020981
  simp only [CollatzResearch.WordTrace]
  refine ⟨73711232691338467920630797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49140821794225645280420531 73711232691338467920630797)
  ·
    refine ⟨27641712259251925470236549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73711232691338467920630797 27641712259251925470236549)
    ·
      refine ⟨5182821048609736025669353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27641712259251925470236549 5182821048609736025669353)
      ·
        refine ⟨3887115786457302019252015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5182821048609736025669353 3887115786457302019252015)
        ·
          refine ⟨5830673679685953028878023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887115786457302019252015 5830673679685953028878023)
          ·
            refine ⟨8746010519528929543317035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5830673679685953028878023 8746010519528929543317035)
            ·
              refine ⟨13119015779293394314975553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746010519528929543317035 13119015779293394314975553)
              ·
                refine ⟨9839261834470045736231665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13119015779293394314975553 9839261834470045736231665)
                ·
                  refine ⟨7379446375852534302173749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9839261834470045736231665 7379446375852534302173749)
                  ·
                    refine ⟨691823097736175090828789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379446375852534302173749 691823097736175090828789)
                    ·
                      rfl

theorem cell22_2020981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2020981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2020981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2020981 prefixEnd_2020981 := by exact prefixLift 2020981
  have htrace : WordTrace (prefixWord ++ tailWord_2020981) baseStart_2020981 baseEnd_2020981 := by
    simpa [prefixWord, tailWord_2020981, baseEnd_2020981] using wordTrace_append hprefix tailTrace_2020981
  have hstable : (prefixWord ++ tailWord_2020981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2020981).length < 2 ^ (prefixWord ++ tailWord_2020981).sum := by decide
  have hdescent : baseEnd_2020981 < baseStart_2020981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2020981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021000 : List Nat := [2, 1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_2021000 : Nat := 118140960795 + 2021000 * 2 ^ 59
def prefixEnd_2021000 : Nat := 4983230072969 + 3 ^ 40 * 2021000 * 2
def baseEnd_2021000 : Nat := 230609867274821791534577

theorem tailTrace_2021000 : CollatzResearch.WordTrace tailWord_2021000 prefixEnd_2021000 230609867274821791534577 := by
  unfold tailWord_2021000
  simp only [CollatzResearch.WordTrace]
  refine ⟨36855962839134817082786227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49141283785513089443714969 36855962839134817082786227)
  ·
    refine ⟨55283944258702225624179341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36855962839134817082786227 55283944258702225624179341)
    ·
      refine ⟨20731479097013334609067253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55283944258702225624179341 20731479097013334609067253)
      ·
        refine ⟨1943576165345000119600055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20731479097013334609067253 1943576165345000119600055)
        ·
          refine ⟨2915364248017500179400083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943576165345000119600055 2915364248017500179400083)
          ·
            refine ⟨4373046372026250269100125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915364248017500179400083 4373046372026250269100125)
            ·
              refine ⟨1639892389509843850912547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4373046372026250269100125 1639892389509843850912547)
              ·
                refine ⟨2459838584264765776368821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639892389509843850912547 2459838584264765776368821)
                ·
                  refine ⟨230609867274821791534577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2459838584264765776368821 230609867274821791534577)
                  ·
                    rfl

theorem cell22_2021000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_2021000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021000 prefixEnd_2021000 := by exact prefixLift 2021000
  have htrace : WordTrace (prefixWord ++ tailWord_2021000) baseStart_2021000 baseEnd_2021000 := by
    simpa [prefixWord, tailWord_2021000, baseEnd_2021000] using wordTrace_append hprefix tailTrace_2021000
  have hstable : (prefixWord ++ tailWord_2021000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021000).length < 2 ^ (prefixWord ++ tailWord_2021000).sum := by decide
  have hdescent : baseEnd_2021000 < baseStart_2021000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021009 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_2021009 : Nat := 118140960795 + 2021009 * 2 ^ 59
def prefixEnd_2021009 : Nat := 4983230072969 + 3 ^ 40 * 2021009 * 2
def baseEnd_2021009 : Nat := 691832682708392351128703

theorem tailTrace_2021009 : CollatzResearch.WordTrace tailWord_2021009 prefixEnd_2021009 691832682708392351128703 := by
  unfold tailWord_2021009
  simp only [CollatzResearch.WordTrace]
  refine ⟨73712253935237028702650081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49141502623491352468433387 73712253935237028702650081)
  ·
    refine ⟨55284190451427771526987561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73712253935237028702650081 55284190451427771526987561)
    ·
      refine ⟨41463142838570828645240671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55284190451427771526987561 41463142838570828645240671)
      ·
        refine ⟨62194714257856242967861007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41463142838570828645240671 62194714257856242967861007)
        ·
          refine ⟨93292071386784364451791511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62194714257856242967861007 93292071386784364451791511)
          ·
            refine ⟨139938107080176546677687267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93292071386784364451791511 139938107080176546677687267)
            ·
              refine ⟨209907160620264820016530901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139938107080176546677687267 209907160620264820016530901)
              ·
                refine ⟨4919699077037456719137443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209907160620264820016530901 4919699077037456719137443)
                ·
                  refine ⟨7379548615556185078706165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4919699077037456719137443 7379548615556185078706165)
                  ·
                    refine ⟨691832682708392351128703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379548615556185078706165 691832682708392351128703)
                    ·
                      rfl

theorem cell22_2021009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_2021009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021009 prefixEnd_2021009 := by exact prefixLift 2021009
  have htrace : WordTrace (prefixWord ++ tailWord_2021009) baseStart_2021009 baseEnd_2021009 := by
    simpa [prefixWord, tailWord_2021009, baseEnd_2021009] using wordTrace_append hprefix tailTrace_2021009
  have hstable : (prefixWord ++ tailWord_2021009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021009).length < 2 ^ (prefixWord ++ tailWord_2021009).sum := by decide
  have hdescent : baseEnd_2021009 < baseStart_2021009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021028 : List Nat := [2, 3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_2021028 : Nat := 118140960795 + 2021028 * 2 ^ 59
def prefixEnd_2021028 : Nat := 4983230072969 + 3 ^ 40 * 2021028 * 2
def baseEnd_2021028 : Nat := 230613062265560878301215

theorem tailTrace_2021028 : CollatzResearch.WordTrace tailWord_2021028 prefixEnd_2021028 230613062265560878301215 := by
  unfold tailWord_2021028
  simp only [CollatzResearch.WordTrace]
  refine ⟨36856473461084097473795869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49141964614778796631727825 36856473461084097473795869)
  ·
    refine ⟨13821177547906536552673451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36856473461084097473795869 13821177547906536552673451)
    ·
      refine ⟨20731766321859804829010177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13821177547906536552673451 20731766321859804829010177)
      ·
        refine ⟨15548824741394853621757633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20731766321859804829010177 15548824741394853621757633)
        ·
          refine ⟨11661618556046140216318225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15548824741394853621757633 11661618556046140216318225)
          ·
            refine ⟨8746213917034605162238669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661618556046140216318225 8746213917034605162238669)
            ·
              refine ⟨3279830218887976935839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746213917034605162238669 3279830218887976935839501)
              ·
                refine ⟨1229936332082991350939813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279830218887976935839501 1229936332082991350939813)
                ·
                  refine ⟨230613062265560878301215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1229936332082991350939813 230613062265560878301215)
                  ·
                    rfl

theorem cell22_2021028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_2021028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021028 prefixEnd_2021028 := by exact prefixLift 2021028
  have htrace : WordTrace (prefixWord ++ tailWord_2021028) baseStart_2021028 baseEnd_2021028 := by
    simpa [prefixWord, tailWord_2021028, baseEnd_2021028] using wordTrace_append hprefix tailTrace_2021028
  have hstable : (prefixWord ++ tailWord_2021028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021028).length < 2 ^ (prefixWord ++ tailWord_2021028).sum := by decide
  have hdescent : baseEnd_2021028 < baseStart_2021028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021045 : List Nat := [1, 3, 3, 3, 3, 1, 1, 1, 6]
def baseStart_2021045 : Nat := 118140960795 + 2021045 * 2 ^ 59
def prefixEnd_2021045 : Nat := 4983230072969 + 3 ^ 40 * 2021045 * 2
def baseEnd_2021045 : Nat := 230615002081366752409531

theorem tailTrace_2021045 : CollatzResearch.WordTrace tailWord_2021045 prefixEnd_2021045 230615002081366752409531 := by
  unfold tailWord_2021045
  simp only [CollatzResearch.WordTrace]
  refine ⟨73713566963106606850960589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49142377975404404567307059 73713566963106606850960589)
  ·
    refine ⟨27642587611164977569110221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73713566963106606850960589 27642587611164977569110221)
    ·
      refine ⟨10365970354186866588416333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27642587611164977569110221 10365970354186866588416333)
      ·
        refine ⟨3887238882820074970656125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10365970354186866588416333 3887238882820074970656125)
        ·
          refine ⟨1457714581057528113996047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3887238882820074970656125 1457714581057528113996047)
          ·
            refine ⟨2186571871586292170994071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457714581057528113996047 2186571871586292170994071)
            ·
              refine ⟨3279857807379438256491107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186571871586292170994071 3279857807379438256491107)
              ·
                refine ⟨4919786711069157384736661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279857807379438256491107 4919786711069157384736661)
                ·
                  refine ⟨230615002081366752409531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4919786711069157384736661 230615002081366752409531)
                  ·
                    rfl

theorem cell22_2021045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_2021045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021045 prefixEnd_2021045 := by exact prefixLift 2021045
  have htrace : WordTrace (prefixWord ++ tailWord_2021045) baseStart_2021045 baseEnd_2021045 := by
    simpa [prefixWord, tailWord_2021045, baseEnd_2021045] using wordTrace_append hprefix tailTrace_2021045
  have hstable : (prefixWord ++ tailWord_2021045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021045).length < 2 ^ (prefixWord ++ tailWord_2021045).sum := by decide
  have hdescent : baseEnd_2021045 < baseStart_2021045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021071 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 3, 3]
def baseStart_2021071 : Nat := 118140960795 + 2021071 * 2 ^ 59
def prefixEnd_2021071 : Nat := 4983230072969 + 3 ^ 40 * 2021071 * 2
def baseEnd_2021071 : Nat := 691853906575444856078513

theorem tailTrace_2021071 : CollatzResearch.WordTrace tailWord_2021071 prefixEnd_2021071 691853906575444856078513 := by
  unfold tailWord_2021071
  simp only [CollatzResearch.WordTrace]
  refine ⟨73714515261012413291407067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49143010174008275527604711 73714515261012413291407067)
  ·
    refine ⟨110571772891518619937110601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73714515261012413291407067 110571772891518619937110601)
    ·
      refine ⟨82928829668638964952832951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110571772891518619937110601 82928829668638964952832951)
      ·
        refine ⟨124393244502958447429249427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82928829668638964952832951 124393244502958447429249427)
        ·
          refine ⟨186589866754437671143874141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124393244502958447429249427 186589866754437671143874141)
          ·
            refine ⟨69971200032914126678952803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186589866754437671143874141 69971200032914126678952803)
            ·
              refine ⟨104956800049371190018429205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69971200032914126678952803 104956800049371190018429205)
              ·
                refine ⟨4919850002314274532113869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104956800049371190018429205 4919850002314274532113869)
                ·
                  refine ⟨1844943750867852949542701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4919850002314274532113869 1844943750867852949542701)
                  ·
                    refine ⟨691853906575444856078513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844943750867852949542701 691853906575444856078513)
                    ·
                      rfl

theorem cell22_2021071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 3].length) (baseStart_2021071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021071 prefixEnd_2021071 := by exact prefixLift 2021071
  have htrace : WordTrace (prefixWord ++ tailWord_2021071) baseStart_2021071 baseEnd_2021071 := by
    simpa [prefixWord, tailWord_2021071, baseEnd_2021071] using wordTrace_append hprefix tailTrace_2021071
  have hstable : (prefixWord ++ tailWord_2021071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021071).length < 2 ^ (prefixWord ++ tailWord_2021071).sum := by decide
  have hdescent : baseEnd_2021071 < baseStart_2021071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021105 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 1, 3]
def baseStart_2021105 : Nat := 118140960795 + 2021105 * 2 ^ 59
def prefixEnd_2021105 : Nat := 4983230072969 + 3 ^ 40 * 2021105 * 2
def baseEnd_2021105 : Nat := 691865545470280100728409

theorem tailTrace_2021105 : CollatzResearch.WordTrace tailWord_2021105 prefixEnd_2021105 691865545470280100728409 := by
  unfold tailWord_2021105
  simp only [CollatzResearch.WordTrace]
  refine ⟨73715755342889237098144769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49143836895259491398763179 73715755342889237098144769)
  ·
    refine ⟨55286816507166927823608577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73715755342889237098144769 55286816507166927823608577)
    ·
      refine ⟨41465112380375195867706433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55286816507166927823608577 41465112380375195867706433)
      ·
        refine ⟨31098834285281396900779825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41465112380375195867706433 31098834285281396900779825)
        ·
          refine ⟨23324125713961047675584869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31098834285281396900779825 23324125713961047675584869)
          ·
            refine ⟨4373273571367696439172163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23324125713961047675584869 4373273571367696439172163)
            ·
              refine ⟨6559910357051544658758245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373273571367696439172163 6559910357051544658758245)
              ·
                refine ⟨1229983191947164623517171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6559910357051544658758245 1229983191947164623517171)
                ·
                  refine ⟨1844974787920746935275757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229983191947164623517171 1844974787920746935275757)
                  ·
                    refine ⟨691865545470280100728409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844974787920746935275757 691865545470280100728409)
                    ·
                      rfl

theorem cell22_2021105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_2021105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021105 prefixEnd_2021105 := by exact prefixLift 2021105
  have htrace : WordTrace (prefixWord ++ tailWord_2021105) baseStart_2021105 baseEnd_2021105 := by
    simpa [prefixWord, tailWord_2021105, baseEnd_2021105] using wordTrace_append hprefix tailTrace_2021105
  have hstable : (prefixWord ++ tailWord_2021105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021105).length < 2 ^ (prefixWord ++ tailWord_2021105).sum := by decide
  have hdescent : baseEnd_2021105 < baseStart_2021105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021116 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_2021116 : Nat := 118140960795 + 2021116 * 2 ^ 59
def prefixEnd_2021116 : Nat := 4983230072969 + 3 ^ 40 * 2021116 * 2
def baseEnd_2021116 : Nat := 691869310995079738703375

theorem tailTrace_2021116 : CollatzResearch.WordTrace tailWord_2021116 prefixEnd_2021116 691869310995079738703375 := by
  unfold tailWord_2021116
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858078272924692988397601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49144104363899590651196801 36858078272924692988397601)
  ·
    refine ⟨27643558704693519741298201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36858078272924692988397601 27643558704693519741298201)
    ·
      refine ⟨20732669028520139805973651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27643558704693519741298201 20732669028520139805973651)
      ·
        refine ⟨31099003542780209708960477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20732669028520139805973651 31099003542780209708960477)
        ·
          refine ⟨11662126328542578640860179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31099003542780209708960477 11662126328542578640860179)
          ·
            refine ⟨17493189492813867961290269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11662126328542578640860179 17493189492813867961290269)
            ·
              refine ⟨6559946059805200485483851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17493189492813867961290269 6559946059805200485483851)
              ·
                refine ⟨9839919089707800728225777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559946059805200485483851 9839919089707800728225777)
                ·
                  refine ⟨7379939317280850546169333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9839919089707800728225777 7379939317280850546169333)
                  ·
                    refine ⟨691869310995079738703375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7379939317280850546169333 691869310995079738703375)
                    ·
                      rfl

theorem cell22_2021116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_2021116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021116 prefixEnd_2021116 := by exact prefixLift 2021116
  have htrace : WordTrace (prefixWord ++ tailWord_2021116) baseStart_2021116 baseEnd_2021116 := by
    simpa [prefixWord, tailWord_2021116, baseEnd_2021116] using wordTrace_append hprefix tailTrace_2021116
  have hstable : (prefixWord ++ tailWord_2021116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021116).length < 2 ^ (prefixWord ++ tailWord_2021116).sum := by decide
  have hdescent : baseEnd_2021116 < baseStart_2021116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021131 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 3, 4]
def baseStart_2021131 : Nat := 118140960795 + 2021131 * 2 ^ 59
def prefixEnd_2021131 : Nat := 4983230072969 + 3 ^ 40 * 2021131 * 2
def baseEnd_2021131 : Nat := 691874445801624699578329

theorem tailTrace_2021131 : CollatzResearch.WordTrace tailWord_2021131 prefixEnd_2021131 691874445801624699578329 := by
  unfold tailWord_2021131
  simp only [CollatzResearch.WordTrace]
  refine ⟨73716703640795043538591247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49144469093863362359060831 73716703640795043538591247)
  ·
    refine ⟨110575055461192565307886871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73716703640795043538591247 110575055461192565307886871)
    ·
      refine ⟨165862583191788847961830307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110575055461192565307886871 165862583191788847961830307)
      ·
        refine ⟨248793874787683271942745461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165862583191788847961830307 248793874787683271942745461)
        ·
          refine ⟨23324425761345306744632387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248793874787683271942745461 23324425761345306744632387)
          ·
            refine ⟨34986638642017960116948581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23324425761345306744632387 34986638642017960116948581)
            ·
              refine ⟨6559994745378367521927859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34986638642017960116948581 6559994745378367521927859)
              ·
                refine ⟨9839992118067551282891789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559994745378367521927859 9839992118067551282891789)
                ·
                  refine ⟨3689997044275331731084421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9839992118067551282891789 3689997044275331731084421)
                  ·
                    refine ⟨691874445801624699578329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3689997044275331731084421 691874445801624699578329)
                    ·
                      rfl

theorem cell22_2021131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 4].length) (baseStart_2021131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021131 prefixEnd_2021131 := by exact prefixLift 2021131
  have htrace : WordTrace (prefixWord ++ tailWord_2021131) baseStart_2021131 baseEnd_2021131 := by
    simpa [prefixWord, tailWord_2021131, baseEnd_2021131] using wordTrace_append hprefix tailTrace_2021131
  have hstable : (prefixWord ++ tailWord_2021131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021131).length < 2 ^ (prefixWord ++ tailWord_2021131).sum := by decide
  have hdescent : baseEnd_2021131 < baseStart_2021131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021148 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2021148 : Nat := 118140960795 + 2021148 * 2 ^ 59
def prefixEnd_2021148 : Nat := 4983230072969 + 3 ^ 40 * 2021148 * 2
def baseEnd_2021148 : Nat := 691880265249042321903277

theorem tailTrace_2021148 : CollatzResearch.WordTrace tailWord_2021148 prefixEnd_2021148 691880265249042321903277 := by
  unfold tailWord_2021148
  simp only [CollatzResearch.WordTrace]
  refine ⟨36858661840866727720980049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49144882454488970294640065 36858661840866727720980049)
  ·
    refine ⟨27643996380650045790735037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36858661840866727720980049 27643996380650045790735037)
    ·
      refine ⟨10366498642743767171525639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27643996380650045790735037 10366498642743767171525639)
      ·
        refine ⟨15549747964115650757288459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10366498642743767171525639 15549747964115650757288459)
        ·
          refine ⟨23324621946173476135932689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15549747964115650757288459 23324621946173476135932689)
          ·
            refine ⟨17493466459630107101949517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23324621946173476135932689 17493466459630107101949517)
            ·
              refine ⟨6560049922361290163231069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17493466459630107101949517 6560049922361290163231069)
              ·
                refine ⟨2460018720885483811211651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6560049922361290163231069 2460018720885483811211651)
                ·
                  refine ⟨3690028081328225716817477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460018720885483811211651 3690028081328225716817477)
                  ·
                    refine ⟨691880265249042321903277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690028081328225716817477 691880265249042321903277)
                    ·
                      rfl

theorem cell22_2021148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2021148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021148 prefixEnd_2021148 := by exact prefixLift 2021148
  have htrace : WordTrace (prefixWord ++ tailWord_2021148) baseStart_2021148 baseEnd_2021148 := by
    simpa [prefixWord, tailWord_2021148, baseEnd_2021148] using wordTrace_append hprefix tailTrace_2021148
  have hstable : (prefixWord ++ tailWord_2021148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021148).length < 2 ^ (prefixWord ++ tailWord_2021148).sum := by decide
  have hdescent : baseEnd_2021148 < baseStart_2021148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021176 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 1, 6]
def baseStart_2021176 : Nat := 118140960795 + 2021176 * 2 ^ 59
def prefixEnd_2021176 : Nat := 4983230072969 + 3 ^ 40 * 2021176 * 2
def baseEnd_2021176 : Nat := 691889850221259582203191

theorem tailTrace_2021176 : CollatzResearch.WordTrace tailWord_2021176 prefixEnd_2021176 691889850221259582203191 := by
  unfold tailWord_2021176
  simp only [CollatzResearch.WordTrace]
  refine ⟨36859172462816008111989691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49145563283754677482652921 36859172462816008111989691)
  ·
    refine ⟨55288758694224012167984537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36859172462816008111989691 55288758694224012167984537)
    ·
      refine ⟨41466569020668009125988403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55288758694224012167984537 41466569020668009125988403)
      ·
        refine ⟨62199853531002013688982605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41466569020668009125988403 62199853531002013688982605)
        ·
          refine ⟨23324945074125755133368477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62199853531002013688982605 23324945074125755133368477)
          ·
            refine ⟨8746854402797158175013179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23324945074125755133368477 8746854402797158175013179)
            ·
              refine ⟨13120281604195737262519769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746854402797158175013179 13120281604195737262519769)
              ·
                refine ⟨9840211203146802946889827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13120281604195737262519769 9840211203146802946889827)
                ·
                  refine ⟨14760316804720204420334741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9840211203146802946889827 14760316804720204420334741)
                  ·
                    refine ⟨691889850221259582203191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14760316804720204420334741 691889850221259582203191)
                    ·
                      rfl

theorem cell22_2021176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_2021176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021176 prefixEnd_2021176 := by exact prefixLift 2021176
  have htrace : WordTrace (prefixWord ++ tailWord_2021176) baseStart_2021176 baseEnd_2021176 := by
    simpa [prefixWord, tailWord_2021176, baseEnd_2021176] using wordTrace_append hprefix tailTrace_2021176
  have hstable : (prefixWord ++ tailWord_2021176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021176).length < 2 ^ (prefixWord ++ tailWord_2021176).sum := by decide
  have hdescent : baseEnd_2021176 < baseStart_2021176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021178 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_2021178 : Nat := 118140960795 + 2021178 * 2 ^ 59
def prefixEnd_2021178 : Nat := 4983230072969 + 3 ^ 40 * 2021178 * 2
def baseEnd_2021178 : Nat := 691890534862132243653185

theorem tailTrace_2021178 : CollatzResearch.WordTrace tailWord_2021178 prefixEnd_2021178 691890534862132243653185 := by
  unfold tailWord_2021178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429604467906192641388047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49145611914416513710368125 18429604467906192641388047)
  ·
    refine ⟨27644406701859288962082071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18429604467906192641388047 27644406701859288962082071)
    ·
      refine ⟨41466610052788933443123107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27644406701859288962082071 41466610052788933443123107)
      ·
        refine ⟨62199915079183400164684661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41466610052788933443123107 62199915079183400164684661)
        ·
          refine ⟨5831242038673443765439187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62199915079183400164684661 5831242038673443765439187)
          ·
            refine ⟨8746863058010165648158781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831242038673443765439187 8746863058010165648158781)
            ·
              refine ⟨3280073646753812118059543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746863058010165648158781 3280073646753812118059543)
              ·
                refine ⟨4920110470130718177089315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280073646753812118059543 4920110470130718177089315)
                ·
                  refine ⟨7380165705196077265633973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920110470130718177089315 7380165705196077265633973)
                  ·
                    refine ⟨691890534862132243653185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7380165705196077265633973 691890534862132243653185)
                    ·
                      rfl

theorem cell22_2021178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_2021178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021178 prefixEnd_2021178 := by exact prefixLift 2021178
  have htrace : WordTrace (prefixWord ++ tailWord_2021178) baseStart_2021178 baseEnd_2021178 := by
    simpa [prefixWord, tailWord_2021178, baseEnd_2021178] using wordTrace_append hprefix tailTrace_2021178
  have hstable : (prefixWord ++ tailWord_2021178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021178).length < 2 ^ (prefixWord ++ tailWord_2021178).sum := by decide
  have hdescent : baseEnd_2021178 < baseStart_2021178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021197 : List Nat := [1, 6, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2021197 : Nat := 118140960795 + 2021197 * 2 ^ 59
def prefixEnd_2021197 : Nat := 4983230072969 + 3 ^ 40 * 2021197 * 2
def baseEnd_2021197 : Nat := 230632346316807509142709

theorem tailTrace_2021197 : CollatzResearch.WordTrace tailWord_2021197 prefixEnd_2021197 230632346316807509142709 := by
  unfold tailWord_2021197
  simp only [CollatzResearch.WordTrace]
  refine ⟨73719110858555936810493845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49146073905703957873662563 73719110858555936810493845)
  ·
    refine ⟨3455583321494809537991899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73719110858555936810493845 3455583321494809537991899)
    ·
      refine ⟨5183374982242214306987849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455583321494809537991899 5183374982242214306987849)
      ·
        refine ⟨3887531236681660730240887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5183374982242214306987849 3887531236681660730240887)
        ·
          refine ⟨5831296855022491095361331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3887531236681660730240887 5831296855022491095361331)
          ·
            refine ⟨8746945282533736643041997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831296855022491095361331 8746945282533736643041997)
            ·
              refine ⟨3280104480950151241140749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8746945282533736643041997 3280104480950151241140749)
              ·
                refine ⟨1230039180356306715427781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3280104480950151241140749 1230039180356306715427781)
                ·
                  refine ⟨230632346316807509142709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230039180356306715427781 230632346316807509142709)
                  ·
                    rfl

theorem cell22_2021197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2021197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021197 prefixEnd_2021197 := by exact prefixLift 2021197
  have htrace : WordTrace (prefixWord ++ tailWord_2021197) baseStart_2021197 baseEnd_2021197 := by
    simpa [prefixWord, tailWord_2021197, baseEnd_2021197] using wordTrace_append hprefix tailTrace_2021197
  have hstable : (prefixWord ++ tailWord_2021197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021197).length < 2 ^ (prefixWord ++ tailWord_2021197).sum := by decide
  have hdescent : baseEnd_2021197 < baseStart_2021197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021221 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_2021221 : Nat := 118140960795 + 2021221 * 2 ^ 59
def prefixEnd_2021221 : Nat := 4983230072969 + 3 ^ 40 * 2021221 * 2
def baseEnd_2021221 : Nat := 691905254640894464828053

theorem tailTrace_2021221 : CollatzResearch.WordTrace tailWord_2021221 prefixEnd_2021221 691905254640894464828053 := by
  unfold tailWord_2021221
  simp only [CollatzResearch.WordTrace]
  refine ⟨73719986210468988909367517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49146657473645992606245011 73719986210468988909367517)
  ·
    refine ⟨27644994828925870841012819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73719986210468988909367517 27644994828925870841012819)
    ·
      refine ⟨41467492243388806261519229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27644994828925870841012819 41467492243388806261519229)
      ·
        refine ⟨15550309591270802348069711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41467492243388806261519229 15550309591270802348069711)
        ·
          refine ⟨23325464386906203522104567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15550309591270802348069711 23325464386906203522104567)
          ·
            refine ⟨34988196580359305283156851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23325464386906203522104567 34988196580359305283156851)
            ·
              refine ⟨52482294870538957924735277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34988196580359305283156851 52482294870538957924735277)
              ·
                refine ⟨19680860576452109221775729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52482294870538957924735277 19680860576452109221775729)
                ·
                  refine ⟨14760645432339081916331797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19680860576452109221775729 14760645432339081916331797)
                  ·
                    refine ⟨691905254640894464828053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14760645432339081916331797 691905254640894464828053)
                    ·
                      rfl

theorem cell22_2021221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_2021221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021221 prefixEnd_2021221 := by exact prefixLift 2021221
  have htrace : WordTrace (prefixWord ++ tailWord_2021221) baseStart_2021221 baseEnd_2021221 := by
    simpa [prefixWord, tailWord_2021221, baseEnd_2021221] using wordTrace_append hprefix tailTrace_2021221
  have hstable : (prefixWord ++ tailWord_2021221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021221).length < 2 ^ (prefixWord ++ tailWord_2021221).sum := by decide
  have hdescent : baseEnd_2021221 < baseStart_2021221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021274 : List Nat := [3, 1, 1, 4, 2, 1, 4, 2, 1, 3]
def baseStart_2021274 : Nat := 118140960795 + 2021274 * 2 ^ 59
def prefixEnd_2021274 : Nat := 4983230072969 + 3 ^ 40 * 2021274 * 2
def baseEnd_2021274 : Nat := 691923397624019993252891

theorem tailTrace_2021274 : CollatzResearch.WordTrace tailWord_2021274 prefixEnd_2021274 691923397624019993252891 := by
  unfold tailWord_2021274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18430479819819244740261719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49147946186184652640697917 18430479819819244740261719)
  ·
    refine ⟨27645719729728867110392579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18430479819819244740261719 27645719729728867110392579)
    ·
      refine ⟨41468579594593300665588869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27645719729728867110392579 41468579594593300665588869)
      ·
        refine ⟨7775358673986243874797913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41468579594593300665588869 7775358673986243874797913)
        ·
          refine ⟨5831519005489682906098435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7775358673986243874797913 5831519005489682906098435)
          ·
            refine ⟨8747278508234524359147653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831519005489682906098435 8747278508234524359147653)
            ·
              refine ⟨1640114720293973317340185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8747278508234524359147653 1640114720293973317340185)
              ·
                refine ⟨1230086040220479988005139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640114720293973317340185 1230086040220479988005139)
                ·
                  refine ⟨1845129060330719982007709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230086040220479988005139 1845129060330719982007709)
                  ·
                    refine ⟨691923397624019993252891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845129060330719982007709 691923397624019993252891)
                    ·
                      rfl

theorem cell22_2021274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_2021274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021274 prefixEnd_2021274 := by exact prefixLift 2021274
  have htrace : WordTrace (prefixWord ++ tailWord_2021274) baseStart_2021274 baseEnd_2021274 := by
    simpa [prefixWord, tailWord_2021274, baseEnd_2021274] using wordTrace_append hprefix tailTrace_2021274
  have hstable : (prefixWord ++ tailWord_2021274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021274).length < 2 ^ (prefixWord ++ tailWord_2021274).sum := by decide
  have hdescent : baseEnd_2021274 < baseStart_2021274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021328 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 2, 4]
def baseStart_2021328 : Nat := 118140960795 + 2021328 * 2 ^ 59
def prefixEnd_2021328 : Nat := 4983230072969 + 3 ^ 40 * 2021328 * 2
def baseEnd_2021328 : Nat := 691941882927581852402725

theorem tailTrace_2021328 : CollatzResearch.WordTrace tailWord_2021328 prefixEnd_2021328 691941882927581852402725 := by
  unfold tailWord_2021328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36861944410540673091756319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49149259214054230789008425 36861944410540673091756319)
  ·
    refine ⟨55292916615811009637634479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36861944410540673091756319 55292916615811009637634479)
    ·
      refine ⟨82939374923716514456451719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55292916615811009637634479 82939374923716514456451719)
      ·
        refine ⟨124409062385574771684677579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82939374923716514456451719 124409062385574771684677579)
        ·
          refine ⟨186613593578362157527016369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124409062385574771684677579 186613593578362157527016369)
          ·
            refine ⟨139960195183771618145262277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186613593578362157527016369 139960195183771618145262277)
            ·
              refine ⟨26242536596957178402236677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139960195183771618145262277 26242536596957178402236677)
              ·
                refine ⟨4920475611929470950419377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26242536596957178402236677 4920475611929470950419377)
                ·
                  refine ⟨3690356708947103212814533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4920475611929470950419377 3690356708947103212814533)
                  ·
                    refine ⟨691941882927581852402725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690356708947103212814533 691941882927581852402725)
                    ·
                      rfl

theorem cell22_2021328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_2021328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021328 prefixEnd_2021328 := by exact prefixLift 2021328
  have htrace : WordTrace (prefixWord ++ tailWord_2021328) baseStart_2021328 baseEnd_2021328 := by
    simpa [prefixWord, tailWord_2021328, baseEnd_2021328] using wordTrace_append hprefix tailTrace_2021328
  have hstable : (prefixWord ++ tailWord_2021328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021328).length < 2 ^ (prefixWord ++ tailWord_2021328).sum := by decide
  have hdescent : baseEnd_2021328 < baseStart_2021328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021366 : List Nat := [5, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_2021366 : Nat := 118140960795 + 2021366 * 2 ^ 59
def prefixEnd_2021366 : Nat := 4983230072969 + 3 ^ 40 * 2021366 * 2
def baseEnd_2021366 : Nat := 230651630368054139984203

theorem tailTrace_2021366 : CollatzResearch.WordTrace tailWord_2021366 prefixEnd_2021366 230651630368054139984203 := by
  unfold tailWord_2021366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607829674683979917087247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49150183196629119115597301 4607829674683979917087247)
  ·
    refine ⟨6911744512025969875630871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607829674683979917087247 6911744512025969875630871)
    ·
      refine ⟨10367616768038954813446307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6911744512025969875630871 10367616768038954813446307)
      ·
        refine ⟨15551425152058432220169461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10367616768038954813446307 15551425152058432220169461)
        ·
          refine ⟨1457946108005478020640887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15551425152058432220169461 1457946108005478020640887)
          ·
            refine ⟨2186919162008217030961331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457946108005478020640887 2186919162008217030961331)
            ·
              refine ⟨3280378743012325546441997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186919162008217030961331 3280378743012325546441997)
              ·
                refine ⟨1230142028629622079915749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3280378743012325546441997 1230142028629622079915749)
                ·
                  refine ⟨230651630368054139984203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230142028629622079915749 230651630368054139984203)
                  ·
                    rfl

theorem cell22_2021366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_2021366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021366 prefixEnd_2021366 := by exact prefixLift 2021366
  have htrace : WordTrace (prefixWord ++ tailWord_2021366) baseStart_2021366 baseEnd_2021366 := by
    simpa [prefixWord, tailWord_2021366, baseEnd_2021366] using wordTrace_append hprefix tailTrace_2021366
  have hstable : (prefixWord ++ tailWord_2021366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021366).length < 2 ^ (prefixWord ++ tailWord_2021366).sum := by decide
  have hdescent : baseEnd_2021366 < baseStart_2021366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021388 : List Nat := [2, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_2021388 : Nat := 118140960795 + 2021388 * 2 ^ 59
def prefixEnd_2021388 : Nat := 4983230072969 + 3 ^ 40 * 2021388 * 2
def baseEnd_2021388 : Nat := 230654140717920565300847

theorem tailTrace_2021388 : CollatzResearch.WordTrace tailWord_2021388 prefixEnd_2021388 230654140717920565300847 := by
  unfold tailWord_2021388
  simp only [CollatzResearch.WordTrace]
  refine ⟨36863038600431988215348409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49150718133909317620464545 36863038600431988215348409)
  ·
    refine ⟨27647278950323991161511307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36863038600431988215348409 27647278950323991161511307)
    ·
      refine ⟨41470918425485986742266961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27647278950323991161511307 41470918425485986742266961)
      ·
        refine ⟨31103188819114490056700221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41470918425485986742266961 31103188819114490056700221)
        ·
          refine ⟨11663695807167933771262583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31103188819114490056700221 11663695807167933771262583)
          ·
            refine ⟨17495543710751900656893875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11663695807167933771262583 17495543710751900656893875)
            ·
              refine ⟨26243315566127850985340813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17495543710751900656893875 26243315566127850985340813)
              ·
                refine ⟨9841243337297944119502805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26243315566127850985340813 9841243337297944119502805)
                ·
                  refine ⟨230654140717920565300847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9841243337297944119502805 230654140717920565300847)
                  ·
                    rfl

theorem cell22_2021388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_2021388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021388 prefixEnd_2021388 := by exact prefixLift 2021388
  have htrace : WordTrace (prefixWord ++ tailWord_2021388) baseStart_2021388 baseEnd_2021388 := by
    simpa [prefixWord, tailWord_2021388, baseEnd_2021388] using wordTrace_append hprefix tailTrace_2021388
  have hstable : (prefixWord ++ tailWord_2021388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021388).length < 2 ^ (prefixWord ++ tailWord_2021388).sum := by decide
  have hdescent : baseEnd_2021388 < baseStart_2021388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021465 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_2021465 : Nat := 118140960795 + 2021465 * 2 ^ 59
def prefixEnd_2021465 : Nat := 4983230072969 + 3 ^ 40 * 2021465 * 2
def baseEnd_2021465 : Nat := 691988780827359161727305

theorem tailTrace_2021465 : CollatzResearch.WordTrace tailWord_2021465 prefixEnd_2021465 691988780827359161727305 := by
  unfold tailWord_2021465
  simp only [CollatzResearch.WordTrace]
  refine ⟨73728885621585018581249849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49152590414390012387499899 73728885621585018581249849)
  ·
    refine ⟨55296664216188763935937387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73728885621585018581249849 55296664216188763935937387)
    ·
      refine ⟨82944996324283145903906081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55296664216188763935937387 82944996324283145903906081)
      ·
        refine ⟨62208747243212359427929561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82944996324283145903906081 62208747243212359427929561)
        ·
          refine ⟨46656560432409269570947171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62208747243212359427929561 46656560432409269570947171)
          ·
            refine ⟨69984840648613904356420757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46656560432409269570947171 69984840648613904356420757)
            ·
              refine ⟨3280539405403776766707223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69984840648613904356420757 3280539405403776766707223)
              ·
                refine ⟨4920809108105665150060835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280539405403776766707223 4920809108105665150060835)
                ·
                  refine ⟨7381213662158497725091253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4920809108105665150060835 7381213662158497725091253)
                  ·
                    refine ⟨691988780827359161727305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7381213662158497725091253 691988780827359161727305)
                    ·
                      rfl

theorem cell22_2021465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_2021465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021465 prefixEnd_2021465 := by exact prefixLift 2021465
  have htrace : WordTrace (prefixWord ++ tailWord_2021465) baseStart_2021465 baseEnd_2021465 := by
    simpa [prefixWord, tailWord_2021465, baseEnd_2021465] using wordTrace_append hprefix tailTrace_2021465
  have hstable : (prefixWord ++ tailWord_2021465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021465).length < 2 ^ (prefixWord ++ tailWord_2021465).sum := by decide
  have hdescent : baseEnd_2021465 < baseStart_2021465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021561 : List Nat := [1, 2, 1, 4, 1, 2, 5, 2, 1, 3]
def baseStart_2021561 : Nat := 118140960795 + 2021561 * 2 ^ 59
def prefixEnd_2021561 : Nat := 4983230072969 + 3 ^ 40 * 2021561 * 2
def baseEnd_2021561 : Nat := 692021643589246911327011

theorem tailTrace_2021561 : CollatzResearch.WordTrace tailWord_2021561 prefixEnd_2021561 692021643589246911327011 := by
  unfold tailWord_2021561
  simp only [CollatzResearch.WordTrace]
  refine ⟨73732387029237226976744537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49154924686158151317829691 73732387029237226976744537)
  ·
    refine ⟨55299290271927920232558403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73732387029237226976744537 55299290271927920232558403)
    ·
      refine ⟨82948935407891880348837605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55299290271927920232558403 82948935407891880348837605)
      ·
        refine ⟨15552925388979727565407051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82948935407891880348837605 15552925388979727565407051)
        ·
          refine ⟨23329388083469591348110577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552925388979727565407051 23329388083469591348110577)
          ·
            refine ⟨17497041062602193511082933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23329388083469591348110577 17497041062602193511082933)
            ·
              refine ⟨1640347599618955641664025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17497041062602193511082933 1640347599618955641664025)
              ·
                refine ⟨1230260699714216731248019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640347599618955641664025 1230260699714216731248019)
                ·
                  refine ⟨1845391049571325096872029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230260699714216731248019 1845391049571325096872029)
                  ·
                    refine ⟨692021643589246911327011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845391049571325096872029 692021643589246911327011)
                    ·
                      rfl

theorem cell22_2021561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_2021561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021561 prefixEnd_2021561 := by exact prefixLift 2021561
  have htrace : WordTrace (prefixWord ++ tailWord_2021561) baseStart_2021561 baseEnd_2021561 := by
    simpa [prefixWord, tailWord_2021561, baseEnd_2021561] using wordTrace_append hprefix tailTrace_2021561
  have hstable : (prefixWord ++ tailWord_2021561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021561).length < 2 ^ (prefixWord ++ tailWord_2021561).sum := by decide
  have hdescent : baseEnd_2021561 < baseStart_2021561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021585 : List Nat := [1, 2, 2, 1, 2, 2, 2, 4, 6]
def baseStart_2021585 : Nat := 118140960795 + 2021585 * 2 ^ 59
def prefixEnd_2021585 : Nat := 4983230072969 + 3 ^ 40 * 2021585 * 2
def baseEnd_2021585 : Nat := 230676619759906282908979

theorem tailTrace_2021585 : CollatzResearch.WordTrace tailWord_2021585 prefixEnd_2021585 230676619759906282908979 := by
  unfold tailWord_2021585
  simp only [CollatzResearch.WordTrace]
  refine ⟨73733262381150279075618209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49155508254100186050412139 73733262381150279075618209)
  ·
    refine ⟨55299946785862709306713657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73733262381150279075618209 55299946785862709306713657)
    ·
      refine ⟨41474960089397031980035243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55299946785862709306713657 41474960089397031980035243)
      ·
        refine ⟨62212440134095547970052865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41474960089397031980035243 62212440134095547970052865)
        ·
          refine ⟨46659330100571660977539649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62212440134095547970052865 46659330100571660977539649)
          ·
            refine ⟨34994497575428745733154737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46659330100571660977539649 34994497575428745733154737)
            ·
              refine ⟨26245873181571559299866053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34994497575428745733154737 26245873181571559299866053)
              ·
                refine ⟨4921101221544667368724885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26245873181571559299866053 4921101221544667368724885)
                ·
                  refine ⟨230676619759906282908979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4921101221544667368724885 230676619759906282908979)
                  ·
                    rfl

theorem cell22_2021585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_2021585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021585 prefixEnd_2021585 := by exact prefixLift 2021585
  have htrace : WordTrace (prefixWord ++ tailWord_2021585) baseStart_2021585 baseEnd_2021585 := by
    simpa [prefixWord, tailWord_2021585, baseEnd_2021585] using wordTrace_append hprefix tailTrace_2021585
  have hstable : (prefixWord ++ tailWord_2021585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021585).length < 2 ^ (prefixWord ++ tailWord_2021585).sum := by decide
  have hdescent : baseEnd_2021585 < baseStart_2021585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021617 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_2021617 : Nat := 118140960795 + 2021617 * 2 ^ 59
def prefixEnd_2021617 : Nat := 4983230072969 + 3 ^ 40 * 2021617 * 2
def baseEnd_2021617 : Nat := 692040813533681431926839

theorem tailTrace_2021617 : CollatzResearch.WordTrace tailWord_2021617 prefixEnd_2021617 692040813533681431926839 := by
  unfold tailWord_2021617
  simp only [CollatzResearch.WordTrace]
  refine ⟨73734429517034348540783105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49156286344689565693855403 73734429517034348540783105)
  ·
    refine ⟨55300822137775761405587329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73734429517034348540783105 55300822137775761405587329)
    ·
      refine ⟨41475616603331821054190497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55300822137775761405587329 41475616603331821054190497)
      ·
        refine ⟨31106712452498865790642873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41475616603331821054190497 31106712452498865790642873)
        ·
          refine ⟨23330034339374149342982155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31106712452498865790642873 23330034339374149342982155)
          ·
            refine ⟨34995051509061224014473233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23330034339374149342982155 34995051509061224014473233)
            ·
              refine ⟨26246288631795918010854925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34995051509061224014473233 26246288631795918010854925)
              ·
                refine ⟨9842358236923469254070597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26246288631795918010854925 9842358236923469254070597)
                ·
                  refine ⟨1845442169423150485138237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9842358236923469254070597 1845442169423150485138237)
                  ·
                    refine ⟨692040813533681431926839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845442169423150485138237 692040813533681431926839)
                    ·
                      rfl

theorem cell22_2021617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_2021617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021617 prefixEnd_2021617 := by exact prefixLift 2021617
  have htrace : WordTrace (prefixWord ++ tailWord_2021617) baseStart_2021617 baseEnd_2021617 := by
    simpa [prefixWord, tailWord_2021617, baseEnd_2021617] using wordTrace_append hprefix tailTrace_2021617
  have hstable : (prefixWord ++ tailWord_2021617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021617).length < 2 ^ (prefixWord ++ tailWord_2021617).sum := by decide
  have hdescent : baseEnd_2021617 < baseStart_2021617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021634 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_2021634 : Nat := 118140960795 + 2021634 * 2 ^ 59
def prefixEnd_2021634 : Nat := 4983230072969 + 3 ^ 40 * 2021634 * 2
def baseEnd_2021634 : Nat := 692046632981099054251787

theorem tailTrace_2021634 : CollatzResearch.WordTrace tailWord_2021634 prefixEnd_2021634 692046632981099054251787 := by
  unfold tailWord_2021634
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433762389493190111037989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49156699705315173629434637 18433762389493190111037989)
  ·
    refine ⟨3456330448029973145819623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18433762389493190111037989 3456330448029973145819623)
    ·
      refine ⟨5184495672044959718729435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3456330448029973145819623 5184495672044959718729435)
      ·
        refine ⟨7776743508067439578094153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184495672044959718729435 7776743508067439578094153)
        ·
          refine ⟨5832557631050579683570615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7776743508067439578094153 5832557631050579683570615)
          ·
            refine ⟨8748836446575869525355923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832557631050579683570615 8748836446575869525355923)
            ·
              refine ⟨13123254669863804288033885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8748836446575869525355923 13123254669863804288033885)
              ·
                refine ⟨4921220501198926608012707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13123254669863804288033885 4921220501198926608012707)
                ·
                  refine ⟨7381830751798389912019061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921220501198926608012707 7381830751798389912019061)
                  ·
                    refine ⟨692046632981099054251787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7381830751798389912019061 692046632981099054251787)
                    ·
                      rfl

theorem cell22_2021634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_2021634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021634 prefixEnd_2021634 := by exact prefixLift 2021634
  have htrace : WordTrace (prefixWord ++ tailWord_2021634) baseStart_2021634 baseEnd_2021634 := by
    simpa [prefixWord, tailWord_2021634, baseEnd_2021634] using wordTrace_append hprefix tailTrace_2021634
  have hstable : (prefixWord ++ tailWord_2021634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021634).length < 2 ^ (prefixWord ++ tailWord_2021634).sum := by decide
  have hdescent : baseEnd_2021634 < baseStart_2021634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021649 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_2021649 : Nat := 118140960795 + 2021649 * 2 ^ 59
def prefixEnd_2021649 : Nat := 4983230072969 + 3 ^ 40 * 2021649 * 2
def baseEnd_2021649 : Nat := 692051767787644015126741

theorem tailTrace_2021649 : CollatzResearch.WordTrace tailWord_2021649 prefixEnd_2021649 692051767787644015126741 := by
  unfold tailWord_2021649
  simp only [CollatzResearch.WordTrace]
  refine ⟨73735596652918418005948001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49157064435278945337298667 73735596652918418005948001)
  ·
    refine ⟨55301697489688813504461001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73735596652918418005948001 55301697489688813504461001)
    ·
      refine ⟨41476273117266610128345751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55301697489688813504461001 41476273117266610128345751)
      ·
        refine ⟨62214409675899915192518627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41476273117266610128345751 62214409675899915192518627)
        ·
          refine ⟨93321614513849872788777941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62214409675899915192518627 93321614513849872788777941)
          ·
            refine ⟨2187225340168356393486983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 93321614513849872788777941 2187225340168356393486983)
            ·
              refine ⟨3280838010252534590230475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187225340168356393486983 3280838010252534590230475)
              ·
                refine ⟨4921257015378801885345713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3280838010252534590230475 4921257015378801885345713)
                ·
                  refine ⟨3690942761534101414009285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4921257015378801885345713 3690942761534101414009285)
                  ·
                    refine ⟨692051767787644015126741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3690942761534101414009285 692051767787644015126741)
                    ·
                      rfl

theorem cell22_2021649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_2021649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021649 prefixEnd_2021649 := by exact prefixLift 2021649
  have htrace : WordTrace (prefixWord ++ tailWord_2021649) baseStart_2021649 baseEnd_2021649 := by
    simpa [prefixWord, tailWord_2021649, baseEnd_2021649] using wordTrace_append hprefix tailTrace_2021649
  have hstable : (prefixWord ++ tailWord_2021649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021649).length < 2 ^ (prefixWord ++ tailWord_2021649).sum := by decide
  have hdescent : baseEnd_2021649 < baseStart_2021649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021713 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 1, 3]
def baseStart_2021713 : Nat := 118140960795 + 2021713 * 2 ^ 59
def prefixEnd_2021713 : Nat := 4983230072969 + 3 ^ 40 * 2021713 * 2
def baseEnd_2021713 : Nat := 692073676295569181526545

theorem tailTrace_2021713 : CollatzResearch.WordTrace tailWord_2021713 prefixEnd_2021713 692073676295569181526545 := by
  unfold tailWord_2021713
  simp only [CollatzResearch.WordTrace]
  refine ⟨73737930924686556936277793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49158620616457704624185195 73737930924686556936277793)
  ·
    refine ⟨55303448193514917702208345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73737930924686556936277793 55303448193514917702208345)
    ·
      refine ⟨41477586145136188276656259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55303448193514917702208345 41477586145136188276656259)
      ·
        refine ⟨62216379217704282414984389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41477586145136188276656259 62216379217704282414984389)
        ·
          refine ⟨11665571103319552952809573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62216379217704282414984389 11665571103319552952809573)
          ·
            refine ⟨2187294581872416178651795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11665571103319552952809573 2187294581872416178651795)
            ·
              refine ⟨3280941872808624267977693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187294581872416178651795 3280941872808624267977693)
              ·
                refine ⟨1230353202303234100491635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3280941872808624267977693 1230353202303234100491635)
                ·
                  refine ⟨1845529803454851150737453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230353202303234100491635 1845529803454851150737453)
                  ·
                    refine ⟨692073676295569181526545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845529803454851150737453 692073676295569181526545)
                    ·
                      rfl

theorem cell22_2021713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_2021713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021713 prefixEnd_2021713 := by exact prefixLift 2021713
  have htrace : WordTrace (prefixWord ++ tailWord_2021713) baseStart_2021713 baseEnd_2021713 := by
    simpa [prefixWord, tailWord_2021713, baseEnd_2021713] using wordTrace_append hprefix tailTrace_2021713
  have hstable : (prefixWord ++ tailWord_2021713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021713).length < 2 ^ (prefixWord ++ tailWord_2021713).sum := by decide
  have hdescent : baseEnd_2021713 < baseStart_2021713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021722 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_2021722 : Nat := 118140960795 + 2021722 * 2 ^ 59
def prefixEnd_2021722 : Nat := 4983230072969 + 3 ^ 40 * 2021722 * 2
def baseEnd_2021722 : Nat := 692076757179496158051517

theorem tailTrace_2021722 : CollatzResearch.WordTrace tailWord_2021722 prefixEnd_2021722 692076757179496158051517 := by
  unfold tailWord_2021722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434564795413487868338855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49158839454435967648903613 18434564795413487868338855)
  ·
    refine ⟨27651847193120231802508283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18434564795413487868338855 27651847193120231802508283)
    ·
      refine ⟨41477770789680347703762425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27651847193120231802508283 41477770789680347703762425)
      ·
        refine ⟨31108328092260260777821819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41477770789680347703762425 31108328092260260777821819)
        ·
          refine ⟨46662492138390391166732729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31108328092260260777821819 46662492138390391166732729)
          ·
            refine ⟨34996869103792793375049547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46662492138390391166732729 34996869103792793375049547)
            ·
              refine ⟨52495303655689190062574321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34996869103792793375049547 52495303655689190062574321)
              ·
                refine ⟨39371477741766892546930741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52495303655689190062574321 39371477741766892546930741)
                ·
                  refine ⟨3691076038290646176274757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39371477741766892546930741 3691076038290646176274757)
                  ·
                    refine ⟨692076757179496158051517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3691076038290646176274757 692076757179496158051517)
                    ·
                      rfl

theorem cell22_2021722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_2021722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021722 prefixEnd_2021722 := by exact prefixLift 2021722
  have htrace : WordTrace (prefixWord ++ tailWord_2021722) baseStart_2021722 baseEnd_2021722 := by
    simpa [prefixWord, tailWord_2021722, baseEnd_2021722] using wordTrace_append hprefix tailTrace_2021722
  have hstable : (prefixWord ++ tailWord_2021722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021722).length < 2 ^ (prefixWord ++ tailWord_2021722).sum := by decide
  have hdescent : baseEnd_2021722 < baseStart_2021722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021730 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_2021730 : Nat := 118140960795 + 2021730 * 2 ^ 59
def prefixEnd_2021730 : Nat := 4983230072969 + 3 ^ 40 * 2021730 * 2
def baseEnd_2021730 : Nat := 692079495742986803851493

theorem tailTrace_2021730 : CollatzResearch.WordTrace tailWord_2021730 prefixEnd_2021730 692079495742986803851493 := by
  unfold tailWord_2021730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434637741406242209911661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49159033977083312559764429 18434637741406242209911661)
  ·
    refine ⟨6912989153027340828716873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18434637741406242209911661 6912989153027340828716873)
    ·
      refine ⟨5184741864770505621537655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6912989153027340828716873 5184741864770505621537655)
      ·
        refine ⟨7777112797155758432306483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184741864770505621537655 7777112797155758432306483)
        ·
          refine ⟨11665669195733637648459725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777112797155758432306483 11665669195733637648459725)
          ·
            refine ⟨4374625948400114118172397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11665669195733637648459725 4374625948400114118172397)
            ·
              refine ⟨1640484730650042794314649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4374625948400114118172397 1640484730650042794314649)
              ·
                refine ⟨1230363547987532095735987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640484730650042794314649 1230363547987532095735987)
                ·
                  refine ⟨1845545321981298143603981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230363547987532095735987 1845545321981298143603981)
                  ·
                    refine ⟨692079495742986803851493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845545321981298143603981 692079495742986803851493)
                    ·
                      rfl

theorem cell22_2021730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_2021730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021730 prefixEnd_2021730 := by exact prefixLift 2021730
  have htrace : WordTrace (prefixWord ++ tailWord_2021730) baseStart_2021730 baseEnd_2021730 := by
    simpa [prefixWord, tailWord_2021730, baseEnd_2021730] using wordTrace_append hprefix tailTrace_2021730
  have hstable : (prefixWord ++ tailWord_2021730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021730).length < 2 ^ (prefixWord ++ tailWord_2021730).sum := by decide
  have hdescent : baseEnd_2021730 < baseStart_2021730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021769 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_2021769 : Nat := 118140960795 + 2021769 * 2 ^ 59
def prefixEnd_2021769 : Nat := 4983230072969 + 3 ^ 40 * 2021769 * 2
def baseEnd_2021769 : Nat := 692092846240003702126373

theorem tailTrace_2021769 : CollatzResearch.WordTrace tailWord_2021769 prefixEnd_2021769 692092846240003702126373 := by
  unfold tailWord_2021769
  simp only [CollatzResearch.WordTrace]
  refine ⟨73739973412483678500316361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49159982274989119000210907 73739973412483678500316361)
  ·
    refine ⟨55304980059362758875237271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73739973412483678500316361 55304980059362758875237271)
    ·
      refine ⟨82957470089044138312855907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55304980059362758875237271 82957470089044138312855907)
      ·
        refine ⟨124436205133566207469283861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82957470089044138312855907 124436205133566207469283861)
        ·
          refine ⟨5832947115635915975122681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 124436205133566207469283861 5832947115635915975122681)
          ·
            refine ⟨4374710336726936981342011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5832947115635915975122681 4374710336726936981342011)
            ·
              refine ⟨6562065505090405472013017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374710336726936981342011 6562065505090405472013017)
              ·
                refine ⟨4921549128817804104009763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6562065505090405472013017 4921549128817804104009763)
                ·
                  refine ⟨7382323693226706156014645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4921549128817804104009763 7382323693226706156014645)
                  ·
                    refine ⟨692092846240003702126373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7382323693226706156014645 692092846240003702126373)
                    ·
                      rfl

theorem cell22_2021769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_2021769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021769 prefixEnd_2021769 := by exact prefixLift 2021769
  have htrace : WordTrace (prefixWord ++ tailWord_2021769) baseStart_2021769 baseEnd_2021769 := by
    simpa [prefixWord, tailWord_2021769, baseEnd_2021769] using wordTrace_append hprefix tailTrace_2021769
  have hstable : (prefixWord ++ tailWord_2021769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021769).length < 2 ^ (prefixWord ++ tailWord_2021769).sum := by decide
  have hdescent : baseEnd_2021769 < baseStart_2021769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021786 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_2021786 : Nat := 118140960795 + 2021786 * 2 ^ 59
def prefixEnd_2021786 : Nat := 4983230072969 + 3 ^ 40 * 2021786 * 2
def baseEnd_2021786 : Nat := 692098665687421324451321

theorem tailTrace_2021786 : CollatzResearch.WordTrace tailWord_2021786 prefixEnd_2021786 692098665687421324451321 := by
  unfold tailWord_2021786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18435148363355522600921303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49160395635614726935790141 18435148363355522600921303)
  ·
    refine ⟨27652722545033283901381955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18435148363355522600921303 27652722545033283901381955)
    ·
      refine ⟨41479083817549925852072933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27652722545033283901381955 41479083817549925852072933)
      ·
        refine ⟨7777328215790611097263675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41479083817549925852072933 7777328215790611097263675)
        ·
          refine ⟨11665992323685916645895513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777328215790611097263675 11665992323685916645895513)
          ·
            refine ⟨8749494242764437484421635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11665992323685916645895513 8749494242764437484421635)
            ·
              refine ⟨13124241364146656226632453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8749494242764437484421635 13124241364146656226632453)
              ·
                refine ⟨2460795255777498042493585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13124241364146656226632453 2460795255777498042493585)
                ·
                  refine ⟨1845596441833123531870189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460795255777498042493585 1845596441833123531870189)
                  ·
                    refine ⟨692098665687421324451321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845596441833123531870189 692098665687421324451321)
                    ·
                      rfl

theorem cell22_2021786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_2021786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021786 prefixEnd_2021786 := by exact prefixLift 2021786
  have htrace : WordTrace (prefixWord ++ tailWord_2021786) baseStart_2021786 baseEnd_2021786 := by
    simpa [prefixWord, tailWord_2021786, baseEnd_2021786] using wordTrace_append hprefix tailTrace_2021786
  have hstable : (prefixWord ++ tailWord_2021786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021786).length < 2 ^ (prefixWord ++ tailWord_2021786).sum := by decide
  have hdescent : baseEnd_2021786 < baseStart_2021786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021799 : List Nat := [1, 1, 6, 1, 1, 2, 3, 7]
def baseStart_2021799 : Nat := 118140960795 + 2021799 * 2 ^ 59
def prefixEnd_2021799 : Nat := 4983230072969 + 3 ^ 40 * 2021799 * 2
def baseEnd_2021799 : Nat := 76900346205899291541809

theorem tailTrace_2021799 : CollatzResearch.WordTrace tailWord_2021799 prefixEnd_2021799 76900346205899291541809 := by
  unfold tailWord_2021799
  simp only [CollatzResearch.WordTrace]
  refine ⟨73741067602374993623908451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49160711734916662415938967 73741067602374993623908451)
  ·
    refine ⟨110611601403562490435862677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73741067602374993623908451 110611601403562490435862677)
    ·
      refine ⟨5184918815791991739181063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110611601403562490435862677 5184918815791991739181063)
      ·
        refine ⟨7777378223687987608771595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184918815791991739181063 7777378223687987608771595)
        ·
          refine ⟨11666067335531981413157393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777378223687987608771595 11666067335531981413157393)
          ·
            refine ⟨8749550501648986059868045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11666067335531981413157393 8749550501648986059868045)
            ·
              refine ⟨3281081438118369772450517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8749550501648986059868045 3281081438118369772450517)
              ·
                refine ⟨76900346205899291541809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3281081438118369772450517 76900346205899291541809)
                ·
                  rfl

theorem cell22_2021799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 7].length) (baseStart_2021799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021799 prefixEnd_2021799 := by exact prefixLift 2021799
  have htrace : WordTrace (prefixWord ++ tailWord_2021799) baseStart_2021799 baseEnd_2021799 := by
    simpa [prefixWord, tailWord_2021799, baseEnd_2021799] using wordTrace_append hprefix tailTrace_2021799
  have hstable : (prefixWord ++ tailWord_2021799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021799).length < 2 ^ (prefixWord ++ tailWord_2021799).sum := by decide
  have hdescent : baseEnd_2021799 < baseStart_2021799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021827 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 7]
def baseStart_2021827 : Nat := 118140960795 + 2021827 * 2 ^ 59
def prefixEnd_2021827 : Nat := 4983230072969 + 3 ^ 40 * 2021827 * 2
def baseEnd_2021827 : Nat := 230704233608436961392065

theorem tailTrace_2021827 : CollatzResearch.WordTrace tailWord_2021827 prefixEnd_2021827 230704233608436961392065 := by
  unfold tailWord_2021827
  simp only [CollatzResearch.WordTrace]
  refine ⟨73742088846273554405927735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49161392564182369603951823 73742088846273554405927735)
  ·
    refine ⟨110613133269410331608891603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73742088846273554405927735 110613133269410331608891603)
    ·
      refine ⟨165919699904115497413337405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110613133269410331608891603 165919699904115497413337405)
      ·
        refine ⟨62219887464043311530001527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165919699904115497413337405 62219887464043311530001527)
        ·
          refine ⟨93329831196064967295002291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62219887464043311530001527 93329831196064967295002291)
          ·
            refine ⟨139994746794097450942503437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93329831196064967295002291 139994746794097450942503437)
            ·
              refine ⟨52498030047786544103438789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139994746794097450942503437 52498030047786544103438789)
              ·
                refine ⟨9843380633959977019394773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52498030047786544103438789 9843380633959977019394773)
                ·
                  refine ⟨230704233608436961392065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9843380633959977019394773 230704233608436961392065)
                  ·
                    rfl

theorem cell22_2021827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 7].length) (baseStart_2021827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021827 prefixEnd_2021827 := by exact prefixLift 2021827
  have htrace : WordTrace (prefixWord ++ tailWord_2021827) baseStart_2021827 baseEnd_2021827 := by
    simpa [prefixWord, tailWord_2021827, baseEnd_2021827] using wordTrace_append hprefix tailTrace_2021827
  have hstable : (prefixWord ++ tailWord_2021827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021827).length < 2 ^ (prefixWord ++ tailWord_2021827).sum := by decide
  have hdescent : baseEnd_2021827 < baseStart_2021827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021919 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 6, 4]
def baseStart_2021919 : Nat := 118140960795 + 2021919 * 2 ^ 59
def prefixEnd_2021919 : Nat := 4983230072969 + 3 ^ 40 * 2021919 * 2
def baseEnd_2021919 : Nat := 692144194305453310875913

theorem tailTrace_2021919 : CollatzResearch.WordTrace tailWord_2021919 prefixEnd_2021919 692144194305453310875913 := by
  unfold tailWord_2021919
  simp only [CollatzResearch.WordTrace]
  refine ⟨73745444361940254118276811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49163629574626836078851207 73745444361940254118276811)
  ·
    refine ⟨110618166542910381177415217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73745444361940254118276811 110618166542910381177415217)
    ·
      refine ⟨82963624907182785883061413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110618166542910381177415217 82963624907182785883061413)
      ·
        refine ⟨15555679670096772353074015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82963624907182785883061413 15555679670096772353074015)
        ·
          refine ⟨23333519505145158529611023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15555679670096772353074015 23333519505145158529611023)
          ·
            refine ⟨35000279257717737794416535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23333519505145158529611023 35000279257717737794416535)
            ·
              refine ⟨52500418886576606691624803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35000279257717737794416535 52500418886576606691624803)
              ·
                refine ⟨78750628329864910037437205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52500418886576606691624803 78750628329864910037437205)
                ·
                  refine ⟨3691435702962417658004869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78750628329864910037437205 3691435702962417658004869)
                  ·
                    refine ⟨692144194305453310875913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3691435702962417658004869 692144194305453310875913)
                    ·
                      rfl

theorem cell22_2021919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_2021919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021919 prefixEnd_2021919 := by exact prefixLift 2021919
  have htrace : WordTrace (prefixWord ++ tailWord_2021919) baseStart_2021919 baseEnd_2021919 := by
    simpa [prefixWord, tailWord_2021919, baseEnd_2021919] using wordTrace_append hprefix tailTrace_2021919
  have hstable : (prefixWord ++ tailWord_2021919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021919).length < 2 ^ (prefixWord ++ tailWord_2021919).sum := by decide
  have hdescent : baseEnd_2021919 < baseStart_2021919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2021964 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_2021964 : Nat := 118140960795 + 2021964 * 2 ^ 59
def prefixEnd_2021964 : Nat := 4983230072969 + 3 ^ 40 * 2021964 * 2
def baseEnd_2021964 : Nat := 692159598725088193500775

theorem tailTrace_2021964 : CollatzResearch.WordTrace tailWord_2021964 prefixEnd_2021964 692159598725088193500775 := by
  unfold tailWord_2021964
  simp only [CollatzResearch.WordTrace]
  refine ⟨36873542823388613401832473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49164723764518151202443297 36873542823388613401832473)
  ·
    refine ⟨27655157117541460051374355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36873542823388613401832473 27655157117541460051374355)
    ·
      refine ⟨41482735676312190077061533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27655157117541460051374355 41482735676312190077061533)
      ·
        refine ⟨15556025878617071278898075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41482735676312190077061533 15556025878617071278898075)
        ·
          refine ⟨23334038817925606918347113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556025878617071278898075 23334038817925606918347113)
          ·
            refine ⟨17500529113444205188760335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23334038817925606918347113 17500529113444205188760335)
            ·
              refine ⟨26250793670166307783140503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17500529113444205188760335 26250793670166307783140503)
              ·
                refine ⟨39376190505249461674710755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26250793670166307783140503 39376190505249461674710755)
                ·
                  refine ⟨59064285757874192512066133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39376190505249461674710755 59064285757874192512066133)
                  ·
                    refine ⟨692159598725088193500775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59064285757874192512066133 692159598725088193500775)
                    ·
                      rfl

theorem cell22_2021964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_2021964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2021964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2021964 prefixEnd_2021964 := by exact prefixLift 2021964
  have htrace : WordTrace (prefixWord ++ tailWord_2021964) baseStart_2021964 baseEnd_2021964 := by
    simpa [prefixWord, tailWord_2021964, baseEnd_2021964] using wordTrace_append hprefix tailTrace_2021964
  have hstable : (prefixWord ++ tailWord_2021964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2021964).length < 2 ^ (prefixWord ++ tailWord_2021964).sum := by decide
  have hdescent : baseEnd_2021964 < baseStart_2021964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2021964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022073 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_2022073 : Nat := 118140960795 + 2022073 * 2 ^ 59
def prefixEnd_2022073 : Nat := 4983230072969 + 3 ^ 40 * 2022073 * 2
def baseEnd_2022073 : Nat := 692196911652648242525441

theorem tailTrace_2022073 : CollatzResearch.WordTrace tailWord_2022073 prefixEnd_2022073 692196911652648242525441 := by
  unfold tailWord_2022073
  simp only [CollatzResearch.WordTrace]
  refine ⟨73751061203382338419382873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49167374135588225612921915 73751061203382338419382873)
  ·
    refine ⟨55313295902536753814537155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73751061203382338419382873 55313295902536753814537155)
    ·
      refine ⟨82969943853805130721805733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55313295902536753814537155 82969943853805130721805733)
      ·
        refine ⟨15556864472588462010338575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82969943853805130721805733 15556864472588462010338575)
        ·
          refine ⟨23335296708882693015507863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15556864472588462010338575 23335296708882693015507863)
          ·
            refine ⟨35002945063324039523261795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23335296708882693015507863 35002945063324039523261795)
            ·
              refine ⟨52504417594986059284892693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35002945063324039523261795 52504417594986059284892693)
              ·
                refine ⟨2461144574764971528979345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52504417594986059284892693 2461144574764971528979345)
                ·
                  refine ⟨1845858431073728646734509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2461144574764971528979345 1845858431073728646734509)
                  ·
                    refine ⟨692196911652648242525441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845858431073728646734509 692196911652648242525441)
                    ·
                      rfl

theorem cell22_2022073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_2022073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022073 prefixEnd_2022073 := by exact prefixLift 2022073
  have htrace : WordTrace (prefixWord ++ tailWord_2022073) baseStart_2022073 baseEnd_2022073 := by
    simpa [prefixWord, tailWord_2022073, baseEnd_2022073] using wordTrace_append hprefix tailTrace_2022073
  have hstable : (prefixWord ++ tailWord_2022073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022073).length < 2 ^ (prefixWord ++ tailWord_2022073).sum := by decide
  have hdescent : baseEnd_2022073 < baseStart_2022073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022090 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_2022090 : Nat := 118140960795 + 2022090 * 2 ^ 59
def prefixEnd_2022090 : Nat := 4983230072969 + 3 ^ 40 * 2022090 * 2
def baseEnd_2022090 : Nat := 692202731100065864850389

theorem tailTrace_2022090 : CollatzResearch.WordTrace tailWord_2022090 prefixEnd_2022090 692202731100065864850389 := by
  unfold tailWord_2022090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18437920311080187580687931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49167787496213833548501149 18437920311080187580687931)
  ·
    refine ⟨27656880466620281371031897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18437920311080187580687931 27656880466620281371031897)
    ·
      refine ⟨20742660349965211028273923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27656880466620281371031897 20742660349965211028273923)
      ·
        refine ⟨31113990524947816542410885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20742660349965211028273923 31113990524947816542410885)
        ·
          refine ⟨5833873223427715601702041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31113990524947816542410885 5833873223427715601702041)
          ·
            refine ⟨4375404917570786701276531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5833873223427715601702041 4375404917570786701276531)
            ·
              refine ⟨6563107376356180051914797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4375404917570786701276531 6563107376356180051914797)
              ·
                refine ⟨2461165266133567519468049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6563107376356180051914797 2461165266133567519468049)
                ·
                  refine ⟨1845873949600175639601037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2461165266133567519468049 1845873949600175639601037)
                  ·
                    refine ⟨692202731100065864850389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1845873949600175639601037 692202731100065864850389)
                    ·
                      rfl

theorem cell22_2022090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_2022090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022090 prefixEnd_2022090 := by exact prefixLift 2022090
  have htrace : WordTrace (prefixWord ++ tailWord_2022090) baseStart_2022090 baseEnd_2022090 := by
    simpa [prefixWord, tailWord_2022090, baseEnd_2022090] using wordTrace_append hprefix tailTrace_2022090
  have hstable : (prefixWord ++ tailWord_2022090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022090).length < 2 ^ (prefixWord ++ tailWord_2022090).sum := by decide
  have hdescent : baseEnd_2022090 < baseStart_2022090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022148 : List Nat := [2, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_2022148 : Nat := 118140960795 + 2022148 * 2 ^ 59
def prefixEnd_2022148 : Nat := 4983230072969 + 3 ^ 40 * 2022148 * 2
def baseEnd_2022148 : Nat := 230740861895124348966737

theorem tailTrace_2022148 : CollatzResearch.WordTrace tailWord_2022148 prefixEnd_2022148 230740861895124348966737 := by
  unfold tailWord_2022148
  simp only [CollatzResearch.WordTrace]
  refine ⟨36876898339055313114181549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49169197785407084152242065 36876898339055313114181549)
  ·
    refine ⟨13828836877145742417818081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36876898339055313114181549 13828836877145742417818081)
    ·
      refine ⟨10371627657859306813363561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13828836877145742417818081 10371627657859306813363561)
      ·
        refine ⟨7778720743394480110022671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10371627657859306813363561 7778720743394480110022671)
        ·
          refine ⟨11668081115091720165034007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7778720743394480110022671 11668081115091720165034007)
          ·
            refine ⟨17502121672637580247551011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11668081115091720165034007 17502121672637580247551011)
            ·
              refine ⟨26253182508956370371326517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17502121672637580247551011 26253182508956370371326517)
              ·
                refine ⟨2461235860214659722311861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26253182508956370371326517 2461235860214659722311861)
                ·
                  refine ⟨230740861895124348966737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2461235860214659722311861 230740861895124348966737)
                  ·
                    rfl

theorem cell22_2022148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_2022148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022148 prefixEnd_2022148 := by exact prefixLift 2022148
  have htrace : WordTrace (prefixWord ++ tailWord_2022148) baseStart_2022148 baseEnd_2022148 := by
    simpa [prefixWord, tailWord_2022148, baseEnd_2022148] using wordTrace_append hprefix tailTrace_2022148
  have hstable : (prefixWord ++ tailWord_2022148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022148).length < 2 ^ (prefixWord ++ tailWord_2022148).sum := by decide
  have hdescent : baseEnd_2022148 < baseStart_2022148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022193 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 6]
def baseStart_2022193 : Nat := 118140960795 + 2022193 * 2 ^ 59
def prefixEnd_2022193 : Nat := 4983230072969 + 3 ^ 40 * 2022193 * 2
def baseEnd_2022193 : Nat := 230745996701669309841691

theorem tailTrace_2022193 : CollatzResearch.WordTrace tailWord_2022193 prefixEnd_2022193 230745996701669309841691 := by
  unfold tailWord_2022193
  simp only [CollatzResearch.WordTrace]
  refine ⟨73755437962947598913751233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49170291975298399275834155 73755437962947598913751233)
  ·
    refine ⟨55316578472210699185313425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73755437962947598913751233 55316578472210699185313425)
    ·
      refine ⟨41487433854158024388985069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55316578472210699185313425 41487433854158024388985069)
      ·
        refine ⟨15557787695309259145869401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41487433854158024388985069 15557787695309259145869401)
        ·
          refine ⟨11668340771481944359402051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15557787695309259145869401 11668340771481944359402051)
          ·
            refine ⟨17502511157222916539103077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11668340771481944359402051 17502511157222916539103077)
            ·
              refine ⟨3281720841979296851081827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17502511157222916539103077 3281720841979296851081827)
              ·
                refine ⟨4922581262968945276622741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281720841979296851081827 4922581262968945276622741)
                ·
                  refine ⟨230745996701669309841691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4922581262968945276622741 230745996701669309841691)
                  ·
                    rfl

theorem cell22_2022193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_2022193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022193 prefixEnd_2022193 := by exact prefixLift 2022193
  have htrace : WordTrace (prefixWord ++ tailWord_2022193) baseStart_2022193 baseEnd_2022193 := by
    simpa [prefixWord, tailWord_2022193, baseEnd_2022193] using wordTrace_append hprefix tailTrace_2022193
  have hstable : (prefixWord ++ tailWord_2022193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022193).length < 2 ^ (prefixWord ++ tailWord_2022193).sum := by decide
  have hdescent : baseEnd_2022193 < baseStart_2022193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022304 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 1, 3]
def baseStart_2022304 : Nat := 118140960795 + 2022304 * 2 ^ 59
def prefixEnd_2022304 : Nat := 4983230072969 + 3 ^ 40 * 2022304 * 2
def baseEnd_2022304 : Nat := 692275987673440639999733

theorem tailTrace_2022304 : CollatzResearch.WordTrace tailWord_2022304 prefixEnd_2022304 692275987673440639999733 := by
  unfold tailWord_2022304
  simp only [CollatzResearch.WordTrace]
  refine ⟨36879743232772732435520983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49172990977030309914027977 36879743232772732435520983)
  ·
    refine ⟨55319614849159098653281475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36879743232772732435520983 55319614849159098653281475)
    ·
      refine ⟨82979422273738647979922213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55319614849159098653281475 82979422273738647979922213)
      ·
        refine ⟨15558641676325996496235415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82979422273738647979922213 15558641676325996496235415)
        ·
          refine ⟨23337962514488994744353123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15558641676325996496235415 23337962514488994744353123)
          ·
            refine ⟨35006943771733492116529685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23337962514488994744353123 35006943771733492116529685)
            ·
              refine ⟨1640950489300007442962329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35006943771733492116529685 1640950489300007442962329)
              ·
                refine ⟨1230712866975005582221747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640950489300007442962329 1230712866975005582221747)
                ·
                  refine ⟨1846069300462508373332621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230712866975005582221747 1846069300462508373332621)
                  ·
                    refine ⟨692275987673440639999733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846069300462508373332621 692275987673440639999733)
                    ·
                      rfl

theorem cell22_2022304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 3].length) (baseStart_2022304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022304 prefixEnd_2022304 := by exact prefixLift 2022304
  have htrace : WordTrace (prefixWord ++ tailWord_2022304) baseStart_2022304 baseEnd_2022304 := by
    simpa [prefixWord, tailWord_2022304, baseEnd_2022304] using wordTrace_append hprefix tailTrace_2022304
  have hstable : (prefixWord ++ tailWord_2022304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022304).length < 2 ^ (prefixWord ++ tailWord_2022304).sum := by decide
  have hdescent : baseEnd_2022304 < baseStart_2022304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022313 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_2022313 : Nat := 118140960795 + 2022313 * 2 ^ 59
def prefixEnd_2022313 : Nat := 4983230072969 + 3 ^ 40 * 2022313 * 2
def baseEnd_2022313 : Nat := 692279068557367616524705

theorem tailTrace_2022313 : CollatzResearch.WordTrace tailWord_2022313 prefixEnd_2022313 692279068557367616524705 := by
  unfold tailWord_2022313
  simp only [CollatzResearch.WordTrace]
  refine ⟨73759814722512859408119593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49173209815008572938746395 73759814722512859408119593)
  ·
    refine ⟨55319861041884644556089695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73759814722512859408119593 55319861041884644556089695)
    ·
      refine ⟨82979791562826966834134543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55319861041884644556089695 82979791562826966834134543)
      ·
        refine ⟨124469687344240450251201815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82979791562826966834134543 124469687344240450251201815)
        ·
          refine ⟨186704531016360675376802723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124469687344240450251201815 186704531016360675376802723)
          ·
            refine ⟨280056796524541013065204085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186704531016360675376802723 280056796524541013065204085)
            ·
              refine ⟨26255324674175719974862883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 280056796524541013065204085 26255324674175719974862883)
              ·
                refine ⟨39382987011263579962294325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26255324674175719974862883 39382987011263579962294325)
                ·
                  refine ⟨3692155032305960621465093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39382987011263579962294325 3692155032305960621465093)
                  ·
                    refine ⟨692279068557367616524705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692155032305960621465093 692279068557367616524705)
                    ·
                      rfl

theorem cell22_2022313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_2022313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022313 prefixEnd_2022313 := by exact prefixLift 2022313
  have htrace : WordTrace (prefixWord ++ tailWord_2022313) baseStart_2022313 baseEnd_2022313 := by
    simpa [prefixWord, tailWord_2022313, baseEnd_2022313] using wordTrace_append hprefix tailTrace_2022313
  have hstable : (prefixWord ++ tailWord_2022313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022313).length < 2 ^ (prefixWord ++ tailWord_2022313).sum := by decide
  have hdescent : baseEnd_2022313 < baseStart_2022313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022328 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_2022328 : Nat := 118140960795 + 2022328 * 2 ^ 59
def prefixEnd_2022328 : Nat := 4983230072969 + 3 ^ 40 * 2022328 * 2
def baseEnd_2022328 : Nat := 230761401121304192466553

theorem tailTrace_2022328 : CollatzResearch.WordTrace tailWord_2022328 prefixEnd_2022328 230761401121304192466553 := by
  unfold tailWord_2022328
  simp only [CollatzResearch.WordTrace]
  refine ⟨36880180908729258484957819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49173574544972344646610425 36880180908729258484957819)
  ·
    refine ⟨55320271363093887727436729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36880180908729258484957819 55320271363093887727436729)
    ·
      refine ⟨41490203522320415795577547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55320271363093887727436729 41490203522320415795577547)
      ·
        refine ⟨62235305283480623693366321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41490203522320415795577547 62235305283480623693366321)
        ·
          refine ⟨46676478962610467770024741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62235305283480623693366321 46676478962610467770024741)
          ·
            refine ⟨8751839805489462706879639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46676478962610467770024741 8751839805489462706879639)
            ·
              refine ⟨13127759708234194060319459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8751839805489462706879639 13127759708234194060319459)
              ·
                refine ⟨19691639562351291090479189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13127759708234194060319459 19691639562351291090479189)
                ·
                  refine ⟨230761401121304192466553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19691639562351291090479189 230761401121304192466553)
                  ·
                    rfl

theorem cell22_2022328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_2022328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022328 prefixEnd_2022328 := by exact prefixLift 2022328
  have htrace : WordTrace (prefixWord ++ tailWord_2022328) baseStart_2022328 baseEnd_2022328 := by
    simpa [prefixWord, tailWord_2022328, baseEnd_2022328] using wordTrace_append hprefix tailTrace_2022328
  have hstable : (prefixWord ++ tailWord_2022328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022328).length < 2 ^ (prefixWord ++ tailWord_2022328).sum := by decide
  have hdescent : baseEnd_2022328 < baseStart_2022328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022330 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_2022330 : Nat := 118140960795 + 2022330 * 2 ^ 59
def prefixEnd_2022330 : Nat := 4983230072969 + 3 ^ 40 * 2022330 * 2
def baseEnd_2022330 : Nat := 692284888004785238849653

theorem tailTrace_2022330 : CollatzResearch.WordTrace tailWord_2022330 prefixEnd_2022330 692284888004785238849653 := by
  unfold tailWord_2022330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18440108690862817827872111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49173623175634180874325629 18440108690862817827872111)
  ·
    refine ⟨27660163036294226741808167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18440108690862817827872111 27660163036294226741808167)
    ·
      refine ⟨41490244554441340112712251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27660163036294226741808167 41490244554441340112712251)
      ·
        refine ⟨62235366831662010169068377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41490244554441340112712251 62235366831662010169068377)
        ·
          refine ⟨46676525123746507626801283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62235366831662010169068377 46676525123746507626801283)
          ·
            refine ⟨70014787685619761440201925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46676525123746507626801283 70014787685619761440201925)
            ·
              refine ⟨13127772691053705270037861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70014787685619761440201925 13127772691053705270037861)
              ·
                refine ⟨2461457379572569738132099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13127772691053705270037861 2461457379572569738132099)
                ·
                  refine ⟨3692186069358854607198149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461457379572569738132099 3692186069358854607198149)
                  ·
                    refine ⟨692284888004785238849653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692186069358854607198149 692284888004785238849653)
                    ·
                      rfl

theorem cell22_2022330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_2022330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022330 prefixEnd_2022330 := by exact prefixLift 2022330
  have htrace : WordTrace (prefixWord ++ tailWord_2022330) baseStart_2022330 baseEnd_2022330 := by
    simpa [prefixWord, tailWord_2022330, baseEnd_2022330] using wordTrace_append hprefix tailTrace_2022330
  have hstable : (prefixWord ++ tailWord_2022330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022330).length < 2 ^ (prefixWord ++ tailWord_2022330).sum := by decide
  have hdescent : baseEnd_2022330 < baseStart_2022330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022347 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 1, 4]
def baseStart_2022347 : Nat := 118140960795 + 2022347 * 2 ^ 59
def prefixEnd_2022347 : Nat := 4983230072969 + 3 ^ 40 * 2022347 * 2
def baseEnd_2022347 : Nat := 692290707452202861174601

theorem tailTrace_2022347 : CollatzResearch.WordTrace tailWord_2022347 prefixEnd_2022347 692290707452202861174601 := by
  unfold tailWord_2022347
  simp only [CollatzResearch.WordTrace]
  refine ⟨73761054804389683214857295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49174036536259788809904863 73761054804389683214857295)
  ·
    refine ⟨110641582206584524822285943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73761054804389683214857295 110641582206584524822285943)
    ·
      refine ⟨165962373309876787233428915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110641582206584524822285943 165962373309876787233428915)
      ·
        refine ⟨248943559964815180850143373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165962373309876787233428915 248943559964815180850143373)
        ·
          refine ⟨93353834986805692818803765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248943559964815180850143373 93353834986805692818803765)
          ·
            refine ⟨8751922030013033701762853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93353834986805692818803765 8751922030013033701762853)
            ·
              refine ⟨1640985380627443819080535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8751922030013033701762853 1640985380627443819080535)
              ·
                refine ⟨2461478070941165728620803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640985380627443819080535 2461478070941165728620803)
                ·
                  refine ⟨3692217106411748592931205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2461478070941165728620803 3692217106411748592931205)
                  ·
                    refine ⟨692290707452202861174601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692217106411748592931205 692290707452202861174601)
                    ·
                      rfl

theorem cell22_2022347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 4].length) (baseStart_2022347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022347 prefixEnd_2022347 := by exact prefixLift 2022347
  have htrace : WordTrace (prefixWord ++ tailWord_2022347) baseStart_2022347 baseEnd_2022347 := by
    simpa [prefixWord, tailWord_2022347, baseEnd_2022347] using wordTrace_append hprefix tailTrace_2022347
  have hstable : (prefixWord ++ tailWord_2022347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022347).length < 2 ^ (prefixWord ++ tailWord_2022347).sum := by decide
  have hdescent : baseEnd_2022347 < baseStart_2022347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022362 : List Nat := [3, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_2022362 : Nat := 118140960795 + 2022362 * 2 ^ 59
def prefixEnd_2022362 : Nat := 4983230072969 + 3 ^ 40 * 2022362 * 2
def baseEnd_2022362 : Nat := 230765280752915940683185

theorem tailTrace_2022362 : CollatzResearch.WordTrace tailWord_2022362 prefixEnd_2022362 230765280752915940683185 := by
  unfold tailWord_2022362
  simp only [CollatzResearch.WordTrace]
  refine ⟨18440400474833835194163335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49174401266223560517768893 18440400474833835194163335)
  ·
    refine ⟨27660600712250752791245003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18440400474833835194163335 27660600712250752791245003)
    ·
      refine ⟨41490901068376129186867505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27660600712250752791245003 41490901068376129186867505)
      ·
        refine ⟨31118175801282096890150629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41490901068376129186867505 31118175801282096890150629)
        ·
          refine ⟨5834657962740393166903243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31118175801282096890150629 5834657962740393166903243)
          ·
            refine ⟨8751986944110589750354865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834657962740393166903243 8751986944110589750354865)
            ·
              refine ⟨6563990208082942312766149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8751986944110589750354865 6563990208082942312766149)
              ·
                refine ⟨1230748164015551683643653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6563990208082942312766149 1230748164015551683643653)
                ·
                  refine ⟨230765280752915940683185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230748164015551683643653 230765280752915940683185)
                  ·
                    rfl

theorem cell22_2022362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_2022362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022362 prefixEnd_2022362 := by exact prefixLift 2022362
  have htrace : WordTrace (prefixWord ++ tailWord_2022362) baseStart_2022362 baseEnd_2022362 := by
    simpa [prefixWord, tailWord_2022362, baseEnd_2022362] using wordTrace_append hprefix tailTrace_2022362
  have hstable : (prefixWord ++ tailWord_2022362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022362).length < 2 ^ (prefixWord ++ tailWord_2022362).sum := by decide
  have hdescent : baseEnd_2022362 < baseStart_2022362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022375 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 1, 6]
def baseStart_2022375 : Nat := 118140960795 + 2022375 * 2 ^ 59
def prefixEnd_2022375 : Nat := 4983230072969 + 3 ^ 40 * 2022375 * 2
def baseEnd_2022375 : Nat := 692300292424420121474515

theorem tailTrace_2022375 : CollatzResearch.WordTrace tailWord_2022375 prefixEnd_2022375 692300292424420121474515 := by
  unfold tailWord_2022375
  simp only [CollatzResearch.WordTrace]
  refine ⟨73762076048288243996876579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49174717365525495997917719 73762076048288243996876579)
  ·
    refine ⟨110643114072432365995314869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73762076048288243996876579 110643114072432365995314869)
    ·
      refine ⟨10372791944290534312060769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110643114072432365995314869 10372791944290534312060769)
      ·
        refine ⟨7779593958217900734045577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10372791944290534312060769 7779593958217900734045577)
        ·
          refine ⟨5834695468663425550534183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7779593958217900734045577 5834695468663425550534183)
          ·
            refine ⟨8752043202995138325801275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5834695468663425550534183 8752043202995138325801275)
            ·
              refine ⟨13128064804492707488701913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752043202995138325801275 13128064804492707488701913)
              ·
                refine ⟨9846048603369530616526435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128064804492707488701913 9846048603369530616526435)
                ·
                  refine ⟨14769072905054295924789653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9846048603369530616526435 14769072905054295924789653)
                  ·
                    refine ⟨692300292424420121474515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14769072905054295924789653 692300292424420121474515)
                    ·
                      rfl

theorem cell22_2022375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_2022375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022375 prefixEnd_2022375 := by exact prefixLift 2022375
  have htrace : WordTrace (prefixWord ++ tailWord_2022375) baseStart_2022375 baseEnd_2022375 := by
    simpa [prefixWord, tailWord_2022375, baseEnd_2022375] using wordTrace_append hprefix tailTrace_2022375
  have hstable : (prefixWord ++ tailWord_2022375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022375).length < 2 ^ (prefixWord ++ tailWord_2022375).sum := by decide
  have hdescent : baseEnd_2022375 < baseStart_2022375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022403 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 8]
def baseStart_2022403 : Nat := 118140960795 + 2022403 * 2 ^ 59
def prefixEnd_2022403 : Nat := 4983230072969 + 3 ^ 40 * 2022403 * 2
def baseEnd_2022403 : Nat := 692309877396637381774429

theorem tailTrace_2022403 : CollatzResearch.WordTrace tailWord_2022403 prefixEnd_2022403 692309877396637381774429 := by
  unfold tailWord_2022403
  simp only [CollatzResearch.WordTrace]
  refine ⟨73763097292186804778895863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49175398194791203185930575 73763097292186804778895863)
  ·
    refine ⟨110644645938280207168343795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73763097292186804778895863 110644645938280207168343795)
    ·
      refine ⟨165966968907420310752515693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110644645938280207168343795 165966968907420310752515693)
      ·
        refine ⟨62237613340282616532193385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165966968907420310752515693 62237613340282616532193385)
        ·
          refine ⟨46678210005211962399145039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62237613340282616532193385 46678210005211962399145039)
          ·
            refine ⟨70017315007817943598717559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46678210005211962399145039 70017315007817943598717559)
            ·
              refine ⟨105025972511726915398076339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70017315007817943598717559 105025972511726915398076339)
              ·
                refine ⟨157538958767590373097114509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105025972511726915398076339 157538958767590373097114509)
                ·
                  refine ⟨59077109537846389911417941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157538958767590373097114509 59077109537846389911417941)
                  ·
                    refine ⟨692309877396637381774429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59077109537846389911417941 692309877396637381774429)
                    ·
                      rfl

theorem cell22_2022403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_2022403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022403 prefixEnd_2022403 := by exact prefixLift 2022403
  have htrace : WordTrace (prefixWord ++ tailWord_2022403) baseStart_2022403 baseEnd_2022403 := by
    simpa [prefixWord, tailWord_2022403, baseEnd_2022403] using wordTrace_append hprefix tailTrace_2022403
  have hstable : (prefixWord ++ tailWord_2022403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022403).length < 2 ^ (prefixWord ++ tailWord_2022403).sum := by decide
  have hdescent : baseEnd_2022403 < baseStart_2022403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022428 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_2022428 : Nat := 118140960795 + 2022428 * 2 ^ 59
def prefixEnd_2022428 : Nat := 4983230072969 + 3 ^ 40 * 2022428 * 2
def baseEnd_2022428 : Nat := 692318435407545649899353

theorem tailTrace_2022428 : CollatzResearch.WordTrace tailWord_2022428 prefixEnd_2022428 692318435407545649899353 := by
  unfold tailWord_2022428
  simp only [CollatzResearch.WordTrace]
  refine ⟨36882004558548117024277969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49176006078064156032370625 36882004558548117024277969)
  ·
    refine ⟨27661503418911087768208477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36882004558548117024277969 27661503418911087768208477)
    ·
      refine ⟨10373063782091657913078179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27661503418911087768208477 10373063782091657913078179)
      ·
        refine ⟨15559595673137486869617269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10373063782091657913078179 15559595673137486869617269)
        ·
          refine ⟨1458712094356639394026619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15559595673137486869617269 1458712094356639394026619)
          ·
            refine ⟨2188068141534959091039929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458712094356639394026619 2188068141534959091039929)
            ·
              refine ⟨1641051106151219318279947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188068141534959091039929 1641051106151219318279947)
              ·
                refine ⟨2461576659226828977419921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1641051106151219318279947 2461576659226828977419921)
                ·
                  refine ⟨1846182494420121733064941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2461576659226828977419921 1846182494420121733064941)
                  ·
                    refine ⟨692318435407545649899353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846182494420121733064941 692318435407545649899353)
                    ·
                      rfl

theorem cell22_2022428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_2022428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022428 prefixEnd_2022428 := by exact prefixLift 2022428
  have htrace : WordTrace (prefixWord ++ tailWord_2022428) baseStart_2022428 baseEnd_2022428 := by
    simpa [prefixWord, tailWord_2022428, baseEnd_2022428] using wordTrace_append hprefix tailTrace_2022428
  have hstable : (prefixWord ++ tailWord_2022428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022428).length < 2 ^ (prefixWord ++ tailWord_2022428).sum := by decide
  have hdescent : baseEnd_2022428 < baseStart_2022428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022482 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2022482 : Nat := 118140960795 + 2022482 * 2 ^ 59
def prefixEnd_2022482 : Nat := 4983230072969 + 3 ^ 40 * 2022482 * 2
def baseEnd_2022482 : Nat := 692336920711107509049187

theorem tailTrace_2022482 : CollatzResearch.WordTrace tailWord_2022482 prefixEnd_2022482 692336920711107509049187 := by
  unfold tailWord_2022482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441494664725150317755425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49177319105933734180681133 18441494664725150317755425)
  ·
    refine ⟨13831120998543862738316569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18441494664725150317755425 13831120998543862738316569)
    ·
      refine ⟨10373340748907897053737427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13831120998543862738316569 10373340748907897053737427)
      ·
        refine ⟨15560011123361845580606141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10373340748907897053737427 15560011123361845580606141)
        ·
          refine ⟨5835004171260692092727303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15560011123361845580606141 5835004171260692092727303)
          ·
            refine ⟨8752506256891038139090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835004171260692092727303 8752506256891038139090955)
            ·
              refine ⟨13128759385336557208636433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8752506256891038139090955 13128759385336557208636433)
              ·
                refine ⟨9846569539002417906477325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128759385336557208636433 9846569539002417906477325)
                ·
                  refine ⟨3692463577125906714928997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9846569539002417906477325 3692463577125906714928997)
                  ·
                    refine ⟨692336920711107509049187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3692463577125906714928997 692336920711107509049187)
                    ·
                      rfl

theorem cell22_2022482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2022482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022482 prefixEnd_2022482 := by exact prefixLift 2022482
  have htrace : WordTrace (prefixWord ++ tailWord_2022482) baseStart_2022482 baseEnd_2022482 := by
    simpa [prefixWord, tailWord_2022482, baseEnd_2022482] using wordTrace_append hprefix tailTrace_2022482
  have hstable : (prefixWord ++ tailWord_2022482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022482).length < 2 ^ (prefixWord ++ tailWord_2022482).sum := by decide
  have hdescent : baseEnd_2022482 < baseStart_2022482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022512 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_2022512 : Nat := 118140960795 + 2022512 * 2 ^ 59
def prefixEnd_2022512 : Nat := 4983230072969 + 3 ^ 40 * 2022512 * 2
def baseEnd_2022512 : Nat := 692347190324197430799095

theorem tailTrace_2022512 : CollatzResearch.WordTrace tailWord_2022512 prefixEnd_2022512 692347190324197430799095 := by
  unfold tailWord_2022512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36883536424395958197306895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49178048565861277596409193 36883536424395958197306895)
  ·
    refine ⟨55325304636593937295960343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36883536424395958197306895 55325304636593937295960343)
    ·
      refine ⟨82987956954890905943940515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55325304636593937295960343 82987956954890905943940515)
      ·
        refine ⟨124481935432336358915910773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82987956954890905943940515 124481935432336358915910773)
        ·
          refine ⟨11670181446781533648366635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124481935432336358915910773 11670181446781533648366635)
          ·
            refine ⟨17505272170172300472549953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670181446781533648366635 17505272170172300472549953)
            ·
              refine ⟨13128954127629225354412465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17505272170172300472549953 13128954127629225354412465)
              ·
                refine ⟨9846715595721919015809349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13128954127629225354412465 9846715595721919015809349)
                ·
                  refine ⟨1846259174197859815464253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9846715595721919015809349 1846259174197859815464253)
                  ·
                    refine ⟨692347190324197430799095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846259174197859815464253 692347190324197430799095)
                    ·
                      rfl

theorem cell22_2022512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_2022512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022512 prefixEnd_2022512 := by exact prefixLift 2022512
  have htrace : WordTrace (prefixWord ++ tailWord_2022512) baseStart_2022512 baseEnd_2022512 := by
    simpa [prefixWord, tailWord_2022512, baseEnd_2022512] using wordTrace_append hprefix tailTrace_2022512
  have hstable : (prefixWord ++ tailWord_2022512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022512).length < 2 ^ (prefixWord ++ tailWord_2022512).sum := by decide
  have hdescent : baseEnd_2022512 < baseStart_2022512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022514 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_2022514 : Nat := 118140960795 + 2022514 * 2 ^ 59
def prefixEnd_2022514 : Nat := 4983230072969 + 3 ^ 40 * 2022514 * 2
def baseEnd_2022514 : Nat := 230782624988356697416363

theorem tailTrace_2022514 : CollatzResearch.WordTrace tailWord_2022514 prefixEnd_2022514 230782624988356697416363 := by
  unfold tailWord_2022514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18441786448696167684046649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49178097196523113824124397 18441786448696167684046649)
  ·
    refine ⟨13831339836522125763034987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18441786448696167684046649 13831339836522125763034987)
    ·
      refine ⟨20747009754783188644552481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13831339836522125763034987 20747009754783188644552481)
      ·
        refine ⟨15560257316087391483414361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20747009754783188644552481 15560257316087391483414361)
        ·
          refine ⟨11670192987065543612560771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15560257316087391483414361 11670192987065543612560771)
          ·
            refine ⟨17505289480598315418841157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670192987065543612560771 17505289480598315418841157)
            ·
              refine ⟨3282241777612184141032717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17505289480598315418841157 3282241777612184141032717)
              ·
                refine ⟨1230840666604569052887269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3282241777612184141032717 1230840666604569052887269)
                ·
                  refine ⟨230782624988356697416363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230840666604569052887269 230782624988356697416363)
                  ·
                    rfl

theorem cell22_2022514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_2022514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022514 prefixEnd_2022514 := by exact prefixLift 2022514
  have htrace : WordTrace (prefixWord ++ tailWord_2022514) baseStart_2022514 baseEnd_2022514 := by
    simpa [prefixWord, tailWord_2022514, baseEnd_2022514] using wordTrace_append hprefix tailTrace_2022514
  have hstable : (prefixWord ++ tailWord_2022514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022514).length < 2 ^ (prefixWord ++ tailWord_2022514).sum := by decide
  have hdescent : baseEnd_2022514 < baseStart_2022514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022525 : List Nat := [1, 4, 1, 1, 3, 1, 11]
def baseStart_2022525 : Nat := 118140960795 + 2022525 * 2 ^ 59
def prefixEnd_2022525 : Nat := 4983230072969 + 3 ^ 40 * 2022525 * 2
def baseEnd_2022525 : Nat := 25642653351476656674965

theorem tailTrace_2022525 : CollatzResearch.WordTrace tailWord_2022525 prefixEnd_2022525 25642653351476656674965 := by
  unfold tailWord_2022525
  simp only [CollatzResearch.WordTrace]
  refine ⟨73767546997744819614837029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49178364665163213076558019 73767546997744819614837029)
  ·
    refine ⟨13831415062077153677781943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73767546997744819614837029 13831415062077153677781943)
    ·
      refine ⟨20747122593115730516672915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13831415062077153677781943 20747122593115730516672915)
      ·
        refine ⟨31120683889673595775009373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20747122593115730516672915 31120683889673595775009373)
        ·
          refine ⟨11670256458627598415628515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31120683889673595775009373 11670256458627598415628515)
          ·
            refine ⟨17505384687941397623442773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670256458627598415628515 17505384687941397623442773)
            ·
              refine ⟨25642653351476656674965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17505384687941397623442773 25642653351476656674965)
              ·
                rfl

theorem cell22_2022525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 11].length) (baseStart_2022525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022525 prefixEnd_2022525 := by exact prefixLift 2022525
  have htrace : WordTrace (prefixWord ++ tailWord_2022525) baseStart_2022525 baseEnd_2022525 := by
    simpa [prefixWord, tailWord_2022525, baseEnd_2022525] using wordTrace_append hprefix tailTrace_2022525
  have hstable : (prefixWord ++ tailWord_2022525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022525).length < 2 ^ (prefixWord ++ tailWord_2022525).sum := by decide
  have hdescent : baseEnd_2022525 < baseStart_2022525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022529 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_2022529 : Nat := 118140960795 + 2022529 * 2 ^ 59
def prefixEnd_2022529 : Nat := 4983230072969 + 3 ^ 40 * 2022529 * 2
def baseEnd_2022529 : Nat := 692353009771615053124043

theorem tailTrace_2022529 : CollatzResearch.WordTrace tailWord_2022529 prefixEnd_2022529 692353009771615053124043 := by
  unfold tailWord_2022529
  simp only [CollatzResearch.WordTrace]
  refine ⟨73767692889730328297982641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49178461926486885531988427 73767692889730328297982641)
  ·
    refine ⟨55325769667297746223486981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73767692889730328297982641 55325769667297746223486981)
    ·
      refine ⟨10373581812618327416903809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55325769667297746223486981 10373581812618327416903809)
      ·
        refine ⟨7780186359463745562677857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10373581812618327416903809 7780186359463745562677857)
        ·
          refine ⟨5835139769597809172008393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7780186359463745562677857 5835139769597809172008393)
          ·
            refine ⟨4376354827198356879006295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5835139769597809172008393 4376354827198356879006295)
            ·
              refine ⟨6564532240797535318509443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376354827198356879006295 6564532240797535318509443)
              ·
                refine ⟨9846798361196302977764165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6564532240797535318509443 9846798361196302977764165)
                ·
                  refine ⟨1846274692724306808330781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9846798361196302977764165 1846274692724306808330781)
                  ·
                    refine ⟨692353009771615053124043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846274692724306808330781 692353009771615053124043)
                    ·
                      rfl

theorem cell22_2022529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_2022529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022529 prefixEnd_2022529 := by exact prefixLift 2022529
  have htrace : WordTrace (prefixWord ++ tailWord_2022529) baseStart_2022529 baseEnd_2022529 := by
    simpa [prefixWord, tailWord_2022529, baseEnd_2022529] using wordTrace_append hprefix tailTrace_2022529
  have hstable : (prefixWord ++ tailWord_2022529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022529).length < 2 ^ (prefixWord ++ tailWord_2022529).sum := by decide
  have hdescent : baseEnd_2022529 < baseStart_2022529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022642 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 1, 3]
def baseStart_2022642 : Nat := 118140960795 + 2022642 * 2 ^ 59
def prefixEnd_2022642 : Nat := 4983230072969 + 3 ^ 40 * 2022642 * 2
def baseEnd_2022642 : Nat := 692391691980920425048697

theorem tailTrace_2022642 : CollatzResearch.WordTrace tailWord_2022642 prefixEnd_2022642 692391691980920425048697 := by
  unfold tailWord_2022642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18442953584580237149211545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49181209558880632397897453 18442953584580237149211545)
  ·
    refine ⟨13832215188435177861908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18442953584580237149211545 13832215188435177861908659)
    ·
      refine ⟨20748322782652766792862989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13832215188435177861908659 20748322782652766792862989)
      ·
        refine ⟨7780621043494787547323621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20748322782652766792862989 7780621043494787547323621)
        ·
          refine ⟨1458866445655272665123179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7780621043494787547323621 1458866445655272665123179)
          ·
            refine ⟨2188299668482908997684769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458866445655272665123179 2188299668482908997684769)
            ·
              refine ⟨1641224751362181748263577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2188299668482908997684769 1641224751362181748263577)
              ·
                refine ⟨1230918563521636311197683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641224751362181748263577 1230918563521636311197683)
                ·
                  refine ⟨1846377845282454466796525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230918563521636311197683 1846377845282454466796525)
                  ·
                    refine ⟨692391691980920425048697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846377845282454466796525 692391691980920425048697)
                    ·
                      rfl

theorem cell22_2022642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_2022642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022642 prefixEnd_2022642 := by exact prefixLift 2022642
  have htrace : WordTrace (prefixWord ++ tailWord_2022642) baseStart_2022642 baseEnd_2022642 := by
    simpa [prefixWord, tailWord_2022642, baseEnd_2022642] using wordTrace_append hprefix tailTrace_2022642
  have hstable : (prefixWord ++ tailWord_2022642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022642).length < 2 ^ (prefixWord ++ tailWord_2022642).sum := by decide
  have hdescent : baseEnd_2022642 < baseStart_2022642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022649 : List Nat := [1, 2, 1, 3, 1, 1, 5, 4, 4]
def baseStart_2022649 : Nat := 118140960795 + 2022649 * 2 ^ 59
def prefixEnd_2022649 : Nat := 4983230072969 + 3 ^ 40 * 2022649 * 2
def baseEnd_2022649 : Nat := 230798029407991580041225

theorem tailTrace_2022649 : CollatzResearch.WordTrace tailWord_2022649 prefixEnd_2022649 230798029407991580041225 := by
  unfold tailWord_2022649
  simp only [CollatzResearch.WordTrace]
  refine ⟨73772069649295588792351001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49181379766197059194900667 73772069649295588792351001)
  ·
    refine ⟨55329052236971691594263251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73772069649295588792351001 55329052236971691594263251)
    ·
      refine ⟨82993578355457537391394877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55329052236971691594263251 82993578355457537391394877)
      ·
        refine ⟨31122591883296576521773079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82993578355457537391394877 31122591883296576521773079)
        ·
          refine ⟨46683887824944864782659619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31122591883296576521773079 46683887824944864782659619)
          ·
            refine ⟨70025831737417297173989429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46683887824944864782659619 70025831737417297173989429)
            ·
              refine ⟨6564921725382871610061509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70025831737417297173989429 6564921725382871610061509)
              ·
                refine ⟨1230922823509288426886533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6564921725382871610061509 1230922823509288426886533)
                ·
                  refine ⟨230798029407991580041225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230922823509288426886533 230798029407991580041225)
                  ·
                    rfl

theorem cell22_2022649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_2022649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022649 prefixEnd_2022649 := by exact prefixLift 2022649
  have htrace : WordTrace (prefixWord ++ tailWord_2022649) baseStart_2022649 baseEnd_2022649 := by
    simpa [prefixWord, tailWord_2022649, baseEnd_2022649] using wordTrace_append hprefix tailTrace_2022649
  have hstable : (prefixWord ++ tailWord_2022649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022649).length < 2 ^ (prefixWord ++ tailWord_2022649).sum := by decide
  have hdescent : baseEnd_2022649 < baseStart_2022649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022698 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_2022698 : Nat := 118140960795 + 2022698 * 2 ^ 59
def prefixEnd_2022698 : Nat := 4983230072969 + 3 ^ 40 * 2022698 * 2
def baseEnd_2022698 : Nat := 692410861925354945648525

theorem tailTrace_2022698 : CollatzResearch.WordTrace tailWord_2022698 prefixEnd_2022698 692410861925354945648525 := by
  unfold tailWord_2022698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18443464206529517540221187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49182571217412046773923165 18443464206529517540221187)
  ·
    refine ⟨27665196309794276310331781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18443464206529517540221187 27665196309794276310331781)
    ·
      refine ⟨5187224308086426808187209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27665196309794276310331781 5187224308086426808187209)
      ·
        refine ⟨3890418231064820106140407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5187224308086426808187209 3890418231064820106140407)
        ·
          refine ⟨5835627346597230159210611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3890418231064820106140407 5835627346597230159210611)
          ·
            refine ⟨8753441019895845238815917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5835627346597230159210611 8753441019895845238815917)
            ·
              refine ⟨3282540382460941964555969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8753441019895845238815917 3282540382460941964555969)
              ·
                refine ⟨2461905286845706473416977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3282540382460941964555969 2461905286845706473416977)
                ·
                  refine ⟨1846428965134279855062733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2461905286845706473416977 1846428965134279855062733)
                  ·
                    refine ⟨692410861925354945648525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846428965134279855062733 692410861925354945648525)
                    ·
                      rfl

theorem cell22_2022698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_2022698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022698 prefixEnd_2022698 := by exact prefixLift 2022698
  have htrace : WordTrace (prefixWord ++ tailWord_2022698) baseStart_2022698 baseEnd_2022698 := by
    simpa [prefixWord, tailWord_2022698, baseEnd_2022698] using wordTrace_append hprefix tailTrace_2022698
  have hstable : (prefixWord ++ tailWord_2022698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022698).length < 2 ^ (prefixWord ++ tailWord_2022698).sum := by decide
  have hdescent : baseEnd_2022698 < baseStart_2022698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022743 : List Nat := [1, 1, 3, 2, 3, 2, 3, 3, 1, 3]
def baseStart_2022743 : Nat := 118140960795 + 2022743 * 2 ^ 59
def prefixEnd_2022743 : Nat := 4983230072969 + 3 ^ 40 * 2022743 * 2
def baseEnd_2022743 : Nat := 692426266344989828273387

theorem tailTrace_2022743 : CollatzResearch.WordTrace tailWord_2022743 prefixEnd_2022743 692426266344989828273387 := by
  unfold tailWord_2022743
  simp only [CollatzResearch.WordTrace]
  refine ⟨73775498110955042846272883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49183665407303361897515255 73775498110955042846272883)
  ·
    refine ⟨110663247166432564269409325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73775498110955042846272883 110663247166432564269409325)
    ·
      refine ⟨41498717687412211601028497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110663247166432564269409325 41498717687412211601028497)
      ·
        refine ⟨31124038265559158700771373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41498717687412211601028497 31124038265559158700771373)
        ·
          refine ⟨11671514349584684512789265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31124038265559158700771373 11671514349584684512789265)
          ·
            refine ⟨8753635762188513384591949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11671514349584684512789265 8753635762188513384591949)
            ·
              refine ⟨3282613410820692519221981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8753635762188513384591949 3282613410820692519221981)
              ·
                refine ⟨1230980029057759694708243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3282613410820692519221981 1230980029057759694708243)
                ·
                  refine ⟨1846470043586639542062365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1230980029057759694708243 1846470043586639542062365)
                  ·
                    refine ⟨692426266344989828273387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846470043586639542062365 692426266344989828273387)
                    ·
                      rfl

theorem cell22_2022743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_2022743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022743 prefixEnd_2022743 := by exact prefixLift 2022743
  have htrace : WordTrace (prefixWord ++ tailWord_2022743) baseStart_2022743 baseEnd_2022743 := by
    simpa [prefixWord, tailWord_2022743, baseEnd_2022743] using wordTrace_append hprefix tailTrace_2022743
  have hstable : (prefixWord ++ tailWord_2022743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022743).length < 2 ^ (prefixWord ++ tailWord_2022743).sum := by decide
  have hdescent : baseEnd_2022743 < baseStart_2022743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022760 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2022760 : Nat := 118140960795 + 2022760 * 2 ^ 59
def prefixEnd_2022760 : Nat := 4983230072969 + 3 ^ 40 * 2022760 * 2
def baseEnd_2022760 : Nat := 692432085792407450598335

theorem tailTrace_2022760 : CollatzResearch.WordTrace tailWord_2022760 prefixEnd_2022760 692432085792407450598335 := by
  unfold tailWord_2022760
  simp only [CollatzResearch.WordTrace]
  refine ⟨36888059075946727374820867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49184078767928969833094489 36888059075946727374820867)
  ·
    refine ⟨55332088613920091062231301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36888059075946727374820867 55332088613920091062231301)
    ·
      refine ⟨10374766615110017074168369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55332088613920091062231301 10374766615110017074168369)
      ·
        refine ⟨7781074961332512805626277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10374766615110017074168369 7781074961332512805626277)
        ·
          refine ⟨1458951555249846151054927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7781074961332512805626277 1458951555249846151054927)
          ·
            refine ⟨2188427332874769226582391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458951555249846151054927 2188427332874769226582391)
            ·
              refine ⟨3282640999312153839873587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188427332874769226582391 3282640999312153839873587)
              ·
                refine ⟨4923961498968230759810381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3282640999312153839873587 4923961498968230759810381)
                ·
                  refine ⟨1846485562113086534928893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4923961498968230759810381 1846485562113086534928893)
                  ·
                    refine ⟨692432085792407450598335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846485562113086534928893 692432085792407450598335)
                    ·
                      rfl

theorem cell22_2022760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2022760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022760 prefixEnd_2022760 := by exact prefixLift 2022760
  have htrace : WordTrace (prefixWord ++ tailWord_2022760) baseStart_2022760 baseEnd_2022760 := by
    simpa [prefixWord, tailWord_2022760, baseEnd_2022760] using wordTrace_append hprefix tailTrace_2022760
  have hstable : (prefixWord ++ tailWord_2022760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022760).length < 2 ^ (prefixWord ++ tailWord_2022760).sum := by decide
  have hdescent : baseEnd_2022760 < baseStart_2022760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022818 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2022818 : Nat := 118140960795 + 2022818 * 2 ^ 59
def prefixEnd_2022818 : Nat := 4983230072969 + 3 ^ 40 * 2022818 * 2
def baseEnd_2022818 : Nat := 230817313459238210882719

theorem tailTrace_2022818 : CollatzResearch.WordTrace tailWord_2022818 prefixEnd_2022818 230817313459238210882719 := by
  unfold tailWord_2022818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444558396420832663813277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49185489057122220436835405 18444558396420832663813277)
  ·
    refine ⟨6916709398657812248929979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18444558396420832663813277 6916709398657812248929979)
    ·
      refine ⟨10375064097986718373394969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6916709398657812248929979 10375064097986718373394969)
      ·
        refine ⟨7781298073490038780046227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10375064097986718373394969 7781298073490038780046227)
        ·
          refine ⟨11671947110235058170069341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7781298073490038780046227 11671947110235058170069341)
          ·
            refine ⟨4376980166338146813776003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11671947110235058170069341 4376980166338146813776003)
            ·
              refine ⟨6565470249507220220664005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4376980166338146813776003 6565470249507220220664005)
              ·
                refine ⟨1231025671782603791374501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6565470249507220220664005 1231025671782603791374501)
                ·
                  refine ⟨230817313459238210882719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231025671782603791374501 230817313459238210882719)
                  ·
                    rfl

theorem cell22_2022818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2022818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022818 prefixEnd_2022818 := by exact prefixLift 2022818
  have htrace : WordTrace (prefixWord ++ tailWord_2022818) baseStart_2022818 baseEnd_2022818 := by
    simpa [prefixWord, tailWord_2022818, baseEnd_2022818] using wordTrace_append hprefix tailTrace_2022818
  have hstable : (prefixWord ++ tailWord_2022818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022818).length < 2 ^ (prefixWord ++ tailWord_2022818).sum := by decide
  have hdescent : baseEnd_2022818 < baseStart_2022818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2022921 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_2022921 : Nat := 118140960795 + 2022921 * 2 ^ 59
def prefixEnd_2022921 : Nat := 4983230072969 + 3 ^ 40 * 2022921 * 2
def baseEnd_2022921 : Nat := 692487199382656697322841

theorem tailTrace_2022921 : CollatzResearch.WordTrace tailWord_2022921 prefixEnd_2022921 692487199382656697322841 := by
  unfold tailWord_2022921
  simp only [CollatzResearch.WordTrace]
  refine ⟨73781990304310179246252617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49187993536206786164168411 73781990304310179246252617)
  ·
    refine ⟨55336492728232634434689463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73781990304310179246252617 55336492728232634434689463)
    ·
      refine ⟨83004739092348951652034195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55336492728232634434689463 83004739092348951652034195)
      ·
        refine ⟨124507108638523427478051293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83004739092348951652034195 124507108638523427478051293)
        ·
          refine ⟨46690165739446285304269235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124507108638523427478051293 46690165739446285304269235)
          ·
            refine ⟨70035248609169427956403853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46690165739446285304269235 70035248609169427956403853)
            ·
              refine ⟨26263218228438535483651445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70035248609169427956403853 26263218228438535483651445)
              ·
                refine ⟨2462176708916112701592323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26263218228438535483651445 2462176708916112701592323)
                ·
                  refine ⟨3693265063374169052388485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2462176708916112701592323 3693265063374169052388485)
                  ·
                    refine ⟨692487199382656697322841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693265063374169052388485 692487199382656697322841)
                    ·
                      rfl

theorem cell22_2022921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_2022921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2022921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2022921 prefixEnd_2022921 := by exact prefixLift 2022921
  have htrace : WordTrace (prefixWord ++ tailWord_2022921) baseStart_2022921 baseEnd_2022921 := by
    simpa [prefixWord, tailWord_2022921, baseEnd_2022921] using wordTrace_append hprefix tailTrace_2022921
  have hstable : (prefixWord ++ tailWord_2022921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2022921).length < 2 ^ (prefixWord ++ tailWord_2022921).sum := by decide
  have hdescent : baseEnd_2022921 < baseStart_2022921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2022921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023013 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_2023013 : Nat := 118140960795 + 2023013 * 2 ^ 59
def prefixEnd_2023013 : Nat := 4983230072969 + 3 ^ 40 * 2023013 * 2
def baseEnd_2023013 : Nat := 692518692862799124022559

theorem tailTrace_2023013 : CollatzResearch.WordTrace tailWord_2023013 prefixEnd_2023013 692518692862799124022559 := by
  unfold tailWord_2023013
  simp only [CollatzResearch.WordTrace]
  refine ⟨73785345819976878958601693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49190230546651252639067795 73785345819976878958601693)
  ·
    refine ⟨27669504682491329609475635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73785345819976878958601693 27669504682491329609475635)
    ·
      refine ⟨41504257023736994414213453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27669504682491329609475635 41504257023736994414213453)
      ·
        refine ⟨15564096383901372905330045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41504257023736994414213453 15564096383901372905330045)
        ·
          refine ⟨5836536143963014839498767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15564096383901372905330045 5836536143963014839498767)
          ·
            refine ⟨8754804215944522259248151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836536143963014839498767 8754804215944522259248151)
            ·
              refine ⟨13132206323916783388872227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8754804215944522259248151 13132206323916783388872227)
              ·
                refine ⟨19698309485875175083308341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13132206323916783388872227 19698309485875175083308341)
                ·
                  refine ⟨1846716514300797664060157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19698309485875175083308341 1846716514300797664060157)
                  ·
                    refine ⟨692518692862799124022559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846716514300797664060157 692518692862799124022559)
                    ·
                      rfl

theorem cell22_2023013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_2023013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023013 prefixEnd_2023013 := by exact prefixLift 2023013
  have htrace : WordTrace (prefixWord ++ tailWord_2023013) baseStart_2023013 baseEnd_2023013 := by
    simpa [prefixWord, tailWord_2023013, baseEnd_2023013] using wordTrace_append hprefix tailTrace_2023013
  have hstable : (prefixWord ++ tailWord_2023013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023013).length < 2 ^ (prefixWord ++ tailWord_2023013).sum := by decide
  have hdescent : baseEnd_2023013 < baseStart_2023013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023056 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 5, 4]
def baseStart_2023056 : Nat := 118140960795 + 2023056 * 2 ^ 59
def prefixEnd_2023056 : Nat := 4983230072969 + 3 ^ 40 * 2023056 * 2
def baseEnd_2023056 : Nat := 692533412641561345197427

theorem tailTrace_2023056 : CollatzResearch.WordTrace tailWord_2023056 prefixEnd_2023056 692533412641561345197427 := by
  unfold tailWord_2023056
  simp only [CollatzResearch.WordTrace]
  refine ⟨36893457079410548651208511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49191276105880731534944681 36893457079410548651208511)
  ·
    refine ⟨55340185619115822976812767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36893457079410548651208511 55340185619115822976812767)
    ·
      refine ⟨83010278428673734465219151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55340185619115822976812767 83010278428673734465219151)
      ·
        refine ⟨124515417643010601697828727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83010278428673734465219151 124515417643010601697828727)
        ·
          refine ⟨186773126464515902546743091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124515417643010601697828727 186773126464515902546743091)
          ·
            refine ⟨280159689696773853820114637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186773126464515902546743091 280159689696773853820114637)
            ·
              refine ⟨105059883636290195182542989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 280159689696773853820114637 105059883636290195182542989)
              ·
                refine ⟨39397456363608823193453621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105059883636290195182542989 39397456363608823193453621)
                ·
                  refine ⟨3693511534088327174386277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39397456363608823193453621 3693511534088327174386277)
                  ·
                    refine ⟨692533412641561345197427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693511534088327174386277 692533412641561345197427)
                    ·
                      rfl

theorem cell22_2023056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 5, 4].length) (baseStart_2023056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023056 prefixEnd_2023056 := by exact prefixLift 2023056
  have htrace : WordTrace (prefixWord ++ tailWord_2023056) baseStart_2023056 baseEnd_2023056 := by
    simpa [prefixWord, tailWord_2023056, baseEnd_2023056] using wordTrace_append hprefix tailTrace_2023056
  have hstable : (prefixWord ++ tailWord_2023056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023056).length < 2 ^ (prefixWord ++ tailWord_2023056).sum := by decide
  have hdescent : baseEnd_2023056 < baseStart_2023056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023103 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 4, 3]
def baseStart_2023103 : Nat := 118140960795 + 2023103 * 2 ^ 59
def prefixEnd_2023103 : Nat := 4983230072969 + 3 ^ 40 * 2023103 * 2
def baseEnd_2023103 : Nat := 692549501702068889272283

theorem tailTrace_2023103 : CollatzResearch.WordTrace tailWord_2023103 prefixEnd_2023103 692549501702068889272283 := by
  unfold tailWord_2023103
  simp only [CollatzResearch.WordTrace]
  refine ⟨73788628389650824329377963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49192418926433882886251975 73788628389650824329377963)
  ·
    refine ⟨110682942584476236494066945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73788628389650824329377963 110682942584476236494066945)
    ·
      refine ⟨83012206938357177370550209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110682942584476236494066945 83012206938357177370550209)
      ·
        refine ⟨62259155203767883027912657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83012206938357177370550209 62259155203767883027912657)
        ·
          refine ⟨46694366402825912270934493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62259155203767883027912657 46694366402825912270934493)
          ·
            refine ⟨17510387401059717101600435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46694366402825912270934493 17510387401059717101600435)
            ·
              refine ⟨26265581101589575652400653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510387401059717101600435 26265581101589575652400653)
              ·
                refine ⟨9849592913096090869650245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26265581101589575652400653 9849592913096090869650245)
                ·
                  refine ⟨1846798671205517038059421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9849592913096090869650245 1846798671205517038059421)
                  ·
                    refine ⟨692549501702068889272283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846798671205517038059421 692549501702068889272283)
                    ·
                      rfl

theorem cell22_2023103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 4, 3].length) (baseStart_2023103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023103 prefixEnd_2023103 := by exact prefixLift 2023103
  have htrace : WordTrace (prefixWord ++ tailWord_2023103) baseStart_2023103 baseEnd_2023103 := by
    simpa [prefixWord, tailWord_2023103, baseEnd_2023103] using wordTrace_append hprefix tailTrace_2023103
  have hstable : (prefixWord ++ tailWord_2023103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023103).length < 2 ^ (prefixWord ++ tailWord_2023103).sum := by decide
  have hdescent : baseEnd_2023103 < baseStart_2023103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023118 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2023118 : Nat := 118140960795 + 2023118 * 2 ^ 59
def prefixEnd_2023118 : Nat := 4983230072969 + 3 ^ 40 * 2023118 * 2
def baseEnd_2023118 : Nat := 692554636508613850147237

theorem tailTrace_2023118 : CollatzResearch.WordTrace tailWord_2023118 prefixEnd_2023118 692554636508613850147237 := by
  unfold tailWord_2023118
  simp only [CollatzResearch.WordTrace]
  refine ⟨9223646935574560236396751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49192783656397654594116005 9223646935574560236396751)
  ·
    refine ⟨13835470403361840354595127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9223646935574560236396751 13835470403361840354595127)
    ·
      refine ⟨20753205605042760531892691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13835470403361840354595127 20753205605042760531892691)
      ·
        refine ⟨31129808407564140797839037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20753205605042760531892691 31129808407564140797839037)
        ·
          refine ⟨11673678152836552799189639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31129808407564140797839037 11673678152836552799189639)
          ·
            refine ⟨17510517229254829198784459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11673678152836552799189639 17510517229254829198784459)
            ·
              refine ⟨26265775843882243798176689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17510517229254829198784459 26265775843882243798176689)
              ·
                refine ⟨19699331882911682848632517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26265775843882243798176689 19699331882911682848632517)
                ·
                  refine ⟨3693624728045940534118597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19699331882911682848632517 3693624728045940534118597)
                  ·
                    refine ⟨692554636508613850147237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3693624728045940534118597 692554636508613850147237)
                    ·
                      rfl

theorem cell22_2023118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2023118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023118 prefixEnd_2023118 := by exact prefixLift 2023118
  have htrace : WordTrace (prefixWord ++ tailWord_2023118) baseStart_2023118 baseEnd_2023118 := by
    simpa [prefixWord, tailWord_2023118, baseEnd_2023118] using wordTrace_append hprefix tailTrace_2023118
  have hstable : (prefixWord ++ tailWord_2023118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023118).length < 2 ^ (prefixWord ++ tailWord_2023118).sum := by decide
  have hdescent : baseEnd_2023118 < baseStart_2023118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023156 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2023156 : Nat := 118140960795 + 2023156 * 2 ^ 59
def prefixEnd_2023156 : Nat := 4983230072969 + 3 ^ 40 * 2023156 * 2
def baseEnd_2023156 : Nat := 230855881561731472565707

theorem tailTrace_2023156 : CollatzResearch.WordTrace tailWord_2023156 prefixEnd_2023156 230855881561731472565707 := by
  unfold tailWord_2023156
  simp only [CollatzResearch.WordTrace]
  refine ⟨36895280729229407190528661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49193707638972542920704881 36895280729229407190528661)
  ·
    refine ⟨1729466284182628462056031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36895280729229407190528661 1729466284182628462056031)
    ·
      refine ⟨2594199426273942693084047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1729466284182628462056031 2594199426273942693084047)
      ·
        refine ⟨3891299139410914039626071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594199426273942693084047 3891299139410914039626071)
        ·
          refine ⟨5836948709116371059439107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3891299139410914039626071 5836948709116371059439107)
          ·
            refine ⟨8755423063674556589158661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5836948709116371059439107 8755423063674556589158661)
            ·
              refine ⟨1641641824438979360467249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8755423063674556589158661 1641641824438979360467249)
              ·
                refine ⟨1231231368329234520350437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1641641824438979360467249 1231231368329234520350437)
                ·
                  refine ⟨230855881561731472565707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231231368329234520350437 230855881561731472565707)
                  ·
                    rfl

theorem cell22_2023156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2023156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023156 prefixEnd_2023156 := by exact prefixLift 2023156
  have htrace : WordTrace (prefixWord ++ tailWord_2023156) baseStart_2023156 baseEnd_2023156 := by
    simpa [prefixWord, tailWord_2023156, baseEnd_2023156] using wordTrace_append hprefix tailTrace_2023156
  have hstable : (prefixWord ++ tailWord_2023156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023156).length < 2 ^ (prefixWord ++ tailWord_2023156).sum := by decide
  have hdescent : baseEnd_2023156 < baseStart_2023156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023272 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2023272 : Nat := 118140960795 + 2023272 * 2 ^ 59
def prefixEnd_2023272 : Nat := 4983230072969 + 3 ^ 40 * 2023272 * 2
def baseEnd_2023272 : Nat := 692607353855808781796765

theorem tailTrace_2023272 : CollatzResearch.WordTrace tailWord_2023272 prefixEnd_2023272 692607353855808781796765 := by
  unfold tailWord_2023272
  simp only [CollatzResearch.WordTrace]
  refine ⟨36897396163019283096140035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49196528217359044128186713 36897396163019283096140035)
  ·
    refine ⟨55346094244528924644210053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36897396163019283096140035 55346094244528924644210053)
    ·
      refine ⟨10377392670849173370789385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55346094244528924644210053 10377392670849173370789385)
      ·
        refine ⟨7783044503136880028092039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10377392670849173370789385 7783044503136880028092039)
        ·
          refine ⟨11674566754705320042138059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783044503136880028092039 11674566754705320042138059)
          ·
            refine ⟨17511850132057980063207089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674566754705320042138059 17511850132057980063207089)
            ·
              refine ⟨13133887599043485047405317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17511850132057980063207089 13133887599043485047405317)
              ·
                refine ⟨2462603924820653446388497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13133887599043485047405317 2462603924820653446388497)
                ·
                  refine ⟨1846952943615490084791373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2462603924820653446388497 1846952943615490084791373)
                  ·
                    refine ⟨692607353855808781796765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1846952943615490084791373 692607353855808781796765)
                    ·
                      rfl

theorem cell22_2023272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2023272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023272 prefixEnd_2023272 := by exact prefixLift 2023272
  have htrace : WordTrace (prefixWord ++ tailWord_2023272) baseStart_2023272 baseEnd_2023272 := by
    simpa [prefixWord, tailWord_2023272, baseEnd_2023272] using wordTrace_append hprefix tailTrace_2023272
  have hstable : (prefixWord ++ tailWord_2023272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023272).length < 2 ^ (prefixWord ++ tailWord_2023272).sum := by decide
  have hdescent : baseEnd_2023272 < baseStart_2023272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023274 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_2023274 : Nat := 118140960795 + 2023274 * 2 ^ 59
def prefixEnd_2023274 : Nat := 4983230072969 + 3 ^ 40 * 2023274 * 2
def baseEnd_2023274 : Nat := 230869346165560481082253

theorem tailTrace_2023274 : CollatzResearch.WordTrace tailWord_2023274 prefixEnd_2023274 230869346165560481082253 := by
  unfold tailWord_2023274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18448716318007830133463219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49196576848020880355901917 18448716318007830133463219)
  ·
    refine ⟨27673074477011745200194829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18448716318007830133463219 27673074477011745200194829)
    ·
      refine ⟨10377402928879404450073061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27673074477011745200194829 10377402928879404450073061)
      ·
        refine ⟨1945763049164888334388699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10377402928879404450073061 1945763049164888334388699)
        ·
          refine ⟨2918644573747332501583049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945763049164888334388699 2918644573747332501583049)
          ·
            refine ⟨2188983430310499376187287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2918644573747332501583049 2188983430310499376187287)
            ·
              refine ⟨3283475145465749064280931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188983430310499376187287 3283475145465749064280931)
              ·
                refine ⟨4925212718198623596421397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283475145465749064280931 4925212718198623596421397)
                ·
                  refine ⟨230869346165560481082253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4925212718198623596421397 230869346165560481082253)
                  ·
                    rfl

theorem cell22_2023274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_2023274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023274 prefixEnd_2023274 := by exact prefixLift 2023274
  have htrace : WordTrace (prefixWord ++ tailWord_2023274) baseStart_2023274 baseEnd_2023274 := by
    simpa [prefixWord, tailWord_2023274, baseEnd_2023274] using wordTrace_append hprefix tailTrace_2023274
  have hstable : (prefixWord ++ tailWord_2023274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023274).length < 2 ^ (prefixWord ++ tailWord_2023274).sum := by decide
  have hdescent : baseEnd_2023274 < baseStart_2023274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023285 : List Nat := [1, 3, 4, 1, 1, 1, 4, 7]
def baseStart_2023285 : Nat := 118140960795 + 2023285 * 2 ^ 59
def prefixEnd_2023285 : Nat := 4983230072969 + 3 ^ 40 * 2023285 * 2
def baseEnd_2023285 : Nat := 76956867113497897913525

theorem tailTrace_2023285 : CollatzResearch.WordTrace tailWord_2023285 prefixEnd_2023285 76956867113497897913525 := by
  unfold tailWord_2023285
  simp only [CollatzResearch.WordTrace]
  refine ⟨73795266474991469412503309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49196844316660979608335539 73795266474991469412503309)
  ·
    refine ⟨27673224928121801029688741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73795266474991469412503309 27673224928121801029688741)
    ·
      refine ⟨5188729674022837693066639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27673224928121801029688741 5188729674022837693066639)
      ·
        refine ⟨7783094511034256539599959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188729674022837693066639 7783094511034256539599959)
        ·
          refine ⟨11674641766551384809399939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7783094511034256539599959 11674641766551384809399939)
          ·
            refine ⟨17511962649827077214099909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11674641766551384809399939 17511962649827077214099909)
            ·
              refine ⟨3283492996842576977643733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17511962649827077214099909 3283492996842576977643733)
              ·
                refine ⟨76956867113497897913525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3283492996842576977643733 76956867113497897913525)
                ·
                  rfl

theorem cell22_2023285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 7].length) (baseStart_2023285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023285 prefixEnd_2023285 := by exact prefixLift 2023285
  have htrace : WordTrace (prefixWord ++ tailWord_2023285) baseStart_2023285 baseEnd_2023285 := by
    simpa [prefixWord, tailWord_2023285, baseEnd_2023285] using wordTrace_append hprefix tailTrace_2023285
  have hstable : (prefixWord ++ tailWord_2023285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023285).length < 2 ^ (prefixWord ++ tailWord_2023285).sum := by decide
  have hdescent : baseEnd_2023285 < baseStart_2023285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023313 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 9]
def baseStart_2023313 : Nat := 118140960795 + 2023313 * 2 ^ 59
def prefixEnd_2023313 : Nat := 4983230072969 + 3 ^ 40 * 2023313 * 2
def baseEnd_2023313 : Nat := 230873796331232780507213

theorem tailTrace_2023313 : CollatzResearch.WordTrace tailWord_2023313 prefixEnd_2023313 230873796331232780507213 := by
  unfold tailWord_2023313
  simp only [CollatzResearch.WordTrace]
  refine ⟨73796287718890030194522593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49197525145926686796348395 73796287718890030194522593)
  ·
    refine ⟨55347215789167522645891945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73796287718890030194522593 55347215789167522645891945)
    ·
      refine ⟨41510411841875641984418959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55347215789167522645891945 41510411841875641984418959)
      ·
        refine ⟨62265617762813462976628439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41510411841875641984418959 62265617762813462976628439)
        ·
          refine ⟨93398426644220194464942659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62265617762813462976628439 93398426644220194464942659)
          ·
            refine ⟨140097639966330291697413989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93398426644220194464942659 140097639966330291697413989)
            ·
              refine ⟨26268307493686929693265123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140097639966330291697413989 26268307493686929693265123)
              ·
                refine ⟨39402461240530394539897685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26268307493686929693265123 39402461240530394539897685)
                ·
                  refine ⟨230873796331232780507213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39402461240530394539897685 230873796331232780507213)
                  ·
                    rfl

theorem cell22_2023313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 9].length) (baseStart_2023313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023313 prefixEnd_2023313 := by exact prefixLift 2023313
  have htrace : WordTrace (prefixWord ++ tailWord_2023313) baseStart_2023313 baseEnd_2023313 := by
    simpa [prefixWord, tailWord_2023313, baseEnd_2023313] using wordTrace_append hprefix tailTrace_2023313
  have hstable : (prefixWord ++ tailWord_2023313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023313).length < 2 ^ (prefixWord ++ tailWord_2023313).sum := by decide
  have hdescent : baseEnd_2023313 < baseStart_2023313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023336 : List Nat := [2, 1, 6, 2, 2, 1, 1, 7]
def baseStart_2023336 : Nat := 118140960795 + 2023336 * 2 ^ 59
def prefixEnd_2023336 : Nat := 4983230072969 + 3 ^ 40 * 2023336 * 2
def baseEnd_2023336 : Nat := 76958806929303772021841

theorem tailTrace_2023336 : CollatzResearch.WordTrace tailWord_2023336 prefixEnd_2023336 76958806929303772021841 := by
  unfold tailWord_2023336
  simp only [CollatzResearch.WordTrace]
  refine ⟨36898563298903352561304931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49198084398537803415073241 36898563298903352561304931)
  ·
    refine ⟨55347844948355028841957397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36898563298903352561304931 55347844948355028841957397)
    ·
      refine ⟨2594430231954141976966753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55347844948355028841957397 2594430231954141976966753)
      ·
        refine ⟨1945822673965606482725065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2594430231954141976966753 1945822673965606482725065)
        ·
          refine ⟨1459367005474204862043799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1945822673965606482725065 1459367005474204862043799)
          ·
            refine ⟨2189050508211307293065699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459367005474204862043799 2189050508211307293065699)
            ·
              refine ⟨3283575762316960939598549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189050508211307293065699 3283575762316960939598549)
              ·
                refine ⟨76958806929303772021841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3283575762316960939598549 76958806929303772021841)
                ·
                  rfl

theorem cell22_2023336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_2023336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023336 prefixEnd_2023336 := by exact prefixLift 2023336
  have htrace : WordTrace (prefixWord ++ tailWord_2023336) baseStart_2023336 baseEnd_2023336 := by
    simpa [prefixWord, tailWord_2023336, baseEnd_2023336] using wordTrace_append hprefix tailTrace_2023336
  have hstable : (prefixWord ++ tailWord_2023336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023336).length < 2 ^ (prefixWord ++ tailWord_2023336).sum := by decide
  have hdescent : baseEnd_2023336 < baseStart_2023336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023345 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_2023345 : Nat := 118140960795 + 2023345 * 2 ^ 59
def prefixEnd_2023345 : Nat := 4983230072969 + 3 ^ 40 * 2023345 * 2
def baseEnd_2023345 : Nat := 692632343247660924721541

theorem tailTrace_2023345 : CollatzResearch.WordTrace tailWord_2023345 prefixEnd_2023345 692632343247660924721541 := by
  unfold tailWord_2023345
  simp only [CollatzResearch.WordTrace]
  refine ⟨73797454854774099659687489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49198303236516066439791659 73797454854774099659687489)
  ·
    refine ⟨55348091141080574744765617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73797454854774099659687489 55348091141080574744765617)
    ·
      refine ⟨41511068355810431058574213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55348091141080574744765617 41511068355810431058574213)
      ·
        refine ⟨7783325316714455823482665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41511068355810431058574213 7783325316714455823482665)
        ·
          refine ⟨5837493987535841867611999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7783325316714455823482665 5837493987535841867611999)
          ·
            refine ⟨8756240981303762801417999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5837493987535841867611999 8756240981303762801417999)
            ·
              refine ⟨13134361471955644202126999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756240981303762801417999 13134361471955644202126999)
              ·
                refine ⟨19701542207933466303190499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13134361471955644202126999 19701542207933466303190499)
                ·
                  refine ⟨29552313311900199454785749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19701542207933466303190499 29552313311900199454785749)
                  ·
                    refine ⟨692632343247660924721541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29552313311900199454785749 692632343247660924721541)
                    ·
                      rfl

theorem cell22_2023345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_2023345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023345 prefixEnd_2023345 := by exact prefixLift 2023345
  have htrace : WordTrace (prefixWord ++ tailWord_2023345) baseStart_2023345 baseEnd_2023345 := by
    simpa [prefixWord, tailWord_2023345, baseEnd_2023345] using wordTrace_append hprefix tailTrace_2023345
  have hstable : (prefixWord ++ tailWord_2023345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023345).length < 2 ^ (prefixWord ++ tailWord_2023345).sum := by decide
  have hdescent : baseEnd_2023345 < baseStart_2023345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023360 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 3, 4]
def baseStart_2023360 : Nat := 118140960795 + 2023360 * 2 ^ 59
def prefixEnd_2023360 : Nat := 4983230072969 + 3 ^ 40 * 2023360 * 2
def baseEnd_2023360 : Nat := 692637478054205885596495

theorem tailTrace_2023360 : CollatzResearch.WordTrace tailWord_2023360 prefixEnd_2023360 692637478054205885596495 := by
  unfold tailWord_2023360
  simp only [CollatzResearch.WordTrace]
  refine ⟨36899000974859878610741767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49198667966479838147655689 36899000974859878610741767)
  ·
    refine ⟨55348501462289817916112651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36899000974859878610741767 55348501462289817916112651)
    ·
      refine ⟨83022752193434726874168977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55348501462289817916112651 83022752193434726874168977)
      ·
        refine ⟨62267064145076045155626733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83022752193434726874168977 62267064145076045155626733)
        ·
          refine ⟨23350149054403516933360025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62267064145076045155626733 23350149054403516933360025)
          ·
            refine ⟨17512611790802637700020019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23350149054403516933360025 17512611790802637700020019)
            ·
              refine ⟨26268917686203956550030029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17512611790802637700020019 26268917686203956550030029)
              ·
                refine ⟨9850844132326483706261261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26268917686203956550030029 9850844132326483706261261)
                ·
                  refine ⟨3694066549622431389847973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9850844132326483706261261 3694066549622431389847973)
                  ·
                    refine ⟨692637478054205885596495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694066549622431389847973 692637478054205885596495)
                    ·
                      rfl

theorem cell22_2023360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 3, 4].length) (baseStart_2023360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023360 prefixEnd_2023360 := by exact prefixLift 2023360
  have htrace : WordTrace (prefixWord ++ tailWord_2023360) baseStart_2023360 baseEnd_2023360 := by
    simpa [prefixWord, tailWord_2023360, baseEnd_2023360] using wordTrace_append hprefix tailTrace_2023360
  have hstable : (prefixWord ++ tailWord_2023360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023360).length < 2 ^ (prefixWord ++ tailWord_2023360).sum := by decide
  have hdescent : baseEnd_2023360 < baseStart_2023360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023420 : List Nat := [2, 2, 2, 1, 2, 2, 3, 8]
def baseStart_2023420 : Nat := 118140960795 + 2023420 * 2 ^ 59
def prefixEnd_2023420 : Nat := 4983230072969 + 3 ^ 40 * 2023420 * 2
def baseEnd_2023420 : Nat := 76962001920042858788479

theorem tailTrace_2023420 : CollatzResearch.WordTrace tailWord_2023420 prefixEnd_2023420 76962001920042858788479 := by
  unfold tailWord_2023420
  simp only [CollatzResearch.WordTrace]
  refine ⟨36900095164751193734333857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49200126886334924979111809 36900095164751193734333857)
  ·
    refine ⟨27675071373563395300750393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36900095164751193734333857 27675071373563395300750393)
    ·
      refine ⟨20756303530172546475562795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27675071373563395300750393 20756303530172546475562795)
      ·
        refine ⟨31134455295258819713344193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20756303530172546475562795 31134455295258819713344193)
        ·
          refine ⟨23350841471444114785008145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31134455295258819713344193 23350841471444114785008145)
          ·
            refine ⟨17513131103583086088756109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23350841471444114785008145 17513131103583086088756109)
            ·
              refine ⟨6567424163843657283283541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17513131103583086088756109 6567424163843657283283541)
              ·
                refine ⟨76962001920042858788479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6567424163843657283283541 76962001920042858788479)
                ·
                  rfl

theorem cell22_2023420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_2023420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023420 prefixEnd_2023420 := by exact prefixLift 2023420
  have htrace : WordTrace (prefixWord ++ tailWord_2023420) baseStart_2023420 baseEnd_2023420 := by
    simpa [prefixWord, tailWord_2023420, baseEnd_2023420] using wordTrace_append hprefix tailTrace_2023420
  have hstable : (prefixWord ++ tailWord_2023420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023420).length < 2 ^ (prefixWord ++ tailWord_2023420).sum := by decide
  have hdescent : baseEnd_2023420 < baseStart_2023420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023512 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 3, 4]
def baseStart_2023512 : Nat := 118140960795 + 2023512 * 2 ^ 59
def prefixEnd_2023512 : Nat := 4983230072969 + 3 ^ 40 * 2023512 * 2
def baseEnd_2023512 : Nat := 692689510760528155796029

theorem tailTrace_2023512 : CollatzResearch.WordTrace tailWord_2023512 prefixEnd_2023512 692689510760528155796029 := by
  unfold tailWord_2023512
  simp only [CollatzResearch.WordTrace]
  refine ⟨36901772922584543590508395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49202363896779391454011193 36901772922584543590508395)
  ·
    refine ⟨55352659383876815385762593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36901772922584543590508395 55352659383876815385762593)
    ·
      refine ⟨41514494537907611539321945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55352659383876815385762593 41514494537907611539321945)
      ·
        refine ⟨31135870903430708654491459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41514494537907611539321945 31135870903430708654491459)
        ·
          refine ⟨46703806355146062981737189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31135870903430708654491459 46703806355146062981737189)
          ·
            refine ⟨8756963691589886809075723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46703806355146062981737189 8756963691589886809075723)
            ·
              refine ⟨13135445537384830213613585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8756963691589886809075723 13135445537384830213613585)
              ·
                refine ⟨9851584153038622660210189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13135445537384830213613585 9851584153038622660210189)
                ·
                  refine ⟨3694344057389483497578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9851584153038622660210189 3694344057389483497578821)
                  ·
                    refine ⟨692689510760528155796029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694344057389483497578821 692689510760528155796029)
                    ·
                      rfl

theorem cell22_2023512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_2023512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023512 prefixEnd_2023512 := by exact prefixLift 2023512
  have htrace : WordTrace (prefixWord ++ tailWord_2023512) baseStart_2023512 baseEnd_2023512 := by
    simpa [prefixWord, tailWord_2023512, baseEnd_2023512] using wordTrace_append hprefix tailTrace_2023512
  have hstable : (prefixWord ++ tailWord_2023512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023512).length < 2 ^ (prefixWord ++ tailWord_2023512).sum := by decide
  have hdescent : baseEnd_2023512 < baseStart_2023512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023527 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 6]
def baseStart_2023527 : Nat := 118140960795 + 2023527 * 2 ^ 59
def prefixEnd_2023527 : Nat := 4983230072969 + 3 ^ 40 * 2023527 * 2
def baseEnd_2023527 : Nat := 230898215189024372223661

theorem tailTrace_2023527 : CollatzResearch.WordTrace tailWord_2023527 prefixEnd_2023527 230898215189024372223661 := by
  unfold tailWord_2023527
  simp only [CollatzResearch.WordTrace]
  refine ⟨73804092940114744742812835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49202728626743163161875223 73804092940114744742812835)
  ·
    refine ⟨110706139410172117114219253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73804092940114744742812835 110706139410172117114219253)
    ·
      refine ⟨10378700569703635979458055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110706139410172117114219253 10378700569703635979458055)
      ·
        refine ⟨15568050854555453969187083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10378700569703635979458055 15568050854555453969187083)
        ·
          refine ⟨23352076281833180953780625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15568050854555453969187083 23352076281833180953780625)
          ·
            refine ⟨17514057211374885715335469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23352076281833180953780625 17514057211374885715335469)
            ·
              refine ⟨6567771454265582143250801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17514057211374885715335469 6567771454265582143250801)
              ·
                refine ⟨4925828590699186607438101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6567771454265582143250801 4925828590699186607438101)
                ·
                  refine ⟨230898215189024372223661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4925828590699186607438101 230898215189024372223661)
                  ·
                    rfl

theorem cell22_2023527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 6].length) (baseStart_2023527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023527 prefixEnd_2023527 := by exact prefixLift 2023527
  have htrace : WordTrace (prefixWord ++ tailWord_2023527) baseStart_2023527 baseEnd_2023527 := by
    simpa [prefixWord, tailWord_2023527, baseEnd_2023527] using wordTrace_append hprefix tailTrace_2023527
  have hstable : (prefixWord ++ tailWord_2023527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023527).length < 2 ^ (prefixWord ++ tailWord_2023527).sum := by decide
  have hdescent : baseEnd_2023527 < baseStart_2023527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023576 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 1, 5]
def baseStart_2023576 : Nat := 118140960795 + 2023576 * 2 ^ 59
def prefixEnd_2023576 : Nat := 4983230072969 + 3 ^ 40 * 2023576 * 2
def baseEnd_2023576 : Nat := 692711419268453322195833

theorem tailTrace_2023576 : CollatzResearch.WordTrace tailWord_2023576 prefixEnd_2023576 692711419268453322195833 := by
  unfold tailWord_2023576
  simp only [CollatzResearch.WordTrace]
  refine ⟨36902940058468613055673291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49203920077958150740897721 36902940058468613055673291)
  ·
    refine ⟨55354410087702919583509937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36902940058468613055673291 55354410087702919583509937)
    ·
      refine ⟨41515807565777189687632453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55354410087702919583509937 41515807565777189687632453)
      ·
        refine ⟨7784213918583223066431085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41515807565777189687632453 7784213918583223066431085)
        ·
          refine ⟨2919080219468708649911657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7784213918583223066431085 2919080219468708649911657)
          ·
            refine ⟨2189310164601531487433743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919080219468708649911657 2189310164601531487433743)
            ·
              refine ⟨3283965246902297231150615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189310164601531487433743 3283965246902297231150615)
              ·
                refine ⟨4925947870353445846725923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3283965246902297231150615 4925947870353445846725923)
                ·
                  refine ⟨7388921805530168770088885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4925947870353445846725923 7388921805530168770088885)
                  ·
                    refine ⟨692711419268453322195833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7388921805530168770088885 692711419268453322195833)
                    ·
                      rfl

theorem cell22_2023576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 5].length) (baseStart_2023576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023576 prefixEnd_2023576 := by exact prefixLift 2023576
  have htrace : WordTrace (prefixWord ++ tailWord_2023576) baseStart_2023576 baseEnd_2023576 := by
    simpa [prefixWord, tailWord_2023576, baseEnd_2023576] using wordTrace_append hprefix tailTrace_2023576
  have hstable : (prefixWord ++ tailWord_2023576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023576).length < 2 ^ (prefixWord ++ tailWord_2023576).sum := by decide
  have hdescent : baseEnd_2023576 < baseStart_2023576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023621 : List Nat := [1, 3, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_2023621 : Nat := 118140960795 + 2023621 * 2 ^ 59
def prefixEnd_2023621 : Nat := 4983230072969 + 3 ^ 40 * 2023621 * 2
def baseEnd_2023621 : Nat := 692726823688088204820695

theorem tailTrace_2023621 : CollatzResearch.WordTrace tailWord_2023621 prefixEnd_2023621 692726823688088204820695 := by
  unfold tailWord_2023621
  simp only [CollatzResearch.WordTrace]
  refine ⟨73807521401774198796734717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49205014267849465864489811 73807521401774198796734717)
  ·
    refine ⟨27677820525665324548775519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73807521401774198796734717 27677820525665324548775519)
    ·
      refine ⟨41516730788497986823163279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27677820525665324548775519 41516730788497986823163279)
      ·
        refine ⟨62275096182746980234744919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41516730788497986823163279 62275096182746980234744919)
        ·
          refine ⟨93412644274120470352117379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62275096182746980234744919 93412644274120470352117379)
          ·
            refine ⟨140118966411180705528176069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93412644274120470352117379 140118966411180705528176069)
            ·
              refine ⟨26272306202096382286533013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140118966411180705528176069 26272306202096382286533013)
              ·
                refine ⟨1231514353223267919681235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26272306202096382286533013 1231514353223267919681235)
                ·
                  refine ⟨1847271529834901879521853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1231514353223267919681235 1847271529834901879521853)
                  ·
                    refine ⟨692726823688088204820695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847271529834901879521853 692726823688088204820695)
                    ·
                      rfl

theorem cell22_2023621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_2023621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023621 prefixEnd_2023621 := by exact prefixLift 2023621
  have htrace : WordTrace (prefixWord ++ tailWord_2023621) baseStart_2023621 baseEnd_2023621 := by
    simpa [prefixWord, tailWord_2023621, baseEnd_2023621] using wordTrace_append hprefix tailTrace_2023621
  have hstable : (prefixWord ++ tailWord_2023621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023621).length < 2 ^ (prefixWord ++ tailWord_2023621).sum := by decide
  have hdescent : baseEnd_2023621 < baseStart_2023621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023664 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_2023664 : Nat := 118140960795 + 2023664 * 2 ^ 59
def prefixEnd_2023664 : Nat := 4983230072969 + 3 ^ 40 * 2023664 * 2
def baseEnd_2023664 : Nat := 692741543466850425995563

theorem tailTrace_2023664 : CollatzResearch.WordTrace tailWord_2023664 prefixEnd_2023664 692741543466850425995563 := by
  unfold tailWord_2023664
  simp only [CollatzResearch.WordTrace]
  refine ⟨36904544870309208570275023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49206059827078944760366697 36904544870309208570275023)
  ·
    refine ⟨55356817305463812855412535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36904544870309208570275023 55356817305463812855412535)
    ·
      refine ⟨83035225958195719283118803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55356817305463812855412535 83035225958195719283118803)
      ·
        refine ⟨124552838937293578924678205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83035225958195719283118803 124552838937293578924678205)
        ·
          refine ⟨46707314601485092096754327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124552838937293578924678205 46707314601485092096754327)
          ·
            refine ⟨70060971902227638145131491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46707314601485092096754327 70060971902227638145131491)
            ·
              refine ⟨105091457853341457217697237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70060971902227638145131491 105091457853341457217697237)
              ·
                refine ⟨2463081043437690403539779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105091457853341457217697237 2463081043437690403539779)
                ·
                  refine ⟨3694621565156535605309669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2463081043437690403539779 3694621565156535605309669)
                  ·
                    refine ⟨692741543466850425995563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3694621565156535605309669 692741543466850425995563)
                    ·
                      rfl

theorem cell22_2023664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_2023664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023664 prefixEnd_2023664 := by exact prefixLift 2023664
  have htrace : WordTrace (prefixWord ++ tailWord_2023664) baseStart_2023664 baseEnd_2023664 := by
    simpa [prefixWord, tailWord_2023664, baseEnd_2023664] using wordTrace_append hprefix tailTrace_2023664
  have hstable : (prefixWord ++ tailWord_2023664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023664).length < 2 ^ (prefixWord ++ tailWord_2023664).sum := by decide
  have hdescent : baseEnd_2023664 < baseStart_2023664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023707 : List Nat := [1, 1, 1, 1, 1, 1, 6, 10]
def baseStart_2023707 : Nat := 118140960795 + 2023707 * 2 ^ 59
def prefixEnd_2023707 : Nat := 4983230072969 + 3 ^ 40 * 2023707 * 2
def baseEnd_2023707 : Nat := 76972918138401405241159

theorem tailTrace_2023707 : CollatzResearch.WordTrace tailWord_2023707 prefixEnd_2023707 76972918138401405241159 := by
  unfold tailWord_2023707
  simp only [CollatzResearch.WordTrace]
  refine ⟨73810658079462635484365375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49207105386308423656243583 73810658079462635484365375)
  ·
    refine ⟨110715987119193953226548063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73810658079462635484365375 110715987119193953226548063)
    ·
      refine ⟨166073980678790929839822095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110715987119193953226548063 166073980678790929839822095)
      ·
        refine ⟨249110971018186394759733143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166073980678790929839822095 249110971018186394759733143)
        ·
          refine ⟨373666456527279592139599715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249110971018186394759733143 373666456527279592139599715)
          ·
            refine ⟨560499684790919388209399573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373666456527279592139599715 560499684790919388209399573)
            ·
              refine ⟨26273422724574346322315605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 560499684790919388209399573 26273422724574346322315605)
              ·
                refine ⟨76972918138401405241159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26273422724574346322315605 76972918138401405241159)
                ·
                  rfl

theorem cell22_2023707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 10].length) (baseStart_2023707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023707 prefixEnd_2023707 := by exact prefixLift 2023707
  have htrace : WordTrace (prefixWord ++ tailWord_2023707) baseStart_2023707 baseEnd_2023707 := by
    simpa [prefixWord, tailWord_2023707, baseEnd_2023707] using wordTrace_append hprefix tailTrace_2023707
  have hstable : (prefixWord ++ tailWord_2023707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023707).length < 2 ^ (prefixWord ++ tailWord_2023707).sum := by decide
  have hdescent : baseEnd_2023707 < baseStart_2023707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023745 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 1, 5]
def baseStart_2023745 : Nat := 118140960795 + 2023745 * 2 ^ 59
def prefixEnd_2023745 : Nat := 4983230072969 + 3 ^ 40 * 2023745 * 2
def baseEnd_2023745 : Nat := 692769271422193214720315

theorem tailTrace_2023745 : CollatzResearch.WordTrace tailWord_2023745 prefixEnd_2023745 692769271422193214720315 := by
  unfold tailWord_2023745
  simp only [CollatzResearch.WordTrace]
  refine ⟨73812044053324967974248689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49208029368883311982832459 73812044053324967974248689)
  ·
    refine ⟨55359033039993725980686517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73812044053324967974248689 55359033039993725980686517)
    ·
      refine ⟨5189909347499411810689361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55359033039993725980686517 5189909347499411810689361)
      ·
        refine ⟨3892432010624558858017021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189909347499411810689361 3892432010624558858017021)
        ·
          refine ⟨1459662003984209571756383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3892432010624558858017021 1459662003984209571756383)
          ·
            refine ⟨2189493005976314357634575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459662003984209571756383 2189493005976314357634575)
            ·
              refine ⟨3284239508964471536451863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2189493005976314357634575 3284239508964471536451863)
              ·
                refine ⟨4926359263446707304677795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284239508964471536451863 4926359263446707304677795)
                ·
                  refine ⟨7389538895170060957016693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4926359263446707304677795 7389538895170060957016693)
                  ·
                    refine ⟨692769271422193214720315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7389538895170060957016693 692769271422193214720315)
                    ·
                      rfl

theorem cell22_2023745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_2023745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023745 prefixEnd_2023745 := by exact prefixLift 2023745
  have htrace : WordTrace (prefixWord ++ tailWord_2023745) baseStart_2023745 baseEnd_2023745 := by
    simpa [prefixWord, tailWord_2023745, baseEnd_2023745] using wordTrace_append hprefix tailTrace_2023745
  have hstable : (prefixWord ++ tailWord_2023745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023745).length < 2 ^ (prefixWord ++ tailWord_2023745).sum := by decide
  have hdescent : baseEnd_2023745 < baseStart_2023745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023756 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 3, 3]
def baseStart_2023756 : Nat := 118140960795 + 2023756 * 2 ^ 59
def prefixEnd_2023756 : Nat := 4983230072969 + 3 ^ 40 * 2023756 * 2
def baseEnd_2023756 : Nat := 692773036946992852695281

theorem tailTrace_2023756 : CollatzResearch.WordTrace tailWord_2023756 prefixEnd_2023756 692773036946992852695281 := by
  unfold tailWord_2023756
  simp only [CollatzResearch.WordTrace]
  refine ⟨36906222628142558426449561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49208296837523411235266081 36906222628142558426449561)
  ·
    refine ⟨27679666971106918819837171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36906222628142558426449561 27679666971106918819837171)
    ·
      refine ⟨41519500456660378229755757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27679666971106918819837171 41519500456660378229755757)
      ·
        refine ⟨15569812671247641836158409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41519500456660378229755757 15569812671247641836158409)
        ·
          refine ⟨11677359503435731377118807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15569812671247641836158409 11677359503435731377118807)
          ·
            refine ⟨17516039255153597065678211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677359503435731377118807 17516039255153597065678211)
            ·
              refine ⟨26274058882730395598517317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17516039255153597065678211 26274058882730395598517317)
              ·
                refine ⟨4926386040511949174721997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26274058882730395598517317 4926386040511949174721997)
                ·
                  refine ⟨1847394765191980940520749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4926386040511949174721997 1847394765191980940520749)
                  ·
                    refine ⟨692773036946992852695281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1847394765191980940520749 692773036946992852695281)
                    ·
                      rfl

theorem cell22_2023756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_2023756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023756 prefixEnd_2023756 := by exact prefixLift 2023756
  have htrace : WordTrace (prefixWord ++ tailWord_2023756) baseStart_2023756 baseEnd_2023756 := by
    simpa [prefixWord, tailWord_2023756, baseEnd_2023756] using wordTrace_append hprefix tailTrace_2023756
  have hstable : (prefixWord ++ tailWord_2023756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023756).length < 2 ^ (prefixWord ++ tailWord_2023756).sum := by decide
  have hdescent : baseEnd_2023756 < baseStart_2023756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2023786 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_2023786 : Nat := 118140960795 + 2023786 * 2 ^ 59
def prefixEnd_2023786 : Nat := 4983230072969 + 3 ^ 40 * 2023786 * 2
def baseEnd_2023786 : Nat := 230927768853360924815063

theorem tailTrace_2023786 : CollatzResearch.WordTrace tailWord_2023786 prefixEnd_2023786 230927768853360924815063 := by
  unfold tailWord_2023786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453384861544107994122803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49209026297450954650994141 18453384861544107994122803)
  ·
    refine ⟨27680077292316161991184205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18453384861544107994122803 27680077292316161991184205)
    ·
      refine ⟨10380028984618560746694077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27680077292316161991184205 10380028984618560746694077)
      ·
        refine ⟨3892510869231960280010279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10380028984618560746694077 3892510869231960280010279)
        ·
          refine ⟨5838766303847940420015419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892510869231960280010279 5838766303847940420015419)
          ·
            refine ⟨8758149455771910630023129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5838766303847940420015419 8758149455771910630023129)
            ·
              refine ⟨6568612091828932972517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8758149455771910630023129 6568612091828932972517347)
              ·
                refine ⟨9852918137743399458776021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6568612091828932972517347 9852918137743399458776021)
                ·
                  refine ⟨230927768853360924815063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9852918137743399458776021 230927768853360924815063)
                  ·
                    rfl

theorem cell22_2023786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_2023786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2023786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2023786 prefixEnd_2023786 := by exact prefixLift 2023786
  have htrace : WordTrace (prefixWord ++ tailWord_2023786) baseStart_2023786 baseEnd_2023786 := by
    simpa [prefixWord, tailWord_2023786, baseEnd_2023786] using wordTrace_append hprefix tailTrace_2023786
  have hstable : (prefixWord ++ tailWord_2023786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2023786).length < 2 ^ (prefixWord ++ tailWord_2023786).sum := by decide
  have hdescent : baseEnd_2023786 < baseStart_2023786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2023786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
