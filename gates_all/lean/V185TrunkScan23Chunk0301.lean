import V185TrunkScan23Chunk0300

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1780217 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 2, 4]
def baseStart_1780217 : Nat := 118140960795 + 1780217 * 2 ^ 59
def prefixEnd_1780217 : Nat := 4983230072969 + 3 ^ 40 * 1780217 * 2
def baseEnd_1780217 : Nat := 304702330101722208833479

theorem tailTrace_1780217 : CollatzResearch.WordTrace tailWord_1780217 prefixEnd_1780217 304702330101722208833479 := by
  unfold tailWord_1780217
  simp only [CollatzResearch.WordTrace]
  refine ⟨64929848191585320703098905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43286565461056880468732603 64929848191585320703098905)
  ·
    refine ⟨48697386143688990527324179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64929848191585320703098905 48697386143688990527324179)
    ·
      refine ⟨73046079215533485790986269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48697386143688990527324179 73046079215533485790986269)
      ·
        refine ⟨27392279705825057171619851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73046079215533485790986269 27392279705825057171619851)
        ·
          refine ⟨41088419558737585757429777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27392279705825057171619851 41088419558737585757429777)
          ·
            refine ⟨30816314669053189318072333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41088419558737585757429777 30816314669053189318072333)
            ·
              refine ⟨11556118000894945994277125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30816314669053189318072333 11556118000894945994277125)
              ·
                refine ⟨2166772125167802373926961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11556118000894945994277125 2166772125167802373926961)
                ·
                  refine ⟨1625079093875851780445221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166772125167802373926961 1625079093875851780445221)
                  ·
                    refine ⟨304702330101722208833479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1625079093875851780445221 304702330101722208833479)
                    ·
                      rfl

theorem cell23_1780217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_1780217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780217 prefixEnd_1780217 := by exact prefixLift 1780217
  have htrace : WordTrace (prefixWord ++ tailWord_1780217) baseStart_1780217 baseEnd_1780217 := by
    simpa [prefixWord, tailWord_1780217, baseEnd_1780217] using wordTrace_append hprefix tailTrace_1780217
  have hstable : (prefixWord ++ tailWord_1780217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780217).length < 2 ^ (prefixWord ++ tailWord_1780217).sum := by decide
  have hdescent : baseEnd_1780217 < baseStart_1780217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780220 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_1780220 : Nat := 118140960795 + 1780220 * 2 ^ 59
def prefixEnd_1780220 : Nat := 4983230072969 + 3 ^ 40 * 1780220 * 2
def baseEnd_1780220 : Nat := 914108530747130114762923

theorem tailTrace_1780220 : CollatzResearch.WordTrace tailWord_1780220 prefixEnd_1780220 914108530747130114762923 := by
  unfold tailWord_1780220
  simp only [CollatzResearch.WordTrace]
  refine ⟨32464978805287226107729057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43286638407049634810305409 32464978805287226107729057)
  ·
    refine ⟨24348734103965419580796793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32464978805287226107729057 24348734103965419580796793)
    ·
      refine ⟨18261550577974064685597595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24348734103965419580796793 18261550577974064685597595)
      ·
        refine ⟨27392325866961097028396393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18261550577974064685597595 27392325866961097028396393)
        ·
          refine ⟨20544244400220822771297295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27392325866961097028396393 20544244400220822771297295)
          ·
            refine ⟨30816366600331234156945943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20544244400220822771297295 30816366600331234156945943)
            ·
              refine ⟨46224549900496851235418915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30816366600331234156945943 46224549900496851235418915)
              ·
                refine ⟨69336824850745276853128373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46224549900496851235418915 69336824850745276853128373)
                ·
                  refine ⟨6500327329757369704980785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69336824850745276853128373 6500327329757369704980785)
                  ·
                    refine ⟨4875245497318027278735589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6500327329757369704980785 4875245497318027278735589)
                    ·
                      refine ⟨914108530747130114762923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4875245497318027278735589 914108530747130114762923)
                      ·
                        rfl

theorem cell23_1780220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_1780220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780220 prefixEnd_1780220 := by exact prefixLift 1780220
  have htrace : WordTrace (prefixWord ++ tailWord_1780220) baseStart_1780220 baseEnd_1780220 := by
    simpa [prefixWord, tailWord_1780220, baseEnd_1780220] using wordTrace_append hprefix tailTrace_1780220
  have hstable : (prefixWord ++ tailWord_1780220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780220).length < 2 ^ (prefixWord ++ tailWord_1780220).sum := by decide
  have hdescent : baseEnd_1780220 < baseStart_1780220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780257 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1780257 : Nat := 118140960795 + 1780257 * 2 ^ 59
def prefixEnd_1780257 : Nat := 4983230072969 + 3 ^ 40 * 1780257 * 2
def baseEnd_1780257 : Nat := 914127529531346470000253

theorem tailTrace_1780257 : CollatzResearch.WordTrace tailWord_1780257 prefixEnd_1780257 914127529531346470000253 := by
  unfold tailWord_1780257
  simp only [CollatzResearch.WordTrace]
  refine ⟨64931307111440407534555025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43287538074293605023036683 64931307111440407534555025)
  ·
    refine ⟨48698480333580305650916269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64931307111440407534555025 48698480333580305650916269)
    ·
      refine ⟨18261930125092614619093601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48698480333580305650916269 18261930125092614619093601)
      ·
        refine ⟨13696447593819460964320201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18261930125092614619093601 13696447593819460964320201)
        ·
          refine ⟨10272335695364595723240151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13696447593819460964320201 10272335695364595723240151)
          ·
            refine ⟨15408503543046893584860227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10272335695364595723240151 15408503543046893584860227)
            ·
              refine ⟨23112755314570340377290341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15408503543046893584860227 23112755314570340377290341)
              ·
                refine ⟨4333641621481938820741939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23112755314570340377290341 4333641621481938820741939)
                ·
                  refine ⟨6500462432222908231112909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4333641621481938820741939 6500462432222908231112909)
                  ·
                    refine ⟨2437673412083590586667341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6500462432222908231112909 2437673412083590586667341)
                    ·
                      refine ⟨914127529531346470000253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2437673412083590586667341 914127529531346470000253)
                      ·
                        rfl

theorem cell23_1780257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1780257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780257 prefixEnd_1780257 := by exact prefixLift 1780257
  have htrace : WordTrace (prefixWord ++ tailWord_1780257) baseStart_1780257 baseEnd_1780257 := by
    simpa [prefixWord, tailWord_1780257, baseEnd_1780257] using wordTrace_append hprefix tailTrace_1780257
  have hstable : (prefixWord ++ tailWord_1780257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780257).length < 2 ^ (prefixWord ++ tailWord_1780257).sum := by decide
  have hdescent : baseEnd_1780257 < baseStart_1780257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780320 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 9]
def baseStart_1780320 : Nat := 118140960795 + 1780320 * 2 ^ 59
def prefixEnd_1780320 : Nat := 4983230072969 + 3 ^ 40 * 1780320 * 2
def baseEnd_1780320 : Nat := 101573319868064413723607

theorem tailTrace_1780320 : CollatzResearch.WordTrace tailWord_1780320 prefixEnd_1780320 101573319868064413723607 := by
  unfold tailWord_1780320
  simp only [CollatzResearch.WordTrace]
  refine ⟨32466802455106084647049207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43289069940141446196065609 32466802455106084647049207)
  ·
    refine ⟨48700203682659126970573811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32466802455106084647049207 48700203682659126970573811)
    ·
      refine ⟨73050305523988690455860717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48700203682659126970573811 73050305523988690455860717)
      ·
        refine ⟨27393864571495758920947769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73050305523988690455860717 27393864571495758920947769)
        ·
          refine ⟨20545398428621819190710827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27393864571495758920947769 20545398428621819190710827)
          ·
            refine ⟨30818097642932728786066241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20545398428621819190710827 30818097642932728786066241)
            ·
              refine ⟨23113573232199546589549681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30818097642932728786066241 23113573232199546589549681)
              ·
                refine ⟨17335179924149659942162261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23113573232199546589549681 17335179924149659942162261)
                ·
                  refine ⟨101573319868064413723607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17335179924149659942162261 101573319868064413723607)
                  ·
                    rfl

theorem cell23_1780320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_1780320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780320 prefixEnd_1780320 := by exact prefixLift 1780320
  have htrace : WordTrace (prefixWord ++ tailWord_1780320) baseStart_1780320 baseEnd_1780320 := by
    simpa [prefixWord, tailWord_1780320, baseEnd_1780320] using wordTrace_append hprefix tailTrace_1780320
  have hstable : (prefixWord ++ tailWord_1780320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780320).length < 2 ^ (prefixWord ++ tailWord_1780320).sum := by decide
  have hdescent : baseEnd_1780320 < baseStart_1780320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780342 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3]
def baseStart_1780342 : Nat := 118140960795 + 1780342 * 2 ^ 59
def prefixEnd_1780342 : Nat := 4983230072969 + 3 ^ 40 * 1780342 * 2
def baseEnd_1780342 : Nat := 914171175386978637437363

theorem tailTrace_1780342 : CollatzResearch.WordTrace tailWord_1780342 prefixEnd_1780342 914171175386978637437363 := by
  unfold tailWord_1780342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4058400457258279190712455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43289604877421644700932853 4058400457258279190712455)
  ·
    refine ⟨6087600685887418786068683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4058400457258279190712455 6087600685887418786068683)
    ·
      refine ⟨9131401028831128179103025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087600685887418786068683 9131401028831128179103025)
      ·
        refine ⟨6848550771623346134327269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9131401028831128179103025 6848550771623346134327269)
        ·
          refine ⟨1284103269679377400186363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6848550771623346134327269 1284103269679377400186363)
          ·
            refine ⟨1926154904519066100279545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284103269679377400186363 1926154904519066100279545)
            ·
              refine ⟨1444616178389299575209659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1926154904519066100279545 1444616178389299575209659)
              ·
                refine ⟨2166924267583949362814489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444616178389299575209659 2166924267583949362814489)
                ·
                  refine ⟨1625193200687962022110867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166924267583949362814489 1625193200687962022110867)
                  ·
                    refine ⟨2437789801031943033166301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1625193200687962022110867 2437789801031943033166301)
                    ·
                      refine ⟨914171175386978637437363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2437789801031943033166301 914171175386978637437363)
                      ·
                        rfl

theorem cell23_1780342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_1780342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780342 prefixEnd_1780342 := by exact prefixLift 1780342
  have htrace : WordTrace (prefixWord ++ tailWord_1780342) baseStart_1780342 baseEnd_1780342 := by
    simpa [prefixWord, tailWord_1780342, baseEnd_1780342] using wordTrace_append hprefix tailTrace_1780342
  have hstable : (prefixWord ++ tailWord_1780342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780342).length < 2 ^ (prefixWord ++ tailWord_1780342).sum := by decide
  have hdescent : baseEnd_1780342 < baseStart_1780342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780348 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_1780348 : Nat := 118140960795 + 1780348 * 2 ^ 59
def prefixEnd_1780348 : Nat := 4983230072969 + 3 ^ 40 * 1780348 * 2
def baseEnd_1780348 : Nat := 914174256270905613962335

theorem tailTrace_1780348 : CollatzResearch.WordTrace tailWord_1780348 prefixEnd_1780348 914174256270905613962335 := by
  unfold tailWord_1780348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32467313077055365038058849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43289750769407153384078465 32467313077055365038058849)
  ·
    refine ⟨24350484807791523778544137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32467313077055365038058849 24350484807791523778544137)
    ·
      refine ⟨18262863605843642833908103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24350484807791523778544137 18262863605843642833908103)
      ·
        refine ⟨27394295408765464250862155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18262863605843642833908103 27394295408765464250862155)
        ·
          refine ⟨41091443113148196376293233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27394295408765464250862155 41091443113148196376293233)
          ·
            refine ⟨30818582334861147282219925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41091443113148196376293233 30818582334861147282219925)
            ·
              refine ⟨1444621046946616278854059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30818582334861147282219925 1444621046946616278854059)
              ·
                refine ⟨2166931570419924418281089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444621046946616278854059 2166931570419924418281089)
                ·
                  refine ⟨1625198677814943313710817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2166931570419924418281089 1625198677814943313710817)
                  ·
                    refine ⟨1218899008361207485283113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1625198677814943313710817 1218899008361207485283113)
                    ·
                      refine ⟨914174256270905613962335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218899008361207485283113 914174256270905613962335)
                      ·
                        rfl

theorem cell23_1780348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_1780348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780348 prefixEnd_1780348 := by exact prefixLift 1780348
  have htrace : WordTrace (prefixWord ++ tailWord_1780348) baseStart_1780348 baseEnd_1780348 := by
    simpa [prefixWord, tailWord_1780348, baseEnd_1780348] using wordTrace_append hprefix tailTrace_1780348
  have hstable : (prefixWord ++ tailWord_1780348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780348).length < 2 ^ (prefixWord ++ tailWord_1780348).sum := by decide
  have hdescent : baseEnd_1780348 < baseStart_1780348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780387 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1780387 : Nat := 118140960795 + 1780387 * 2 ^ 59
def prefixEnd_1780387 : Nat := 4983230072969 + 3 ^ 40 * 1780387 * 2
def baseEnd_1780387 : Nat := 914194282016430961374655

theorem tailTrace_1780387 : CollatzResearch.WordTrace tailWord_1780387 prefixEnd_1780387 914194282016430961374655 := by
  unfold tailWord_1780387
  simp only [CollatzResearch.WordTrace]
  refine ⟨64936048600969439736787415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43290699067312959824524943 64936048600969439736787415)
  ·
    refine ⟨97404072901454159605181123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64936048600969439736787415 97404072901454159605181123)
    ·
      refine ⟨146106109352181239407771685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97404072901454159605181123 146106109352181239407771685)
      ·
        refine ⟨27394895503533982388957191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146106109352181239407771685 27394895503533982388957191)
        ·
          refine ⟨41092343255300973583435787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27394895503533982388957191 41092343255300973583435787)
          ·
            refine ⟨61638514882951460375153681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41092343255300973583435787 61638514882951460375153681)
            ·
              refine ⟨46228886162213595281365261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61638514882951460375153681 46228886162213595281365261)
              ·
                refine ⟨17335832310830098230511973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46228886162213595281365261 17335832310830098230511973)
                ·
                  refine ⟨3250468558280643418220995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17335832310830098230511973 3250468558280643418220995)
                  ·
                    refine ⟨4875702837420965127331493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250468558280643418220995 4875702837420965127331493)
                    ·
                      refine ⟨914194282016430961374655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4875702837420965127331493 914194282016430961374655)
                      ·
                        rfl

theorem cell23_1780387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1780387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780387 prefixEnd_1780387 := by exact prefixLift 1780387
  have htrace : WordTrace (prefixWord ++ tailWord_1780387) baseStart_1780387 baseEnd_1780387 := by
    simpa [prefixWord, tailWord_1780387, baseEnd_1780387] using wordTrace_append hprefix tailTrace_1780387
  have hstable : (prefixWord ++ tailWord_1780387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780387).length < 2 ^ (prefixWord ++ tailWord_1780387).sum := by decide
  have hdescent : baseEnd_1780387 < baseStart_1780387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780424 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_1780424 : Nat := 118140960795 + 1780424 * 2 ^ 59
def prefixEnd_1780424 : Nat := 4983230072969 + 3 ^ 40 * 1780424 * 2
def baseEnd_1780424 : Nat := 914213280800647316611985

theorem tailTrace_1780424 : CollatzResearch.WordTrace tailWord_1780424 prefixEnd_1780424 914213280800647316611985 := by
  unfold tailWord_1780424
  simp only [CollatzResearch.WordTrace]
  refine ⟨32468699050917697527942163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43291598734556930037256217 32468699050917697527942163)
  ·
    refine ⟨48703048576376546291913245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32468699050917697527942163 48703048576376546291913245)
    ·
      refine ⟨18263643216141204859467467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48703048576376546291913245 18263643216141204859467467)
      ·
        refine ⟨27395464824211807289201201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18263643216141204859467467 27395464824211807289201201)
        ·
          refine ⟨20546598618158855466900901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27395464824211807289201201 20546598618158855466900901)
          ·
            refine ⟨3852487240904785400043919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20546598618158855466900901 3852487240904785400043919)
            ·
              refine ⟨5778730861357178100065879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852487240904785400043919 5778730861357178100065879)
              ·
                refine ⟨8668096292035767150098819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5778730861357178100065879 8668096292035767150098819)
                ·
                  refine ⟨13002144438053650725148229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8668096292035767150098819 13002144438053650725148229)
                  ·
                    refine ⟨2437902082135059510965293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13002144438053650725148229 2437902082135059510965293)
                    ·
                      refine ⟨914213280800647316611985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2437902082135059510965293 914213280800647316611985)
                      ·
                        rfl

theorem cell23_1780424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_1780424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780424 prefixEnd_1780424 := by exact prefixLift 1780424
  have htrace : WordTrace (prefixWord ++ tailWord_1780424) baseStart_1780424 baseEnd_1780424 := by
    simpa [prefixWord, tailWord_1780424, baseEnd_1780424] using wordTrace_append hprefix tailTrace_1780424
  have hstable : (prefixWord ++ tailWord_1780424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780424).length < 2 ^ (prefixWord ++ tailWord_1780424).sum := by decide
  have hdescent : baseEnd_1780424 < baseStart_1780424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780447 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1780447 : Nat := 118140960795 + 1780447 * 2 ^ 59
def prefixEnd_1780447 : Nat := 4983230072969 + 3 ^ 40 * 1780447 * 2
def baseEnd_1780447 : Nat := 914225090855700726624379

theorem tailTrace_1780447 : CollatzResearch.WordTrace tailWord_1780447 prefixEnd_1780447 914225090855700726624379 := by
  unfold tailWord_1780447
  simp only [CollatzResearch.WordTrace]
  refine ⟨64938236980752069983971595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43292157987168046655981063 64938236980752069983971595)
  ·
    refine ⟨97407355471128104975957393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64938236980752069983971595 97407355471128104975957393)
    ·
      refine ⟨73055516603346078731968045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97407355471128104975957393 73055516603346078731968045)
      ·
        refine ⟨27395818726254779524488017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73055516603346078731968045 27395818726254779524488017)
        ·
          refine ⟨20546864044691084643366013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27395818726254779524488017 20546864044691084643366013)
          ·
            refine ⟨7705074016759156741262255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20546864044691084643366013 7705074016759156741262255)
            ·
              refine ⟨11557611025138735111893383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7705074016759156741262255 11557611025138735111893383)
              ·
                refine ⟨17336416537708102667840075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11557611025138735111893383 17336416537708102667840075)
                ·
                  refine ⟨26004624806562154001760113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17336416537708102667840075 26004624806562154001760113)
                  ·
                    refine ⟨19503468604921615501320085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26004624806562154001760113 19503468604921615501320085)
                    ·
                      refine ⟨914225090855700726624379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19503468604921615501320085 914225090855700726624379)
                      ·
                        rfl

theorem cell23_1780447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1780447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780447 prefixEnd_1780447 := by exact prefixLift 1780447
  have htrace : WordTrace (prefixWord ++ tailWord_1780447) baseStart_1780447 baseEnd_1780447 := by
    simpa [prefixWord, tailWord_1780447, baseEnd_1780447] using wordTrace_append hprefix tailTrace_1780447
  have hstable : (prefixWord ++ tailWord_1780447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780447).length < 2 ^ (prefixWord ++ tailWord_1780447).sum := by decide
  have hdescent : baseEnd_1780447 < baseStart_1780447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780457 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 5, 5]
def baseStart_1780457 : Nat := 118140960795 + 1780457 * 2 ^ 59
def prefixEnd_1780457 : Nat := 4983230072969 + 3 ^ 40 * 1780457 * 2
def baseEnd_1780457 : Nat := 304743408554081895833111

theorem tailTrace_1780457 : CollatzResearch.WordTrace tailWord_1780457 prefixEnd_1780457 304743408554081895833111 := by
  unfold tailWord_1780457
  simp only [CollatzResearch.WordTrace]
  refine ⟨64938601710715841691835625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43292401140477227794557083 64938601710715841691835625)
  ·
    refine ⟨48703951283036881268876719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64938601710715841691835625 48703951283036881268876719)
    ·
      refine ⟨73055926924555321903315079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48703951283036881268876719 73055926924555321903315079)
      ·
        refine ⟨109583890386832982854972619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73055926924555321903315079 109583890386832982854972619)
        ·
          refine ⟨164375835580249474282458929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109583890386832982854972619 164375835580249474282458929)
          ·
            refine ⟨123281876685187105711844197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164375835580249474282458929 123281876685187105711844197)
            ·
              refine ⟨23115351878472582320970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123281876685187105711844197 23115351878472582320970787)
              ·
                refine ⟨34673027817708873481456181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23115351878472582320970787 34673027817708873481456181)
                ·
                  refine ⟨3250596357910206888886517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34673027817708873481456181 3250596357910206888886517)
                  ·
                    refine ⟨304743408554081895833111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3250596357910206888886517 304743408554081895833111)
                    ·
                      rfl

theorem cell23_1780457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_1780457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780457 prefixEnd_1780457 := by exact prefixLift 1780457
  have htrace : WordTrace (prefixWord ++ tailWord_1780457) baseStart_1780457 baseEnd_1780457 := by
    simpa [prefixWord, tailWord_1780457, baseEnd_1780457] using wordTrace_append hprefix tailTrace_1780457
  have hstable : (prefixWord ++ tailWord_1780457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780457).length < 2 ^ (prefixWord ++ tailWord_1780457).sum := by decide
  have hdescent : baseEnd_1780457 < baseStart_1780457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780461 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1780461 : Nat := 118140960795 + 1780461 * 2 ^ 59
def prefixEnd_1780461 : Nat := 4983230072969 + 3 ^ 40 * 1780461 * 2
def baseEnd_1780461 : Nat := 101581364398318185761035

theorem tailTrace_1780461 : CollatzResearch.WordTrace tailWord_1780461 prefixEnd_1780461 101581364398318185761035 := by
  unfold tailWord_1780461
  simp only [CollatzResearch.WordTrace]
  refine ⟨64938747602701350374981237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43292498401800900249987491 64938747602701350374981237)
  ·
    refine ⟨6088007587753251597654491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64938747602701350374981237 6088007587753251597654491)
    ·
      refine ⟨9132011381629877396481737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6088007587753251597654491 9132011381629877396481737)
      ·
        refine ⟨6849008536222408047361303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9132011381629877396481737 6849008536222408047361303)
        ·
          refine ⟨10273512804333612071041955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6849008536222408047361303 10273512804333612071041955)
          ·
            refine ⟨15410269206500418106562933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10273512804333612071041955 15410269206500418106562933)
            ·
              refine ⟨1444712738109414197490275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15410269206500418106562933 1444712738109414197490275)
              ·
                refine ⟨2167069107164121296235413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444712738109414197490275 2167069107164121296235413)
                ·
                  refine ⟨101581364398318185761035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2167069107164121296235413 101581364398318185761035)
                  ·
                    rfl

theorem cell23_1780461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1780461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780461 prefixEnd_1780461 := by exact prefixLift 1780461
  have htrace : WordTrace (prefixWord ++ tailWord_1780461) baseStart_1780461 baseEnd_1780461 := by
    simpa [prefixWord, tailWord_1780461, baseEnd_1780461] using wordTrace_append hprefix tailTrace_1780461
  have hstable : (prefixWord ++ tailWord_1780461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780461).length < 2 ^ (prefixWord ++ tailWord_1780461).sum := by decide
  have hdescent : baseEnd_1780461 < baseStart_1780461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780464 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2]
def baseStart_1780464 : Nat := 118140960795 + 1780464 * 2 ^ 59
def prefixEnd_1780464 : Nat := 4983230072969 + 3 ^ 40 * 1780464 * 2
def baseEnd_1780464 : Nat := 914233820026827160111801

theorem tailTrace_1780464 : CollatzResearch.WordTrace tailWord_1780464 prefixEnd_1780464 914233820026827160111801 := by
  unfold tailWord_1780464
  simp only [CollatzResearch.WordTrace]
  refine ⟨32469428510845240943670223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43292571347793654591560297 32469428510845240943670223)
  ·
    refine ⟨48704142766267861415505335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32469428510845240943670223 48704142766267861415505335)
    ·
      refine ⟨73056214149401792123258003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48704142766267861415505335 73056214149401792123258003)
      ·
        refine ⟨109584321224102688184887005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73056214149401792123258003 109584321224102688184887005)
        ·
          refine ⟨41094120459038508069332627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109584321224102688184887005 41094120459038508069332627)
          ·
            refine ⟨61641180688557762103998941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41094120459038508069332627 61641180688557762103998941)
            ·
              refine ⟨23115442758209160788999603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61641180688557762103998941 23115442758209160788999603)
              ·
                refine ⟨34673164137313741183499405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23115442758209160788999603 34673164137313741183499405)
                ·
                  refine ⟨13002436551492652943812277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34673164137313741183499405 13002436551492652943812277)
                  ·
                    refine ⟨1218978426702436213482401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13002436551492652943812277 1218978426702436213482401)
                    ·
                      refine ⟨914233820026827160111801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218978426702436213482401 914233820026827160111801)
                      ·
                        rfl

theorem cell23_1780464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2].length) (baseStart_1780464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780464 prefixEnd_1780464 := by exact prefixLift 1780464
  have htrace : WordTrace (prefixWord ++ tailWord_1780464) baseStart_1780464 baseEnd_1780464 := by
    simpa [prefixWord, tailWord_1780464, baseEnd_1780464] using wordTrace_append hprefix tailTrace_1780464
  have hstable : (prefixWord ++ tailWord_1780464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780464).length < 2 ^ (prefixWord ++ tailWord_1780464).sum := by decide
  have hdescent : baseEnd_1780464 < baseStart_1780464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780474 : List Nat := [3, 1, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_1780474 : Nat := 118140960795 + 1780474 * 2 ^ 59
def prefixEnd_1780474 : Nat := 4983230072969 + 3 ^ 40 * 1780474 * 2
def baseEnd_1780474 : Nat := 304746318277790706995585

theorem tailTrace_1780474 : CollatzResearch.WordTrace tailWord_1780474 prefixEnd_1780474 304746318277790706995585 := by
  unfold tailWord_1780474
  simp only [CollatzResearch.WordTrace]
  refine ⟨16234805437913563398801119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43292814501102835730136317 16234805437913563398801119)
  ·
    refine ⟨24352208156870345098201679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16234805437913563398801119 24352208156870345098201679)
    ·
      refine ⟨36528312235305517647302519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24352208156870345098201679 36528312235305517647302519)
      ·
        refine ⟨54792468352958276470953779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36528312235305517647302519 54792468352958276470953779)
        ·
          refine ⟨82188702529437414706430669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54792468352958276470953779 82188702529437414706430669)
          ·
            refine ⟨30820763448539030514911501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82188702529437414706430669 30820763448539030514911501)
            ·
              refine ⟨11557786293202136443091813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30820763448539030514911501 11557786293202136443091813)
              ·
                refine ⟨2167084929975400583079715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11557786293202136443091813 2167084929975400583079715)
                ·
                  refine ⟨3250627394963100874619573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167084929975400583079715 3250627394963100874619573)
                  ·
                    refine ⟨304746318277790706995585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3250627394963100874619573 304746318277790706995585)
                    ·
                      rfl

theorem cell23_1780474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_1780474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780474 prefixEnd_1780474 := by exact prefixLift 1780474
  have htrace : WordTrace (prefixWord ++ tailWord_1780474) baseStart_1780474 baseEnd_1780474 := by
    simpa [prefixWord, tailWord_1780474, baseEnd_1780474] using wordTrace_append hprefix tailTrace_1780474
  have hstable : (prefixWord ++ tailWord_1780474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780474).length < 2 ^ (prefixWord ++ tailWord_1780474).sum := by decide
  have hdescent : baseEnd_1780474 < baseStart_1780474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780481 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_1780481 : Nat := 118140960795 + 1780481 * 2 ^ 59
def prefixEnd_1780481 : Nat := 4983230072969 + 3 ^ 40 * 1780481 * 2
def baseEnd_1780481 : Nat := 914242549197953593599223

theorem tailTrace_1780481 : CollatzResearch.WordTrace tailWord_1780481 prefixEnd_1780481 914242549197953593599223 := by
  unfold tailWord_1780481
  simp only [CollatzResearch.WordTrace]
  refine ⟨64939477062628893790709297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43292984708419262527139531 64939477062628893790709297)
  ·
    refine ⟨48704607796971670343031973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64939477062628893790709297 48704607796971670343031973)
    ·
      refine ⟨9132113961932188189318495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48704607796971670343031973 9132113961932188189318495)
      ·
        refine ⟨13698170942898282283977743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9132113961932188189318495 13698170942898282283977743)
        ·
          refine ⟨20547256414347423425966615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13698170942898282283977743 20547256414347423425966615)
          ·
            refine ⟨30820884621521135138949923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20547256414347423425966615 30820884621521135138949923)
            ·
              refine ⟨46231326932281702708424885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30820884621521135138949923 46231326932281702708424885)
              ·
                refine ⟨4334186899901409628914833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46231326932281702708424885 4334186899901409628914833)
                ·
                  refine ⟨3250640174926057221686125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4334186899901409628914833 3250640174926057221686125)
                  ·
                    refine ⟨1218990065597271458132297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250640174926057221686125 1218990065597271458132297)
                    ·
                      refine ⟨914242549197953593599223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1218990065597271458132297 914242549197953593599223)
                      ·
                        rfl

theorem cell23_1780481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_1780481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780481 prefixEnd_1780481 := by exact prefixLift 1780481
  have htrace : WordTrace (prefixWord ++ tailWord_1780481) baseStart_1780481 baseEnd_1780481 := by
    simpa [prefixWord, tailWord_1780481, baseEnd_1780481] using wordTrace_append hprefix tailTrace_1780481
  have hstable : (prefixWord ++ tailWord_1780481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780481).length < 2 ^ (prefixWord ++ tailWord_1780481).sum := by decide
  have hdescent : baseEnd_1780481 < baseStart_1780481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780494 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1780494 : Nat := 118140960795 + 1780494 * 2 ^ 59
def prefixEnd_1780494 : Nat := 4983230072969 + 3 ^ 40 * 1780494 * 2
def baseEnd_1780494 : Nat := 914249224446462042736663

theorem tailTrace_1780494 : CollatzResearch.WordTrace tailWord_1780494 prefixEnd_1780494 914249224446462042736663 := by
  unfold tailWord_1780494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117493901447724626366567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43293300807721198007288357 8117493901447724626366567)
  ·
    refine ⟨12176240852171586939549851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8117493901447724626366567 12176240852171586939549851)
    ·
      refine ⟨18264361278257380409324777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176240852171586939549851 18264361278257380409324777)
      ·
        refine ⟨13698270958693035306993583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18264361278257380409324777 13698270958693035306993583)
        ·
          refine ⟨20547406438039552960490375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13698270958693035306993583 20547406438039552960490375)
          ·
            refine ⟨30821109657059329440735563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20547406438039552960490375 30821109657059329440735563)
            ·
              refine ⟨46231664485588994161103345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30821109657059329440735563 46231664485588994161103345)
              ·
                refine ⟨34673748364191745620827509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46231664485588994161103345 34673748364191745620827509)
                ·
                  refine ⟨3250663909142976151952579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34673748364191745620827509 3250663909142976151952579)
                  ·
                    refine ⟨4875995863714464227928869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3250663909142976151952579 4875995863714464227928869)
                    ·
                      refine ⟨914249224446462042736663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4875995863714464227928869 914249224446462042736663)
                      ·
                        rfl

theorem cell23_1780494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1780494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780494 prefixEnd_1780494 := by exact prefixLift 1780494
  have htrace : WordTrace (prefixWord ++ tailWord_1780494) baseStart_1780494 baseEnd_1780494 := by
    simpa [prefixWord, tailWord_1780494, baseEnd_1780494] using wordTrace_append hprefix tailTrace_1780494
  have hstable : (prefixWord ++ tailWord_1780494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780494).length < 2 ^ (prefixWord ++ tailWord_1780494).sum := by decide
  have hdescent : baseEnd_1780494 < baseStart_1780494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780507 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_1780507 : Nat := 118140960795 + 1780507 * 2 ^ 59
def prefixEnd_1780507 : Nat := 4983230072969 + 3 ^ 40 * 1780507 * 2
def baseEnd_1780507 : Nat := 914255899694970491874103

theorem tailTrace_1780507 : CollatzResearch.WordTrace tailWord_1780507 prefixEnd_1780507 914255899694970491874103 := by
  unfold tailWord_1780507
  simp only [CollatzResearch.WordTrace]
  refine ⟨64940425360534700231155775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43293616907023133487437183 64940425360534700231155775)
  ·
    refine ⟨97410638040802050346733663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64940425360534700231155775 97410638040802050346733663)
    ·
      refine ⟨146115957061203075520100495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97410638040802050346733663 146115957061203075520100495)
      ·
        refine ⟨219173935591804613280150743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146115957061203075520100495 219173935591804613280150743)
        ·
          refine ⟨328760903387706919920226115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219173935591804613280150743 328760903387706919920226115)
          ·
            refine ⟨493141355081560379880339173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328760903387706919920226115 493141355081560379880339173)
            ·
              refine ⟨92464004077792571227563595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 493141355081560379880339173 92464004077792571227563595)
              ·
                refine ⟨138696006116688856841345393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92464004077792571227563595 138696006116688856841345393)
                ·
                  refine ⟨104022004587516642631009045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 138696006116688856841345393 104022004587516642631009045)
                  ·
                    refine ⟨4876031465039842623328549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104022004587516642631009045 4876031465039842623328549)
                    ·
                      refine ⟨914255899694970491874103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4876031465039842623328549 914255899694970491874103)
                      ·
                        rfl

theorem cell23_1780507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_1780507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780507 prefixEnd_1780507 := by exact prefixLift 1780507
  have htrace : WordTrace (prefixWord ++ tailWord_1780507) baseStart_1780507 baseEnd_1780507 := by
    simpa [prefixWord, tailWord_1780507, baseEnd_1780507] using wordTrace_append hprefix tailTrace_1780507
  have hstable : (prefixWord ++ tailWord_1780507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780507).length < 2 ^ (prefixWord ++ tailWord_1780507).sum := by decide
  have hdescent : baseEnd_1780507 < baseStart_1780507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780524 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1780524 : Nat := 118140960795 + 1780524 * 2 ^ 59
def prefixEnd_1780524 : Nat := 4983230072969 + 3 ^ 40 * 1780524 * 2
def baseEnd_1780524 : Nat := 914264628866096925361525

theorem tailTrace_1780524 : CollatzResearch.WordTrace tailWord_1780524 prefixEnd_1780524 914264628866096925361525 := by
  unfold tailWord_1780524
  simp only [CollatzResearch.WordTrace]
  refine ⟨32470522700736556067262313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43294030267648741423016417 32470522700736556067262313)
  ·
    refine ⟨24352892025552417050446735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32470522700736556067262313 24352892025552417050446735)
    ·
      refine ⟨36529338038328625575670103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24352892025552417050446735 36529338038328625575670103)
      ·
        refine ⟨54794007057492938363505155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36529338038328625575670103 54794007057492938363505155)
        ·
          refine ⟨82191010586239407545257733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54794007057492938363505155 82191010586239407545257733)
          ·
            refine ⟨15410814484919888914735825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82191010586239407545257733 15410814484919888914735825)
            ·
              refine ⟨11558110863689916686051869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15410814484919888914735825 11558110863689916686051869)
              ·
                refine ⟨4334291573883718757269451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11558110863689916686051869 4334291573883718757269451)
                ·
                  refine ⟨6501437360825578135904177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4334291573883718757269451 6501437360825578135904177)
                  ·
                    refine ⟨4876078020619183601928133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6501437360825578135904177 4876078020619183601928133)
                    ·
                      refine ⟨914264628866096925361525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4876078020619183601928133 914264628866096925361525)
                      ·
                        rfl

theorem cell23_1780524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1780524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780524 prefixEnd_1780524 := by exact prefixLift 1780524
  have htrace : WordTrace (prefixWord ++ tailWord_1780524) baseStart_1780524 baseEnd_1780524 := by
    simpa [prefixWord, tailWord_1780524, baseEnd_1780524] using wordTrace_append hprefix tailTrace_1780524
  have hstable : (prefixWord ++ tailWord_1780524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780524).length < 2 ^ (prefixWord ++ tailWord_1780524).sum := by decide
  have hdescent : baseEnd_1780524 < baseStart_1780524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780531 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3]
def baseStart_1780531 : Nat := 118140960795 + 1780531 * 2 ^ 59
def prefixEnd_1780531 : Nat := 4983230072969 + 3 ^ 40 * 1780531 * 2
def baseEnd_1780531 : Nat := 914268223230678397973993

theorem tailTrace_1780531 : CollatzResearch.WordTrace tailWord_1780531 prefixEnd_1780531 914268223230678397973993 := by
  unfold tailWord_1780531
  simp only [CollatzResearch.WordTrace]
  refine ⟨64941300712447752330029447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43294200474965168220019631 64941300712447752330029447)
  ·
    refine ⟨97411951068671628495044171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64941300712447752330029447 97411951068671628495044171)
    ·
      refine ⟨146117926603007442742566257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97411951068671628495044171 146117926603007442742566257)
      ·
        refine ⟨109588444952255582056924693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146117926603007442742566257 109588444952255582056924693)
        ·
          refine ⟨5136958357136980408918345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109588444952255582056924693 5136958357136980408918345)
          ·
            refine ⟨3852718767852735306688759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5136958357136980408918345 3852718767852735306688759)
            ·
              refine ⟨5779078151779102960033139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3852718767852735306688759 5779078151779102960033139)
              ·
                refine ⟨8668617227668654440049709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779078151779102960033139 8668617227668654440049709)
                ·
                  refine ⟨3250731460375745415018641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8668617227668654440049709 3250731460375745415018641)
                  ·
                    refine ⟨2438048595281809061263981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3250731460375745415018641 2438048595281809061263981)
                    ·
                      refine ⟨914268223230678397973993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2438048595281809061263981 914268223230678397973993)
                      ·
                        rfl

theorem cell23_1780531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_1780531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780531 prefixEnd_1780531 := by exact prefixLift 1780531
  have htrace : WordTrace (prefixWord ++ tailWord_1780531) baseStart_1780531 baseEnd_1780531 := by
    simpa [prefixWord, tailWord_1780531, baseEnd_1780531] using wordTrace_append hprefix tailTrace_1780531
  have hstable : (prefixWord ++ tailWord_1780531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780531).length < 2 ^ (prefixWord ++ tailWord_1780531).sum := by decide
  have hdescent : baseEnd_1780531 < baseStart_1780531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780588 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_1780588 : Nat := 118140960795 + 1780588 * 2 ^ 59
def prefixEnd_1780588 : Nat := 4983230072969 + 3 ^ 40 * 1780588 * 2
def baseEnd_1780588 : Nat := 914297491627984674961231

theorem tailTrace_1780588 : CollatzResearch.WordTrace tailWord_1780588 prefixEnd_1780588 914297491627984674961231 := by
  unfold tailWord_1780588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32471689836620625532427209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43295586448827500709902945 32471689836620625532427209)
  ·
    refine ⟨24353767377465469149320407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32471689836620625532427209 24353767377465469149320407)
    ·
      refine ⟨36530651066198203723980611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24353767377465469149320407 36530651066198203723980611)
      ·
        refine ⟨54795976599297305585970917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36530651066198203723980611 54795976599297305585970917)
        ·
          refine ⟨10274245612368244797369547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54795976599297305585970917 10274245612368244797369547)
          ·
            refine ⟨15411368418552367196054321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10274245612368244797369547 15411368418552367196054321)
            ·
              refine ⟨11558526313914275397040741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15411368418552367196054321 11558526313914275397040741)
              ·
                refine ⟨2167223683858926636945139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11558526313914275397040741 2167223683858926636945139)
                ·
                  refine ⟨3250835525788389955417709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167223683858926636945139 3250835525788389955417709)
                  ·
                    refine ⟨1219063322170646233281641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250835525788389955417709 1219063322170646233281641)
                    ·
                      refine ⟨914297491627984674961231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219063322170646233281641 914297491627984674961231)
                      ·
                        rfl

theorem cell23_1780588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_1780588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780588 prefixEnd_1780588 := by exact prefixLift 1780588
  have htrace : WordTrace (prefixWord ++ tailWord_1780588) baseStart_1780588 baseEnd_1780588 := by
    simpa [prefixWord, tailWord_1780588, baseEnd_1780588] using wordTrace_append hprefix tailTrace_1780588
  have hstable : (prefixWord ++ tailWord_1780588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780588).length < 2 ^ (prefixWord ++ tailWord_1780588).sum := by decide
  have hdescent : baseEnd_1780588 < baseStart_1780588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780604 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_1780604 : Nat := 118140960795 + 1780604 * 2 ^ 59
def prefixEnd_1780604 : Nat := 4983230072969 + 3 ^ 40 * 1780604 * 2
def baseEnd_1780604 : Nat := 914305707318456612361157

theorem tailTrace_1780604 : CollatzResearch.WordTrace tailWord_1780604 prefixEnd_1780604 914305707318456612361157 := by
  unfold tailWord_1780604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32471981620591642898718433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43295975494122190531624577 32471981620591642898718433)
  ·
    refine ⟨24353986215443732174038825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32471981620591642898718433 24353986215443732174038825)
    ·
      refine ⟨18265489661582799130529119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24353986215443732174038825 18265489661582799130529119)
      ·
        refine ⟨27398234492374198695793679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18265489661582799130529119 27398234492374198695793679)
        ·
          refine ⟨41097351738561298043690519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27398234492374198695793679 41097351738561298043690519)
          ·
            refine ⟨61646027607841947065535779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41097351738561298043690519 61646027607841947065535779)
            ·
              refine ⟨92469041411762920598303669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61646027607841947065535779 92469041411762920598303669)
              ·
                refine ⟨8668972632352773806090969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92469041411762920598303669 8668972632352773806090969)
                ·
                  refine ⟨6501729474264580354568227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8668972632352773806090969 6501729474264580354568227)
                  ·
                    refine ⟨9752594211396870531852341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6501729474264580354568227 9752594211396870531852341)
                    ·
                      refine ⟨914305707318456612361157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9752594211396870531852341 914305707318456612361157)
                      ·
                        rfl

theorem cell23_1780604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_1780604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780604 prefixEnd_1780604 := by exact prefixLift 1780604
  have htrace : WordTrace (prefixWord ++ tailWord_1780604) baseStart_1780604 baseEnd_1780604 := by
    simpa [prefixWord, tailWord_1780604, baseEnd_1780604] using wordTrace_append hprefix tailTrace_1780604
  have hstable : (prefixWord ++ tailWord_1780604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780604).length < 2 ^ (prefixWord ++ tailWord_1780604).sum := by decide
  have hdescent : baseEnd_1780604 < baseStart_1780604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780605 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_1780605 : Nat := 118140960795 + 1780605 * 2 ^ 59
def prefixEnd_1780605 : Nat := 4983230072969 + 3 ^ 40 * 1780605 * 2
def baseEnd_1780605 : Nat := 914306220799111108448653

theorem tailTrace_1780605 : CollatzResearch.WordTrace tailWord_1780605 prefixEnd_1780605 914306220799111108448653 := by
  unfold tailWord_1780605
  simp only [CollatzResearch.WordTrace]
  refine ⟨64943999714179662968223269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43295999809453108645482179 64943999714179662968223269)
  ·
    refine ⟨12176999946408686806541863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64943999714179662968223269 12176999946408686806541863)
    ·
      refine ⟨18265499919613030209812795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12176999946408686806541863 18265499919613030209812795)
      ·
        refine ⟨27398249879419545314719193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18265499919613030209812795 27398249879419545314719193)
        ·
          refine ⟨20548687409564658986039395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27398249879419545314719193 20548687409564658986039395)
          ·
            refine ⟨30823031114346988479059093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20548687409564658986039395 30823031114346988479059093)
            ·
              refine ⟨1444829583485015084955895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30823031114346988479059093 1444829583485015084955895)
              ·
                refine ⟨2167244375227522627433843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1444829583485015084955895 2167244375227522627433843)
                ·
                  refine ⟨3250866562841283941150765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167244375227522627433843 3250866562841283941150765)
                  ·
                    refine ⟨1219074961065481477931537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3250866562841283941150765 1219074961065481477931537)
                    ·
                      refine ⟨914306220799111108448653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219074961065481477931537 914306220799111108448653)
                      ·
                        rfl

theorem cell23_1780605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_1780605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780605 prefixEnd_1780605 := by exact prefixLift 1780605
  have htrace : WordTrace (prefixWord ++ tailWord_1780605) baseStart_1780605 baseEnd_1780605 := by
    simpa [prefixWord, tailWord_1780605, baseEnd_1780605] using wordTrace_append hprefix tailTrace_1780605
  have hstable : (prefixWord ++ tailWord_1780605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780605).length < 2 ^ (prefixWord ++ tailWord_1780605).sum := by decide
  have hdescent : baseEnd_1780605 < baseStart_1780605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780641 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 7]
def baseStart_1780641 : Nat := 118140960795 + 1780641 * 2 ^ 59
def prefixEnd_1780641 : Nat := 4983230072969 + 3 ^ 40 * 1780641 * 2
def baseEnd_1780641 : Nat := 101591634011408107510943

theorem tailTrace_1780641 : CollatzResearch.WordTrace tailWord_1780641 prefixEnd_1780641 101591634011408107510943 := by
  unfold tailWord_1780641
  simp only [CollatzResearch.WordTrace]
  refine ⟨64945312742049241116533777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43296875161366160744355851 64945312742049241116533777)
  ·
    refine ⟨48708984556536930837400333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64945312742049241116533777 48708984556536930837400333)
    ·
      refine ⟨18265869208701349064025125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48708984556536930837400333 18265869208701349064025125)
      ·
        refine ⟨3424850476631502949504711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18265869208701349064025125 3424850476631502949504711)
        ·
          refine ⟨5137275714947254424257067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3424850476631502949504711 5137275714947254424257067)
          ·
            refine ⟨7705913572420881636385601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137275714947254424257067 7705913572420881636385601)
            ·
              refine ⟨5779435179315661227289201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7705913572420881636385601 5779435179315661227289201)
              ·
                refine ⟨4334576384486745920466901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5779435179315661227289201 4334576384486745920466901)
                ·
                  refine ⟨101591634011408107510943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4334576384486745920466901 101591634011408107510943)
                  ·
                    rfl

theorem cell23_1780641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 7].length) (baseStart_1780641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780641 prefixEnd_1780641 := by exact prefixLift 1780641
  have htrace : WordTrace (prefixWord ++ tailWord_1780641) baseStart_1780641 baseEnd_1780641 := by
    simpa [prefixWord, tailWord_1780641, baseEnd_1780641] using wordTrace_append hprefix tailTrace_1780641
  have hstable : (prefixWord ++ tailWord_1780641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780641).length < 2 ^ (prefixWord ++ tailWord_1780641).sum := by decide
  have hdescent : baseEnd_1780641 < baseStart_1780641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780704 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1780704 : Nat := 118140960795 + 1780704 * 2 ^ 59
def prefixEnd_1780704 : Nat := 4983230072969 + 3 ^ 40 * 1780704 * 2
def baseEnd_1780704 : Nat := 914357055383906221110697

theorem tailTrace_1780704 : CollatzResearch.WordTrace tailWord_1780704 prefixEnd_1780704 914357055383906221110697 := by
  unfold tailWord_1780704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32473805270410501438038583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43298407027214001917384777 32473805270410501438038583)
  ·
    refine ⟨48710707905615752157057875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32473805270410501438038583 48710707905615752157057875)
    ·
      refine ⟨73066061858423628235586813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48710707905615752157057875 73066061858423628235586813)
      ·
        refine ⟨27399773196908860588345055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73066061858423628235586813 27399773196908860588345055)
        ·
          refine ⟨41099659795363290882517583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27399773196908860588345055 41099659795363290882517583)
          ·
            refine ⟨61649489693044936323776375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41099659795363290882517583 61649489693044936323776375)
            ·
              refine ⟨92474234539567404485664563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61649489693044936323776375 92474234539567404485664563)
              ·
                refine ⟨138711351809351106728496845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92474234539567404485664563 138711351809351106728496845)
                ·
                  refine ⟨52016756928506665023186317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 138711351809351106728496845 52016756928506665023186317)
                  ·
                    refine ⟨19506283848189999383694869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52016756928506665023186317 19506283848189999383694869)
                    ·
                      refine ⟨914357055383906221110697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19506283848189999383694869 914357055383906221110697)
                      ·
                        rfl

theorem cell23_1780704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1780704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780704 prefixEnd_1780704 := by exact prefixLift 1780704
  have htrace : WordTrace (prefixWord ++ tailWord_1780704) baseStart_1780704 baseEnd_1780704 := by
    simpa [prefixWord, tailWord_1780704, baseEnd_1780704] using wordTrace_append hprefix tailTrace_1780704
  have hstable : (prefixWord ++ tailWord_1780704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780704).length < 2 ^ (prefixWord ++ tailWord_1780704).sum := by decide
  have hdescent : baseEnd_1780704 < baseStart_1780704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780761 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 3, 5]
def baseStart_1780761 : Nat := 118140960795 + 1780761 * 2 ^ 59
def prefixEnd_1780761 : Nat := 4983230072969 + 3 ^ 40 * 1780761 * 2
def baseEnd_1780761 : Nat := 304795441260404166032645

theorem tailTrace_1780761 : CollatzResearch.WordTrace tailWord_1780761 prefixEnd_1780761 304795441260404166032645 := by
  unfold tailWord_1780761
  simp only [CollatzResearch.WordTrace]
  refine ⟨64949689501614501610902137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43299793001076334407268091 64949689501614501610902137)
  ·
    refine ⟨48712267126210876208176603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64949689501614501610902137 48712267126210876208176603)
    ·
      refine ⟨73068400689316314312264905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48712267126210876208176603 73068400689316314312264905)
      ·
        refine ⟨54801300516987235734198679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73068400689316314312264905 54801300516987235734198679)
        ·
          refine ⟨82201950775480853601298019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54801300516987235734198679 82201950775480853601298019)
          ·
            refine ⟨123302926163221280401947029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82201950775480853601298019 123302926163221280401947029)
            ·
              refine ⟨5779824663900997518841267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 123302926163221280401947029 5779824663900997518841267)
              ·
                refine ⟨8669736995851496278261901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5779824663900997518841267 8669736995851496278261901)
                ·
                  refine ⟨3251151373444311104348213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8669736995851496278261901 3251151373444311104348213)
                  ·
                    refine ⟨304795441260404166032645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3251151373444311104348213 304795441260404166032645)
                    ·
                      rfl

theorem cell23_1780761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_1780761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780761 prefixEnd_1780761 := by exact prefixLift 1780761
  have htrace : WordTrace (prefixWord ++ tailWord_1780761) baseStart_1780761 baseEnd_1780761 := by
    simpa [prefixWord, tailWord_1780761, baseEnd_1780761] using wordTrace_append hprefix tailTrace_1780761
  have hstable : (prefixWord ++ tailWord_1780761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780761).length < 2 ^ (prefixWord ++ tailWord_1780761).sum := by decide
  have hdescent : baseEnd_1780761 < baseStart_1780761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780792 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 1, 1, 3]
def baseStart_1780792 : Nat := 118140960795 + 1780792 * 2 ^ 59
def prefixEnd_1780792 : Nat := 4983230072969 + 3 ^ 40 * 1780792 * 2
def baseEnd_1780792 : Nat := 914402241681501876810293

theorem tailTrace_1780792 : CollatzResearch.WordTrace tailWord_1780792 prefixEnd_1780792 914402241681501876810293 := by
  unfold tailWord_1780792
  simp only [CollatzResearch.WordTrace]
  refine ⟨32475410082251096952640315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43300546776334795936853753 32475410082251096952640315)
  ·
    refine ⟨48713115123376645428960473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32475410082251096952640315 48713115123376645428960473)
    ·
      refine ⟨36534836342532484071720355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48713115123376645428960473 36534836342532484071720355)
      ·
        refine ⟨54802254513798726107580533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36534836342532484071720355 54802254513798726107580533)
        ·
          refine ⟨5137711360668630572585675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54802254513798726107580533 5137711360668630572585675)
          ·
            refine ⟨7706567041002945858878513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5137711360668630572585675 7706567041002945858878513)
            ·
              refine ⟨5779925280752209394158885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7706567041002945858878513 5779925280752209394158885)
              ·
                refine ⟨1083735990141039261404791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5779925280752209394158885 1083735990141039261404791)
                ·
                  refine ⟨1625603985211558892107187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1083735990141039261404791 1625603985211558892107187)
                  ·
                    refine ⟨2438405977817338338160781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1625603985211558892107187 2438405977817338338160781)
                    ·
                      refine ⟨914402241681501876810293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2438405977817338338160781 914402241681501876810293)
                      ·
                        rfl

theorem cell23_1780792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_1780792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780792 prefixEnd_1780792 := by exact prefixLift 1780792
  have htrace : WordTrace (prefixWord ++ tailWord_1780792) baseStart_1780792 baseEnd_1780792 := by
    simpa [prefixWord, tailWord_1780792, baseEnd_1780792] using wordTrace_append hprefix tailTrace_1780792
  have hstable : (prefixWord ++ tailWord_1780792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780792).length < 2 ^ (prefixWord ++ tailWord_1780792).sum := by decide
  have hdescent : baseEnd_1780792 < baseStart_1780792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780821 : List Nat := [1, 3, 2, 2, 1, 2, 3, 9]
def baseStart_1780821 : Nat := 118140960795 + 1780821 * 2 ^ 59
def prefixEnd_1780821 : Nat := 4983230072969 + 3 ^ 40 * 1780821 * 2
def baseEnd_1780821 : Nat := 33867301208166009753617

theorem tailTrace_1780821 : CollatzResearch.WordTrace tailWord_1780821 prefixEnd_1780821 33867301208166009753617 := by
  unfold tailWord_1780821
  simp only [CollatzResearch.WordTrace]
  refine ⟨64951877881397131858086317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43301251920931421238724211 64951877881397131858086317)
  ·
    refine ⟨24356954205523924446782369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64951877881397131858086317 24356954205523924446782369)
    ·
      refine ⟨18267715654142943335086777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24356954205523924446782369 18267715654142943335086777)
      ·
        refine ⟨13700786740607207501315083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18267715654142943335086777 13700786740607207501315083)
        ·
          refine ⟨20551180110910811251972625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13700786740607207501315083 20551180110910811251972625)
          ·
            refine ⟨15413385083183108438979469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20551180110910811251972625 15413385083183108438979469)
            ·
              refine ⟨5780019406193665664617301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15413385083183108438979469 5780019406193665664617301)
              ·
                refine ⟨33867301208166009753617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5780019406193665664617301 33867301208166009753617)
                ·
                  rfl

theorem cell23_1780821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 9].length) (baseStart_1780821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780821 prefixEnd_1780821 := by exact prefixLift 1780821
  have htrace : WordTrace (prefixWord ++ tailWord_1780821) baseStart_1780821 baseEnd_1780821 := by
    simpa [prefixWord, tailWord_1780821, baseEnd_1780821] using wordTrace_append hprefix tailTrace_1780821
  have hstable : (prefixWord ++ tailWord_1780821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780821).length < 2 ^ (prefixWord ++ tailWord_1780821).sum := by decide
  have hdescent : baseEnd_1780821 < baseStart_1780821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780828 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1780828 : Nat := 118140960795 + 1780828 * 2 ^ 59
def prefixEnd_1780828 : Nat := 4983230072969 + 3 ^ 40 * 1780828 * 2
def baseEnd_1780828 : Nat := 914420726985063735960127

theorem tailTrace_1780828 : CollatzResearch.WordTrace tailWord_1780828 prefixEnd_1780828 914420726985063735960127 := by
  unfold tailWord_1780828
  simp only [CollatzResearch.WordTrace]
  refine ⟨32476066596185886026795569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43301422128247848035727425 32476066596185886026795569)
  ·
    refine ⟨24357049947139414520096677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32476066596185886026795569 24357049947139414520096677)
    ·
      refine ⟨4566946865088640222518127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24357049947139414520096677 4566946865088640222518127)
      ·
        refine ⟨6850420297632960333777191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4566946865088640222518127 6850420297632960333777191)
        ·
          refine ⟨10275630446449440500665787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6850420297632960333777191 10275630446449440500665787)
          ·
            refine ⟨15413445669674160750998681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10275630446449440500665787 15413445669674160750998681)
            ·
              refine ⟨11560084252255620563249011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15413445669674160750998681 11560084252255620563249011)
              ·
                refine ⟨17340126378383430844873517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560084252255620563249011 17340126378383430844873517)
                ·
                  refine ⟨6502547391893786566827569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17340126378383430844873517 6502547391893786566827569)
                  ·
                    refine ⟨4876910543920339925120677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6502547391893786566827569 4876910543920339925120677)
                    ·
                      refine ⟨914420726985063735960127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4876910543920339925120677 914420726985063735960127)
                      ·
                        rfl

theorem cell23_1780828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1780828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780828 prefixEnd_1780828 := by exact prefixLift 1780828
  have htrace : WordTrace (prefixWord ++ tailWord_1780828) baseStart_1780828 baseEnd_1780828 := by
    simpa [prefixWord, tailWord_1780828, baseEnd_1780828] using wordTrace_append hprefix tailTrace_1780828
  have hstable : (prefixWord ++ tailWord_1780828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780828).length < 2 ^ (prefixWord ++ tailWord_1780828).sum := by decide
  have hdescent : baseEnd_1780828 < baseStart_1780828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780869 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_1780869 : Nat := 118140960795 + 1780869 * 2 ^ 59
def prefixEnd_1780869 : Nat := 4983230072969 + 3 ^ 40 * 1780869 * 2
def baseEnd_1780869 : Nat := 914441779691898075547439

theorem tailTrace_1780869 : CollatzResearch.WordTrace tailWord_1780869 prefixEnd_1780869 914441779691898075547439 := by
  unfold tailWord_1780869
  simp only [CollatzResearch.WordTrace]
  refine ⟨64953628585223236055833661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43302419056815490703889107 64953628585223236055833661)
  ·
    refine ⟨24357610719458713520937623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64953628585223236055833661 24357610719458713520937623)
    ·
      refine ⟨36536416079188070281406435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24357610719458713520937623 36536416079188070281406435)
      ·
        refine ⟨54804624118782105422109653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36536416079188070281406435 54804624118782105422109653)
        ·
          refine ⟨1284483377783955595830695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 54804624118782105422109653 1284483377783955595830695)
          ·
            refine ⟨1926725066675933393746043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1284483377783955595830695 1926725066675933393746043)
            ·
              refine ⟨2890087600013900090619065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1926725066675933393746043 2890087600013900090619065)
              ·
                refine ⟨2167565700010425067964299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890087600013900090619065 2167565700010425067964299)
                ·
                  refine ⟨3251348550015637601946449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167565700010425067964299 3251348550015637601946449)
                  ·
                    refine ⟨2438511412511728201459837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251348550015637601946449 2438511412511728201459837)
                    ·
                      refine ⟨914441779691898075547439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2438511412511728201459837 914441779691898075547439)
                      ·
                        rfl

theorem cell23_1780869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_1780869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780869 prefixEnd_1780869 := by exact prefixLift 1780869
  have htrace : WordTrace (prefixWord ++ tailWord_1780869) baseStart_1780869 baseEnd_1780869 := by
    simpa [prefixWord, tailWord_1780869, baseEnd_1780869] using wordTrace_append hprefix tailTrace_1780869
  have hstable : (prefixWord ++ tailWord_1780869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780869).length < 2 ^ (prefixWord ++ tailWord_1780869).sum := by decide
  have hdescent : baseEnd_1780869 < baseStart_1780869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780871 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1780871 : Nat := 118140960795 + 1780871 * 2 ^ 59
def prefixEnd_1780871 : Nat := 4983230072969 + 3 ^ 40 * 1780871 * 2
def baseEnd_1780871 : Nat := 914442806653207067722429

theorem tailTrace_1780871 : CollatzResearch.WordTrace tailWord_1780871 prefixEnd_1780871 914442806653207067722429 := by
  unfold tailWord_1780871
  simp only [CollatzResearch.WordTrace]
  refine ⟨64953701531215990397406467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43302467687477326931604311 64953701531215990397406467)
  ·
    refine ⟨97430552296823985596109701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64953701531215990397406467 97430552296823985596109701)
    ·
      refine ⟨18268228555654497299270569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97430552296823985596109701 18268228555654497299270569)
      ·
        refine ⟨13701171416740872974452927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18268228555654497299270569 13701171416740872974452927)
        ·
          refine ⟨20551757125111309461679391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13701171416740872974452927 20551757125111309461679391)
          ·
            refine ⟨30827635687666964192519087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20551757125111309461679391 30827635687666964192519087)
            ·
              refine ⟨46241453531500446288778631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30827635687666964192519087 46241453531500446288778631)
              ·
                refine ⟨69362180297250669433167947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46241453531500446288778631 69362180297250669433167947)
                ·
                  refine ⟨104043270445876004149751921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69362180297250669433167947 104043270445876004149751921)
                  ·
                    refine ⟨78032452834407003112313941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104043270445876004149751921 78032452834407003112313941)
                    ·
                      refine ⟨914442806653207067722429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78032452834407003112313941 914442806653207067722429)
                      ·
                        rfl

theorem cell23_1780871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1780871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780871 prefixEnd_1780871 := by exact prefixLift 1780871
  have htrace : WordTrace (prefixWord ++ tailWord_1780871) baseStart_1780871 baseEnd_1780871 := by
    simpa [prefixWord, tailWord_1780871, baseEnd_1780871] using wordTrace_append hprefix tailTrace_1780871
  have hstable : (prefixWord ++ tailWord_1780871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780871).length < 2 ^ (prefixWord ++ tailWord_1780871).sum := by decide
  have hdescent : baseEnd_1780871 < baseStart_1780871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1780968 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1780968 : Nat := 118140960795 + 1780968 * 2 ^ 59
def prefixEnd_1780968 : Nat := 4983230072969 + 3 ^ 40 * 1780968 * 2
def baseEnd_1780968 : Nat := 914492614276693188209483

theorem tailTrace_1780968 : CollatzResearch.WordTrace tailWord_1780968 prefixEnd_1780968 914492614276693188209483 := by
  unfold tailWord_1780968
  simp only [CollatzResearch.WordTrace]
  refine ⟨32478619705932287981843779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43304826274576383975791705 32478619705932287981843779)
  ·
    refine ⟨48717929558898431972765669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32478619705932287981843779 48717929558898431972765669)
    ·
      refine ⟨9134611792293455994893563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48717929558898431972765669 9134611792293455994893563)
      ·
        refine ⟨13701917688440183992340345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9134611792293455994893563 13701917688440183992340345)
        ·
          refine ⟨10276438266330137994255259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13701917688440183992340345 10276438266330137994255259)
          ·
            refine ⟨15414657399495206991382889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10276438266330137994255259 15414657399495206991382889)
            ·
              refine ⟨11560993049621405243537167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15414657399495206991382889 11560993049621405243537167)
              ·
                refine ⟨17341489574432107865305751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11560993049621405243537167 17341489574432107865305751)
                ·
                  refine ⟨26012234361648161797958627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17341489574432107865305751 26012234361648161797958627)
                  ·
                    refine ⟨39018351542472242696937941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26012234361648161797958627 39018351542472242696937941)
                    ·
                      refine ⟨914492614276693188209483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39018351542472242696937941 914492614276693188209483)
                      ·
                        rfl

theorem cell23_1780968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1780968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1780968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1780968 prefixEnd_1780968 := by exact prefixLift 1780968
  have htrace : WordTrace (prefixWord ++ tailWord_1780968) baseStart_1780968 baseEnd_1780968 := by
    simpa [prefixWord, tailWord_1780968, baseEnd_1780968] using wordTrace_append hprefix tailTrace_1780968
  have hstable : (prefixWord ++ tailWord_1780968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1780968).length < 2 ^ (prefixWord ++ tailWord_1780968).sum := by decide
  have hdescent : baseEnd_1780968 < baseStart_1780968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1780968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781046 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1781046 : Nat := 118140960795 + 1781046 * 2 ^ 59
def prefixEnd_1781046 : Nat := 4983230072969 + 3 ^ 40 * 1781046 * 2
def baseEnd_1781046 : Nat := 914532665767743883034125

theorem tailTrace_1781046 : CollatzResearch.WordTrace tailWord_1781046 prefixEnd_1781046 914532665767743883034125 := by
  unfold tailWord_1781046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060005269098874705314187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43306722870387996856684661 4060005269098874705314187)
  ·
    refine ⟨6090007903648312057971281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4060005269098874705314187 6090007903648312057971281)
    ·
      refine ⟨4567505927736234043478461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6090007903648312057971281 4567505927736234043478461)
      ·
        refine ⟨1712814722901087766304423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4567505927736234043478461 1712814722901087766304423)
        ·
          refine ⟨2569222084351631649456635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1712814722901087766304423 2569222084351631649456635)
          ·
            refine ⟨3853833126527447474184953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569222084351631649456635 3853833126527447474184953)
            ·
              refine ⟨2890374844895585605638715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853833126527447474184953 2890374844895585605638715)
              ·
                refine ⟨4335562267343378408458073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890374844895585605638715 4335562267343378408458073)
                ·
                  refine ⟨3251671700507533806343555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335562267343378408458073 3251671700507533806343555)
                  ·
                    refine ⟨4877507550761300709515333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3251671700507533806343555 4877507550761300709515333)
                    ·
                      refine ⟨914532665767743883034125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4877507550761300709515333 914532665767743883034125)
                      ·
                        rfl

theorem cell23_1781046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1781046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781046 prefixEnd_1781046 := by exact prefixLift 1781046
  have htrace : WordTrace (prefixWord ++ tailWord_1781046) baseStart_1781046 baseEnd_1781046 := by
    simpa [prefixWord, tailWord_1781046, baseEnd_1781046] using wordTrace_append hprefix tailTrace_1781046
  have hstable : (prefixWord ++ tailWord_1781046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781046).length < 2 ^ (prefixWord ++ tailWord_1781046).sum := by decide
  have hdescent : baseEnd_1781046 < baseStart_1781046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781049 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1781049 : Nat := 118140960795 + 1781049 * 2 ^ 59
def prefixEnd_1781049 : Nat := 4983230072969 + 3 ^ 40 * 1781049 * 2
def baseEnd_1781049 : Nat := 914534206209707371296611

theorem tailTrace_1781049 : CollatzResearch.WordTrace tailWord_1781049 prefixEnd_1781049 914534206209707371296611 := by
  unfold tailWord_1781049
  simp only [CollatzResearch.WordTrace]
  refine ⟨64960193724571126797386201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43306795816380751198257467 64960193724571126797386201)
  ·
    refine ⟨48720145293428345098039651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64960193724571126797386201 48720145293428345098039651)
    ·
      refine ⟨73080217940142517647059477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48720145293428345098039651 73080217940142517647059477)
      ·
        refine ⟨3425635215944180514705913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73080217940142517647059477 3425635215944180514705913)
        ·
          refine ⟨2569226411958135386029435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3425635215944180514705913 2569226411958135386029435)
          ·
            refine ⟨3853839617937203079044153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569226411958135386029435 3853839617937203079044153)
            ·
              refine ⟨2890379713452902309283115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853839617937203079044153 2890379713452902309283115)
              ·
                refine ⟨4335569570179353463924673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890379713452902309283115 4335569570179353463924673)
                ·
                  refine ⟨3251677177634515097943505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335569570179353463924673 3251677177634515097943505)
                  ·
                    refine ⟨2438757883225886323457629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3251677177634515097943505 2438757883225886323457629)
                    ·
                      refine ⟨914534206209707371296611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2438757883225886323457629 914534206209707371296611)
                      ·
                        rfl

theorem cell23_1781049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1781049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781049 prefixEnd_1781049 := by exact prefixLift 1781049
  have htrace : WordTrace (prefixWord ++ tailWord_1781049) baseStart_1781049 baseEnd_1781049 := by
    simpa [prefixWord, tailWord_1781049, baseEnd_1781049] using wordTrace_append hprefix tailTrace_1781049
  have hstable : (prefixWord ++ tailWord_1781049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781049).length < 2 ^ (prefixWord ++ tailWord_1781049).sum := by decide
  have hdescent : baseEnd_1781049 < baseStart_1781049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781065 : List Nat := [1, 2, 1, 1, 2, 3, 2, 5, 1, 5]
def baseStart_1781065 : Nat := 118140960795 + 1781065 * 2 ^ 59
def prefixEnd_1781065 : Nat := 4983230072969 + 3 ^ 40 * 1781065 * 2
def baseEnd_1781065 : Nat := 304847473966726436232179

theorem tailTrace_1781065 : CollatzResearch.WordTrace tailWord_1781065 prefixEnd_1781065 304847473966726436232179 := by
  unfold tailWord_1781065
  simp only [CollatzResearch.WordTrace]
  refine ⟨64960777292513161529968649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43307184861675441019979099 64960777292513161529968649)
  ·
    refine ⟨48720582969384871147476487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64960777292513161529968649 48720582969384871147476487)
    ·
      refine ⟨73080874454077306721214731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48720582969384871147476487 73080874454077306721214731)
      ·
        refine ⟨109621311681115960081822097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73080874454077306721214731 109621311681115960081822097)
        ·
          refine ⟨82215983760836970061366573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109621311681115960081822097 82215983760836970061366573)
          ·
            refine ⟨30830993910313863773012465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82215983760836970061366573 30830993910313863773012465)
            ·
              refine ⟨23123245432735397829759349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30830993910313863773012465 23123245432735397829759349)
              ·
                refine ⟨2167804259318943546539939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23123245432735397829759349 2167804259318943546539939)
                ·
                  refine ⟨3251706388978415319809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167804259318943546539939 3251706388978415319809909)
                  ·
                    refine ⟨304847473966726436232179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3251706388978415319809909 304847473966726436232179)
                    ·
                      rfl

theorem cell23_1781065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_1781065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781065 prefixEnd_1781065 := by exact prefixLift 1781065
  have htrace : WordTrace (prefixWord ++ tailWord_1781065) baseStart_1781065 baseEnd_1781065 := by
    simpa [prefixWord, tailWord_1781065, baseEnd_1781065] using wordTrace_append hprefix tailTrace_1781065
  have hstable : (prefixWord ++ tailWord_1781065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781065).length < 2 ^ (prefixWord ++ tailWord_1781065).sum := by decide
  have hdescent : baseEnd_1781065 < baseStart_1781065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781072 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2]
def baseStart_1781072 : Nat := 118140960795 + 1781072 * 2 ^ 59
def prefixEnd_1781072 : Nat := 4983230072969 + 3 ^ 40 * 1781072 * 2
def baseEnd_1781072 : Nat := 914546016264760781309005

theorem tailTrace_1781072 : CollatzResearch.WordTrace tailWord_1781072 prefixEnd_1781072 914546016264760781309005 := by
  unfold tailWord_1781072
  simp only [CollatzResearch.WordTrace]
  refine ⟨32480516301743900862736735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43307355068991867816982313 32480516301743900862736735)
  ·
    refine ⟨48720774452615851294105103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32480516301743900862736735 48720774452615851294105103)
    ·
      refine ⟨73081161678923776941157655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48720774452615851294105103 73081161678923776941157655)
      ·
        refine ⟨109621742518385665411736483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73081161678923776941157655 109621742518385665411736483)
        ·
          refine ⟨164432613777578498117604725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109621742518385665411736483 164432613777578498117604725)
          ·
            refine ⟨15415557541647984198525443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 164432613777578498117604725 15415557541647984198525443)
            ·
              refine ⟨23123336312471976297788165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15415557541647984198525443 23123336312471976297788165)
              ·
                refine ⟨4335625558588495555835281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23123336312471976297788165 4335625558588495555835281)
                ·
                  refine ⟨3251719168941371666876461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4335625558588495555835281 3251719168941371666876461)
                  ·
                    refine ⟨1219394688353014375078673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251719168941371666876461 1219394688353014375078673)
                    ·
                      refine ⟨914546016264760781309005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219394688353014375078673 914546016264760781309005)
                      ·
                        rfl

theorem cell23_1781072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 3, 2].length) (baseStart_1781072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781072 prefixEnd_1781072 := by exact prefixLift 1781072
  have htrace : WordTrace (prefixWord ++ tailWord_1781072) baseStart_1781072 baseEnd_1781072 := by
    simpa [prefixWord, tailWord_1781072, baseEnd_1781072] using wordTrace_append hprefix tailTrace_1781072
  have hstable : (prefixWord ++ tailWord_1781072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781072).length < 2 ^ (prefixWord ++ tailWord_1781072).sum := by decide
  have hdescent : baseEnd_1781072 < baseStart_1781072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781115 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4]
def baseStart_1781115 : Nat := 118140960795 + 1781115 * 2 ^ 59
def prefixEnd_1781115 : Nat := 4983230072969 + 3 ^ 40 * 1781115 * 2
def baseEnd_1781115 : Nat := 914568095932904113071307

theorem tailTrace_1781115 : CollatzResearch.WordTrace tailWord_1781115 prefixEnd_1781115 914568095932904113071307 := by
  unfold tailWord_1781115
  simp only [CollatzResearch.WordTrace]
  refine ⟨64962600942332020069288799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43308400628221346712859199 64962600942332020069288799)
  ·
    refine ⟨97443901413498030103933199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64962600942332020069288799 97443901413498030103933199)
    ·
      refine ⟨146165852120247045155899799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97443901413498030103933199 146165852120247045155899799)
      ·
        refine ⟨219248778180370567733849699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146165852120247045155899799 219248778180370567733849699)
        ·
          refine ⟨328873167270555851600774549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219248778180370567733849699 328873167270555851600774549)
          ·
            refine ⟨15415929715807305543786307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328873167270555851600774549 15415929715807305543786307)
            ·
              refine ⟨23123894573710958315679461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15415929715807305543786307 23123894573710958315679461)
              ·
                refine ⟨4335730232570804684189899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23123894573710958315679461 4335730232570804684189899)
                ·
                  refine ⟨6503595348856207026284849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335730232570804684189899 6503595348856207026284849)
                  ·
                    refine ⟨4877696511642155269713637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503595348856207026284849 4877696511642155269713637)
                    ·
                      refine ⟨914568095932904113071307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4877696511642155269713637 914568095932904113071307)
                      ·
                        rfl

theorem cell23_1781115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_1781115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781115 prefixEnd_1781115 := by exact prefixLift 1781115
  have htrace : WordTrace (prefixWord ++ tailWord_1781115) baseStart_1781115 baseEnd_1781115 := by
    simpa [prefixWord, tailWord_1781115, baseEnd_1781115] using wordTrace_append hprefix tailTrace_1781115
  have hstable : (prefixWord ++ tailWord_1781115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781115).length < 2 ^ (prefixWord ++ tailWord_1781115).sum := by decide
  have hdescent : baseEnd_1781115 < baseStart_1781115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781149 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1781149 : Nat := 118140960795 + 1781149 * 2 ^ 59
def prefixEnd_1781149 : Nat := 4983230072969 + 3 ^ 40 * 1781149 * 2
def baseEnd_1781149 : Nat := 914585554275156980046151

theorem tailTrace_1781149 : CollatzResearch.WordTrace tailWord_1781149 prefixEnd_1781149 914585554275156980046151 := by
  unfold tailWord_1781149
  simp only [CollatzResearch.WordTrace]
  refine ⟨64963841024208843876026501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43309227349472562584017667 64963841024208843876026501)
  ·
    refine ⟨12180720192039158226754969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64963841024208843876026501 12180720192039158226754969)
    ·
      refine ⟨9135540144029368670066227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12180720192039158226754969 9135540144029368670066227)
      ·
        refine ⟨13703310216044053005099341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9135540144029368670066227 13703310216044053005099341)
        ·
          refine ⟨5138741331016519876912253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13703310216044053005099341 5138741331016519876912253)
          ·
            refine ⟨1927027999131194953842095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5138741331016519876912253 1927027999131194953842095)
            ·
              refine ⟨2890541998696792430763143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927027999131194953842095 2890541998696792430763143)
              ·
                refine ⟨4335812998045188646144715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2890541998696792430763143 4335812998045188646144715)
                ·
                  refine ⟨6503719497067782969217073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4335812998045188646144715 6503719497067782969217073)
                  ·
                    refine ⟨4877789622800837226912805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6503719497067782969217073 4877789622800837226912805)
                    ·
                      refine ⟨914585554275156980046151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4877789622800837226912805 914585554275156980046151)
                      ·
                        rfl

theorem cell23_1781149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1781149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781149 prefixEnd_1781149 := by exact prefixLift 1781149
  have htrace : WordTrace (prefixWord ++ tailWord_1781149) baseStart_1781149 baseEnd_1781149 := by
    simpa [prefixWord, tailWord_1781149, baseEnd_1781149] using wordTrace_append hprefix tailTrace_1781149
  have hstable : (prefixWord ++ tailWord_1781149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781149).length < 2 ^ (prefixWord ++ tailWord_1781149).sum := by decide
  have hdescent : baseEnd_1781149 < baseStart_1781149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781213 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1781213 : Nat := 118140960795 + 1781213 * 2 ^ 59
def prefixEnd_1781213 : Nat := 4983230072969 + 3 ^ 40 * 1781213 * 2
def baseEnd_1781213 : Nat := 914618417037044729645857

theorem tailTrace_1781213 : CollatzResearch.WordTrace tailWord_1781213 prefixEnd_1781213 914618417037044729645857 := by
  unfold tailWord_1781213
  simp only [CollatzResearch.WordTrace]
  refine ⟨64966175295976982806356293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43310783530651321870904195 64966175295976982806356293)
  ·
    refine ⟨12181157867995684276191805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64966175295976982806356293 12181157867995684276191805)
    ·
      refine ⟨4567934200498381603571927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12181157867995684276191805 4567934200498381603571927)
      ·
        refine ⟨6851901300747572405357891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4567934200498381603571927 6851901300747572405357891)
        ·
          refine ⟨10277851951121358608036837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6851901300747572405357891 10277851951121358608036837)
          ·
            refine ⟨1927097240835254739006907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10277851951121358608036837 1927097240835254739006907)
            ·
              refine ⟨2890645861252882108510361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927097240835254739006907 2890645861252882108510361)
              ·
                refine ⟨2167984395939661581382771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890645861252882108510361 2167984395939661581382771)
                ·
                  refine ⟨3251976593909492372074157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2167984395939661581382771 3251976593909492372074157)
                  ·
                    refine ⟨1219491222716059639527809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3251976593909492372074157 1219491222716059639527809)
                    ·
                      refine ⟨914618417037044729645857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219491222716059639527809 914618417037044729645857)
                      ·
                        rfl

theorem cell23_1781213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1781213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781213 prefixEnd_1781213 := by exact prefixLift 1781213
  have htrace : WordTrace (prefixWord ++ tailWord_1781213) baseStart_1781213 baseEnd_1781213 := by
    simpa [prefixWord, tailWord_1781213, baseEnd_1781213] using wordTrace_append hprefix tailTrace_1781213
  have hstable : (prefixWord ++ tailWord_1781213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781213).length < 2 ^ (prefixWord ++ tailWord_1781213).sum := by decide
  have hdescent : baseEnd_1781213 < baseStart_1781213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781215 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 9]
def baseStart_1781215 : Nat := 118140960795 + 1781215 * 2 ^ 59
def prefixEnd_1781215 : Nat := 4983230072969 + 3 ^ 40 * 1781215 * 2
def baseEnd_1781215 : Nat := 101624382666483746868983

theorem tailTrace_1781215 : CollatzResearch.WordTrace tailWord_1781215 prefixEnd_1781215 101624382666483746868983 := by
  unfold tailWord_1781215
  simp only [CollatzResearch.WordTrace]
  refine ⟨64966248241969737147929099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43310832161313158098619399 64966248241969737147929099)
  ·
    refine ⟨97449372362954605721893649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64966248241969737147929099 97449372362954605721893649)
    ·
      refine ⟨73087029272215954291420237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97449372362954605721893649 73087029272215954291420237)
      ·
        refine ⟨27407635977080982859282589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73087029272215954291420237 27407635977080982859282589)
        ·
          refine ⟨10277863491405368572230971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27407635977080982859282589 10277863491405368572230971)
          ·
            refine ⟨15416795237108052858346457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10277863491405368572230971 15416795237108052858346457)
            ·
              refine ⟨11562596427831039643759843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15416795237108052858346457 11562596427831039643759843)
              ·
                refine ⟨17343894641746559465639765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11562596427831039643759843 17343894641746559465639765)
                ·
                  refine ⟨101624382666483746868983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17343894641746559465639765 101624382666483746868983)
                  ·
                    rfl

theorem cell23_1781215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 9].length) (baseStart_1781215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781215 prefixEnd_1781215 := by exact prefixLift 1781215
  have htrace : WordTrace (prefixWord ++ tailWord_1781215) baseStart_1781215 baseEnd_1781215 := by
    simpa [prefixWord, tailWord_1781215, baseEnd_1781215] using wordTrace_append hprefix tailTrace_1781215
  have hstable : (prefixWord ++ tailWord_1781215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781215).length < 2 ^ (prefixWord ++ tailWord_1781215).sum := by decide
  have hdescent : baseEnd_1781215 < baseStart_1781215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781226 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_1781226 : Nat := 118140960795 + 1781226 * 2 ^ 59
def prefixEnd_1781226 : Nat := 4983230072969 + 3 ^ 40 * 1781226 * 2
def baseEnd_1781226 : Nat := 914625092285553178783297

theorem tailTrace_1781226 : CollatzResearch.WordTrace tailWord_1781226 prefixEnd_1781226 914625092285553178783297 := by
  unfold tailWord_1781226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241662361232471506644883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43311099629953257351053021 16241662361232471506644883)
  ·
    refine ⟨24362493541848707259967325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16241662361232471506644883 24362493541848707259967325)
    ·
      refine ⟨9135935078193265222487747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24362493541848707259967325 9135935078193265222487747)
      ·
        refine ⟨13703902617289897833731621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9135935078193265222487747 13703902617289897833731621)
        ·
          refine ⟨2569481740741855843824679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13703902617289897833731621 2569481740741855843824679)
          ·
            refine ⟨3854222611112783765737019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569481740741855843824679 3854222611112783765737019)
            ·
              refine ⟨5781333916669175648605529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854222611112783765737019 5781333916669175648605529)
              ·
                refine ⟨4336000437501881736454147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5781333916669175648605529 4336000437501881736454147)
                ·
                  refine ⟨6504000656252822604681221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336000437501881736454147 6504000656252822604681221)
                  ·
                    refine ⟨1219500123047404238377729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504000656252822604681221 1219500123047404238377729)
                    ·
                      refine ⟨914625092285553178783297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219500123047404238377729 914625092285553178783297)
                      ·
                        rfl

theorem cell23_1781226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_1781226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781226 prefixEnd_1781226 := by exact prefixLift 1781226
  have htrace : WordTrace (prefixWord ++ tailWord_1781226) baseStart_1781226 baseEnd_1781226 := by
    simpa [prefixWord, tailWord_1781226, baseEnd_1781226] using wordTrace_append hprefix tailTrace_1781226
  have hstable : (prefixWord ++ tailWord_1781226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781226).length < 2 ^ (prefixWord ++ tailWord_1781226).sum := by decide
  have hdescent : baseEnd_1781226 < baseStart_1781226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781242 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_1781242 : Nat := 118140960795 + 1781242 * 2 ^ 59
def prefixEnd_1781242 : Nat := 4983230072969 + 3 ^ 40 * 1781242 * 2
def baseEnd_1781242 : Nat := 914633307976025116183223

theorem tailTrace_1781242 : CollatzResearch.WordTrace tailWord_1781242 prefixEnd_1781242 914633307976025116183223 := by
  unfold tailWord_1781242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16241808253217980189790495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43311488675247947172774653 16241808253217980189790495)
  ·
    refine ⟨24362712379826970284685743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16241808253217980189790495 24362712379826970284685743)
    ·
      refine ⟨36544068569740455427028615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24362712379826970284685743 36544068569740455427028615)
      ·
        refine ⟨54816102854610683140542923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36544068569740455427028615 54816102854610683140542923)
        ·
          refine ⟨82224154281916024710814385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54816102854610683140542923 82224154281916024710814385)
          ·
            refine ⟨61668115711437018533110789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82224154281916024710814385 61668115711437018533110789)
            ·
              refine ⟨11562771695894440974958273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61668115711437018533110789 11562771695894440974958273)
              ·
                refine ⟨8672078771920830731218705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11562771695894440974958273 8672078771920830731218705)
                ·
                  refine ⟨6504059078940623048414029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672078771920830731218705 6504059078940623048414029)
                  ·
                    refine ⟨2439022154602733643155261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6504059078940623048414029 2439022154602733643155261)
                    ·
                      refine ⟨914633307976025116183223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439022154602733643155261 914633307976025116183223)
                      ·
                        rfl

theorem cell23_1781242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_1781242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781242 prefixEnd_1781242 := by exact prefixLift 1781242
  have htrace : WordTrace (prefixWord ++ tailWord_1781242) baseStart_1781242 baseEnd_1781242 := by
    simpa [prefixWord, tailWord_1781242, baseEnd_1781242] using wordTrace_append hprefix tailTrace_1781242
  have hstable : (prefixWord ++ tailWord_1781242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781242).length < 2 ^ (prefixWord ++ tailWord_1781242).sum := by decide
  have hdescent : baseEnd_1781242 < baseStart_1781242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781259 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3]
def baseStart_1781259 : Nat := 118140960795 + 1781259 * 2 ^ 59
def prefixEnd_1781259 : Nat := 4983230072969 + 3 ^ 40 * 1781259 * 2
def baseEnd_1781259 : Nat := 914642037147151549670645

theorem tailTrace_1781259 : CollatzResearch.WordTrace tailWord_1781259 prefixEnd_1781259 914642037147151549670645 := by
  unfold tailWord_1781259
  simp only [CollatzResearch.WordTrace]
  refine ⟨64967853053810332662530831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43311902035873555108353887 64967853053810332662530831)
  ·
    refine ⟨97451779580715498993796247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64967853053810332662530831 97451779580715498993796247)
    ·
      refine ⟨146177669371073248490694371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97451779580715498993796247 146177669371073248490694371)
      ·
        refine ⟨219266504056609872736041557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146177669371073248490694371 219266504056609872736041557)
        ·
          refine ⟨2569529344413396946125487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 219266504056609872736041557 2569529344413396946125487)
          ·
            refine ⟨3854294016620095419188231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569529344413396946125487 3854294016620095419188231)
            ·
              refine ⟨5781441024930143128782347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854294016620095419188231 5781441024930143128782347)
              ·
                refine ⟨8672161537395214693173521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5781441024930143128782347 8672161537395214693173521)
                ·
                  refine ⟨6504121153046411019880141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672161537395214693173521 6504121153046411019880141)
                  ·
                    refine ⟨2439045432392404132455053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6504121153046411019880141 2439045432392404132455053)
                    ·
                      refine ⟨914642037147151549670645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439045432392404132455053 914642037147151549670645)
                      ·
                        rfl

theorem cell23_1781259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3].length) (baseStart_1781259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781259 prefixEnd_1781259 := by exact prefixLift 1781259
  have htrace : WordTrace (prefixWord ++ tailWord_1781259) baseStart_1781259 baseEnd_1781259 := by
    simpa [prefixWord, tailWord_1781259, baseEnd_1781259] using wordTrace_append hprefix tailTrace_1781259
  have hstable : (prefixWord ++ tailWord_1781259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781259).length < 2 ^ (prefixWord ++ tailWord_1781259).sum := by decide
  have hdescent : baseEnd_1781259 < baseStart_1781259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781299 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 2, 4, 2]
def baseStart_1781299 : Nat := 118140960795 + 1781299 * 2 ^ 59
def prefixEnd_1781299 : Nat := 4983230072969 + 3 ^ 40 * 1781299 * 2
def baseEnd_1781299 : Nat := 914662576373331393170461

theorem tailTrace_1781299 : CollatzResearch.WordTrace tailWord_1781299 prefixEnd_1781299 914662576373331393170461 := by
  unfold tailWord_1781299
  simp only [CollatzResearch.WordTrace]
  refine ⟨64969311973665419493986951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43312874649110279662657967 64969311973665419493986951)
  ·
    refine ⟨97453967960498129240980427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64969311973665419493986951 97453967960498129240980427)
    ·
      refine ⟨146180951940747193861470641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97453967960498129240980427 146180951940747193861470641)
      ·
        refine ⟨109635713955560395396102981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146180951940747193861470641 109635713955560395396102981)
        ·
          refine ⟨20556696366667574136769309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109635713955560395396102981 20556696366667574136769309)
          ·
            refine ⟨7708761137500340301288491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20556696366667574136769309 7708761137500340301288491)
            ·
              refine ⟨11563141706250510451932737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7708761137500340301288491 11563141706250510451932737)
              ·
                refine ⟨8672356279687882838949553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11563141706250510451932737 8672356279687882838949553)
                ·
                  refine ⟨6504267209765912129212165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8672356279687882838949553 6504267209765912129212165)
                  ·
                    refine ⟨1219550101831108524227281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504267209765912129212165 1219550101831108524227281)
                    ·
                      refine ⟨914662576373331393170461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219550101831108524227281 914662576373331393170461)
                      ·
                        rfl

theorem cell23_1781299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 4, 2].length) (baseStart_1781299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781299 prefixEnd_1781299 := by exact prefixLift 1781299
  have htrace : WordTrace (prefixWord ++ tailWord_1781299) baseStart_1781299 baseEnd_1781299 := by
    simpa [prefixWord, tailWord_1781299, baseEnd_1781299] using wordTrace_append hprefix tailTrace_1781299
  have hstable : (prefixWord ++ tailWord_1781299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781299).length < 2 ^ (prefixWord ++ tailWord_1781299).sum := by decide
  have hdescent : baseEnd_1781299 < baseStart_1781299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781372 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_1781372 : Nat := 118140960795 + 1781372 * 2 ^ 59
def prefixEnd_1781372 : Nat := 4983230072969 + 3 ^ 40 * 1781372 * 2
def baseEnd_1781372 : Nat := 914700060461109607557625

theorem tailTrace_1781372 : CollatzResearch.WordTrace tailWord_1781372 prefixEnd_1781372 914700060461109607557625 := by
  unfold tailWord_1781372
  simp only [CollatzResearch.WordTrace]
  refine ⟨32485987251200476480697185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43314649668267301974262913 32485987251200476480697185)
  ·
    refine ⟨24364490438400357360522889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32485987251200476480697185 24364490438400357360522889)
    ·
      refine ⟨18273367828800268020392167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24364490438400357360522889 18273367828800268020392167)
      ·
        refine ⟨27410051743200402030588251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18273367828800268020392167 27410051743200402030588251)
        ·
          refine ⟨41115077614800603045882377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27410051743200402030588251 41115077614800603045882377)
          ·
            refine ⟨30836308211100452284411783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41115077614800603045882377 30836308211100452284411783)
            ·
              refine ⟨46254462316650678426617675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30836308211100452284411783 46254462316650678426617675)
              ·
                refine ⟨69381693474976017639926513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46254462316650678426617675 69381693474976017639926513)
                ·
                  refine ⟨52036270106232013229944885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69381693474976017639926513 52036270106232013229944885)
                  ·
                    refine ⟨4878400322459251240307333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52036270106232013229944885 4878400322459251240307333)
                    ·
                      refine ⟨914700060461109607557625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4878400322459251240307333 914700060461109607557625)
                      ·
                        rfl

theorem cell23_1781372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_1781372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781372 prefixEnd_1781372 := by exact prefixLift 1781372
  have htrace : WordTrace (prefixWord ++ tailWord_1781372) baseStart_1781372 baseEnd_1781372 := by
    simpa [prefixWord, tailWord_1781372, baseEnd_1781372] using wordTrace_append hprefix tailTrace_1781372
  have hstable : (prefixWord ++ tailWord_1781372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781372).length < 2 ^ (prefixWord ++ tailWord_1781372).sum := by decide
  have hdescent : baseEnd_1781372 < baseStart_1781372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781386 : List Nat := [3, 1, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1781386 : Nat := 118140960795 + 1781386 * 2 ^ 59
def prefixEnd_1781386 : Nat := 4983230072969 + 3 ^ 40 * 1781386 * 2
def baseEnd_1781386 : Nat := 304902416396757517594187

theorem tailTrace_1781386 : CollatzResearch.WordTrace tailWord_1781386 prefixEnd_1781386 304902416396757517594187 := by
  unfold tailWord_1781386
  simp only [CollatzResearch.WordTrace]
  refine ⟨16243121281087558338101003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43314990082900155568269341 16243121281087558338101003)
  ·
    refine ⟨24364681921631337507151505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16243121281087558338101003 24364681921631337507151505)
    ·
      refine ⟨18273511441223503130363629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24364681921631337507151505 18273511441223503130363629)
      ·
        refine ⟨6852566790458813673886361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18273511441223503130363629 6852566790458813673886361)
        ·
          refine ⟨5139425092844110255414771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6852566790458813673886361 5139425092844110255414771)
          ·
            refine ⟨7709137639266165383122157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139425092844110255414771 7709137639266165383122157)
            ·
              refine ⟨2890926614724812018670809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7709137639266165383122157 2890926614724812018670809)
              ·
                refine ⟨2168194961043609014003107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2890926614724812018670809 2168194961043609014003107)
                ·
                  refine ⟨3252292441565413521004661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168194961043609014003107 3252292441565413521004661)
                  ·
                    refine ⟨304902416396757517594187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3252292441565413521004661 304902416396757517594187)
                    ·
                      rfl

theorem cell23_1781386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1781386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781386 prefixEnd_1781386 := by exact prefixLift 1781386
  have htrace : WordTrace (prefixWord ++ tailWord_1781386) baseStart_1781386 baseEnd_1781386 := by
    simpa [prefixWord, tailWord_1781386, baseEnd_1781386] using wordTrace_append hprefix tailTrace_1781386
  have hstable : (prefixWord ++ tailWord_1781386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781386).length < 2 ^ (prefixWord ++ tailWord_1781386).sum := by decide
  have hdescent : baseEnd_1781386 < baseStart_1781386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781392 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_1781392 : Nat := 118140960795 + 1781392 * 2 ^ 59
def prefixEnd_1781392 : Nat := 4983230072969 + 3 ^ 40 * 1781392 * 2
def baseEnd_1781392 : Nat := 914710330074199529307533

theorem tailTrace_1781392 : CollatzResearch.WordTrace tailWord_1781392 prefixEnd_1781392 914710330074199529307533 := by
  unfold tailWord_1781392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32486351981164248188561215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43315135974885664251414953 32486351981164248188561215)
  ·
    refine ⟨48729527971746372282841823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32486351981164248188561215 48729527971746372282841823)
    ·
      refine ⟨73094291957619558424262735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48729527971746372282841823 73094291957619558424262735)
      ·
        refine ⟨109641437936429337636394103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73094291957619558424262735 109641437936429337636394103)
        ·
          refine ⟨164462156904644006454591155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109641437936429337636394103 164462156904644006454591155)
          ·
            refine ⟨246693235356966009681886733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164462156904644006454591155 246693235356966009681886733)
            ·
              refine ⟨92509963258862253630707525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246693235356966009681886733 92509963258862253630707525)
              ·
                refine ⟨17345618111036672555757661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92509963258862253630707525 17345618111036672555757661)
                ·
                  refine ⟨6504606791638752208409123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17345618111036672555757661 6504606791638752208409123)
                  ·
                    refine ⟨9756910187458128312613685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6504606791638752208409123 9756910187458128312613685)
                    ·
                      refine ⟨914710330074199529307533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9756910187458128312613685 914710330074199529307533)
                      ·
                        rfl

theorem cell23_1781392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_1781392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781392 prefixEnd_1781392 := by exact prefixLift 1781392
  have htrace : WordTrace (prefixWord ++ tailWord_1781392) baseStart_1781392 baseEnd_1781392 := by
    simpa [prefixWord, tailWord_1781392, baseEnd_1781392] using wordTrace_append hprefix tailTrace_1781392
  have hstable : (prefixWord ++ tailWord_1781392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781392).length < 2 ^ (prefixWord ++ tailWord_1781392).sum := by decide
  have hdescent : baseEnd_1781392 < baseStart_1781392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781399 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 1, 6]
def baseStart_1781399 : Nat := 118140960795 + 1781399 * 2 ^ 59
def prefixEnd_1781399 : Nat := 4983230072969 + 3 ^ 40 * 1781399 * 2
def baseEnd_1781399 : Nat := 304904641479593667306667

theorem tailTrace_1781399 : CollatzResearch.WordTrace tailWord_1781399 prefixEnd_1781399 304904641479593667306667 := by
  unfold tailWord_1781399
  simp only [CollatzResearch.WordTrace]
  refine ⟨64972959273303136572627251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43315306182202091048418167 64972959273303136572627251)
  ·
    refine ⟨97459438909954704858940877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64972959273303136572627251 97459438909954704858940877)
    ·
      refine ⟨36547289591233014322102829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97459438909954704858940877 36547289591233014322102829)
      ·
        refine ⟨13705233596712380370788561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36547289591233014322102829 13705233596712380370788561)
        ·
          refine ⟨10278925197534285278091421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13705233596712380370788561 10278925197534285278091421)
          ·
            refine ⟨3854596949075356979284283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10278925197534285278091421 3854596949075356979284283)
            ·
              refine ⟨5781895423613035468926425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854596949075356979284283 5781895423613035468926425)
              ·
                refine ⟨4336421567709776601694819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5781895423613035468926425 4336421567709776601694819)
                ·
                  refine ⟨6504632351564664902542229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336421567709776601694819 6504632351564664902542229)
                  ·
                    refine ⟨304904641479593667306667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6504632351564664902542229 304904641479593667306667)
                    ·
                      rfl

theorem cell23_1781399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_1781399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781399 prefixEnd_1781399 := by exact prefixLift 1781399
  have htrace : WordTrace (prefixWord ++ tailWord_1781399) baseStart_1781399 baseEnd_1781399 := by
    simpa [prefixWord, tailWord_1781399, baseEnd_1781399] using wordTrace_append hprefix tailTrace_1781399
  have hstable : (prefixWord ++ tailWord_1781399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781399).length < 2 ^ (prefixWord ++ tailWord_1781399).sum := by decide
  have hdescent : baseEnd_1781399 < baseStart_1781399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781412 : List Nat := [2, 3, 1, 2, 2, 13]
def baseStart_1781412 : Nat := 118140960795 + 1781412 * 2 ^ 59
def prefixEnd_1781412 : Nat := 4983230072969 + 3 ^ 40 * 1781412 * 2
def baseEnd_1781412 : Nat := 3764282303239874284187

theorem tailTrace_1781412 : CollatzResearch.WordTrace tailWord_1781412 prefixEnd_1781412 3764282303239874284187 := by
  unfold tailWord_1781412
  simp only [CollatzResearch.WordTrace]
  refine ⟨32486716711128019896425245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43315622281504026528566993 32486716711128019896425245)
  ·
    refine ⟨12182518766673007461159467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32486716711128019896425245 12182518766673007461159467)
    ·
      refine ⟨18273778150009511191739201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12182518766673007461159467 18273778150009511191739201)
      ·
        refine ⟨13705333612507133393804401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18273778150009511191739201 13705333612507133393804401)
        ·
          refine ⟨10279000209380350045353301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13705333612507133393804401 10279000209380350045353301)
          ·
            refine ⟨3764282303239874284187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 10279000209380350045353301 3764282303239874284187)
            ·
              rfl

theorem cell23_1781412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 13].length) (baseStart_1781412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781412 prefixEnd_1781412 := by exact prefixLift 1781412
  have htrace : WordTrace (prefixWord ++ tailWord_1781412) baseStart_1781412 baseEnd_1781412 := by
    simpa [prefixWord, tailWord_1781412, baseEnd_1781412] using wordTrace_append hprefix tailTrace_1781412
  have hstable : (prefixWord ++ tailWord_1781412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781412).length < 2 ^ (prefixWord ++ tailWord_1781412).sum := by decide
  have hdescent : baseEnd_1781412 < baseStart_1781412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781432 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_1781432 : Nat := 118140960795 + 1781432 * 2 ^ 59
def prefixEnd_1781432 : Nat := 4983230072969 + 3 ^ 40 * 1781432 * 2
def baseEnd_1781432 : Nat := 914730869300379372807349

theorem tailTrace_1781432 : CollatzResearch.WordTrace tailWord_1781432 prefixEnd_1781432 914730869300379372807349 := by
  unfold tailWord_1781432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487081441091791604289275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43316108588122388805719033 32487081441091791604289275)
  ·
    refine ⟨48730622161637687406433913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32487081441091791604289275 48730622161637687406433913)
    ·
      refine ⟨36547966621228265554825435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48730622161637687406433913 36547966621228265554825435)
      ·
        refine ⟨54821949931842398332238153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36547966621228265554825435 54821949931842398332238153)
        ·
          refine ⟨41116462448881798749178615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54821949931842398332238153 41116462448881798749178615)
          ·
            refine ⟨61674693673322698123767923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41116462448881798749178615 61674693673322698123767923)
            ·
              refine ⟨92512040509984047185651885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61674693673322698123767923 92512040509984047185651885)
              ·
                refine ⟨34692015191244017694619457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92512040509984047185651885 34692015191244017694619457)
                ·
                  refine ⟨26019011393433013270964593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34692015191244017694619457 26019011393433013270964593)
                  ·
                    refine ⟨19514258545074759953223445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26019011393433013270964593 19514258545074759953223445)
                    ·
                      refine ⟨914730869300379372807349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19514258545074759953223445 914730869300379372807349)
                      ·
                        rfl

theorem cell23_1781432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_1781432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781432 prefixEnd_1781432 := by exact prefixLift 1781432
  have htrace : WordTrace (prefixWord ++ tailWord_1781432) baseStart_1781432 baseEnd_1781432 := by
    simpa [prefixWord, tailWord_1781432, baseEnd_1781432] using wordTrace_append hprefix tailTrace_1781432
  have hstable : (prefixWord ++ tailWord_1781432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781432).length < 2 ^ (prefixWord ++ tailWord_1781432).sum := by decide
  have hdescent : baseEnd_1781432 < baseStart_1781432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781436 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_1781436 : Nat := 118140960795 + 1781436 * 2 ^ 59
def prefixEnd_1781436 : Nat := 4983230072969 + 3 ^ 40 * 1781436 * 2
def baseEnd_1781436 : Nat := 914732923222997357157331

theorem tailTrace_1781436 : CollatzResearch.WordTrace tailWord_1781436 prefixEnd_1781436 914732923222997357157331 := by
  unfold tailWord_1781436
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487154387084545945862081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43316205849446061261149441 32487154387084545945862081)
  ·
    refine ⟨24365365790313409459396561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32487154387084545945862081 24365365790313409459396561)
    ·
      refine ⟨18274024342735057094547421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24365365790313409459396561 18274024342735057094547421)
      ·
        refine ⟨6852759128525646410455283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18274024342735057094547421 6852759128525646410455283)
        ·
          refine ⟨10279138692788469615682925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852759128525646410455283 10279138692788469615682925)
          ·
            refine ⟨3854677009795676105881097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10279138692788469615682925 3854677009795676105881097)
            ·
              refine ⟨2891007757346757079410823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3854677009795676105881097 2891007757346757079410823)
              ·
                refine ⟨4336511636020135619116235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2891007757346757079410823 4336511636020135619116235)
                ·
                  refine ⟨6504767454030203428674353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336511636020135619116235 6504767454030203428674353)
                  ·
                    refine ⟨4878575590522652571505765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504767454030203428674353 4878575590522652571505765)
                    ·
                      refine ⟨914732923222997357157331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4878575590522652571505765 914732923222997357157331)
                      ·
                        rfl

theorem cell23_1781436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_1781436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781436 prefixEnd_1781436 := by exact prefixLift 1781436
  have htrace : WordTrace (prefixWord ++ tailWord_1781436) baseStart_1781436 baseEnd_1781436 := by
    simpa [prefixWord, tailWord_1781436, baseEnd_1781436] using wordTrace_append hprefix tailTrace_1781436
  have hstable : (prefixWord ++ tailWord_1781436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781436).length < 2 ^ (prefixWord ++ tailWord_1781436).sum := by decide
  have hdescent : baseEnd_1781436 < baseStart_1781436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781453 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1781453 : Nat := 118140960795 + 1781453 * 2 ^ 59
def prefixEnd_1781453 : Nat := 4983230072969 + 3 ^ 40 * 1781453 * 2
def baseEnd_1781453 : Nat := 914741652394123790644753

theorem tailTrace_1781453 : CollatzResearch.WordTrace tailWord_1781453 prefixEnd_1781453 914741652394123790644753 := by
  unfold tailWord_1781453
  simp only [CollatzResearch.WordTrace]
  refine ⟨64974928815107503795093013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43316619210071669196728675 64974928815107503795093013)
  ·
    refine ⟨3045699788208164240394985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 64974928815107503795093013 3045699788208164240394985)
    ·
      refine ⟨2284274841156123180296239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3045699788208164240394985 2284274841156123180296239)
      ·
        refine ⟨3426412261734184770444359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284274841156123180296239 3426412261734184770444359)
        ·
          refine ⟨5139618392601277155666539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426412261734184770444359 5139618392601277155666539)
          ·
            refine ⟨7709427588901915733499809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139618392601277155666539 7709427588901915733499809)
            ·
              refine ⟨5782070691676436800124857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709427588901915733499809 5782070691676436800124857)
              ·
                refine ⟨4336553018757327600093643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5782070691676436800124857 4336553018757327600093643)
                ·
                  refine ⟨6504829528135991400140465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336553018757327600093643 6504829528135991400140465)
                  ·
                    refine ⟨4878622146101993550105349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6504829528135991400140465 4878622146101993550105349)
                    ·
                      refine ⟨914741652394123790644753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4878622146101993550105349 914741652394123790644753)
                      ·
                        rfl

theorem cell23_1781453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1781453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781453 prefixEnd_1781453 := by exact prefixLift 1781453
  have htrace : WordTrace (prefixWord ++ tailWord_1781453) baseStart_1781453 baseEnd_1781453 := by
    simpa [prefixWord, tailWord_1781453, baseEnd_1781453] using wordTrace_append hprefix tailTrace_1781453
  have hstable : (prefixWord ++ tailWord_1781453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781453).length < 2 ^ (prefixWord ++ tailWord_1781453).sum := by decide
  have hdescent : baseEnd_1781453 < baseStart_1781453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781460 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1781460 : Nat := 118140960795 + 1781460 * 2 ^ 59
def prefixEnd_1781460 : Nat := 4983230072969 + 3 ^ 40 * 1781460 * 2
def baseEnd_1781460 : Nat := 914745246758705263257221

theorem tailTrace_1781460 : CollatzResearch.WordTrace tailWord_1781460 prefixEnd_1781460 914745246758705263257221 := by
  unfold tailWord_1781460
  simp only [CollatzResearch.WordTrace]
  refine ⟨32487592063041071995298917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43316789417388095993731889 32487592063041071995298917)
  ·
    refine ⟨6091423511820200999118547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32487592063041071995298917 6091423511820200999118547)
    ·
      refine ⟨9137135267730301498677821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6091423511820200999118547 9137135267730301498677821)
      ·
        refine ⟨3426425725398863062004183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9137135267730301498677821 3426425725398863062004183)
        ·
          refine ⟨5139638588098294593006275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426425725398863062004183 5139638588098294593006275)
          ·
            refine ⟨7709457882147441889509413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5139638588098294593006275 7709457882147441889509413)
            ·
              refine ⟨1445523352902645354283015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7709457882147441889509413 1445523352902645354283015)
              ·
                refine ⟨2168285029353968031424523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445523352902645354283015 2168285029353968031424523)
                ·
                  refine ⟨3252427544030952047136785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168285029353968031424523 3252427544030952047136785)
                  ·
                    refine ⟨2439320658023214035352589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3252427544030952047136785 2439320658023214035352589)
                    ·
                      refine ⟨914745246758705263257221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439320658023214035352589 914745246758705263257221)
                      ·
                        rfl

theorem cell23_1781460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1781460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781460 prefixEnd_1781460 := by exact prefixLift 1781460
  have htrace : WordTrace (prefixWord ++ tailWord_1781460) baseStart_1781460 baseEnd_1781460 := by
    simpa [prefixWord, tailWord_1781460, baseEnd_1781460] using wordTrace_append hprefix tailTrace_1781460
  have hstable : (prefixWord ++ tailWord_1781460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781460).length < 2 ^ (prefixWord ++ tailWord_1781460).sum := by decide
  have hdescent : baseEnd_1781460 < baseStart_1781460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781473 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_1781473 : Nat := 118140960795 + 1781473 * 2 ^ 59
def prefixEnd_1781473 : Nat := 4983230072969 + 3 ^ 40 * 1781473 * 2
def baseEnd_1781473 : Nat := 914751922007213712394661

theorem tailTrace_1781473 : CollatzResearch.WordTrace tailWord_1781473 prefixEnd_1781473 914751922007213712394661 := by
  unfold tailWord_1781473
  simp only [CollatzResearch.WordTrace]
  refine ⟨64975658275035047210821073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43317105516690031473880715 64975658275035047210821073)
  ·
    refine ⟨48731743706276285408115805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64975658275035047210821073 48731743706276285408115805)
    ·
      refine ⟨18274403889853607028043427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48731743706276285408115805 18274403889853607028043427)
      ·
        refine ⟨27411605834780410542065141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18274403889853607028043427 27411605834780410542065141)
        ·
          refine ⟨2569838047010663488318607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27411605834780410542065141 2569838047010663488318607)
          ·
            refine ⟨3854757070515995232477911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2569838047010663488318607 3854757070515995232477911)
            ·
              refine ⟨5782135605773992848716867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3854757070515995232477911 5782135605773992848716867)
              ·
                refine ⟨8673203408660989273075301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782135605773992848716867 8673203408660989273075301)
                ·
                  refine ⟨1626225639123935488701619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8673203408660989273075301 1626225639123935488701619)
                  ·
                    refine ⟨2439338458685903233052429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626225639123935488701619 2439338458685903233052429)
                    ·
                      refine ⟨914751922007213712394661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439338458685903233052429 914751922007213712394661)
                      ·
                        rfl

theorem cell23_1781473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_1781473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781473 prefixEnd_1781473 := by exact prefixLift 1781473
  have htrace : WordTrace (prefixWord ++ tailWord_1781473) baseStart_1781473 baseEnd_1781473 := by
    simpa [prefixWord, tailWord_1781473, baseEnd_1781473] using wordTrace_append hprefix tailTrace_1781473
  have hstable : (prefixWord ++ tailWord_1781473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781473).length < 2 ^ (prefixWord ++ tailWord_1781473).sum := by decide
  have hdescent : baseEnd_1781473 < baseStart_1781473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781489 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 2, 6]
def baseStart_1781489 : Nat := 118140960795 + 1781489 * 2 ^ 59
def prefixEnd_1781489 : Nat := 4983230072969 + 3 ^ 40 * 1781489 * 2
def baseEnd_1781489 : Nat := 304920045899228549931529

theorem tailTrace_1781489 : CollatzResearch.WordTrace tailWord_1781489 prefixEnd_1781489 304920045899228549931529 := by
  unfold tailWord_1781489
  simp only [CollatzResearch.WordTrace]
  refine ⟨64976241842977081943403521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43317494561984721295602347 64976241842977081943403521)
  ·
    refine ⟨48732181382232811457552641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64976241842977081943403521 48732181382232811457552641)
    ·
      refine ⟨36549136036674608593164481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48732181382232811457552641 36549136036674608593164481)
      ·
        refine ⟨27411852027505956444873361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36549136036674608593164481 27411852027505956444873361)
        ·
          refine ⟨20558889020629467333655021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27411852027505956444873361 20558889020629467333655021)
          ·
            refine ⟨7709583382736050250120633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20558889020629467333655021 7709583382736050250120633)
            ·
              refine ⟨5782187537052037687590475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7709583382736050250120633 5782187537052037687590475)
              ·
                refine ⟨8673281305578056531385713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5782187537052037687590475 8673281305578056531385713)
                ·
                  refine ⟨6504960979183542398539285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8673281305578056531385713 6504960979183542398539285)
                  ·
                    refine ⟨304920045899228549931529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6504960979183542398539285 304920045899228549931529)
                    ·
                      rfl

theorem cell23_1781489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_1781489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781489 prefixEnd_1781489 := by exact prefixLift 1781489
  have htrace : WordTrace (prefixWord ++ tailWord_1781489) baseStart_1781489 baseEnd_1781489 := by
    simpa [prefixWord, tailWord_1781489, baseEnd_1781489] using wordTrace_append hprefix tailTrace_1781489
  have hstable : (prefixWord ++ tailWord_1781489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781489).length < 2 ^ (prefixWord ++ tailWord_1781489).sum := by decide
  have hdescent : baseEnd_1781489 < baseStart_1781489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781490 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_1781490 : Nat := 118140960795 + 1781490 * 2 ^ 59
def prefixEnd_1781490 : Nat := 4983230072969 + 3 ^ 40 * 1781490 * 2
def baseEnd_1781490 : Nat := 914760651178340145882083

theorem tailTrace_1781490 : CollatzResearch.WordTrace tailWord_1781490 prefixEnd_1781490 914760651178340145882083 := by
  unfold tailWord_1781490
  simp only [CollatzResearch.WordTrace]
  refine ⟨16244069578993364778547481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43317518877315639409459949 16244069578993364778547481)
  ·
    refine ⟨12183052184245023583910611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16244069578993364778547481 12183052184245023583910611)
    ·
      refine ⟨18274578276367535375865917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12183052184245023583910611 18274578276367535375865917)
      ·
        refine ⟨6852966853637825765949719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18274578276367535375865917 6852966853637825765949719)
        ·
          refine ⟨10279450280456738648924579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6852966853637825765949719 10279450280456738648924579)
          ·
            refine ⟨15419175420685107973386869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10279450280456738648924579 15419175420685107973386869)
            ·
              refine ⟨1445547695689228872505019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15419175420685107973386869 1445547695689228872505019)
              ·
                refine ⟨2168321543533843308757529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445547695689228872505019 2168321543533843308757529)
                ·
                  refine ⟨1626241157650382481568147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2168321543533843308757529 1626241157650382481568147)
                  ·
                    refine ⟨2439361736475573722352221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626241157650382481568147 2439361736475573722352221)
                    ·
                      refine ⟨914760651178340145882083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439361736475573722352221 914760651178340145882083)
                      ·
                        rfl

theorem cell23_1781490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_1781490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781490 prefixEnd_1781490 := by exact prefixLift 1781490
  have htrace : WordTrace (prefixWord ++ tailWord_1781490) baseStart_1781490 baseEnd_1781490 := by
    simpa [prefixWord, tailWord_1781490, baseEnd_1781490] using wordTrace_append hprefix tailTrace_1781490
  have hstable : (prefixWord ++ tailWord_1781490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781490).length < 2 ^ (prefixWord ++ tailWord_1781490).sum := by decide
  have hdescent : baseEnd_1781490 < baseStart_1781490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781496 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_1781496 : Nat := 118140960795 + 1781496 * 2 ^ 59
def prefixEnd_1781496 : Nat := 4983230072969 + 3 ^ 40 * 1781496 * 2
def baseEnd_1781496 : Nat := 914763732062267122407055

theorem tailTrace_1781496 : CollatzResearch.WordTrace tailWord_1781496 prefixEnd_1781496 914763732062267122407055 := by
  unfold tailWord_1781496
  simp only [CollatzResearch.WordTrace]
  refine ⟨32488248576975861069454171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43317664769301148092605561 32488248576975861069454171)
  ·
    refine ⟨48732372865463791604181257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32488248576975861069454171 48732372865463791604181257)
    ·
      refine ⟨36549279649097843703135943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48732372865463791604181257 36549279649097843703135943)
      ·
        refine ⟨54823919473646765554703915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36549279649097843703135943 54823919473646765554703915)
        ·
          refine ⟨82235879210470148332055873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54823919473646765554703915 82235879210470148332055873)
          ·
            refine ⟨61676909407852611249041905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82235879210470148332055873 61676909407852611249041905)
            ·
              refine ⟨46257682055889458436781429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61676909407852611249041905 46257682055889458436781429)
              ·
                refine ⟨4336657692739636728448259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46257682055889458436781429 4336657692739636728448259)
                ·
                  refine ⟨6504986539109455092672389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4336657692739636728448259 6504986539109455092672389)
                  ·
                    refine ⟨1219684976083022829876073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6504986539109455092672389 1219684976083022829876073)
                    ·
                      refine ⟨914763732062267122407055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1219684976083022829876073 914763732062267122407055)
                      ·
                        rfl

theorem cell23_1781496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_1781496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781496 prefixEnd_1781496 := by exact prefixLift 1781496
  have htrace : WordTrace (prefixWord ++ tailWord_1781496) baseStart_1781496 baseEnd_1781496 := by
    simpa [prefixWord, tailWord_1781496, baseEnd_1781496] using wordTrace_append hprefix tailTrace_1781496
  have hstable : (prefixWord ++ tailWord_1781496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781496).length < 2 ^ (prefixWord ++ tailWord_1781496).sum := by decide
  have hdescent : baseEnd_1781496 < baseStart_1781496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781660 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 6]
def baseStart_1781660 : Nat := 118140960795 + 1781660 * 2 ^ 59
def prefixEnd_1781660 : Nat := 4983230072969 + 3 ^ 40 * 1781660 * 2
def baseEnd_1781660 : Nat := 101649771432178275639589

theorem tailTrace_1781660 : CollatzResearch.WordTrace tailWord_1781660 prefixEnd_1781660 101649771432178275639589 := by
  unfold tailWord_1781660
  simp only [CollatzResearch.WordTrace]
  refine ⟨32491239362678789073939217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43321652483571718765252289 32491239362678789073939217)
  ·
    refine ⟨24368429522009091805454413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32491239362678789073939217 24368429522009091805454413)
    ·
      refine ⟨9138161070753409427045405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24368429522009091805454413 9138161070753409427045405)
      ·
        refine ⟨3426810401532528535142027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9138161070753409427045405 3426810401532528535142027)
        ·
          refine ⟨5140215602298792802713041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3426810401532528535142027 5140215602298792802713041)
          ·
            refine ⟨3855161701724094602034781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5140215602298792802713041 3855161701724094602034781)
            ·
              refine ⟨1445685638146535475763043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3855161701724094602034781 1445685638146535475763043)
              ·
                refine ⟨2168528457219803213644565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445685638146535475763043 2168528457219803213644565)
                ·
                  refine ⟨101649771432178275639589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2168528457219803213644565 101649771432178275639589)
                  ·
                    rfl

theorem cell23_1781660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_1781660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781660 prefixEnd_1781660 := by exact prefixLift 1781660
  have htrace : WordTrace (prefixWord ++ tailWord_1781660) baseStart_1781660 baseEnd_1781660 := by
    simpa [prefixWord, tailWord_1781660, baseEnd_1781660] using wordTrace_append hprefix tailTrace_1781660
  have hstable : (prefixWord ++ tailWord_1781660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781660).length < 2 ^ (prefixWord ++ tailWord_1781660).sum := by decide
  have hdescent : baseEnd_1781660 < baseStart_1781660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781703 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 2, 4]
def baseStart_1781703 : Nat := 118140960795 + 1781703 * 2 ^ 59
def prefixEnd_1781703 : Nat := 4983230072969 + 3 ^ 40 * 1781703 * 2
def baseEnd_1781703 : Nat := 304956674185915937506201

theorem tailTrace_1781703 : CollatzResearch.WordTrace tailWord_1781703 prefixEnd_1781703 304956674185915937506201 := by
  unfold tailWord_1781703
  simp only [CollatzResearch.WordTrace]
  refine ⟨64984047064201796491693763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43322698042801197661129175 64984047064201796491693763)
  ·
    refine ⟨97476070596302694737540645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64984047064201796491693763 97476070596302694737540645)
    ·
      refine ⟨18276763236806755263288871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97476070596302694737540645 18276763236806755263288871)
      ·
        refine ⟨27415144855210132894933307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18276763236806755263288871 27415144855210132894933307)
        ·
          refine ⟨41122717282815199342399961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27415144855210132894933307 41122717282815199342399961)
          ·
            refine ⟨30842037962111399506799971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41122717282815199342399961 30842037962111399506799971)
            ·
              refine ⟨46263056943167099260199957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30842037962111399506799971 46263056943167099260199957)
              ·
                refine ⟨2168580794210957777821873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46263056943167099260199957 2168580794210957777821873)
                ·
                  refine ⟨1626435595658218333366405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2168580794210957777821873 1626435595658218333366405)
                  ·
                    refine ⟨304956674185915937506201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1626435595658218333366405 304956674185915937506201)
                    ·
                      rfl

theorem cell23_1781703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_1781703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781703 prefixEnd_1781703 := by exact prefixLift 1781703
  have htrace : WordTrace (prefixWord ++ tailWord_1781703) baseStart_1781703 baseEnd_1781703 := by
    simpa [prefixWord, tailWord_1781703, baseEnd_1781703] using wordTrace_append hprefix tailTrace_1781703
  have hstable : (prefixWord ++ tailWord_1781703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781703).length < 2 ^ (prefixWord ++ tailWord_1781703).sum := by decide
  have hdescent : baseEnd_1781703 < baseStart_1781703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781704 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_1781704 : Nat := 118140960795 + 1781704 * 2 ^ 59
def prefixEnd_1781704 : Nat := 4983230072969 + 3 ^ 40 * 1781704 * 2
def baseEnd_1781704 : Nat := 914870536038402308606099

theorem tailTrace_1781704 : CollatzResearch.WordTrace tailWord_1781704 prefixEnd_1781704 914870536038402308606099 := by
  unfold tailWord_1781704
  simp only [CollatzResearch.WordTrace]
  refine ⟨32492041768599086831240083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43322722358132115774986777 32492041768599086831240083)
  ·
    refine ⟨48738062652898630246860125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32492041768599086831240083 48738062652898630246860125)
    ·
      refine ⟨18276773494836986342572547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48738062652898630246860125 18276773494836986342572547)
      ·
        refine ⟨27415160242255479513858821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18276773494836986342572547 27415160242255479513858821)
        ·
          refine ⟨5140342545422902408848529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27415160242255479513858821 5140342545422902408848529)
          ·
            refine ⟨3855256909067176806636397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5140342545422902408848529 3855256909067176806636397)
            ·
              refine ⟨1445721340900191302488649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3855256909067176806636397 1445721340900191302488649)
              ·
                refine ⟨1084291005675143476866487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445721340900191302488649 1084291005675143476866487)
                ·
                  refine ⟨1626436508512715215299731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084291005675143476866487 1626436508512715215299731)
                  ·
                    refine ⟨2439654762769072822949597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626436508512715215299731 2439654762769072822949597)
                    ·
                      refine ⟨914870536038402308606099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439654762769072822949597 914870536038402308606099)
                      ·
                        rfl

theorem cell23_1781704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_1781704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781704 prefixEnd_1781704 := by exact prefixLift 1781704
  have htrace : WordTrace (prefixWord ++ tailWord_1781704) baseStart_1781704 baseEnd_1781704 := by
    simpa [prefixWord, tailWord_1781704, baseEnd_1781704] using wordTrace_append hprefix tailTrace_1781704
  have hstable : (prefixWord ++ tailWord_1781704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781704).length < 2 ^ (prefixWord ++ tailWord_1781704).sum := by decide
  have hdescent : baseEnd_1781704 < baseStart_1781704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781706 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_1781706 : Nat := 118140960795 + 1781706 * 2 ^ 59
def prefixEnd_1781706 : Nat := 4983230072969 + 3 ^ 40 * 1781706 * 2
def baseEnd_1781706 : Nat := 914871562999711300781089

theorem tailTrace_1781706 : CollatzResearch.WordTrace tailWord_1781706 prefixEnd_1781706 914871562999711300781089 := by
  unfold tailWord_1781706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16246039120797732001013243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43322770988793952002701981 16246039120797732001013243)
  ·
    refine ⟨24369058681196598001519865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16246039120797732001013243 24369058681196598001519865)
    ·
      refine ⟨18276794010897448501139899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24369058681196598001519865 18276794010897448501139899)
      ·
        refine ⟨27415191016346172751709849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18276794010897448501139899 27415191016346172751709849)
        ·
          refine ⟨20561393262259629563782387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27415191016346172751709849 20561393262259629563782387)
          ·
            refine ⟨30842089893389444345673581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20561393262259629563782387 30842089893389444345673581)
            ·
              refine ⟨11565783710021041629627593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30842089893389444345673581 11565783710021041629627593)
              ·
                refine ⟨8674337782515781222220695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11565783710021041629627593 8674337782515781222220695)
                ·
                  refine ⟨13011506673773671833331043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8674337782515781222220695 13011506673773671833331043)
                  ·
                    refine ⟨19517260010660507749996565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13011506673773671833331043 19517260010660507749996565)
                    ·
                      refine ⟨914871562999711300781089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19517260010660507749996565 914871562999711300781089)
                      ·
                        rfl

theorem cell23_1781706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_1781706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781706 prefixEnd_1781706 := by exact prefixLift 1781706
  have htrace : WordTrace (prefixWord ++ tailWord_1781706) baseStart_1781706 baseEnd_1781706 := by
    simpa [prefixWord, tailWord_1781706, baseEnd_1781706] using wordTrace_append hprefix tailTrace_1781706
  have hstable : (prefixWord ++ tailWord_1781706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781706).length < 2 ^ (prefixWord ++ tailWord_1781706).sum := by decide
  have hdescent : baseEnd_1781706 < baseStart_1781706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781743 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_1781743 : Nat := 118140960795 + 1781743 * 2 ^ 59
def prefixEnd_1781743 : Nat := 4983230072969 + 3 ^ 40 * 1781743 * 2
def baseEnd_1781743 : Nat := 914890561783927656018419

theorem tailTrace_1781743 : CollatzResearch.WordTrace tailWord_1781743 prefixEnd_1781743 914890561783927656018419 := by
  unfold tailWord_1781743
  simp only [CollatzResearch.WordTrace]
  refine ⟨64985505984056883323149883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43323670656037922215433255 64985505984056883323149883)
  ·
    refine ⟨97478258976085324984724825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64985505984056883323149883 97478258976085324984724825)
    ·
      refine ⟨73108694232063993738543619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97478258976085324984724825 73108694232063993738543619)
      ·
        refine ⟨109663041348095990607815429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73108694232063993738543619 109663041348095990607815429)
        ·
          refine ⟨20561820252767998238965393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109663041348095990607815429 20561820252767998238965393)
          ·
            refine ⟨15421365189575998679224045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20561820252767998238965393 15421365189575998679224045)
            ·
              refine ⟨5783011946090999504709017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15421365189575998679224045 5783011946090999504709017)
              ·
                refine ⟨4337258959568249628531763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5783011946090999504709017 4337258959568249628531763)
                ·
                  refine ⟨6505888439352374442797645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4337258959568249628531763 6505888439352374442797645)
                  ·
                    refine ⟨2439708164757140416049117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6505888439352374442797645 2439708164757140416049117)
                    ·
                      refine ⟨914890561783927656018419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439708164757140416049117 914890561783927656018419)
                      ·
                        rfl

theorem cell23_1781743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_1781743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781743 prefixEnd_1781743 := by exact prefixLift 1781743
  have htrace : WordTrace (prefixWord ++ tailWord_1781743) baseStart_1781743 baseEnd_1781743 := by
    simpa [prefixWord, tailWord_1781743, baseEnd_1781743] using wordTrace_append hprefix tailTrace_1781743
  have hstable : (prefixWord ++ tailWord_1781743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781743).length < 2 ^ (prefixWord ++ tailWord_1781743).sum := by decide
  have hdescent : baseEnd_1781743 < baseStart_1781743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781776 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_1781776 : Nat := 118140960795 + 1781776 * 2 ^ 59
def prefixEnd_1781776 : Nat := 4983230072969 + 3 ^ 40 * 1781776 * 2
def baseEnd_1781776 : Nat := 304969168881842008968589

theorem tailTrace_1781776 : CollatzResearch.WordTrace tailWord_1781776 prefixEnd_1781776 304969168881842008968589 := by
  unfold tailWord_1781776
  simp only [CollatzResearch.WordTrace]
  refine ⟨32493354796468664979550591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43324473061958219972734121 32493354796468664979550591)
  ·
    refine ⟨48740032194702997469325887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32493354796468664979550591 48740032194702997469325887)
    ·
      refine ⟨73110048292054496203988831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48740032194702997469325887 73110048292054496203988831)
      ·
        refine ⟨109665072438081744305983247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73110048292054496203988831 109665072438081744305983247)
        ·
          refine ⟨164497608657122616458974871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109665072438081744305983247 164497608657122616458974871)
          ·
            refine ⟨246746412985683924688462307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164497608657122616458974871 246746412985683924688462307)
            ·
              refine ⟨370119619478525887032693461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246746412985683924688462307 370119619478525887032693461)
              ·
                refine ⟨8674678581527950477328753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 370119619478525887032693461 8674678581527950477328753)
                ·
                  refine ⟨6506008936145962857996565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674678581527950477328753 6506008936145962857996565)
                  ·
                    refine ⟨304969168881842008968589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6506008936145962857996565 304969168881842008968589)
                    ·
                      rfl

theorem cell23_1781776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_1781776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781776 prefixEnd_1781776 := by exact prefixLift 1781776
  have htrace : WordTrace (prefixWord ++ tailWord_1781776) baseStart_1781776 baseEnd_1781776 := by
    simpa [prefixWord, tailWord_1781776, baseEnd_1781776] using wordTrace_append hprefix tailTrace_1781776
  have hstable : (prefixWord ++ tailWord_1781776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781776).length < 2 ^ (prefixWord ++ tailWord_1781776).sum := by decide
  have hdescent : baseEnd_1781776 < baseStart_1781776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781813 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1781813 : Nat := 118140960795 + 1781813 * 2 ^ 59
def prefixEnd_1781813 : Nat := 4983230072969 + 3 ^ 40 * 1781813 * 2
def baseEnd_1781813 : Nat := 914926505429742382143097

theorem tailTrace_1781813 : CollatzResearch.WordTrace tailWord_1781813 prefixEnd_1781813 914926505429742382143097 := by
  unfold tailWord_1781813
  simp only [CollatzResearch.WordTrace]
  refine ⟨64988059093803285278198093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43325372729202190185465395 64988059093803285278198093)
  ·
    refine ⟨24370522160176231979324285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64988059093803285278198093 24370522160176231979324285)
    ·
      refine ⟨9138945810066086992246607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24370522160176231979324285 9138945810066086992246607)
      ·
        refine ⟨13708418715099130488369911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9138945810066086992246607 13708418715099130488369911)
        ·
          refine ⟨20562628072648695732554867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13708418715099130488369911 20562628072648695732554867)
          ·
            refine ⟨30843942108973043598832301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20562628072648695732554867 30843942108973043598832301)
            ·
              refine ⟨11566478290864891349562113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30843942108973043598832301 11566478290864891349562113)
              ·
                refine ⟨8674858718148668512171585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11566478290864891349562113 8674858718148668512171585)
                ·
                  refine ⟨6506144038611501384128689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674858718148668512171585 6506144038611501384128689)
                  ·
                    refine ⟨4879608028958626038096517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6506144038611501384128689 4879608028958626038096517)
                    ·
                      refine ⟨914926505429742382143097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4879608028958626038096517 914926505429742382143097)
                      ·
                        rfl

theorem cell23_1781813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1781813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781813 prefixEnd_1781813 := by exact prefixLift 1781813
  have htrace : WordTrace (prefixWord ++ tailWord_1781813) baseStart_1781813 baseEnd_1781813 := by
    simpa [prefixWord, tailWord_1781813, baseEnd_1781813] using wordTrace_append hprefix tailTrace_1781813
  have hstable : (prefixWord ++ tailWord_1781813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781813).length < 2 ^ (prefixWord ++ tailWord_1781813).sum := by decide
  have hdescent : baseEnd_1781813 < baseStart_1781813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781833 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 3]
def baseStart_1781833 : Nat := 118140960795 + 1781833 * 2 ^ 59
def prefixEnd_1781833 : Nat := 4983230072969 + 3 ^ 40 * 1781833 * 2
def baseEnd_1781833 : Nat := 914936775042832303893005

theorem tailTrace_1781833 : CollatzResearch.WordTrace tailWord_1781833 prefixEnd_1781833 914936775042832303893005 := by
  unfold tailWord_1781833
  simp only [CollatzResearch.WordTrace]
  refine ⟨64988788553730828693926153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43325859035820552462617435 64988788553730828693926153)
  ·
    refine ⟨48741591415298121520444615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64988788553730828693926153 48741591415298121520444615)
    ·
      refine ⟨73112387122947182280666923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48741591415298121520444615 73112387122947182280666923)
      ·
        refine ⟨109668580684420773421000385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73112387122947182280666923 109668580684420773421000385)
        ·
          refine ⟨82251435513315580065750289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109668580684420773421000385 82251435513315580065750289)
          ·
            refine ⟨61688576634986685049312717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82251435513315580065750289 61688576634986685049312717)
            ·
              refine ⟨23133216238120006893492269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61688576634986685049312717 23133216238120006893492269)
              ·
                refine ⟨8674956089295002585059601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23133216238120006893492269 8674956089295002585059601)
                ·
                  refine ⟨6506217066971251938794701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8674956089295002585059601 6506217066971251938794701)
                  ·
                    refine ⟨2439831400114219477048013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6506217066971251938794701 2439831400114219477048013)
                    ·
                      refine ⟨914936775042832303893005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2439831400114219477048013 914936775042832303893005)
                      ·
                        rfl

theorem cell23_1781833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_1781833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781833 prefixEnd_1781833 := by exact prefixLift 1781833
  have htrace : WordTrace (prefixWord ++ tailWord_1781833) baseStart_1781833 baseEnd_1781833 := by
    simpa [prefixWord, tailWord_1781833, baseEnd_1781833] using wordTrace_append hprefix tailTrace_1781833
  have hstable : (prefixWord ++ tailWord_1781833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781833).length < 2 ^ (prefixWord ++ tailWord_1781833).sum := by decide
  have hdescent : baseEnd_1781833 < baseStart_1781833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781854 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_1781854 : Nat := 118140960795 + 1781854 * 2 ^ 59
def prefixEnd_1781854 : Nat := 4983230072969 + 3 ^ 40 * 1781854 * 2
def baseEnd_1781854 : Nat := 914947558136576721730409

theorem tailTrace_1781854 : CollatzResearch.WordTrace tailWord_1781854 prefixEnd_1781854 914947558136576721730409 := by
  unfold tailWord_1781854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8123694310831843660055077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43326369657769832853627077 8123694310831843660055077)
  ·
    refine ⟨1523192683280970686260327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8123694310831843660055077 1523192683280970686260327)
    ·
      refine ⟨2284789024921456029390491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523192683280970686260327 2284789024921456029390491)
      ·
        refine ⟨3427183537382184044085737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284789024921456029390491 3427183537382184044085737)
        ·
          refine ⟨2570387653036638033064303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3427183537382184044085737 2570387653036638033064303)
          ·
            refine ⟨3855581479554957049596455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2570387653036638033064303 3855581479554957049596455)
            ·
              refine ⟨5783372219332435574394683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855581479554957049596455 5783372219332435574394683)
              ·
                refine ⟨8675058328998653361592025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783372219332435574394683 8675058328998653361592025)
                ·
                  refine ⟨6506293746748990021194019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8675058328998653361592025 6506293746748990021194019)
                  ·
                    refine ⟨9759440620123485031791029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6506293746748990021194019 9759440620123485031791029)
                    ·
                      refine ⟨914947558136576721730409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9759440620123485031791029 914947558136576721730409)
                      ·
                        rfl

theorem cell23_1781854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_1781854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781854 prefixEnd_1781854 := by exact prefixLift 1781854
  have htrace : WordTrace (prefixWord ++ tailWord_1781854) baseStart_1781854 baseEnd_1781854 := by
    simpa [prefixWord, tailWord_1781854, baseEnd_1781854] using wordTrace_append hprefix tailTrace_1781854
  have hstable : (prefixWord ++ tailWord_1781854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781854).length < 2 ^ (prefixWord ++ tailWord_1781854).sum := by decide
  have hdescent : baseEnd_1781854 < baseStart_1781854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781863 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1781863 : Nat := 118140960795 + 1781863 * 2 ^ 59
def prefixEnd_1781863 : Nat := 4983230072969 + 3 ^ 40 * 1781863 * 2
def baseEnd_1781863 : Nat := 914952179462467186517867

theorem tailTrace_1781863 : CollatzResearch.WordTrace tailWord_1781863 prefixEnd_1781863 914952179462467186517867 := by
  unfold tailWord_1781863
  simp only [CollatzResearch.WordTrace]
  refine ⟨64989882743622143817518243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43326588495748095878345495 64989882743622143817518243)
  ·
    refine ⟨97484824115433215726277365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64989882743622143817518243 97484824115433215726277365)
    ·
      refine ⟨9139202260821863974338503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97484824115433215726277365 9139202260821863974338503)
      ·
        refine ⟨13708803391232795961507755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9139202260821863974338503 13708803391232795961507755)
        ·
          refine ⟨20563205086849193942261633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13708803391232795961507755 20563205086849193942261633)
          ·
            refine ⟨15422403815136895456696225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20563205086849193942261633 15422403815136895456696225)
            ·
              refine ⟨11566802861352671592522169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15422403815136895456696225 11566802861352671592522169)
              ·
                refine ⟨8675102146014503694391627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11566802861352671592522169 8675102146014503694391627)
                ·
                  refine ⟨13012653219021755541587441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675102146014503694391627 13012653219021755541587441)
                  ·
                    refine ⟨9759489914266316656190581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13012653219021755541587441 9759489914266316656190581)
                    ·
                      refine ⟨914952179462467186517867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9759489914266316656190581 914952179462467186517867)
                      ·
                        rfl

theorem cell23_1781863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1781863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781863 prefixEnd_1781863 := by exact prefixLift 1781863
  have htrace : WordTrace (prefixWord ++ tailWord_1781863) baseStart_1781863 baseEnd_1781863 := by
    simpa [prefixWord, tailWord_1781863, baseEnd_1781863] using wordTrace_append hprefix tailTrace_1781863
  have hstable : (prefixWord ++ tailWord_1781863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781863).length < 2 ^ (prefixWord ++ tailWord_1781863).sum := by decide
  have hdescent : baseEnd_1781863 < baseStart_1781863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781870 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1781870 : Nat := 118140960795 + 1781870 * 2 ^ 59
def prefixEnd_1781870 : Nat := 4983230072969 + 3 ^ 40 * 1781870 * 2
def baseEnd_1781870 : Nat := 304985257942349553043445

theorem tailTrace_1781870 : CollatzResearch.WordTrace tailWord_1781870 prefixEnd_1781870 304985257942349553043445 := by
  unfold tailWord_1781870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8123767256824598001627883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43326758703064522675348709 8123767256824598001627883)
  ·
    refine ⟨12185650885236897002441825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8123767256824598001627883 12185650885236897002441825)
    ·
      refine ⟨9139238163927672751831369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12185650885236897002441825 9139238163927672751831369)
      ·
        refine ⟨6854428622945754563873527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9139238163927672751831369 6854428622945754563873527)
        ·
          refine ⟨10281642934418631845810291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854428622945754563873527 10281642934418631845810291)
          ·
            refine ⟨15422464401627947768715437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10281642934418631845810291 15422464401627947768715437)
            ·
              refine ⟨5783424150610480413268289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15422464401627947768715437 5783424150610480413268289)
              ·
                refine ⟨4337568112957860309951217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5783424150610480413268289 4337568112957860309951217)
                ·
                  refine ⟨3253176084718395232463413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4337568112957860309951217 3253176084718395232463413)
                  ·
                    refine ⟨304985257942349553043445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3253176084718395232463413 304985257942349553043445)
                    ·
                      rfl

theorem cell23_1781870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1781870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781870 prefixEnd_1781870 := by exact prefixLift 1781870
  have htrace : WordTrace (prefixWord ++ tailWord_1781870) baseStart_1781870 baseEnd_1781870 := by
    simpa [prefixWord, tailWord_1781870, baseEnd_1781870] using wordTrace_append hprefix tailTrace_1781870
  have hstable : (prefixWord ++ tailWord_1781870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781870).length < 2 ^ (prefixWord ++ tailWord_1781870).sum := by decide
  have hdescent : baseEnd_1781870 < baseStart_1781870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781960 : List Nat := [2, 1, 3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_1781960 : Nat := 118140960795 + 1781960 * 2 ^ 59
def prefixEnd_1781960 : Nat := 4983230072969 + 3 ^ 40 * 1781960 * 2
def baseEnd_1781960 : Nat := 305000662361984435668307

theorem tailTrace_1781960 : CollatzResearch.WordTrace tailWord_1781960 prefixEnd_1781960 305000662361984435668307 := by
  unfold tailWord_1781960
  simp only [CollatzResearch.WordTrace]
  refine ⟨32496710312135364691899667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43328947082847152922532889 32496710312135364691899667)
  ·
    refine ⟨48745065468203047037849501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32496710312135364691899667 48745065468203047037849501)
    ·
      refine ⟨18279399550576142639193563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48745065468203047037849501 18279399550576142639193563)
      ·
        refine ⟨27419099325864213958790345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18279399550576142639193563 27419099325864213958790345)
        ·
          refine ⟨20564324494398160469092759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27419099325864213958790345 20564324494398160469092759)
          ·
            refine ⟨30846486741597240703639139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20564324494398160469092759 30846486741597240703639139)
            ·
              refine ⟨46269730112395861055458709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30846486741597240703639139 46269730112395861055458709)
              ·
                refine ⟨2168893599018555986974627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46269730112395861055458709 2168893599018555986974627)
                ·
                  refine ⟨3253340398527833980461941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168893599018555986974627 3253340398527833980461941)
                  ·
                    refine ⟨305000662361984435668307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3253340398527833980461941 305000662361984435668307)
                    ·
                      rfl

theorem cell23_1781960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_1781960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781960 prefixEnd_1781960 := by exact prefixLift 1781960
  have htrace : WordTrace (prefixWord ++ tailWord_1781960) baseStart_1781960 baseEnd_1781960 := by
    simpa [prefixWord, tailWord_1781960, baseEnd_1781960] using wordTrace_append hprefix tailTrace_1781960
  have hstable : (prefixWord ++ tailWord_1781960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781960).length < 2 ^ (prefixWord ++ tailWord_1781960).sum := by decide
  have hdescent : baseEnd_1781960 < baseStart_1781960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781977 : List Nat := [1, 2, 1, 2, 3, 1, 6, 1, 1, 5]
def baseStart_1781977 : Nat := 118140960795 + 1781977 * 2 ^ 59
def prefixEnd_1781977 : Nat := 4983230072969 + 3 ^ 40 * 1781977 * 2
def baseEnd_1781977 : Nat := 305003572085693246830781

theorem tailTrace_1781977 : CollatzResearch.WordTrace tailWord_1781977 prefixEnd_1781977 305003572085693246830781 := by
  unfold tailWord_1781977
  simp only [CollatzResearch.WordTrace]
  refine ⟨64994040665209141287168185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43329360443472760858112123 64994040665209141287168185)
  ·
    refine ⟨48745530498906855965376139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64994040665209141287168185 48745530498906855965376139)
    ·
      refine ⟨73118295748360283948064209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48745530498906855965376139 73118295748360283948064209)
      ·
        refine ⟨54838721811270212961048157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73118295748360283948064209 54838721811270212961048157)
        ·
          refine ⟨20564520679226329860393059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54838721811270212961048157 20564520679226329860393059)
          ·
            refine ⟨30846781018839494790589589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20564520679226329860393059 30846781018839494790589589)
            ·
              refine ⟨1445942860258101318308887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30846781018839494790589589 1445942860258101318308887)
              ·
                refine ⟨2168914290387151977463331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1445942860258101318308887 2168914290387151977463331)
                ·
                  refine ⟨3253371435580727966194997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168914290387151977463331 3253371435580727966194997)
                  ·
                    refine ⟨305003572085693246830781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3253371435580727966194997 305003572085693246830781)
                    ·
                      rfl

theorem cell23_1781977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 1, 1, 5].length) (baseStart_1781977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781977 prefixEnd_1781977 := by exact prefixLift 1781977
  have htrace : WordTrace (prefixWord ++ tailWord_1781977) baseStart_1781977 baseEnd_1781977 := by
    simpa [prefixWord, tailWord_1781977, baseEnd_1781977] using wordTrace_append hprefix tailTrace_1781977
  have hstable : (prefixWord ++ tailWord_1781977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781977).length < 2 ^ (prefixWord ++ tailWord_1781977).sum := by decide
  have hdescent : baseEnd_1781977 < baseStart_1781977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781991 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1781991 : Nat := 118140960795 + 1781991 * 2 ^ 59
def prefixEnd_1781991 : Nat := 4983230072969 + 3 ^ 40 * 1781991 * 2
def baseEnd_1781991 : Nat := 915017904986242685717279

theorem tailTrace_1781991 : CollatzResearch.WordTrace tailWord_1781991 prefixEnd_1781991 915017904986242685717279 := by
  unfold tailWord_1781991
  simp only [CollatzResearch.WordTrace]
  refine ⟨64994551287158421678177827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43329700858105614452118551 64994551287158421678177827)
  ·
    refine ⟨97491826930737632517266741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64994551287158421678177827 97491826930737632517266741)
    ·
      refine ⟨9139858774756653048493757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97491826930737632517266741 9139858774756653048493757)
      ·
        refine ⟨3427447040533744893185159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9139858774756653048493757 3427447040533744893185159)
        ·
          refine ⟨5141170560800617339777739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427447040533744893185159 5141170560800617339777739)
          ·
            refine ⟨7711755841200926009666609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141170560800617339777739 7711755841200926009666609)
            ·
              refine ⟨5783816880900694507249957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7711755841200926009666609 5783816880900694507249957)
              ·
                refine ⟨1084465665168880220109367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5783816880900694507249957 1084465665168880220109367)
                ·
                  refine ⟨1626698497753320330164051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1084465665168880220109367 1626698497753320330164051)
                  ·
                    refine ⟨2440047746629980495246077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1626698497753320330164051 2440047746629980495246077)
                    ·
                      refine ⟨915017904986242685717279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2440047746629980495246077 915017904986242685717279)
                      ·
                        rfl

theorem cell23_1781991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1781991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781991 prefixEnd_1781991 := by exact prefixLift 1781991
  have htrace : WordTrace (prefixWord ++ tailWord_1781991) baseStart_1781991 baseEnd_1781991 := by
    simpa [prefixWord, tailWord_1781991, baseEnd_1781991] using wordTrace_append hprefix tailTrace_1781991
  have hstable : (prefixWord ++ tailWord_1781991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781991).length < 2 ^ (prefixWord ++ tailWord_1781991).sum := by decide
  have hdescent : baseEnd_1781991 < baseStart_1781991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1781993 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 6]
def baseStart_1781993 : Nat := 118140960795 + 1781993 * 2 ^ 59
def prefixEnd_1781993 : Nat := 4983230072969 + 3 ^ 40 * 1781993 * 2
def baseEnd_1781993 : Nat := 915018931947551677892269

theorem tailTrace_1781993 : CollatzResearch.WordTrace tailWord_1781993 prefixEnd_1781993 915018931947551677892269 := by
  unfold tailWord_1781993
  simp only [CollatzResearch.WordTrace]
  refine ⟨64994624233151176019750633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43329749488767450679833755 64994624233151176019750633)
  ·
    refine ⟨48745968174863382014812975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64994624233151176019750633 48745968174863382014812975)
    ·
      refine ⟨73118952262295073022219463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48745968174863382014812975 73118952262295073022219463)
      ·
        refine ⟨109678428393442609533329195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73118952262295073022219463 109678428393442609533329195)
        ·
          refine ⟨164517642590163914299993793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109678428393442609533329195 164517642590163914299993793)
          ·
            refine ⟨123388231942622935724995345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164517642590163914299993793 123388231942622935724995345)
            ·
              refine ⟨92541173956967201793746509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123388231942622935724995345 92541173956967201793746509)
              ·
                refine ⟨34702940233862700672654941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92541173956967201793746509 34702940233862700672654941)
                ·
                  refine ⟨13013602587698512752245603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34702940233862700672654941 13013602587698512752245603)
                  ·
                    refine ⟨19520403881547769128368405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13013602587698512752245603 19520403881547769128368405)
                    ·
                      refine ⟨915018931947551677892269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19520403881547769128368405 915018931947551677892269)
                      ·
                        rfl

theorem cell23_1781993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_1781993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1781993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1781993 prefixEnd_1781993 := by exact prefixLift 1781993
  have htrace : WordTrace (prefixWord ++ tailWord_1781993) baseStart_1781993 baseEnd_1781993 := by
    simpa [prefixWord, tailWord_1781993, baseEnd_1781993] using wordTrace_append hprefix tailTrace_1781993
  have hstable : (prefixWord ++ tailWord_1781993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1781993).length < 2 ^ (prefixWord ++ tailWord_1781993).sum := by decide
  have hdescent : baseEnd_1781993 < baseStart_1781993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1781993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782000 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3]
def baseStart_1782000 : Nat := 118140960795 + 1782000 * 2 ^ 59
def prefixEnd_1782000 : Nat := 4983230072969 + 3 ^ 40 * 1782000 * 2
def baseEnd_1782000 : Nat := 915022526312133150504737

theorem tailTrace_1782000 : CollatzResearch.WordTrace tailWord_1782000 prefixEnd_1782000 915022526312133150504737 := by
  unfold tailWord_1782000
  simp only [CollatzResearch.WordTrace]
  refine ⟨32497439772062908107627727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43329919696083877476836969 32497439772062908107627727)
  ·
    refine ⟨48746159658094362161441591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32497439772062908107627727 48746159658094362161441591)
    ·
      refine ⟨73119239487141543242162387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48746159658094362161441591 73119239487141543242162387)
      ·
        refine ⟨109678859230712314863243581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73119239487141543242162387 109678859230712314863243581)
        ·
          refine ⟨41129572211517118073716343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109678859230712314863243581 41129572211517118073716343)
          ·
            refine ⟨61694358317275677110574515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41129572211517118073716343 61694358317275677110574515)
            ·
              refine ⟨92541537475913515665861773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61694358317275677110574515 92541537475913515665861773)
              ·
                refine ⟨34703076553467568374698165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92541537475913515665861773 34703076553467568374698165)
                ·
                  refine ⟨3253413426887584535127953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34703076553467568374698165 3253413426887584535127953)
                  ·
                    refine ⟨2440060070165688401345965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3253413426887584535127953 2440060070165688401345965)
                    ·
                      refine ⟨915022526312133150504737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2440060070165688401345965 915022526312133150504737)
                      ·
                        rfl

theorem cell23_1782000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3].length) (baseStart_1782000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782000 prefixEnd_1782000 := by exact prefixLift 1782000
  have htrace : WordTrace (prefixWord ++ tailWord_1782000) baseStart_1782000 baseEnd_1782000 := by
    simpa [prefixWord, tailWord_1782000, baseEnd_1782000] using wordTrace_append hprefix tailTrace_1782000
  have hstable : (prefixWord ++ tailWord_1782000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782000).length < 2 ^ (prefixWord ++ tailWord_1782000).sum := by decide
  have hdescent : baseEnd_1782000 < baseStart_1782000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782003 : List Nat := [1, 1, 1, 2, 2, 4, 2, 10]
def baseStart_1782003 : Nat := 118140960795 + 1782003 * 2 ^ 59
def prefixEnd_1782003 : Nat := 4983230072969 + 3 ^ 40 * 1782003 * 2
def baseEnd_1782003 : Nat := 33889780250151727361749

theorem tailTrace_1782003 : CollatzResearch.WordTrace tailWord_1782003 prefixEnd_1782003 33889780250151727361749 := by
  unfold tailWord_1782003
  simp only [CollatzResearch.WordTrace]
  refine ⟨64994988963114947727614663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43329992642076631818409775 64994988963114947727614663)
  ·
    refine ⟨97492483444672421591421995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64994988963114947727614663 97492483444672421591421995)
    ·
      refine ⟨146238725167008632387132993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97492483444672421591421995 146238725167008632387132993)
      ·
        refine ⟨109679043875256474290349745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146238725167008632387132993 109679043875256474290349745)
        ·
          refine ⟨82259282906442355717762309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109679043875256474290349745 82259282906442355717762309)
          ·
            refine ⟨15423615544957941697080433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82259282906442355717762309 15423615544957941697080433)
            ·
              refine ⟨11567711658718456272810325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15423615544957941697080433 11567711658718456272810325)
              ·
                refine ⟨33889780250151727361749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11567711658718456272810325 33889780250151727361749)
                ·
                  rfl

theorem cell23_1782003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 10].length) (baseStart_1782003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782003 prefixEnd_1782003 := by exact prefixLift 1782003
  have htrace : WordTrace (prefixWord ++ tailWord_1782003) baseStart_1782003 baseEnd_1782003 := by
    simpa [prefixWord, tailWord_1782003, baseEnd_1782003] using wordTrace_append hprefix tailTrace_1782003
  have hstable : (prefixWord ++ tailWord_1782003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782003).length < 2 ^ (prefixWord ++ tailWord_1782003).sum := by decide
  have hdescent : baseEnd_1782003 < baseStart_1782003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782010 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_1782010 : Nat := 118140960795 + 1782010 * 2 ^ 59
def prefixEnd_1782010 : Nat := 4983230072969 + 3 ^ 40 * 1782010 * 2
def baseEnd_1782010 : Nat := 915027661118678111379691

theorem tailTrace_1782010 : CollatzResearch.WordTrace tailWord_1782010 prefixEnd_1782010 915027661118678111379691 := by
  unfold tailWord_1782010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16248811068522396980779871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43330162849393058615412989 16248811068522396980779871)
  ·
    refine ⟨24373216602783595471169807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16248811068522396980779871 24373216602783595471169807)
    ·
      refine ⟨36559824904175393206754711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24373216602783595471169807 36559824904175393206754711)
      ·
        refine ⟨54839737356263089810132067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36559824904175393206754711 54839737356263089810132067)
        ·
          refine ⟨82259606034394634715198101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54839737356263089810132067 82259606034394634715198101)
          ·
            refine ⟨3855919032862248502274911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82259606034394634715198101 3855919032862248502274911)
            ·
              refine ⟨5783878549293372753412367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3855919032862248502274911 5783878549293372753412367)
              ·
                refine ⟨8675817823940059130118551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5783878549293372753412367 8675817823940059130118551)
                ·
                  refine ⟨13013726735910088695177827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8675817823940059130118551 13013726735910088695177827)
                  ·
                    refine ⟨19520590103865133042766741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13013726735910088695177827 19520590103865133042766741)
                    ·
                      refine ⟨915027661118678111379691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19520590103865133042766741 915027661118678111379691)
                      ·
                        rfl

theorem cell23_1782010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_1782010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782010 prefixEnd_1782010 := by exact prefixLift 1782010
  have htrace : WordTrace (prefixWord ++ tailWord_1782010) baseStart_1782010 baseEnd_1782010 := by
    simpa [prefixWord, tailWord_1782010, baseEnd_1782010] using wordTrace_append hprefix tailTrace_1782010
  have hstable : (prefixWord ++ tailWord_1782010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782010).length < 2 ^ (prefixWord ++ tailWord_1782010).sum := by decide
  have hdescent : baseEnd_1782010 < baseStart_1782010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782014 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1782014 : Nat := 118140960795 + 1782014 * 2 ^ 59
def prefixEnd_1782014 : Nat := 4983230072969 + 3 ^ 40 * 1782014 * 2
def baseEnd_1782014 : Nat := 915029715041296095729673

theorem tailTrace_1782014 : CollatzResearch.WordTrace tailWord_1782014 prefixEnd_1782014 915029715041296095729673 := by
  unfold tailWord_1782014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8124423770759387075783137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43330260110716731070843397 8124423770759387075783137)
  ·
    refine ⟨6093317828069540306837353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8124423770759387075783137 6093317828069540306837353)
    ·
      refine ⟨4569988371052155230128015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6093317828069540306837353 4569988371052155230128015)
      ·
        refine ⟨6854982556578232845192023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4569988371052155230128015 6854982556578232845192023)
        ·
          refine ⟨10282473834867349267788035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6854982556578232845192023 10282473834867349267788035)
          ·
            refine ⟨15423710752301023901682053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10282473834867349267788035 15423710752301023901682053)
            ·
              refine ⟨2891945766056441981565385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15423710752301023901682053 2891945766056441981565385)
              ·
                refine ⟨2168959324542331486174039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2891945766056441981565385 2168959324542331486174039)
                ·
                  refine ⟨3253438986813497229261059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2168959324542331486174039 3253438986813497229261059)
                  ·
                    refine ⟨4880158480220245843891589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253438986813497229261059 4880158480220245843891589)
                    ·
                      refine ⟨915029715041296095729673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880158480220245843891589 915029715041296095729673)
                      ·
                        rfl

theorem cell23_1782014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1782014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782014 prefixEnd_1782014 := by exact prefixLift 1782014
  have htrace : WordTrace (prefixWord ++ tailWord_1782014) baseStart_1782014 baseEnd_1782014 := by
    simpa [prefixWord, tailWord_1782014, baseEnd_1782014] using wordTrace_append hprefix tailTrace_1782014
  have hstable : (prefixWord ++ tailWord_1782014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782014).length < 2 ^ (prefixWord ++ tailWord_1782014).sum := by decide
  have hdescent : baseEnd_1782014 < baseStart_1782014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782058 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1782058 : Nat := 118140960795 + 1782058 * 2 ^ 59
def prefixEnd_1782058 : Nat := 4983230072969 + 3 ^ 40 * 1782058 * 2
def baseEnd_1782058 : Nat := 305017436063364641193157

theorem tailTrace_1782058 : CollatzResearch.WordTrace tailWord_1782058 prefixEnd_1782058 305017436063364641193157 := by
  unfold tailWord_1782058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249248744478923030216707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43331329985277128080577885 16249248744478923030216707)
  ·
    refine ⟨24373873116718384545325061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16249248744478923030216707 24373873116718384545325061)
    ·
      refine ⟨4570101209384697102248449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24373873116718384545325061 4570101209384697102248449)
      ·
        refine ⟨3427575907038522826686337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4570101209384697102248449 3427575907038522826686337)
        ·
          refine ⟨2570681930278892120014753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3427575907038522826686337 2570681930278892120014753)
          ·
            refine ⟨1928011447709169090011065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2570681930278892120014753 1928011447709169090011065)
            ·
              refine ⟨1446008585781876817508299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928011447709169090011065 1446008585781876817508299)
              ·
                refine ⟨2169012878672815226262449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446008585781876817508299 2169012878672815226262449)
                ·
                  refine ⟨1626759659004611419696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169012878672815226262449 1626759659004611419696837)
                  ·
                    refine ⟨305017436063364641193157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1626759659004611419696837 305017436063364641193157)
                    ·
                      rfl

theorem cell23_1782058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1782058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782058 prefixEnd_1782058 := by exact prefixLift 1782058
  have htrace : WordTrace (prefixWord ++ tailWord_1782058) baseStart_1782058 baseEnd_1782058 := by
    simpa [prefixWord, tailWord_1782058, baseEnd_1782058] using wordTrace_append hprefix tailTrace_1782058
  have hstable : (prefixWord ++ tailWord_1782058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782058).length < 2 ^ (prefixWord ++ tailWord_1782058).sum := by decide
  have hdescent : baseEnd_1782058 < baseStart_1782058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782074 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_1782074 : Nat := 118140960795 + 1782074 * 2 ^ 59
def prefixEnd_1782074 : Nat := 4983230072969 + 3 ^ 40 * 1782074 * 2
def baseEnd_1782074 : Nat := 915060523880565860979397

theorem tailTrace_1782074 : CollatzResearch.WordTrace tailWord_1782074 prefixEnd_1782074 915060523880565860979397 := by
  unfold tailWord_1782074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16249394636464431713362319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43331719030571817902299517 16249394636464431713362319)
  ·
    refine ⟨24374091954696647570043479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16249394636464431713362319 24374091954696647570043479)
    ·
      refine ⟨36561137932044971355065219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24374091954696647570043479 36561137932044971355065219)
      ·
        refine ⟨54841706898067457032597829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36561137932044971355065219 54841706898067457032597829)
        ·
          refine ⟨10282820043387648193612093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54841706898067457032597829 10282820043387648193612093)
          ·
            refine ⟨3856057516270368072604535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10282820043387648193612093 3856057516270368072604535)
            ·
              refine ⟨5784086274405552108906803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856057516270368072604535 5784086274405552108906803)
              ·
                refine ⟨8676129411608328163360205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784086274405552108906803 8676129411608328163360205)
                ·
                  refine ⟨3253548529353123061260077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8676129411608328163360205 3253548529353123061260077)
                  ·
                    refine ⟨1220080698507421147972529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3253548529353123061260077 1220080698507421147972529)
                    ·
                      refine ⟨915060523880565860979397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220080698507421147972529 915060523880565860979397)
                      ·
                        rfl

theorem cell23_1782074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_1782074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782074 prefixEnd_1782074 := by exact prefixLift 1782074
  have htrace : WordTrace (prefixWord ++ tailWord_1782074) baseStart_1782074 baseEnd_1782074 := by
    simpa [prefixWord, tailWord_1782074, baseEnd_1782074] using wordTrace_append hprefix tailTrace_1782074
  have hstable : (prefixWord ++ tailWord_1782074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782074).length < 2 ^ (prefixWord ++ tailWord_1782074).sum := by decide
  have hdescent : baseEnd_1782074 < baseStart_1782074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782117 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1782117 : Nat := 118140960795 + 1782117 * 2 ^ 59
def prefixEnd_1782117 : Nat := 4983230072969 + 3 ^ 40 * 1782117 * 2
def baseEnd_1782117 : Nat := 915082603548709192741699

theorem tailTrace_1782117 : CollatzResearch.WordTrace tailWord_1782117 prefixEnd_1782117 915082603548709192741699 := by
  unfold tailWord_1782117
  simp only [CollatzResearch.WordTrace]
  refine ⟨64999146884701945197264605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43332764589801296798176403 64999146884701945197264605)
  ·
    refine ⟨24374680081763229448974227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64999146884701945197264605 24374680081763229448974227)
    ·
      refine ⟨36562020122644844173461341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24374680081763229448974227 36562020122644844173461341)
      ·
        refine ⟨13710757545991816565048003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36562020122644844173461341 13710757545991816565048003)
        ·
          refine ⟨20566136318987724847572005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13710757545991816565048003 20566136318987724847572005)
          ·
            refine ⟨3856150559810198408919751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20566136318987724847572005 3856150559810198408919751)
            ·
              refine ⟨5784225839715297613379627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856150559810198408919751 5784225839715297613379627)
              ·
                refine ⟨8676338759572946420069441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5784225839715297613379627 8676338759572946420069441)
                ·
                  refine ⟨6507254069679709815052081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8676338759572946420069441 6507254069679709815052081)
                  ·
                    refine ⟨4880440552259782361289061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6507254069679709815052081 4880440552259782361289061)
                    ·
                      refine ⟨915082603548709192741699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880440552259782361289061 915082603548709192741699)
                      ·
                        rfl

theorem cell23_1782117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1782117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782117 prefixEnd_1782117 := by exact prefixLift 1782117
  have htrace : WordTrace (prefixWord ++ tailWord_1782117) baseStart_1782117 baseEnd_1782117 := by
    simpa [prefixWord, tailWord_1782117, baseEnd_1782117] using wordTrace_append hprefix tailTrace_1782117
  have hstable : (prefixWord ++ tailWord_1782117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782117).length < 2 ^ (prefixWord ++ tailWord_1782117).sum := by decide
  have hdescent : baseEnd_1782117 < baseStart_1782117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782160 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4]
def baseStart_1782160 : Nat := 118140960795 + 1782160 * 2 ^ 59
def prefixEnd_1782160 : Nat := 4983230072969 + 3 ^ 40 * 1782160 * 2
def baseEnd_1782160 : Nat := 915104683216852524504001

theorem tailTrace_1782160 : CollatzResearch.WordTrace tailWord_1782160 prefixEnd_1782160 915104683216852524504001 := by
  unfold tailWord_1782160
  simp only [CollatzResearch.WordTrace]
  refine ⟨32500357611773081770539967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43333810149030775694053289 32500357611773081770539967)
  ·
    refine ⟨48750536417659622655809951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32500357611773081770539967 48750536417659622655809951)
    ·
      refine ⟨73125804626489433983714927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48750536417659622655809951 73125804626489433983714927)
      ·
        refine ⟨109688706939734150975572391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73125804626489433983714927 109688706939734150975572391)
        ·
          refine ⟨164533060409601226463358587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109688706939734150975572391 164533060409601226463358587)
          ·
            refine ⟨246799590614401839695037881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164533060409601226463358587 246799590614401839695037881)
            ·
              refine ⟨185099692960801379771278411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246799590614401839695037881 185099692960801379771278411)
              ·
                refine ⟨277649539441202069656917617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185099692960801379771278411 277649539441202069656917617)
                ·
                  refine ⟨208237154580901552242688213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 277649539441202069656917617 208237154580901552242688213)
                  ·
                    refine ⟨4880558310489880130688005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 208237154580901552242688213 4880558310489880130688005)
                    ·
                      refine ⟨915104683216852524504001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880558310489880130688005 915104683216852524504001)
                      ·
                        rfl

theorem cell23_1782160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_1782160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782160 prefixEnd_1782160 := by exact prefixLift 1782160
  have htrace : WordTrace (prefixWord ++ tailWord_1782160) baseStart_1782160 baseEnd_1782160 := by
    simpa [prefixWord, tailWord_1782160, baseEnd_1782160] using wordTrace_append hprefix tailTrace_1782160
  have hstable : (prefixWord ++ tailWord_1782160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782160).length < 2 ^ (prefixWord ++ tailWord_1782160).sum := by decide
  have hdescent : baseEnd_1782160 < baseStart_1782160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782174 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1782174 : Nat := 118140960795 + 1782174 * 2 ^ 59
def prefixEnd_1782174 : Nat := 4983230072969 + 3 ^ 40 * 1782174 * 2
def baseEnd_1782174 : Nat := 305037290648671823242979

theorem tailTrace_1782174 : CollatzResearch.WordTrace tailWord_1782174 prefixEnd_1782174 305037290648671823242979 := by
  unfold tailWord_1782174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125153230686930491511197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43334150563663629288059717 8125153230686930491511197)
  ·
    refine ⟨3046932461507598934316699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8125153230686930491511197 3046932461507598934316699)
    ·
      refine ⟨4570398692261398401475049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3046932461507598934316699 4570398692261398401475049)
      ·
        refine ⟨3427799019196048801106287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4570398692261398401475049 3427799019196048801106287)
        ·
          refine ⟨5141698528794073201659431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3427799019196048801106287 5141698528794073201659431)
          ·
            refine ⟨7712547793191109802489147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5141698528794073201659431 7712547793191109802489147)
            ·
              refine ⟨11568821689786664703733721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7712547793191109802489147 11568821689786664703733721)
              ·
                refine ⟨8676616267339998527800291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11568821689786664703733721 8676616267339998527800291)
                ·
                  refine ⟨13014924401009997791700437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8676616267339998527800291 13014924401009997791700437)
                  ·
                    refine ⟨305037290648671823242979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13014924401009997791700437 305037290648671823242979)
                    ·
                      rfl

theorem cell23_1782174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1782174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782174 prefixEnd_1782174 := by exact prefixLift 1782174
  have htrace : WordTrace (prefixWord ++ tailWord_1782174) baseStart_1782174 baseEnd_1782174 := by
    simpa [prefixWord, tailWord_1782174, baseEnd_1782174] using wordTrace_append hprefix tailTrace_1782174
  have hstable : (prefixWord ++ tailWord_1782174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782174).length < 2 ^ (prefixWord ++ tailWord_1782174).sum := by decide
  have hdescent : baseEnd_1782174 < baseStart_1782174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782267 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4]
def baseStart_1782267 : Nat := 118140960795 + 1782267 * 2 ^ 59
def prefixEnd_1782267 : Nat := 4983230072969 + 3 ^ 40 * 1782267 * 2
def baseEnd_1782267 : Nat := 915159625646883605866009

theorem tailTrace_1782267 : CollatzResearch.WordTrace tailWord_1782267 prefixEnd_1782267 915159625646883605866009 := by
  unfold tailWord_1782267
  simp only [CollatzResearch.WordTrace]
  refine ⟨65004617834158520815225055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43336411889439013876816703 65004617834158520815225055)
  ·
    refine ⟨97506926751237781222837583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65004617834158520815225055 97506926751237781222837583)
    ·
      refine ⟨146260390126856671834256375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97506926751237781222837583 146260390126856671834256375)
      ·
        refine ⟨219390585190285007751384563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146260390126856671834256375 219390585190285007751384563)
        ·
          refine ⟨329085877785427511627076845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219390585190285007751384563 329085877785427511627076845)
          ·
            refine ⟨123407204169535316860153817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329085877785427511627076845 123407204169535316860153817)
            ·
              refine ⟨92555403127151487645115363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123407204169535316860153817 92555403127151487645115363)
              ·
                refine ⟨138833104690727231467673045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92555403127151487645115363 138833104690727231467673045)
                ·
                  refine ⟨3253900891188919487523587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 138833104690727231467673045 3253900891188919487523587)
                  ·
                    refine ⟨4880851336783379231285381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253900891188919487523587 4880851336783379231285381)
                    ·
                      refine ⟨915159625646883605866009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880851336783379231285381 915159625646883605866009)
                      ·
                        rfl

theorem cell23_1782267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4].length) (baseStart_1782267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782267 prefixEnd_1782267 := by exact prefixLift 1782267
  have htrace : WordTrace (prefixWord ++ tailWord_1782267) baseStart_1782267 baseEnd_1782267 := by
    simpa [prefixWord, tailWord_1782267, baseEnd_1782267] using wordTrace_append hprefix tailTrace_1782267
  have hstable : (prefixWord ++ tailWord_1782267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782267).length < 2 ^ (prefixWord ++ tailWord_1782267).sum := by decide
  have hdescent : baseEnd_1782267 < baseStart_1782267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782284 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1782284 : Nat := 118140960795 + 1782284 * 2 ^ 59
def prefixEnd_1782284 : Nat := 4983230072969 + 3 ^ 40 * 1782284 * 2
def baseEnd_1782284 : Nat := 915168354818010039353431

theorem tailTrace_1782284 : CollatzResearch.WordTrace tailWord_1782284 prefixEnd_1782284 915168354818010039353431 := by
  unfold tailWord_1782284
  simp only [CollatzResearch.WordTrace]
  refine ⟨32502618937548466359296953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43336825250064621812395937 32502618937548466359296953)
  ·
    refine ⟨24376964203161349769472715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32502618937548466359296953 24376964203161349769472715)
    ·
      refine ⟨36565446304742024654209073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24376964203161349769472715 36565446304742024654209073)
      ·
        refine ⟨27424084728556518490656805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36565446304742024654209073 27424084728556518490656805)
        ·
          refine ⟨5142015886604347216998151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27424084728556518490656805 5142015886604347216998151)
          ·
            refine ⟨7713023829906520825497227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5142015886604347216998151 7713023829906520825497227)
            ·
              refine ⟨11569535744859781238245841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713023829906520825497227 11569535744859781238245841)
              ·
                refine ⟨8677151808644835928684381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11569535744859781238245841 8677151808644835928684381)
                ·
                  refine ⟨3253931928241813473256643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8677151808644835928684381 3253931928241813473256643)
                  ·
                    refine ⟨4880897892362720209884965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253931928241813473256643 4880897892362720209884965)
                    ·
                      refine ⟨915168354818010039353431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880897892362720209884965 915168354818010039353431)
                      ·
                        rfl

theorem cell23_1782284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1782284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782284 prefixEnd_1782284 := by exact prefixLift 1782284
  have htrace : WordTrace (prefixWord ++ tailWord_1782284) baseStart_1782284 baseEnd_1782284 := by
    simpa [prefixWord, tailWord_1782284, baseEnd_1782284] using wordTrace_append hprefix tailTrace_1782284
  have hstable : (prefixWord ++ tailWord_1782284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782284).length < 2 ^ (prefixWord ++ tailWord_1782284).sum := by decide
  have hdescent : baseEnd_1782284 < baseStart_1782284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782287 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_1782287 : Nat := 118140960795 + 1782287 * 2 ^ 59
def prefixEnd_1782287 : Nat := 4983230072969 + 3 ^ 40 * 1782287 * 2
def baseEnd_1782287 : Nat := 915169895259973527615917

theorem tailTrace_1782287 : CollatzResearch.WordTrace tailWord_1782287 prefixEnd_1782287 915169895259973527615917 := by
  unfold tailWord_1782287
  simp only [CollatzResearch.WordTrace]
  refine ⟨65005347294086064230953115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43336898196057376153968743 65005347294086064230953115)
  ·
    refine ⟨97508020941129096346429673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65005347294086064230953115 97508020941129096346429673)
    ·
      refine ⟨73131015705846822259822255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97508020941129096346429673 73131015705846822259822255)
      ·
        refine ⟨109696523558770233389733383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73131015705846822259822255 109696523558770233389733383)
        ·
          refine ⟨164544785338155350084600075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109696523558770233389733383 164544785338155350084600075)
          ·
            refine ⟨246817178007233025126900113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164544785338155350084600075 246817178007233025126900113)
            ·
              refine ⟨185112883505424768845175085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 246817178007233025126900113 185112883505424768845175085)
              ·
                refine ⟨69417331314534288316940657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185112883505424768845175085 69417331314534288316940657)
                ·
                  refine ⟨52062998485900716237705493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69417331314534288316940657 52062998485900716237705493)
                  ·
                    refine ⟨2440453054026596073642445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 52062998485900716237705493 2440453054026596073642445)
                    ·
                      refine ⟨915169895259973527615917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2440453054026596073642445 915169895259973527615917)
                      ·
                        rfl

theorem cell23_1782287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_1782287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782287 prefixEnd_1782287 := by exact prefixLift 1782287
  have htrace : WordTrace (prefixWord ++ tailWord_1782287) baseStart_1782287 baseEnd_1782287 := by
    simpa [prefixWord, tailWord_1782287, baseEnd_1782287] using wordTrace_append hprefix tailTrace_1782287
  have hstable : (prefixWord ++ tailWord_1782287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782287).length < 2 ^ (prefixWord ++ tailWord_1782287).sum := by decide
  have hdescent : baseEnd_1782287 < baseStart_1782287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782297 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 4]
def baseStart_1782297 : Nat := 118140960795 + 1782297 * 2 ^ 59
def prefixEnd_1782297 : Nat := 4983230072969 + 3 ^ 40 * 1782297 * 2
def baseEnd_1782297 : Nat := 915175030066518488490871

theorem tailTrace_1782297 : CollatzResearch.WordTrace tailWord_1782297 prefixEnd_1782297 915175030066518488490871 := by
  unfold tailWord_1782297
  simp only [CollatzResearch.WordTrace]
  refine ⟨65005712024049835938817145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43337141349366557292544763 65005712024049835938817145)
  ·
    refine ⟨48754284018037376954112859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65005712024049835938817145 48754284018037376954112859)
    ·
      refine ⟨73131426027056065431169289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48754284018037376954112859 73131426027056065431169289)
      ·
        refine ⟨54848569520292049073376967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73131426027056065431169289 54848569520292049073376967)
        ·
          refine ⟨82272854280438073610065451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54848569520292049073376967 82272854280438073610065451)
          ·
            refine ⟨123409281420657110415098177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82272854280438073610065451 123409281420657110415098177)
            ·
              refine ⟨92556961065492832811323633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123409281420657110415098177 92556961065492832811323633)
              ·
                refine ⟨69417720799119624608492725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92556961065492832811323633 69417720799119624608492725)
                ·
                  refine ⟨6507911324917464807046193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69417720799119624608492725 6507911324917464807046193)
                  ·
                    refine ⟨4880933493688098605284645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6507911324917464807046193 4880933493688098605284645)
                    ·
                      refine ⟨915175030066518488490871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880933493688098605284645 915175030066518488490871)
                      ·
                        rfl

theorem cell23_1782297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_1782297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782297 prefixEnd_1782297 := by exact prefixLift 1782297
  have htrace : WordTrace (prefixWord ++ tailWord_1782297) baseStart_1782297 baseEnd_1782297 := by
    simpa [prefixWord, tailWord_1782297, baseEnd_1782297] using wordTrace_append hprefix tailTrace_1782297
  have hstable : (prefixWord ++ tailWord_1782297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782297).length < 2 ^ (prefixWord ++ tailWord_1782297).sum := by decide
  have hdescent : baseEnd_1782297 < baseStart_1782297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782318 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_1782318 : Nat := 118140960795 + 1782318 * 2 ^ 59
def prefixEnd_1782318 : Nat := 4983230072969 + 3 ^ 40 * 1782318 * 2
def baseEnd_1782318 : Nat := 915185813160262906328275

theorem tailTrace_1782318 : CollatzResearch.WordTrace tailWord_1782318 prefixEnd_1782318 915185813160262906328275 := by
  unfold tailWord_1782318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125809744621719565666451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43337651971315837683554405 8125809744621719565666451)
  ·
    refine ⟨12188714616932579348499677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8125809744621719565666451 12188714616932579348499677)
    ·
      refine ⟨4570767981349717255687379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12188714616932579348499677 4570767981349717255687379)
      ·
        refine ⟨6856151972024575883531069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4570767981349717255687379 6856151972024575883531069)
        ·
          refine ⟨2571056989509215956324151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6856151972024575883531069 2571056989509215956324151)
          ·
            refine ⟨3856585484263823934486227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571056989509215956324151 3856585484263823934486227)
            ·
              refine ⟨5784878226395735901729341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3856585484263823934486227 5784878226395735901729341)
              ·
                refine ⟨2169329334898400963148503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5784878226395735901729341 2169329334898400963148503)
                ·
                  refine ⟨3253994002347601444722755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169329334898400963148503 3253994002347601444722755)
                  ·
                    refine ⟨4880991003521402167084133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3253994002347601444722755 4880991003521402167084133)
                    ·
                      refine ⟨915185813160262906328275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4880991003521402167084133 915185813160262906328275)
                      ·
                        rfl

theorem cell23_1782318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_1782318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782318 prefixEnd_1782318 := by exact prefixLift 1782318
  have htrace : WordTrace (prefixWord ++ tailWord_1782318) baseStart_1782318 baseEnd_1782318 := by
    simpa [prefixWord, tailWord_1782318, baseEnd_1782318] using wordTrace_append hprefix tailTrace_1782318
  have hstable : (prefixWord ++ tailWord_1782318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782318).length < 2 ^ (prefixWord ++ tailWord_1782318).sum := by decide
  have hdescent : baseEnd_1782318 < baseStart_1782318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782351 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 3]
def baseStart_1782351 : Nat := 118140960795 + 1782351 * 2 ^ 59
def prefixEnd_1782351 : Nat := 4983230072969 + 3 ^ 40 * 1782351 * 2
def baseEnd_1782351 : Nat := 915202758021861277215623

theorem tailTrace_1782351 : CollatzResearch.WordTrace tailWord_1782351 prefixEnd_1782351 915202758021861277215623 := by
  unfold tailWord_1782351
  simp only [CollatzResearch.WordTrace]
  refine ⟨65007681565854203161282907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43338454377236135440855271 65007681565854203161282907)
  ·
    refine ⟨97511522348781304741924361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65007681565854203161282907 97511522348781304741924361)
    ·
      refine ⟨73133641761585978556443271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97511522348781304741924361 73133641761585978556443271)
      ·
        refine ⟨109700462642378967834664907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73133641761585978556443271 109700462642378967834664907)
        ·
          refine ⟨164550693963568451751997361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109700462642378967834664907 164550693963568451751997361)
          ·
            refine ⟨123413020472676338813998021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164550693963568451751997361 123413020472676338813998021)
            ·
              refine ⟨23139941338626813527624629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123413020472676338813998021 23139941338626813527624629)
              ·
                refine ⟨2169369500496263768214809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23139941338626813527624629 2169369500496263768214809)
                ·
                  refine ⟨1627027125372197826161107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169369500496263768214809 1627027125372197826161107)
                  ·
                    refine ⟨2440540688058296739241661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1627027125372197826161107 2440540688058296739241661)
                    ·
                      refine ⟨915202758021861277215623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2440540688058296739241661 915202758021861277215623)
                      ·
                        rfl

theorem cell23_1782351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_1782351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782351 prefixEnd_1782351 := by exact prefixLift 1782351
  have htrace : WordTrace (prefixWord ++ tailWord_1782351) baseStart_1782351 baseEnd_1782351 := by
    simpa [prefixWord, tailWord_1782351, baseEnd_1782351] using wordTrace_append hprefix tailTrace_1782351
  have hstable : (prefixWord ++ tailWord_1782351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782351).length < 2 ^ (prefixWord ++ tailWord_1782351).sum := by decide
  have hdescent : baseEnd_1782351 < baseStart_1782351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782367 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 8]
def baseStart_1782367 : Nat := 118140960795 + 1782367 * 2 ^ 59
def prefixEnd_1782367 : Nat := 4983230072969 + 3 ^ 40 * 1782367 * 2
def baseEnd_1782367 : Nat := 305070324570777738205183

theorem tailTrace_1782367 : CollatzResearch.WordTrace tailWord_1782367 prefixEnd_1782367 305070324570777738205183 := by
  unfold tailWord_1782367
  simp only [CollatzResearch.WordTrace]
  refine ⟨65008265133796237893865355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43338843422530825262576903 65008265133796237893865355)
  ·
    refine ⟨97512397700694356840798033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65008265133796237893865355 97512397700694356840798033)
    ·
      refine ⟨73134298275520767630598525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97512397700694356840798033 73134298275520767630598525)
      ·
        refine ⟨27425361853320287861474447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73134298275520767630598525 27425361853320287861474447)
        ·
          refine ⟨41138042779980431792211671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27425361853320287861474447 41138042779980431792211671)
          ·
            refine ⟨61707064169970647688317507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41138042779980431792211671 61707064169970647688317507)
            ·
              refine ⟨92560596254955971532476261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61707064169970647688317507 92560596254955971532476261)
              ·
                refine ⟨17355111797804244662339299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92560596254955971532476261 17355111797804244662339299)
                ·
                  refine ⟨26032667696706366993508949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17355111797804244662339299 26032667696706366993508949)
                  ·
                    refine ⟨305070324570777738205183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26032667696706366993508949 305070324570777738205183)
                    ·
                      rfl

theorem cell23_1782367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_1782367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782367 prefixEnd_1782367 := by exact prefixLift 1782367
  have htrace : WordTrace (prefixWord ++ tailWord_1782367) baseStart_1782367 baseEnd_1782367 := by
    simpa [prefixWord, tailWord_1782367, baseEnd_1782367] using wordTrace_append hprefix tailTrace_1782367
  have hstable : (prefixWord ++ tailWord_1782367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782367).length < 2 ^ (prefixWord ++ tailWord_1782367).sum := by decide
  have hdescent : baseEnd_1782367 < baseStart_1782367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782378 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_1782378 : Nat := 118140960795 + 1782378 * 2 ^ 59
def prefixEnd_1782378 : Nat := 4983230072969 + 3 ^ 40 * 1782378 * 2
def baseEnd_1782378 : Nat := 915216621999532671577999

theorem tailTrace_1782378 : CollatzResearch.WordTrace tailWord_1782378 prefixEnd_1782378 915216621999532671577999 := by
  unfold tailWord_1782378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16252166584189096693128947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43339110891170924515010525 16252166584189096693128947)
  ·
    refine ⟨24378249876283645039693421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16252166584189096693128947 24378249876283645039693421)
    ·
      refine ⟨9141843703606366889885033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24378249876283645039693421 9141843703606366889885033)
      ·
        refine ⟨6856382777704775167413775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9141843703606366889885033 6856382777704775167413775)
        ·
          refine ⟨10284574166557162751120663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856382777704775167413775 10284574166557162751120663)
          ·
            refine ⟨15426861249835744126680995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284574166557162751120663 15426861249835744126680995)
            ·
              refine ⟨23140291874753616190021493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15426861249835744126680995 23140291874753616190021493)
              ·
                refine ⟨2169402363258151517814515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23140291874753616190021493 2169402363258151517814515)
                ·
                  refine ⟨3254103544887227276721773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169402363258151517814515 3254103544887227276721773)
                  ·
                    refine ⟨1220288829332710228770665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3254103544887227276721773 1220288829332710228770665)
                    ·
                      refine ⟨915216621999532671577999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220288829332710228770665 915216621999532671577999)
                      ·
                        rfl

theorem cell23_1782378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_1782378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782378 prefixEnd_1782378 := by exact prefixLift 1782378
  have htrace : WordTrace (prefixWord ++ tailWord_1782378) baseStart_1782378 baseEnd_1782378 := by
    simpa [prefixWord, tailWord_1782378, baseEnd_1782378] using wordTrace_append hprefix tailTrace_1782378
  have hstable : (prefixWord ++ tailWord_1782378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782378).length < 2 ^ (prefixWord ++ tailWord_1782378).sum := by decide
  have hdescent : baseEnd_1782378 < baseStart_1782378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782387 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_1782387 : Nat := 118140960795 + 1782387 * 2 ^ 59
def prefixEnd_1782387 : Nat := 4983230072969 + 3 ^ 40 * 1782387 * 2
def baseEnd_1782387 : Nat := 915221243325423136365457

theorem tailTrace_1782387 : CollatzResearch.WordTrace tailWord_1782387 prefixEnd_1782387 915221243325423136365457 := by
  unfold tailWord_1782387
  simp only [CollatzResearch.WordTrace]
  refine ⟨65008994593723781309593415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43339329729149187539728943 65008994593723781309593415)
  ·
    refine ⟨97513491890585671964390123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65008994593723781309593415 97513491890585671964390123)
    ·
      refine ⟨146270237835878507946585185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97513491890585671964390123 146270237835878507946585185)
      ·
        refine ⟨109702678376908880959938889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146270237835878507946585185 109702678376908880959938889)
        ·
          refine ⟨82277008782681660719954167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109702678376908880959938889 82277008782681660719954167)
          ·
            refine ⟨123415513174022491079931251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82277008782681660719954167 123415513174022491079931251)
            ·
              refine ⟨185123269761033736619896877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123415513174022491079931251 185123269761033736619896877)
              ·
                refine ⟨69421226160387651232461329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185123269761033736619896877 69421226160387651232461329)
                ·
                  refine ⟨52065919620290738424345997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69421226160387651232461329 52065919620290738424345997)
                  ·
                    refine ⟨19524719857609026909129749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52065919620290738424345997 19524719857609026909129749)
                    ·
                      refine ⟨915221243325423136365457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19524719857609026909129749 915221243325423136365457)
                      ·
                        rfl

theorem cell23_1782387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_1782387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782387 prefixEnd_1782387 := by exact prefixLift 1782387
  have htrace : WordTrace (prefixWord ++ tailWord_1782387) baseStart_1782387 baseEnd_1782387 := by
    simpa [prefixWord, tailWord_1782387, baseEnd_1782387] using wordTrace_append hprefix tailTrace_1782387
  have hstable : (prefixWord ++ tailWord_1782387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782387).length < 2 ^ (prefixWord ++ tailWord_1782387).sum := by decide
  have hdescent : baseEnd_1782387 < baseStart_1782387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782414 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_1782414 : Nat := 118140960795 + 1782414 * 2 ^ 59
def prefixEnd_1782414 : Nat := 4983230072969 + 3 ^ 40 * 1782414 * 2
def baseEnd_1782414 : Nat := 101692789700343836747537

theorem tailTrace_1782414 : CollatzResearch.WordTrace tailWord_1782414 prefixEnd_1782414 101692789700343836747537 := by
  unfold tailWord_1782414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126247420578245615103287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43339986243083976613884197 8126247420578245615103287)
  ·
    refine ⟨12189371130867368422654931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8126247420578245615103287 12189371130867368422654931)
    ·
      refine ⟨18284056696301052633982397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12189371130867368422654931 18284056696301052633982397)
      ·
        refine ⟨6856521261112894737743399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18284056696301052633982397 6856521261112894737743399)
        ·
          refine ⟨10284781891669342106615099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856521261112894737743399 10284781891669342106615099)
          ·
            refine ⟨15427172837504013159922649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284781891669342106615099 15427172837504013159922649)
            ·
              refine ⟨11570379628128009869941987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15427172837504013159922649 11570379628128009869941987)
              ·
                refine ⟨17355569442192014804912981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570379628128009869941987 17355569442192014804912981)
                ·
                  refine ⟨101692789700343836747537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17355569442192014804912981 101692789700343836747537)
                  ·
                    rfl

theorem cell23_1782414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_1782414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782414 prefixEnd_1782414 := by exact prefixLift 1782414
  have htrace : WordTrace (prefixWord ++ tailWord_1782414) baseStart_1782414 baseEnd_1782414 := by
    simpa [prefixWord, tailWord_1782414, baseEnd_1782414] using wordTrace_append hprefix tailTrace_1782414
  have hstable : (prefixWord ++ tailWord_1782414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782414).length < 2 ^ (prefixWord ++ tailWord_1782414).sum := by decide
  have hdescent : baseEnd_1782414 < baseStart_1782414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782451 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 5, 2]
def baseStart_1782451 : Nat := 118140960795 + 1782451 * 2 ^ 59
def prefixEnd_1782451 : Nat := 4983230072969 + 3 ^ 40 * 1782451 * 2
def baseEnd_1782451 : Nat := 915254106087310885965163

theorem tailTrace_1782451 : CollatzResearch.WordTrace tailWord_1782451 prefixEnd_1782451 915254106087310885965163 := by
  unfold tailWord_1782451
  simp only [CollatzResearch.WordTrace]
  refine ⟨65011328865491920239923207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43340885910327946826615471 65011328865491920239923207)
  ·
    refine ⟨97516993298237880359884811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65011328865491920239923207 97516993298237880359884811)
    ·
      refine ⟨146275489947356820539827217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97516993298237880359884811 146275489947356820539827217)
      ·
        refine ⟨109706617460517615404870413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146275489947356820539827217 109706617460517615404870413)
        ·
          refine ⟨41139981547694105776826405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109706617460517615404870413 41139981547694105776826405)
          ·
            refine ⟨7713746540192644833154951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41139981547694105776826405 7713746540192644833154951)
            ·
              refine ⟨11570619810288967249732427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7713746540192644833154951 11570619810288967249732427)
              ·
                refine ⟨17355929715433450874598641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11570619810288967249732427 17355929715433450874598641)
                ·
                  refine ⟨13016947286575088155948981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17355929715433450874598641 13016947286575088155948981)
                  ·
                    refine ⟨1220338808116414514620217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13016947286575088155948981 1220338808116414514620217)
                    ·
                      refine ⟨915254106087310885965163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220338808116414514620217 915254106087310885965163)
                      ·
                        rfl

theorem cell23_1782451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 5, 2].length) (baseStart_1782451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782451 prefixEnd_1782451 := by exact prefixLift 1782451
  have htrace : WordTrace (prefixWord ++ tailWord_1782451) baseStart_1782451 baseEnd_1782451 := by
    simpa [prefixWord, tailWord_1782451, baseEnd_1782451] using wordTrace_append hprefix tailTrace_1782451
  have hstable : (prefixWord ++ tailWord_1782451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782451).length < 2 ^ (prefixWord ++ tailWord_1782451).sum := by decide
  have hdescent : baseEnd_1782451 < baseStart_1782451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782478 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_1782478 : Nat := 118140960795 + 1782478 * 2 ^ 59
def prefixEnd_1782478 : Nat := 4983230072969 + 3 ^ 40 * 1782478 * 2
def baseEnd_1782478 : Nat := 305089323354994093442513

theorem tailTrace_1782478 : CollatzResearch.WordTrace tailWord_1782478 prefixEnd_1782478 305089323354994093442513 := by
  unfold tailWord_1782478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8126539204549262981394511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43341542424262735900770725 8126539204549262981394511)
  ·
    refine ⟨12189808806823894472091767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8126539204549262981394511 12189808806823894472091767)
    ·
      refine ⟨18284713210235841708137651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12189808806823894472091767 18284713210235841708137651)
      ·
        refine ⟨27427069815353762562206477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18284713210235841708137651 27427069815353762562206477)
        ·
          refine ⟨10285151180757660960827429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27427069815353762562206477 10285151180757660960827429)
          ·
            refine ⟨1928465846392061430155143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10285151180757660960827429 1928465846392061430155143)
            ·
              refine ⟨2892698769588092145232715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928465846392061430155143 2892698769588092145232715)
              ·
                refine ⟨4339048154382138217849073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2892698769588092145232715 4339048154382138217849073)
                ·
                  refine ⟨3254286115786603663386805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339048154382138217849073 3254286115786603663386805)
                  ·
                    refine ⟨305089323354994093442513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3254286115786603663386805 305089323354994093442513)
                    ·
                      rfl

theorem cell23_1782478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_1782478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782478 prefixEnd_1782478 := by exact prefixLift 1782478
  have htrace : WordTrace (prefixWord ++ tailWord_1782478) baseStart_1782478 baseEnd_1782478 := by
    simpa [prefixWord, tailWord_1782478, baseEnd_1782478] using wordTrace_append hprefix tailTrace_1782478
  have hstable : (prefixWord ++ tailWord_1782478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782478).length < 2 ^ (prefixWord ++ tailWord_1782478).sum := by decide
  have hdescent : baseEnd_1782478 < baseStart_1782478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782481 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 6, 2]
def baseStart_1782481 : Nat := 118140960795 + 1782481 * 2 ^ 59
def prefixEnd_1782481 : Nat := 4983230072969 + 3 ^ 40 * 1782481 * 2
def baseEnd_1782481 : Nat := 915269510506945768590025

theorem tailTrace_1782481 : CollatzResearch.WordTrace tailWord_1782481 prefixEnd_1782481 915269510506945768590025 := by
  unfold tailWord_1782481
  simp only [CollatzResearch.WordTrace]
  refine ⟨65012423055383235363515297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43341615370255490242343531 65012423055383235363515297)
  ·
    refine ⟨48759317291537426522636473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65012423055383235363515297 48759317291537426522636473)
    ·
      refine ⟨36569487968653069891977355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48759317291537426522636473 36569487968653069891977355)
      ·
        refine ⟨54854231952979604837966033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36569487968653069891977355 54854231952979604837966033)
        ·
          refine ⟨41140673964734703628474525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54854231952979604837966033 41140673964734703628474525)
          ·
            refine ⟨15427752736775513860677947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41140673964734703628474525 15427752736775513860677947)
            ·
              refine ⟨23141629105163270791016921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15427752736775513860677947 23141629105163270791016921)
              ·
                refine ⟨17356221828872453093262691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23141629105163270791016921 17356221828872453093262691)
                ·
                  refine ⟨26034332743308679639894037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17356221828872453093262691 26034332743308679639894037)
                  ·
                    refine ⟨1220359347342594358120033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26034332743308679639894037 1220359347342594358120033)
                    ·
                      refine ⟨915269510506945768590025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220359347342594358120033 915269510506945768590025)
                      ·
                        rfl

theorem cell23_1782481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_1782481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782481 prefixEnd_1782481 := by exact prefixLift 1782481
  have htrace : WordTrace (prefixWord ++ tailWord_1782481) baseStart_1782481 baseEnd_1782481 := by
    simpa [prefixWord, tailWord_1782481, baseEnd_1782481] using wordTrace_append hprefix tailTrace_1782481
  have hstable : (prefixWord ++ tailWord_1782481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782481).length < 2 ^ (prefixWord ++ tailWord_1782481).sum := by decide
  have hdescent : baseEnd_1782481 < baseStart_1782481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782601 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_1782601 : Nat := 118140960795 + 1782601 * 2 ^ 59
def prefixEnd_1782601 : Nat := 4983230072969 + 3 ^ 40 * 1782601 * 2
def baseEnd_1782601 : Nat := 915331128185485299089473

theorem tailTrace_1782601 : CollatzResearch.WordTrace tailWord_1782601 prefixEnd_1782601 915331128185485299089473 := by
  unfold tailWord_1782601
  simp only [CollatzResearch.WordTrace]
  refine ⟨65016799814948495857883657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43344533209965663905255771 65016799814948495857883657)
  ·
    refine ⟨48762599861211371893412743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65016799814948495857883657 48762599861211371893412743)
    ·
      refine ⟨73143899791817057840119115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48762599861211371893412743 73143899791817057840119115)
      ·
        refine ⟨109715849687725586760178673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73143899791817057840119115 109715849687725586760178673)
        ·
          refine ⟨82286887265794190070134005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109715849687725586760178673 82286887265794190070134005)
          ·
            refine ⟨7714395681168205319075063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82286887265794190070134005 7714395681168205319075063)
            ·
              refine ⟨11571593521752307978612595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7714395681168205319075063 11571593521752307978612595)
              ·
                refine ⟨17357390282628461967918893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11571593521752307978612595 17357390282628461967918893)
                ·
                  refine ⟨6509021355985673237969585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17357390282628461967918893 6509021355985673237969585)
                  ·
                    refine ⟨4881766016989254928477189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6509021355985673237969585 4881766016989254928477189)
                    ·
                      refine ⟨915331128185485299089473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4881766016989254928477189 915331128185485299089473)
                      ·
                        rfl

theorem cell23_1782601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_1782601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782601 prefixEnd_1782601 := by exact prefixLift 1782601
  have htrace : WordTrace (prefixWord ++ tailWord_1782601) baseStart_1782601 baseEnd_1782601 := by
    simpa [prefixWord, tailWord_1782601, baseEnd_1782601] using wordTrace_append hprefix tailTrace_1782601
  have hstable : (prefixWord ++ tailWord_1782601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782601).length < 2 ^ (prefixWord ++ tailWord_1782601).sum := by decide
  have hdescent : baseEnd_1782601 < baseStart_1782601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782608 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3]
def baseStart_1782608 : Nat := 118140960795 + 1782608 * 2 ^ 59
def prefixEnd_1782608 : Nat := 4983230072969 + 3 ^ 40 * 1782608 * 2
def baseEnd_1782608 : Nat := 915334722550066771701941

theorem tailTrace_1782608 : CollatzResearch.WordTrace tailWord_1782608 prefixEnd_1782608 915334722550066771701941 := by
  unfold tailWord_1782608
  simp only [CollatzResearch.WordTrace]
  refine ⟨32508527562961568026694239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43344703417282090702258985 32508527562961568026694239)
  ·
    refine ⟨48762791344442352040041359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32508527562961568026694239 48762791344442352040041359)
    ·
      refine ⟨73144187016663528060062039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48762791344442352040041359 73144187016663528060062039)
      ·
        refine ⟨109716280524995292090093059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73144187016663528060062039 109716280524995292090093059)
        ·
          refine ⟨164574420787492938135139589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109716280524995292090093059 164574420787492938135139589)
          ·
            refine ⟨30857703897654925900338673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 164574420787492938135139589 30857703897654925900338673)
            ·
              refine ⟨23143277923241194425254005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30857703897654925900338673 23143277923241194425254005)
              ·
                refine ⟨2169682305303861977367563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23143277923241194425254005 2169682305303861977367563)
                ·
                  refine ⟨3254523457955792966051345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2169682305303861977367563 3254523457955792966051345)
                  ·
                    refine ⟨2440892593466844724538509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3254523457955792966051345 2440892593466844724538509)
                    ·
                      refine ⟨915334722550066771701941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2440892593466844724538509 915334722550066771701941)
                      ·
                        rfl

theorem cell23_1782608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 3].length) (baseStart_1782608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782608 prefixEnd_1782608 := by exact prefixLift 1782608
  have htrace : WordTrace (prefixWord ++ tailWord_1782608) baseStart_1782608 baseEnd_1782608 := by
    simpa [prefixWord, tailWord_1782608, baseEnd_1782608] using wordTrace_append hprefix tailTrace_1782608
  have hstable : (prefixWord ++ tailWord_1782608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782608).length < 2 ^ (prefixWord ++ tailWord_1782608).sum := by decide
  have hdescent : baseEnd_1782608 < baseStart_1782608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782615 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 2, 4]
def baseStart_1782615 : Nat := 118140960795 + 1782615 * 2 ^ 59
def prefixEnd_1782615 : Nat := 4983230072969 + 3 ^ 40 * 1782615 * 2
def baseEnd_1782615 : Nat := 305112772304882748104803

theorem tailTrace_1782615 : CollatzResearch.WordTrace tailWord_1782615 prefixEnd_1782615 305112772304882748104803 := by
  unfold tailWord_1782615
  simp only [CollatzResearch.WordTrace]
  refine ⟨65017310436897776248893299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43344873624598517499262199 65017310436897776248893299)
  ·
    refine ⟨97525965655346664373339949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65017310436897776248893299 97525965655346664373339949)
    ·
      refine ⟨36572237120754999140002481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97525965655346664373339949 36572237120754999140002481)
      ·
        refine ⟨27429177840566249355001861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36572237120754999140002481 27429177840566249355001861)
        ·
          refine ⟨5142970845106171754062849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27429177840566249355001861 5142970845106171754062849)
          ·
            refine ⟨3857228133829628815547137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5142970845106171754062849 3857228133829628815547137)
            ·
              refine ⟨2892921100372221611660353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3857228133829628815547137 2892921100372221611660353)
              ·
                refine ⟨2169690825279166208745265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2892921100372221611660353 2169690825279166208745265)
                ·
                  refine ⟨1627268118959374656558949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169690825279166208745265 1627268118959374656558949)
                  ·
                    refine ⟨305112772304882748104803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627268118959374656558949 305112772304882748104803)
                    ·
                      rfl

theorem cell23_1782615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_1782615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782615 prefixEnd_1782615 := by exact prefixLift 1782615
  have htrace : WordTrace (prefixWord ++ tailWord_1782615) baseStart_1782615 baseEnd_1782615 := by
    simpa [prefixWord, tailWord_1782615, baseEnd_1782615] using wordTrace_append hprefix tailTrace_1782615
  have hstable : (prefixWord ++ tailWord_1782615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782615).length < 2 ^ (prefixWord ++ tailWord_1782615).sum := by decide
  have hdescent : baseEnd_1782615 < baseStart_1782615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782628 : List Nat := [2, 3, 1, 1, 4, 3, 1, 8]
def baseStart_1782628 : Nat := 118140960795 + 1782628 * 2 ^ 59
def prefixEnd_1782628 : Nat := 4983230072969 + 3 ^ 40 * 1782628 * 2
def baseEnd_1782628 : Nat := 33901666376413210868587

theorem tailTrace_1782628 : CollatzResearch.WordTrace tailWord_1782628 prefixEnd_1782628 33901666376413210868587 := by
  unfold tailWord_1782628
  simp only [CollatzResearch.WordTrace]
  refine ⟨32508892292925339734558269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43345189723900452979411025 32508892292925339734558269)
  ·
    refine ⟨12190834609847002400459351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32508892292925339734558269 12190834609847002400459351)
    ·
      refine ⟨18286251914770503600689027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12190834609847002400459351 18286251914770503600689027)
      ·
        refine ⟨27429377872155755401033541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18286251914770503600689027 27429377872155755401033541)
        ·
          refine ⟨5143008351029204137693789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27429377872155755401033541 5143008351029204137693789)
          ·
            refine ⟨1928628131635951551635171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5143008351029204137693789 1928628131635951551635171)
            ·
              refine ⟨2892942197453927327452757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928628131635951551635171 2892942197453927327452757)
              ·
                refine ⟨33901666376413210868587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2892942197453927327452757 33901666376413210868587)
                ·
                  rfl

theorem cell23_1782628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 8].length) (baseStart_1782628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782628 prefixEnd_1782628 := by exact prefixLift 1782628
  have htrace : WordTrace (prefixWord ++ tailWord_1782628) baseStart_1782628 baseEnd_1782628 := by
    simpa [prefixWord, tailWord_1782628, baseEnd_1782628] using wordTrace_append hprefix tailTrace_1782628
  have hstable : (prefixWord ++ tailWord_1782628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782628).length < 2 ^ (prefixWord ++ tailWord_1782628).sum := by decide
  have hdescent : baseEnd_1782628 < baseStart_1782628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782681 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_1782681 : Nat := 118140960795 + 1782681 * 2 ^ 59
def prefixEnd_1782681 : Nat := 4983230072969 + 3 ^ 40 * 1782681 * 2
def baseEnd_1782681 : Nat := 915372206637844986089105

theorem tailTrace_1782681 : CollatzResearch.WordTrace tailWord_1782681 prefixEnd_1782681 915372206637844986089105 := by
  unfold tailWord_1782681
  simp only [CollatzResearch.WordTrace]
  refine ⟨65019717654658669520795897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43346478436439113013863931 65019717654658669520795897)
  ·
    refine ⟨48764788240994002140596923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65019717654658669520795897 48764788240994002140596923)
    ·
      refine ⟨73147182361491003210895385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48764788240994002140596923 73147182361491003210895385)
      ·
        refine ⟨54860386771118252408171539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73147182361491003210895385 54860386771118252408171539)
        ·
          refine ⟨82290580156677378612257309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54860386771118252408171539 82290580156677378612257309)
          ·
            refine ⟨30858967558754016979596491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82290580156677378612257309 30858967558754016979596491)
            ·
              refine ⟨46288451338131025469394737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30858967558754016979596491 46288451338131025469394737)
              ·
                refine ⟨34716338503598269102046053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46288451338131025469394737 34716338503598269102046053)
                ·
                  refine ⟨6509313469424675456633635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34716338503598269102046053 6509313469424675456633635)
                  ·
                    refine ⟨9763970204137013184950453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6509313469424675456633635 9763970204137013184950453)
                    ·
                      refine ⟨915372206637844986089105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9763970204137013184950453 915372206637844986089105)
                      ·
                        rfl

theorem cell23_1782681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_1782681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782681 prefixEnd_1782681 := by exact prefixLift 1782681
  have htrace : WordTrace (prefixWord ++ tailWord_1782681) baseStart_1782681 baseEnd_1782681 := by
    simpa [prefixWord, tailWord_1782681, baseEnd_1782681] using wordTrace_append hprefix tailTrace_1782681
  have hstable : (prefixWord ++ tailWord_1782681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782681).length < 2 ^ (prefixWord ++ tailWord_1782681).sum := by decide
  have hdescent : baseEnd_1782681 < baseStart_1782681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782689 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1782689 : Nat := 118140960795 + 1782689 * 2 ^ 59
def prefixEnd_1782689 : Nat := 4983230072969 + 3 ^ 40 * 1782689 * 2
def baseEnd_1782689 : Nat := 915376314483080954789069

theorem tailTrace_1782689 : CollatzResearch.WordTrace tailWord_1782689 prefixEnd_1782689 915376314483080954789069 := by
  unfold tailWord_1782689
  simp only [CollatzResearch.WordTrace]
  refine ⟨65020009438629686887087121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43346672959086457924724747 65020009438629686887087121)
  ·
    refine ⟨48765007078972265165315341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65020009438629686887087121 48765007078972265165315341)
    ·
      refine ⟨18286877654614599436993253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48765007078972265165315341 18286877654614599436993253)
      ·
        refine ⟨3428789560240237394436235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18286877654614599436993253 3428789560240237394436235)
        ·
          refine ⟨5143184340360356091654353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428789560240237394436235 5143184340360356091654353)
          ·
            refine ⟨3857388255270267068740765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5143184340360356091654353 3857388255270267068740765)
            ·
              refine ⟨1446520595726350150777787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3857388255270267068740765 1446520595726350150777787)
              ·
                refine ⟨2169780893589525226166681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446520595726350150777787 2169780893589525226166681)
                ·
                  refine ⟨1627335670192143919625011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169780893589525226166681 1627335670192143919625011)
                  ·
                    refine ⟨2441003505288215879437517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1627335670192143919625011 2441003505288215879437517)
                    ·
                      refine ⟨915376314483080954789069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2441003505288215879437517 915376314483080954789069)
                      ·
                        rfl

theorem cell23_1782689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1782689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782689 prefixEnd_1782689 := by exact prefixLift 1782689
  have htrace : WordTrace (prefixWord ++ tailWord_1782689) baseStart_1782689 baseEnd_1782689 := by
    simpa [prefixWord, tailWord_1782689, baseEnd_1782689] using wordTrace_append hprefix tailTrace_1782689
  have hstable : (prefixWord ++ tailWord_1782689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782689).length < 2 ^ (prefixWord ++ tailWord_1782689).sum := by decide
  have hdescent : baseEnd_1782689 < baseStart_1782689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782746 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_1782746 : Nat := 118140960795 + 1782746 * 2 ^ 59
def prefixEnd_1782746 : Nat := 4983230072969 + 3 ^ 40 * 1782746 * 2
def baseEnd_1782746 : Nat := 915405582880387231776307

theorem tailTrace_1782746 : CollatzResearch.WordTrace tailWord_1782746 prefixEnd_1782746 915405582880387231776307 := by
  unfold tailWord_1782746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16255522099855796405478023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43348058932948790414608061 16255522099855796405478023)
  ·
    refine ⟨24383283149783694608217035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16255522099855796405478023 24383283149783694608217035)
    ·
      refine ⟨36574924724675541912325553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24383283149783694608217035 36574924724675541912325553)
      ·
        refine ⟨27431193543506656434244165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36574924724675541912325553 27431193543506656434244165)
        ·
          refine ⟨5143348789407498081420781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27431193543506656434244165 5143348789407498081420781)
          ·
            refine ⟨1928755796027811780532793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5143348789407498081420781 1928755796027811780532793)
            ·
              refine ⟨1446566847020858835399595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928755796027811780532793 1446566847020858835399595)
              ·
                refine ⟨2169850270531288253099393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446566847020858835399595 2169850270531288253099393)
                ·
                  refine ⟨1627387702898466189824545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2169850270531288253099393 1627387702898466189824545)
                  ·
                    refine ⟨1220540777173849642368409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1627387702898466189824545 1220540777173849642368409)
                    ·
                      refine ⟨915405582880387231776307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220540777173849642368409 915405582880387231776307)
                      ·
                        rfl

theorem cell23_1782746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_1782746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782746 prefixEnd_1782746 := by exact prefixLift 1782746
  have htrace : WordTrace (prefixWord ++ tailWord_1782746) baseStart_1782746 baseEnd_1782746 := by
    simpa [prefixWord, tailWord_1782746, baseEnd_1782746] using wordTrace_append hprefix tailTrace_1782746
  have hstable : (prefixWord ++ tailWord_1782746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782746).length < 2 ^ (prefixWord ++ tailWord_1782746).sum := by decide
  have hdescent : baseEnd_1782746 < baseStart_1782746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782771 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_1782771 : Nat := 118140960795 + 1782771 * 2 ^ 59
def prefixEnd_1782771 : Nat := 4983230072969 + 3 ^ 40 * 1782771 * 2
def baseEnd_1782771 : Nat := 915418419896749633963691

theorem tailTrace_1782771 : CollatzResearch.WordTrace tailWord_1782771 prefixEnd_1782771 915418419896749633963691 := by
  unfold tailWord_1782771
  simp only [CollatzResearch.WordTrace]
  refine ⟨65023000224332614891572167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43348666816221743261048111 65023000224332614891572167)
  ·
    refine ⟨97534500336498922337358251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65023000224332614891572167 97534500336498922337358251)
    ·
      refine ⟨146301750504748383506037377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97534500336498922337358251 146301750504748383506037377)
      ·
        refine ⟨109726312878561287629528033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146301750504748383506037377 109726312878561287629528033)
        ·
          refine ⟨82294734658920965722146025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109726312878561287629528033 82294734658920965722146025)
          ·
            refine ⟨61721050994190724291609519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82294734658920965722146025 61721050994190724291609519)
            ·
              refine ⟨92581576491286086437414279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61721050994190724291609519 92581576491286086437414279)
              ·
                refine ⟨138872364736929129656121419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92581576491286086437414279 138872364736929129656121419)
                ·
                  refine ⟨208308547105393694484182129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 138872364736929129656121419 208308547105393694484182129)
                  ·
                    refine ⟨156231410329045270863136597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 208308547105393694484182129 156231410329045270863136597)
                    ·
                      refine ⟨915418419896749633963691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 156231410329045270863136597 915418419896749633963691)
                      ·
                        rfl

theorem cell23_1782771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1782771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782771 prefixEnd_1782771 := by exact prefixLift 1782771
  have htrace : WordTrace (prefixWord ++ tailWord_1782771) baseStart_1782771 baseEnd_1782771 := by
    simpa [prefixWord, tailWord_1782771, baseEnd_1782771] using wordTrace_append hprefix tailTrace_1782771
  have hstable : (prefixWord ++ tailWord_1782771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782771).length < 2 ^ (prefixWord ++ tailWord_1782771).sum := by decide
  have hdescent : baseEnd_1782771 < baseStart_1782771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782785 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_1782785 : Nat := 118140960795 + 1782785 * 2 ^ 59
def prefixEnd_1782785 : Nat := 4983230072969 + 3 ^ 40 * 1782785 * 2
def baseEnd_1782785 : Nat := 915425608625912579188627

theorem tailTrace_1782785 : CollatzResearch.WordTrace tailWord_1782785 prefixEnd_1782785 915425608625912579188627 := by
  unfold tailWord_1782785
  simp only [CollatzResearch.WordTrace]
  refine ⟨65023510846281895282581809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43349007230854596855054539 65023510846281895282581809)
  ·
    refine ⟨48767633134711421461936357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65023510846281895282581809 48767633134711421461936357)
    ·
      refine ⟨9143931212758391524113067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48767633134711421461936357 9143931212758391524113067)
      ·
        refine ⟨13715896819137587286169601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9143931212758391524113067 13715896819137587286169601)
        ·
          refine ⟨10286922614353190464627201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13715896819137587286169601 10286922614353190464627201)
          ·
            refine ⟨7715191960764892848470401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10286922614353190464627201 7715191960764892848470401)
            ·
              refine ⟨5786393970573669636352801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7715191960764892848470401 5786393970573669636352801)
              ·
                refine ⟨4339795477930252227264601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786393970573669636352801 4339795477930252227264601)
                ·
                  refine ⟨3254846608447689170448451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4339795477930252227264601 3254846608447689170448451)
                  ·
                    refine ⟨4882269912671533755672677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3254846608447689170448451 4882269912671533755672677)
                    ·
                      refine ⟨915425608625912579188627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4882269912671533755672677 915425608625912579188627)
                      ·
                        rfl

theorem cell23_1782785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_1782785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782785 prefixEnd_1782785 := by exact prefixLift 1782785
  have htrace : WordTrace (prefixWord ++ tailWord_1782785) baseStart_1782785 baseEnd_1782785 := by
    simpa [prefixWord, tailWord_1782785, baseEnd_1782785] using wordTrace_append hprefix tailTrace_1782785
  have hstable : (prefixWord ++ tailWord_1782785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782785).length < 2 ^ (prefixWord ++ tailWord_1782785).sum := by decide
  have hdescent : baseEnd_1782785 < baseStart_1782785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782812 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1782812 : Nat := 118140960795 + 1782812 * 2 ^ 59
def prefixEnd_1782812 : Nat := 4983230072969 + 3 ^ 40 * 1782812 * 2
def baseEnd_1782812 : Nat := 305146490867861324517001

theorem tailTrace_1782812 : CollatzResearch.WordTrace tailWord_1782812 prefixEnd_1782812 305146490867861324517001 := by
  unfold tailWord_1782812
  simp only [CollatzResearch.WordTrace]
  refine ⟨32512247808592039446907345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43349663744789385929209793 32512247808592039446907345)
  ·
    refine ⟨24384185856444029585180509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32512247808592039446907345 24384185856444029585180509)
    ·
      refine ⟨9144069696166511094442691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24384185856444029585180509 9144069696166511094442691)
      ·
        refine ⟨13716104544249766641664037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9144069696166511094442691 13716104544249766641664037)
        ·
          refine ⟨2571769602046831245312007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13716104544249766641664037 2571769602046831245312007)
          ·
            refine ⟨3857654403070246867968011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2571769602046831245312007 3857654403070246867968011)
            ·
              refine ⟨5786481604605370301952017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3857654403070246867968011 5786481604605370301952017)
              ·
                refine ⟨4339861203454027726464013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5786481604605370301952017 4339861203454027726464013)
                ·
                  refine ⟨1627447951295260397424005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4339861203454027726464013 1627447951295260397424005)
                  ·
                    refine ⟨305146490867861324517001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627447951295260397424005 305146490867861324517001)
                    ·
                      rfl

theorem cell23_1782812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1782812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782812 prefixEnd_1782812 := by exact prefixLift 1782812
  have htrace : WordTrace (prefixWord ++ tailWord_1782812) baseStart_1782812 baseEnd_1782812 := by
    simpa [prefixWord, tailWord_1782812, baseEnd_1782812] using wordTrace_append hprefix tailTrace_1782812
  have hstable : (prefixWord ++ tailWord_1782812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782812).length < 2 ^ (prefixWord ++ tailWord_1782812).sum := by decide
  have hdescent : baseEnd_1782812 < baseStart_1782812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782835 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 3]
def baseStart_1782835 : Nat := 118140960795 + 1782835 * 2 ^ 59
def prefixEnd_1782835 : Nat := 4983230072969 + 3 ^ 40 * 1782835 * 2
def baseEnd_1782835 : Nat := 915451282658637383563397

theorem tailTrace_1782835 : CollatzResearch.WordTrace tailWord_1782835 prefixEnd_1782835 915451282658637383563397 := by
  unfold tailWord_1782835
  simp only [CollatzResearch.WordTrace]
  refine ⟨65025334496100753821901959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43350222997400502547934639 65025334496100753821901959)
  ·
    refine ⟨97538001744151130732852939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65025334496100753821901959 97538001744151130732852939)
    ·
      refine ⟨146307002616226696099279409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97538001744151130732852939 146307002616226696099279409)
      ·
        refine ⟨109730251962170022074459557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146307002616226696099279409 109730251962170022074459557)
        ·
          refine ⟨20574422242906879138961167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109730251962170022074459557 20574422242906879138961167)
          ·
            refine ⟨30861633364360318708441751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20574422242906879138961167 30861633364360318708441751)
            ·
              refine ⟨46292450046540478062662627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30861633364360318708441751 46292450046540478062662627)
              ·
                refine ⟨69438675069810717093993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46292450046540478062662627 69438675069810717093993941)
                ·
                  refine ⟨1627468946948688681890483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 69438675069810717093993941 1627468946948688681890483)
                  ·
                    refine ⟨2441203420423033022835725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1627468946948688681890483 2441203420423033022835725)
                    ·
                      refine ⟨915451282658637383563397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2441203420423033022835725 915451282658637383563397)
                      ·
                        rfl

theorem cell23_1782835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 3].length) (baseStart_1782835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782835 prefixEnd_1782835 := by exact prefixLift 1782835
  have htrace : WordTrace (prefixWord ++ tailWord_1782835) baseStart_1782835 baseEnd_1782835 := by
    simpa [prefixWord, tailWord_1782835, baseEnd_1782835] using wordTrace_append hprefix tailTrace_1782835
  have hstable : (prefixWord ++ tailWord_1782835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782835).length < 2 ^ (prefixWord ++ tailWord_1782835).sum := by decide
  have hdescent : baseEnd_1782835 < baseStart_1782835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782885 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_1782885 : Nat := 118140960795 + 1782885 * 2 ^ 59
def prefixEnd_1782885 : Nat := 4983230072969 + 3 ^ 40 * 1782885 * 2
def baseEnd_1782885 : Nat := 305158985563787395979389

theorem tailTrace_1782885 : CollatzResearch.WordTrace tailWord_1782885 prefixEnd_1782885 305158985563787395979389 := by
  unfold tailWord_1782885
  simp only [CollatzResearch.WordTrace]
  refine ⟨65027158145919612361222109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43351438763946408240814739 65027158145919612361222109)
  ·
    refine ⟨24385184304719854635458291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65027158145919612361222109 24385184304719854635458291)
    ·
      refine ⟨36577776457079781953187437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24385184304719854635458291 36577776457079781953187437)
      ·
        refine ⟨13716666171404918232445289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36577776457079781953187437 13716666171404918232445289)
        ·
          refine ⟨10287499628553688674333967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13716666171404918232445289 10287499628553688674333967)
          ·
            refine ⟨15431249442830533011500951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287499628553688674333967 15431249442830533011500951)
            ·
              refine ⟨23146874164245799517251427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15431249442830533011500951 23146874164245799517251427)
              ·
                refine ⟨34720311246368699275877141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23146874164245799517251427 34720311246368699275877141)
                ·
                  refine ⟨1627514589673532778556741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 34720311246368699275877141 1627514589673532778556741)
                  ·
                    refine ⟨305158985563787395979389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627514589673532778556741 305158985563787395979389)
                    ·
                      rfl

theorem cell23_1782885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_1782885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782885 prefixEnd_1782885 := by exact prefixLift 1782885
  have htrace : WordTrace (prefixWord ++ tailWord_1782885) baseStart_1782885 baseEnd_1782885 := by
    simpa [prefixWord, tailWord_1782885, baseEnd_1782885] using wordTrace_append hprefix tailTrace_1782885
  have hstable : (prefixWord ++ tailWord_1782885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782885).length < 2 ^ (prefixWord ++ tailWord_1782885).sum := by decide
  have hdescent : baseEnd_1782885 < baseStart_1782885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782895 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_1782895 : Nat := 118140960795 + 1782895 * 2 ^ 59
def prefixEnd_1782895 : Nat := 4983230072969 + 3 ^ 40 * 1782895 * 2
def baseEnd_1782895 : Nat := 915482091497907148813121

theorem tailTrace_1782895 : CollatzResearch.WordTrace tailWord_1782895 prefixEnd_1782895 915482091497907148813121 := by
  unfold tailWord_1782895
  simp only [CollatzResearch.WordTrace]
  refine ⟨65027522875883384069086139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43351681917255589379390759 65027522875883384069086139)
  ·
    refine ⟨97541284313825076103629209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65027522875883384069086139 97541284313825076103629209)
    ·
      refine ⟨73155963235368807077721907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97541284313825076103629209 73155963235368807077721907)
      ·
        refine ⟨109733944853053210616582861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73155963235368807077721907 109733944853053210616582861)
        ·
          refine ⟨41150229319894953981218573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109733944853053210616582861 41150229319894953981218573)
          ·
            refine ⟨15431335994960607742956965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41150229319894953981218573 15431335994960607742956965)
            ·
              refine ⟨2893375499055113951804431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15431335994960607742956965 2893375499055113951804431)
              ·
                refine ⟨4340063248582670927706647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893375499055113951804431 4340063248582670927706647)
                ·
                  refine ⟨6510094872874006391559971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340063248582670927706647 6510094872874006391559971)
                  ·
                    refine ⟨9765142309311009587339957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510094872874006391559971 9765142309311009587339957)
                    ·
                      refine ⟨915482091497907148813121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9765142309311009587339957 915482091497907148813121)
                      ·
                        rfl

theorem cell23_1782895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_1782895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782895 prefixEnd_1782895 := by exact prefixLift 1782895
  have htrace : WordTrace (prefixWord ++ tailWord_1782895) baseStart_1782895 baseEnd_1782895 := by
    simpa [prefixWord, tailWord_1782895, baseEnd_1782895] using wordTrace_append hprefix tailTrace_1782895
  have hstable : (prefixWord ++ tailWord_1782895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782895).length < 2 ^ (prefixWord ++ tailWord_1782895).sum := by decide
  have hdescent : baseEnd_1782895 < baseStart_1782895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782902 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1782902 : Nat := 118140960795 + 1782902 * 2 ^ 59
def prefixEnd_1782902 : Nat := 4983230072969 + 3 ^ 40 * 1782902 * 2
def baseEnd_1782902 : Nat := 305161895287496207141863

theorem tailTrace_1782902 : CollatzResearch.WordTrace tailWord_1782902 prefixEnd_1782902 305161895287496207141863 := by
  unfold tailWord_1782902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064236136678626516536935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43351852124572016176393973 4064236136678626516536935)
  ·
    refine ⟨6096354205017939774805403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064236136678626516536935 6096354205017939774805403)
    ·
      refine ⟨9144531307526909662208105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096354205017939774805403 9144531307526909662208105)
      ·
        refine ⟨6858398480645182246656079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9144531307526909662208105 6858398480645182246656079)
        ·
          refine ⟨10287597720967773369984119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6858398480645182246656079 10287597720967773369984119)
          ·
            refine ⟨15431396581451660054976179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10287597720967773369984119 15431396581451660054976179)
            ·
              refine ⟨23147094872177490082464269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15431396581451660054976179 23147094872177490082464269)
              ·
                refine ⟨8680160577066558780924101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23147094872177490082464269 8680160577066558780924101)
                ·
                  refine ⟨1627530108199979771423269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8680160577066558780924101 1627530108199979771423269)
                  ·
                    refine ⟨305161895287496207141863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1627530108199979771423269 305161895287496207141863)
                    ·
                      rfl

theorem cell23_1782902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1782902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782902 prefixEnd_1782902 := by exact prefixLift 1782902
  have htrace : WordTrace (prefixWord ++ tailWord_1782902) baseStart_1782902 baseEnd_1782902 := by
    simpa [prefixWord, tailWord_1782902, baseEnd_1782902] using wordTrace_append hprefix tailTrace_1782902
  have hstable : (prefixWord ++ tailWord_1782902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782902).length < 2 ^ (prefixWord ++ tailWord_1782902).sum := by decide
  have hdescent : baseEnd_1782902 < baseStart_1782902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782910 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_1782910 : Nat := 118140960795 + 1782910 * 2 ^ 59
def prefixEnd_1782910 : Nat := 4983230072969 + 3 ^ 40 * 1782910 * 2
def baseEnd_1782910 : Nat := 101721088189747176680617

theorem tailTrace_1782910 : CollatzResearch.WordTrace tailWord_1782910 prefixEnd_1782910 101721088189747176680617 := by
  unfold tailWord_1782910
  simp only [CollatzResearch.WordTrace]
  refine ⟨8128508746353630203860273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43352046647219361087254789 8128508746353630203860273)
  ·
    refine ⟨6096381559765222652895205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8128508746353630203860273 6096381559765222652895205)
    ·
      refine ⟨1143071542455979247417851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6096381559765222652895205 1143071542455979247417851)
      ·
        refine ⟨1714607313683968871126777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143071542455979247417851 1714607313683968871126777)
        ·
          refine ⟨1285955485262976653345083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714607313683968871126777 1285955485262976653345083)
          ·
            refine ⟨1928933227894464980017625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285955485262976653345083 1928933227894464980017625)
            ·
              refine ⟨1446699920920848735013219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1928933227894464980017625 1446699920920848735013219)
              ·
                refine ⟨2170049881381273102519829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446699920920848735013219 2170049881381273102519829)
                ·
                  refine ⟨101721088189747176680617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2170049881381273102519829 101721088189747176680617)
                  ·
                    rfl

theorem cell23_1782910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_1782910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782910 prefixEnd_1782910 := by exact prefixLift 1782910
  have htrace : WordTrace (prefixWord ++ tailWord_1782910) baseStart_1782910 baseEnd_1782910 := by
    simpa [prefixWord, tailWord_1782910, baseEnd_1782910] using wordTrace_append hprefix tailTrace_1782910
  have hstable : (prefixWord ++ tailWord_1782910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782910).length < 2 ^ (prefixWord ++ tailWord_1782910).sum := by decide
  have hdescent : baseEnd_1782910 < baseStart_1782910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782928 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_1782928 : Nat := 118140960795 + 1782928 * 2 ^ 59
def prefixEnd_1782928 : Nat := 4983230072969 + 3 ^ 40 * 1782928 * 2
def baseEnd_1782928 : Nat := 305166345453168506566823

theorem tailTrace_1782928 : CollatzResearch.WordTrace tailWord_1782928 prefixEnd_1782928 305166345453168506566823 := by
  unfold tailWord_1782928
  simp only [CollatzResearch.WordTrace]
  refine ⟨32514363242381915352518719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43352484323175887136691625 32514363242381915352518719)
  ·
    refine ⟨48771544863572873028778079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32514363242381915352518719 48771544863572873028778079)
    ·
      refine ⟨73157317295359309543167119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48771544863572873028778079 73157317295359309543167119)
      ·
        refine ⟨109735975943038964314750679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73157317295359309543167119 109735975943038964314750679)
        ·
          refine ⟨164603963914558446472126019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109735975943038964314750679 164603963914558446472126019)
          ·
            refine ⟨246905945871837669708189029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164603963914558446472126019 246905945871837669708189029)
            ·
              refine ⟨46294864850969563070285443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 246905945871837669708189029 46294864850969563070285443)
              ·
                refine ⟨69442297276454344605428165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46294864850969563070285443 69442297276454344605428165)
                ·
                  refine ⟨13020430739335189613517781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69442297276454344605428165 13020430739335189613517781)
                  ·
                    refine ⟨305166345453168506566823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13020430739335189613517781 305166345453168506566823)
                    ·
                      rfl

theorem cell23_1782928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_1782928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782928 prefixEnd_1782928 := by exact prefixLift 1782928
  have htrace : WordTrace (prefixWord ++ tailWord_1782928) baseStart_1782928 baseEnd_1782928 := by
    simpa [prefixWord, tailWord_1782928, baseEnd_1782928] using wordTrace_append hprefix tailTrace_1782928
  have hstable : (prefixWord ++ tailWord_1782928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782928).length < 2 ^ (prefixWord ++ tailWord_1782928).sum := by decide
  have hdescent : baseEnd_1782928 < baseStart_1782928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782946 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_1782946 : Nat := 118140960795 + 1782946 * 2 ^ 59
def prefixEnd_1782946 : Nat := 4983230072969 + 3 ^ 40 * 1782946 * 2
def baseEnd_1782946 : Nat := 915508279011286449275387

theorem tailTrace_1782946 : CollatzResearch.WordTrace tailWord_1782946 prefixEnd_1782946 915508279011286449275387 := by
  unfold tailWord_1782946
  simp only [CollatzResearch.WordTrace]
  refine ⟨16257345749674654944798173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43352921999132413186128461 16257345749674654944798173)
  ·
    refine ⟨6096504656127995604299315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16257345749674654944798173 6096504656127995604299315)
    ·
      refine ⟨9144756984191993406448973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6096504656127995604299315 9144756984191993406448973)
      ·
        refine ⟨3429283869071997527418365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9144756984191993406448973 3429283869071997527418365)
        ·
          refine ⟨1285981450901999072781887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3429283869071997527418365 1285981450901999072781887)
          ·
            refine ⟨1928972176352998609172831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285981450901999072781887 1928972176352998609172831)
            ·
              refine ⟨2893458264529497913759247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928972176352998609172831 2893458264529497913759247)
              ·
                refine ⟨4340187396794246870638871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2893458264529497913759247 4340187396794246870638871)
                ·
                  refine ⟨6510281095191370305958307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340187396794246870638871 6510281095191370305958307)
                  ·
                    refine ⟨9765421642787055458937461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6510281095191370305958307 9765421642787055458937461)
                    ·
                      refine ⟨915508279011286449275387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9765421642787055458937461 915508279011286449275387)
                      ·
                        rfl

theorem cell23_1782946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_1782946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782946 prefixEnd_1782946 := by exact prefixLift 1782946
  have htrace : WordTrace (prefixWord ++ tailWord_1782946) baseStart_1782946 baseEnd_1782946 := by
    simpa [prefixWord, tailWord_1782946, baseEnd_1782946] using wordTrace_append hprefix tailTrace_1782946
  have hstable : (prefixWord ++ tailWord_1782946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782946).length < 2 ^ (prefixWord ++ tailWord_1782946).sum := by decide
  have hdescent : baseEnd_1782946 < baseStart_1782946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1782966 : List Nat := [5, 1, 3, 2, 1, 2, 1, 8]
def baseStart_1782966 : Nat := 118140960795 + 1782966 * 2 ^ 59
def prefixEnd_1782966 : Nat := 4983230072969 + 3 ^ 40 * 1782966 * 2
def baseEnd_1782966 : Nat := 33908094393495421149085

theorem tailTrace_1782966 : CollatzResearch.WordTrace tailWord_1782966 prefixEnd_1782966 33908094393495421149085 := by
  unfold tailWord_1782966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064382028664135199682547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43353408305750775463280501 4064382028664135199682547)
  ·
    refine ⟨6096573042996202799523821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064382028664135199682547 6096573042996202799523821)
    ·
      refine ⟨2286214891123576049821433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6096573042996202799523821 2286214891123576049821433)
      ·
        refine ⟨1714661168342682037366075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2286214891123576049821433 1714661168342682037366075)
        ·
          refine ⟨2571991752514023056049113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714661168342682037366075 2571991752514023056049113)
          ·
            refine ⟨1928993814385517292036835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2571991752514023056049113 1928993814385517292036835)
            ·
              refine ⟨2893490721578275938055253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1928993814385517292036835 2893490721578275938055253)
              ·
                refine ⟨33908094393495421149085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2893490721578275938055253 33908094393495421149085)
                ·
                  rfl

theorem cell23_1782966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_1782966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1782966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1782966 prefixEnd_1782966 := by exact prefixLift 1782966
  have htrace : WordTrace (prefixWord ++ tailWord_1782966) baseStart_1782966 baseEnd_1782966 := by
    simpa [prefixWord, tailWord_1782966, baseEnd_1782966] using wordTrace_append hprefix tailTrace_1782966
  have hstable : (prefixWord ++ tailWord_1782966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1782966).length < 2 ^ (prefixWord ++ tailWord_1782966).sum := by decide
  have hdescent : baseEnd_1782966 < baseStart_1782966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1782966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783069 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1783069 : Nat := 118140960795 + 1783069 * 2 ^ 59
def prefixEnd_1783069 : Nat := 4983230072969 + 3 ^ 40 * 1783069 * 2
def baseEnd_1783069 : Nat := 305190479043929822679107

theorem tailTrace_1783069 : CollatzResearch.WordTrace tailWord_1783069 prefixEnd_1783069 305190479043929822679107 := by
  unfold tailWord_1783069
  simp only [CollatzResearch.WordTrace]
  refine ⟨65033869177253011785920261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43355912784835341190613507 65033869177253011785920261)
  ·
    refine ⟨12193850470734939709860049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65033869177253011785920261 12193850470734939709860049)
    ·
      refine ⟨9145387853051204782395037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12193850470734939709860049 9145387853051204782395037)
      ·
        refine ⟨3429520444894201793398139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9145387853051204782395037 3429520444894201793398139)
        ·
          refine ⟨5144280667341302690097209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429520444894201793398139 5144280667341302690097209)
          ·
            refine ⟨3858210500505977017572907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144280667341302690097209 3858210500505977017572907)
            ·
              refine ⟨5787315750758965526359361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858210500505977017572907 5787315750758965526359361)
              ·
                refine ⟨4340486813069224144769521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787315750758965526359361 4340486813069224144769521)
                ·
                  refine ⟨3255365109801918108577141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4340486813069224144769521 3255365109801918108577141)
                  ·
                    refine ⟨305190479043929822679107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3255365109801918108577141 305190479043929822679107)
                    ·
                      rfl

theorem cell23_1783069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1783069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783069 prefixEnd_1783069 := by exact prefixLift 1783069
  have htrace : WordTrace (prefixWord ++ tailWord_1783069) baseStart_1783069 baseEnd_1783069 := by
    simpa [prefixWord, tailWord_1783069, baseEnd_1783069] using wordTrace_append hprefix tailTrace_1783069
  have hstable : (prefixWord ++ tailWord_1783069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783069).length < 2 ^ (prefixWord ++ tailWord_1783069).sum := by decide
  have hdescent : baseEnd_1783069 < baseStart_1783069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783176 : List Nat := [2, 1, 3, 3, 1, 2, 4, 1, 1, 5]
def baseStart_1783176 : Nat := 118140960795 + 1783176 * 2 ^ 59
def prefixEnd_1783176 : Nat := 4983230072969 + 3 ^ 40 * 1783176 * 2
def baseEnd_1783176 : Nat := 305208793187273516466443

theorem tailTrace_1783176 : CollatzResearch.WordTrace tailWord_1783176 prefixEnd_1783176 305208793187273516466443 := by
  unfold tailWord_1783176
  simp only [CollatzResearch.WordTrace]
  refine ⟨32518885893932684530032691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43358514525243579373376921 32518885893932684530032691)
  ·
    refine ⟨48778328840899026795049037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32518885893932684530032691 48778328840899026795049037)
    ·
      refine ⟨18291873315337135048143389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48778328840899026795049037 18291873315337135048143389)
      ·
        refine ⟨6859452493251425643053771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18291873315337135048143389 6859452493251425643053771)
        ·
          refine ⟨10289178739877138464580657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859452493251425643053771 10289178739877138464580657)
          ·
            refine ⟨7716884054907853848435493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10289178739877138464580657 7716884054907853848435493)
            ·
              refine ⟨1446915760295222596581655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7716884054907853848435493 1446915760295222596581655)
              ·
                refine ⟨2170373640442833894872483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1446915760295222596581655 2170373640442833894872483)
                ·
                  refine ⟨3255560460664250842308725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170373640442833894872483 3255560460664250842308725)
                  ·
                    refine ⟨305208793187273516466443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3255560460664250842308725 305208793187273516466443)
                    ·
                      rfl

theorem cell23_1783176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_1783176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783176 prefixEnd_1783176 := by exact prefixLift 1783176
  have htrace : WordTrace (prefixWord ++ tailWord_1783176) baseStart_1783176 baseEnd_1783176 := by
    simpa [prefixWord, tailWord_1783176, baseEnd_1783176] using wordTrace_append hprefix tailTrace_1783176
  have hstable : (prefixWord ++ tailWord_1783176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783176).length < 2 ^ (prefixWord ++ tailWord_1783176).sum := by decide
  have hdescent : baseEnd_1783176 < baseStart_1783176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783179 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 4]
def baseStart_1783179 : Nat := 118140960795 + 1783179 * 2 ^ 59
def prefixEnd_1783179 : Nat := 4983230072969 + 3 ^ 40 * 1783179 * 2
def baseEnd_1783179 : Nat := 915627920003784037661815

theorem tailTrace_1783179 : CollatzResearch.WordTrace tailWord_1783179 prefixEnd_1783179 915627920003784037661815 := by
  unfold tailWord_1783179
  simp only [CollatzResearch.WordTrace]
  refine ⟨65037881206854500572424591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43358587471236333714949727 65037881206854500572424591)
  ·
    refine ⟨97556821810281750858636887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65037881206854500572424591 97556821810281750858636887)
    ·
      refine ⟨146335232715422626287955331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97556821810281750858636887 146335232715422626287955331)
      ·
        refine ⟨219502849073133939431932997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146335232715422626287955331 219502849073133939431932997)
        ·
          refine ⟨41156784201212613643487437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219502849073133939431932997 41156784201212613643487437)
          ·
            refine ⟨15433794075454730116307789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41156784201212613643487437 15433794075454730116307789)
            ·
              refine ⟨5787672778295523793615421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15433794075454730116307789 5787672778295523793615421)
              ·
                refine ⟨2170377291860821422605783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5787672778295523793615421 2170377291860821422605783)
                ·
                  refine ⟨3255565937791232133908675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170377291860821422605783 3255565937791232133908675)
                  ·
                    refine ⟨4883348906686848200863013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3255565937791232133908675 4883348906686848200863013)
                    ·
                      refine ⟨915627920003784037661815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4883348906686848200863013 915627920003784037661815)
                      ·
                        rfl

theorem cell23_1783179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 4].length) (baseStart_1783179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783179 prefixEnd_1783179 := by exact prefixLift 1783179
  have htrace : WordTrace (prefixWord ++ tailWord_1783179) baseStart_1783179 baseEnd_1783179 := by
    simpa [prefixWord, tailWord_1783179, baseEnd_1783179] using wordTrace_append hprefix tailTrace_1783179
  have hstable : (prefixWord ++ tailWord_1783179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783179).length < 2 ^ (prefixWord ++ tailWord_1783179).sum := by decide
  have hdescent : baseEnd_1783179 < baseStart_1783179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783199 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1783199 : Nat := 118140960795 + 1783199 * 2 ^ 59
def prefixEnd_1783199 : Nat := 4983230072969 + 3 ^ 40 * 1783199 * 2
def baseEnd_1783199 : Nat := 915638189616873959411723

theorem tailTrace_1783199 : CollatzResearch.WordTrace tailWord_1783199 prefixEnd_1783199 915638189616873959411723 := by
  unfold tailWord_1783199
  simp only [CollatzResearch.WordTrace]
  refine ⟨65038610666782043988152651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43359073777854695992101767 65038610666782043988152651)
  ·
    refine ⟨97557916000173065982228977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65038610666782043988152651 97557916000173065982228977)
    ·
      refine ⟨73168437000129799486671733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97557916000173065982228977 73168437000129799486671733)
      ·
        refine ⟨6859540968762168701875475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73168437000129799486671733 6859540968762168701875475)
        ·
          refine ⟨10289311453143253052813213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6859540968762168701875475 10289311453143253052813213)
          ·
            refine ⟨3858491794928719894804955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10289311453143253052813213 3858491794928719894804955)
            ·
              refine ⟨5787737692393079842207433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858491794928719894804955 5787737692393079842207433)
              ·
                refine ⟨4340803269294809881655575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787737692393079842207433 4340803269294809881655575)
                ·
                  refine ⟨6511204903942214822483363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4340803269294809881655575 6511204903942214822483363)
                  ·
                    refine ⟨9766807355913322233725045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6511204903942214822483363 9766807355913322233725045)
                    ·
                      refine ⟨915638189616873959411723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9766807355913322233725045 915638189616873959411723)
                      ·
                        rfl

theorem cell23_1783199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1783199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783199 prefixEnd_1783199 := by exact prefixLift 1783199
  have htrace : WordTrace (prefixWord ++ tailWord_1783199) baseStart_1783199 baseEnd_1783199 := by
    simpa [prefixWord, tailWord_1783199, baseEnd_1783199] using wordTrace_append hprefix tailTrace_1783199
  have hstable : (prefixWord ++ tailWord_1783199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783199).length < 2 ^ (prefixWord ++ tailWord_1783199).sum := by decide
  have hdescent : baseEnd_1783199 < baseStart_1783199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783213 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1783213 : Nat := 118140960795 + 1783213 * 2 ^ 59
def prefixEnd_1783213 : Nat := 4983230072969 + 3 ^ 40 * 1783213 * 2
def baseEnd_1783213 : Nat := 915645378346036904636659

theorem tailTrace_1783213 : CollatzResearch.WordTrace tailWord_1783213 prefixEnd_1783213 915645378346036904636659 := by
  unfold tailWord_1783213
  simp only [CollatzResearch.WordTrace]
  refine ⟨65039121288731324379162293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43359414192487549586108195 65039121288731324379162293)
  ·
    refine ⟨6097417620818561660546465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65039121288731324379162293 6097417620818561660546465)
    ·
      refine ⟨4573063215613921245409849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6097417620818561660546465 4573063215613921245409849)
      ·
        refine ⟨3429797411710440934057387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4573063215613921245409849 3429797411710440934057387)
        ·
          refine ⟨5144696117565661401086081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3429797411710440934057387 5144696117565661401086081)
          ·
            refine ⟨3858522088174246050814561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5144696117565661401086081 3858522088174246050814561)
            ·
              refine ⟨2893891566130684538110921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3858522088174246050814561 2893891566130684538110921)
              ·
                refine ⟨2170418674598013403583191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2893891566130684538110921 2170418674598013403583191)
                ·
                  refine ⟨3255628011897020105374787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170418674598013403583191 3255628011897020105374787)
                  ·
                    refine ⟨4883442017845530158062181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3255628011897020105374787 4883442017845530158062181)
                    ·
                      refine ⟨915645378346036904636659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4883442017845530158062181 915645378346036904636659)
                      ·
                        rfl

theorem cell23_1783213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1783213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783213 prefixEnd_1783213 := by exact prefixLift 1783213
  have htrace : WordTrace (prefixWord ++ tailWord_1783213) baseStart_1783213 baseEnd_1783213 := by
    simpa [prefixWord, tailWord_1783213, baseEnd_1783213] using wordTrace_append hprefix tailTrace_1783213
  have hstable : (prefixWord ++ tailWord_1783213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783213).length < 2 ^ (prefixWord ++ tailWord_1783213).sum := by decide
  have hdescent : baseEnd_1783213 < baseStart_1783213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783229 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_1783229 : Nat := 118140960795 + 1783229 * 2 ^ 59
def prefixEnd_1783229 : Nat := 4983230072969 + 3 ^ 40 * 1783229 * 2
def baseEnd_1783229 : Nat := 915653594036508842036585

theorem tailTrace_1783229 : CollatzResearch.WordTrace tailWord_1783229 prefixEnd_1783229 915653594036508842036585 := by
  unfold tailWord_1783229
  simp only [CollatzResearch.WordTrace]
  refine ⟨65039704856673359111744741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43359803237782239407829827 65039704856673359111744741)
  ·
    refine ⟨12194944660626254833452139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65039704856673359111744741 12194944660626254833452139)
    ·
      refine ⟨18292416990939382250178209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12194944660626254833452139 18292416990939382250178209)
      ·
        refine ⟨13719312743204536687633657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18292416990939382250178209 13719312743204536687633657)
        ·
          refine ⟨10289484557403402515725243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13719312743204536687633657 10289484557403402515725243)
          ·
            refine ⟨15434226836105103773587865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10289484557403402515725243 15434226836105103773587865)
            ·
              refine ⟨11575670127078827830190899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15434226836105103773587865 11575670127078827830190899)
              ·
                refine ⟨17363505190618241745286349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11575670127078827830190899 17363505190618241745286349)
                ·
                  refine ⟨6511314446481840654482381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17363505190618241745286349 6511314446481840654482381)
                  ·
                    refine ⟨2441742917430690245430893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6511314446481840654482381 2441742917430690245430893)
                    ·
                      refine ⟨915653594036508842036585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2441742917430690245430893 915653594036508842036585)
                      ·
                        rfl

theorem cell23_1783229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_1783229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783229 prefixEnd_1783229 := by exact prefixLift 1783229
  have htrace : WordTrace (prefixWord ++ tailWord_1783229) baseStart_1783229 baseEnd_1783229 := by
    simpa [prefixWord, tailWord_1783229, baseEnd_1783229] using wordTrace_append hprefix tailTrace_1783229
  have hstable : (prefixWord ++ tailWord_1783229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783229).length < 2 ^ (prefixWord ++ tailWord_1783229).sum := by decide
  have hdescent : baseEnd_1783229 < baseStart_1783229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783234 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_1783234 : Nat := 118140960795 + 1783234 * 2 ^ 59
def prefixEnd_1783234 : Nat := 4983230072969 + 3 ^ 40 * 1783234 * 2
def baseEnd_1783234 : Nat := 915656161439781322474063

theorem tailTrace_1783234 : CollatzResearch.WordTrace tailWord_1783234 prefixEnd_1783234 915656161439781322474063 := by
  unfold tailWord_1783234
  simp only [CollatzResearch.WordTrace]
  refine ⟨16259971805413811241419189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43359924814436829977117837 16259971805413811241419189)
  ·
    refine ⟨1524372356757544803883049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16259971805413811241419189 1524372356757544803883049)
    ·
      refine ⟨1143279267568158602912287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524372356757544803883049 1143279267568158602912287)
      ·
        refine ⟨1714918901352237904368431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143279267568158602912287 1714918901352237904368431)
        ·
          refine ⟨2572378352028356856552647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714918901352237904368431 2572378352028356856552647)
          ·
            refine ⟨3858567528042535284828971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572378352028356856552647 3858567528042535284828971)
            ·
              refine ⟨5787851292063802927243457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3858567528042535284828971 5787851292063802927243457)
              ·
                refine ⟨4340888469047852195432593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5787851292063802927243457 4340888469047852195432593)
                ·
                  refine ⟨3255666351785889146574445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4340888469047852195432593 3255666351785889146574445)
                  ·
                    refine ⟨1220874881919708429965417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3255666351785889146574445 1220874881919708429965417)
                    ·
                      refine ⟨915656161439781322474063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220874881919708429965417 915656161439781322474063)
                      ·
                        rfl

theorem cell23_1783234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_1783234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783234 prefixEnd_1783234 := by exact prefixLift 1783234
  have htrace : WordTrace (prefixWord ++ tailWord_1783234) baseStart_1783234 baseEnd_1783234 := by
    simpa [prefixWord, tailWord_1783234, baseEnd_1783234] using wordTrace_append hprefix tailTrace_1783234
  have hstable : (prefixWord ++ tailWord_1783234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783234).length < 2 ^ (prefixWord ++ tailWord_1783234).sum := by decide
  have hdescent : baseEnd_1783234 < baseStart_1783234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783246 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1783246 : Nat := 118140960795 + 1783246 * 2 ^ 59
def prefixEnd_1783246 : Nat := 4983230072969 + 3 ^ 40 * 1783246 * 2
def baseEnd_1783246 : Nat := 915662323207635275524007

theorem tailTrace_1783246 : CollatzResearch.WordTrace tailWord_1783246 prefixEnd_1783246 915662323207635275524007 := by
  unfold tailWord_1783246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130040612201471376889199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43360216598407847343409061 8130040612201471376889199)
  ·
    refine ⟨12195060918302207065333799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8130040612201471376889199 12195060918302207065333799)
    ·
      refine ⟨18292591377453310598000699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12195060918302207065333799 18292591377453310598000699)
      ·
        refine ⟨27438887066179965897001049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18292591377453310598000699 27438887066179965897001049)
        ·
          refine ⟨20579165299634974422750787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27438887066179965897001049 20579165299634974422750787)
          ·
            refine ⟨30868747949452461634126181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20579165299634974422750787 30868747949452461634126181)
            ·
              refine ⟨5787890240522336556398659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30868747949452461634126181 5787890240522336556398659)
              ·
                refine ⟨8681835360783504834597989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5787890240522336556398659 8681835360783504834597989)
                ·
                  refine ⟨1627844130146907156487123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8681835360783504834597989 1627844130146907156487123)
                  ·
                    refine ⟨2441766195220360734730685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1627844130146907156487123 2441766195220360734730685)
                    ·
                      refine ⟨915662323207635275524007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2441766195220360734730685 915662323207635275524007)
                      ·
                        rfl

theorem cell23_1783246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1783246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783246 prefixEnd_1783246 := by exact prefixLift 1783246
  have htrace : WordTrace (prefixWord ++ tailWord_1783246) baseStart_1783246 baseEnd_1783246 := by
    simpa [prefixWord, tailWord_1783246, baseEnd_1783246] using wordTrace_append hprefix tailTrace_1783246
  have hstable : (prefixWord ++ tailWord_1783246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783246).length < 2 ^ (prefixWord ++ tailWord_1783246).sum := by decide
  have hdescent : baseEnd_1783246 < baseStart_1783246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783312 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6]
def baseStart_1783312 : Nat := 118140960795 + 1783312 * 2 ^ 59
def prefixEnd_1783312 : Nat := 4983230072969 + 3 ^ 40 * 1783312 * 2
def baseEnd_1783312 : Nat := 915696212930832017298703

theorem tailTrace_1783312 : CollatzResearch.WordTrace tailWord_1783312 prefixEnd_1783312 915696212930832017298703 := by
  unfold tailWord_1783312
  simp only [CollatzResearch.WordTrace]
  refine ⟨32521366057686332143508095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43361821410248442858010793 32521366057686332143508095)
  ·
    refine ⟨48782049086529498215262143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32521366057686332143508095 48782049086529498215262143)
    ·
      refine ⟨73173073629794247322893215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48782049086529498215262143 73173073629794247322893215)
      ·
        refine ⟨109759610444691370984339823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73173073629794247322893215 109759610444691370984339823)
        ·
          refine ⟨164639415667037056476509735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109759610444691370984339823 164639415667037056476509735)
          ·
            refine ⟨246959123500555584714764603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164639415667037056476509735 246959123500555584714764603)
            ·
              refine ⟨370438685250833377072146905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 246959123500555584714764603 370438685250833377072146905)
              ·
                refine ⟨277829013938125032804110179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370438685250833377072146905 277829013938125032804110179)
                ·
                  refine ⟨416743520907187549206165269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 277829013938125032804110179 416743520907187549206165269)
                  ·
                    refine ⟨19534852542524416369038997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 416743520907187549206165269 19534852542524416369038997)
                    ·
                      refine ⟨915696212930832017298703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19534852542524416369038997 915696212930832017298703)
                      ·
                        rfl

theorem cell23_1783312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_1783312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783312 prefixEnd_1783312 := by exact prefixLift 1783312
  have htrace : WordTrace (prefixWord ++ tailWord_1783312) baseStart_1783312 baseEnd_1783312 := by
    simpa [prefixWord, tailWord_1783312, baseEnd_1783312] using wordTrace_append hprefix tailTrace_1783312
  have hstable : (prefixWord ++ tailWord_1783312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783312).length < 2 ^ (prefixWord ++ tailWord_1783312).sum := by decide
  have hdescent : baseEnd_1783312 < baseStart_1783312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783376 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2]
def baseStart_1783376 : Nat := 118140960795 + 1783376 * 2 ^ 59
def prefixEnd_1783376 : Nat := 4983230072969 + 3 ^ 40 * 1783376 * 2
def baseEnd_1783376 : Nat := 915729075692719766898409

theorem tailTrace_1783376 : CollatzResearch.WordTrace tailWord_1783376 prefixEnd_1783376 915729075692719766898409 := by
  unfold tailWord_1783376
  simp only [CollatzResearch.WordTrace]
  refine ⟨32522533193570401608672991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43363377591427202144897321 32522533193570401608672991)
  ·
    refine ⟨48783799790355602413009487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32522533193570401608672991 48783799790355602413009487)
    ·
      refine ⟨73175699685533403619514231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48783799790355602413009487 73175699685533403619514231)
      ·
        refine ⟨109763549528300105429271347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73175699685533403619514231 109763549528300105429271347)
        ·
          refine ⟨164645324292450158143907021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109763549528300105429271347 164645324292450158143907021)
          ·
            refine ⟨61741996609668809303965133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164645324292450158143907021 61741996609668809303965133)
            ·
              refine ⟨23153248728625803488986925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61741996609668809303965133 23153248728625803488986925)
              ·
                refine ⟨8682468273234676308370097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23153248728625803488986925 8682468273234676308370097)
                ·
                  refine ⟨6511851204926007231277573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8682468273234676308370097 6511851204926007231277573)
                  ·
                    refine ⟨1220972100923626355864545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6511851204926007231277573 1220972100923626355864545)
                    ·
                      refine ⟨915729075692719766898409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1220972100923626355864545 915729075692719766898409)
                      ·
                        rfl

theorem cell23_1783376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2].length) (baseStart_1783376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783376 prefixEnd_1783376 := by exact prefixLift 1783376
  have htrace : WordTrace (prefixWord ++ tailWord_1783376) baseStart_1783376 baseEnd_1783376 := by
    simpa [prefixWord, tailWord_1783376, baseEnd_1783376] using wordTrace_append hprefix tailTrace_1783376
  have hstable : (prefixWord ++ tailWord_1783376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783376).length < 2 ^ (prefixWord ++ tailWord_1783376).sum := by decide
  have hdescent : baseEnd_1783376 < baseStart_1783376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783396 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_1783396 : Nat := 118140960795 + 1783396 * 2 ^ 59
def prefixEnd_1783396 : Nat := 4983230072969 + 3 ^ 40 * 1783396 * 2
def baseEnd_1783396 : Nat := 915739345305809688648317

theorem tailTrace_1783396 : CollatzResearch.WordTrace tailWord_1783396 prefixEnd_1783396 915739345305809688648317 := by
  unfold tailWord_1783396
  simp only [CollatzResearch.WordTrace]
  refine ⟨32522897923534173316537021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43363863898045564422049361 32522897923534173316537021)
  ·
    refine ⟨12196086721325314993701383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32522897923534173316537021 12196086721325314993701383)
    ·
      refine ⟨18294130081987972490552075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12196086721325314993701383 18294130081987972490552075)
      ·
        refine ⟨27441195122981958735828113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18294130081987972490552075 27441195122981958735828113)
        ·
          refine ⟨20580896342236469051871085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27441195122981958735828113 20580896342236469051871085)
          ·
            refine ⟨7717836128338675894451657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20580896342236469051871085 7717836128338675894451657)
            ·
              refine ⟨5788377096254006920838743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7717836128338675894451657 5788377096254006920838743)
              ·
                refine ⟨8682565644381010381258115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5788377096254006920838743 8682565644381010381258115)
                ·
                  refine ⟨13023848466571515571887173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8682565644381010381258115 13023848466571515571887173)
                  ·
                    refine ⟨2441971587482159169728845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13023848466571515571887173 2441971587482159169728845)
                    ·
                      refine ⟨915739345305809688648317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2441971587482159169728845 915739345305809688648317)
                      ·
                        rfl

theorem cell23_1783396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_1783396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783396 prefixEnd_1783396 := by exact prefixLift 1783396
  have htrace : WordTrace (prefixWord ++ tailWord_1783396) baseStart_1783396 baseEnd_1783396 := by
    simpa [prefixWord, tailWord_1783396, baseEnd_1783396] using wordTrace_append hprefix tailTrace_1783396
  have hstable : (prefixWord ++ tailWord_1783396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783396).length < 2 ^ (prefixWord ++ tailWord_1783396).sum := by decide
  have hdescent : baseEnd_1783396 < baseStart_1783396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783399 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 8]
def baseStart_1783399 : Nat := 118140960795 + 1783399 * 2 ^ 59
def prefixEnd_1783399 : Nat := 4983230072969 + 3 ^ 40 * 1783399 * 2
def baseEnd_1783399 : Nat := 101748987305308130767867

theorem tailTrace_1783399 : CollatzResearch.WordTrace tailWord_1783399 prefixEnd_1783399 101748987305308130767867 := by
  unfold tailWord_1783399
  simp only [CollatzResearch.WordTrace]
  refine ⟨65045905266057478145433251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43363936844038318763622167 65045905266057478145433251)
  ·
    refine ⟨97568857899086217218149877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65045905266057478145433251 97568857899086217218149877)
    ·
      refine ⟨9147080428039332864201551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97568857899086217218149877 9147080428039332864201551)
      ·
        refine ⟨13720620642058999296302327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9147080428039332864201551 13720620642058999296302327)
        ·
          refine ⟨20580930963088498944453491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13720620642058999296302327 20580930963088498944453491)
          ·
            refine ⟨30871396444632748416680237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20580930963088498944453491 30871396444632748416680237)
            ·
              refine ⟨11576773666737280656255089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30871396444632748416680237 11576773666737280656255089)
              ·
                refine ⟨8682580250052960492191317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11576773666737280656255089 8682580250052960492191317)
                ·
                  refine ⟨101748987305308130767867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8682580250052960492191317 101748987305308130767867)
                  ·
                    rfl

theorem cell23_1783399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 8].length) (baseStart_1783399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783399 prefixEnd_1783399 := by exact prefixLift 1783399
  have htrace : WordTrace (prefixWord ++ tailWord_1783399) baseStart_1783399 baseEnd_1783399 := by
    simpa [prefixWord, tailWord_1783399, baseEnd_1783399] using wordTrace_append hprefix tailTrace_1783399
  have hstable : (prefixWord ++ tailWord_1783399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783399).length < 2 ^ (prefixWord ++ tailWord_1783399).sum := by decide
  have hdescent : baseEnd_1783399 < baseStart_1783399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783413 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1783413 : Nat := 118140960795 + 1783413 * 2 ^ 59
def prefixEnd_1783413 : Nat := 4983230072969 + 3 ^ 40 * 1783413 * 2
def baseEnd_1783413 : Nat := 915748074476936122135739

theorem tailTrace_1783413 : CollatzResearch.WordTrace tailWord_1783413 prefixEnd_1783413 915748074476936122135739 := by
  unfold tailWord_1783413
  simp only [CollatzResearch.WordTrace]
  refine ⟨65046415888006758536442893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43364277258671172357628595 65046415888006758536442893)
  ·
    refine ⟨24392405958002534451166085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65046415888006758536442893 24392405958002534451166085)
    ·
      refine ⟨4573576117125475209593641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24392405958002534451166085 4573576117125475209593641)
      ·
        refine ⟨3430182087844106407195231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4573576117125475209593641 3430182087844106407195231)
        ·
          refine ⟨5145273131766159610792847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3430182087844106407195231 5145273131766159610792847)
          ·
            refine ⟨7717909697649239416189271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5145273131766159610792847 7717909697649239416189271)
            ·
              refine ⟨11576864546473859124283907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7717909697649239416189271 11576864546473859124283907)
              ·
                refine ⟨17365296819710788686425861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11576864546473859124283907 17365296819710788686425861)
                ·
                  refine ⟨3255993153695772878704849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17365296819710788686425861 3255993153695772878704849)
                  ·
                    refine ⟨2441994865271829659028637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3255993153695772878704849 2441994865271829659028637)
                    ·
                      refine ⟨915748074476936122135739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2441994865271829659028637 915748074476936122135739)
                      ·
                        rfl

theorem cell23_1783413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1783413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783413 prefixEnd_1783413 := by exact prefixLift 1783413
  have htrace : WordTrace (prefixWord ++ tailWord_1783413) baseStart_1783413 baseEnd_1783413 := by
    simpa [prefixWord, tailWord_1783413, baseEnd_1783413] using wordTrace_append hprefix tailTrace_1783413
  have hstable : (prefixWord ++ tailWord_1783413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783413).length < 2 ^ (prefixWord ++ tailWord_1783413).sum := by decide
  have hdescent : baseEnd_1783413 < baseStart_1783413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783483 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 7, 2, 2]
def baseStart_1783483 : Nat := 118140960795 + 1783483 * 2 ^ 59
def prefixEnd_1783483 : Nat := 4983230072969 + 3 ^ 40 * 1783483 * 2
def baseEnd_1783483 : Nat := 915784018122750848260417

theorem tailTrace_1783483 : CollatzResearch.WordTrace tailWord_1783483 prefixEnd_1783483 915784018122750848260417 := by
  unfold tailWord_1783483
  simp only [CollatzResearch.WordTrace]
  refine ⟨65048968997753160491491103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43365979331835440327660735 65048968997753160491491103)
  ·
    refine ⟨97573453496629740737236655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65048968997753160491491103 97573453496629740737236655)
    ·
      refine ⟨146360180244944611105854983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97573453496629740737236655 146360180244944611105854983)
      ·
        refine ⟨219540270367416916658782475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146360180244944611105854983 219540270367416916658782475)
        ·
          refine ⟨329310405551125374988173713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219540270367416916658782475 329310405551125374988173713)
          ·
            refine ⟨246982804163344031241130285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 329310405551125374988173713 246982804163344031241130285)
            ·
              refine ⟨92618551561254011715423857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246982804163344031241130285 92618551561254011715423857)
              ·
                refine ⟨69463913670940508786567893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92618551561254011715423857 69463913670940508786567893)
                ·
                  refine ⟨1628060476662668174685185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 69463913670940508786567893 1628060476662668174685185)
                  ·
                    refine ⟨1221045357497001131013889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628060476662668174685185 1221045357497001131013889)
                    ·
                      refine ⟨915784018122750848260417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221045357497001131013889 915784018122750848260417)
                      ·
                        rfl

theorem cell23_1783483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 2, 2].length) (baseStart_1783483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783483 prefixEnd_1783483 := by exact prefixLift 1783483
  have htrace : WordTrace (prefixWord ++ tailWord_1783483) baseStart_1783483 baseEnd_1783483 := by
    simpa [prefixWord, tailWord_1783483, baseEnd_1783483] using wordTrace_append hprefix tailTrace_1783483
  have hstable : (prefixWord ++ tailWord_1783483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783483).length < 2 ^ (prefixWord ++ tailWord_1783483).sum := by decide
  have hdescent : baseEnd_1783483 < baseStart_1783483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783494 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1783494 : Nat := 118140960795 + 1783494 * 2 ^ 59
def prefixEnd_1783494 : Nat := 4983230072969 + 3 ^ 40 * 1783494 * 2
def baseEnd_1783494 : Nat := 915789666409950305222867

theorem tailTrace_1783494 : CollatzResearch.WordTrace tailWord_1783494 prefixEnd_1783494 915789666409950305222867 := by
  unfold tailWord_1783494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032792818772290917816923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43366246800475539580094357 2032792818772290917816923)
  ·
    refine ⟨3049189228158436376725385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032792818772290917816923 3049189228158436376725385)
    ·
      refine ⟨2286891921118827282544039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3049189228158436376725385 2286891921118827282544039)
      ·
        refine ⟨3430337881678240923816059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2286891921118827282544039 3430337881678240923816059)
        ·
          refine ⟨5145506822517361385724089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3430337881678240923816059 5145506822517361385724089)
          ·
            refine ⟨3859130116888021039293067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5145506822517361385724089 3859130116888021039293067)
            ·
              refine ⟨5788695175332031558939601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859130116888021039293067 5788695175332031558939601)
              ·
                refine ⟨4341521381499023669204701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5788695175332031558939601 4341521381499023669204701)
                ·
                  refine ⟨1628070518062133875951763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4341521381499023669204701 1628070518062133875951763)
                  ·
                    refine ⟨2442105777093200813927645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1628070518062133875951763 2442105777093200813927645)
                    ·
                      refine ⟨915789666409950305222867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442105777093200813927645 915789666409950305222867)
                      ·
                        rfl

theorem cell23_1783494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1783494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783494 prefixEnd_1783494 := by exact prefixLift 1783494
  have htrace : WordTrace (prefixWord ++ tailWord_1783494) baseStart_1783494 baseEnd_1783494 := by
    simpa [prefixWord, tailWord_1783494, baseEnd_1783494] using wordTrace_append hprefix tailTrace_1783494
  have hstable : (prefixWord ++ tailWord_1783494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783494).length < 2 ^ (prefixWord ++ tailWord_1783494).sum := by decide
  have hdescent : baseEnd_1783494 < baseStart_1783494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783499 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_1783499 : Nat := 118140960795 + 1783499 * 2 ^ 59
def prefixEnd_1783499 : Nat := 4983230072969 + 3 ^ 40 * 1783499 * 2
def baseEnd_1783499 : Nat := 915792233813222785660343

theorem tailTrace_1783499 : CollatzResearch.WordTrace tailWord_1783499 prefixEnd_1783499 915792233813222785660343 := by
  unfold tailWord_1783499
  simp only [CollatzResearch.WordTrace]
  refine ⟨65049552565695195224073551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43366368377130130149382367 65049552565695195224073551)
  ·
    refine ⟨97574328848542792836110327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65049552565695195224073551 97574328848542792836110327)
    ·
      refine ⟨146361493272814189254165491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97574328848542792836110327 146361493272814189254165491)
      ·
        refine ⟨219542239909221283881248237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146361493272814189254165491 219542239909221283881248237)
        ·
          refine ⟨82328339965957981455468089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219542239909221283881248237 82328339965957981455468089)
          ·
            refine ⟨61746254974468486091601067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82328339965957981455468089 61746254974468486091601067)
            ·
              refine ⟨92619382461702729137401601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61746254974468486091601067 92619382461702729137401601)
              ·
                refine ⟨69464536846277046853051201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92619382461702729137401601 69464536846277046853051201)
                ·
                  refine ⟨52098402634707785139788401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69464536846277046853051201 52098402634707785139788401)
                  ·
                    refine ⟨39073801976030838854841301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52098402634707785139788401 39073801976030838854841301)
                    ·
                      refine ⟨915792233813222785660343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39073801976030838854841301 915792233813222785660343)
                      ·
                        rfl

theorem cell23_1783499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_1783499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783499 prefixEnd_1783499 := by exact prefixLift 1783499
  have htrace : WordTrace (prefixWord ++ tailWord_1783499) baseStart_1783499 baseEnd_1783499 := by
    simpa [prefixWord, tailWord_1783499, baseEnd_1783499] using wordTrace_append hprefix tailTrace_1783499
  have hstable : (prefixWord ++ tailWord_1783499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783499).length < 2 ^ (prefixWord ++ tailWord_1783499).sum := by decide
  have hdescent : baseEnd_1783499 < baseStart_1783499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783517 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1783517 : Nat := 118140960795 + 1783517 * 2 ^ 59
def prefixEnd_1783517 : Nat := 4983230072969 + 3 ^ 40 * 1783517 * 2
def baseEnd_1783517 : Nat := 915801476465003715235261

theorem tailTrace_1783517 : CollatzResearch.WordTrace tailWord_1783517 prefixEnd_1783517 915801476465003715235261 := by
  unfold tailWord_1783517
  simp only [CollatzResearch.WordTrace]
  refine ⟨65050209079629984298228805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43366806053086656198819203 65050209079629984298228805)
  ·
    refine ⟨12196914202430622055917901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65050209079629984298228805 12196914202430622055917901)
    ·
      refine ⟨4573842825911483270969213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12196914202430622055917901 4573842825911483270969213)
      ·
        refine ⟨1715191059716806226613455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4573842825911483270969213 1715191059716806226613455)
        ·
          refine ⟨2572786589575209339920183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715191059716806226613455 2572786589575209339920183)
          ·
            refine ⟨3859179884362814009880275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2572786589575209339920183 3859179884362814009880275)
            ·
              refine ⟨5788769826544221014820413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859179884362814009880275 5788769826544221014820413)
              ·
                refine ⟨2170788684954082880557655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5788769826544221014820413 2170788684954082880557655)
                ·
                  refine ⟨3256183027431124320836483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170788684954082880557655 3256183027431124320836483)
                  ·
                    refine ⟨4884274541146686481254725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3256183027431124320836483 4884274541146686481254725)
                    ·
                      refine ⟨915801476465003715235261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4884274541146686481254725 915801476465003715235261)
                      ·
                        rfl

theorem cell23_1783517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1783517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783517 prefixEnd_1783517 := by exact prefixLift 1783517
  have htrace : WordTrace (prefixWord ++ tailWord_1783517) baseStart_1783517 baseEnd_1783517 := by
    simpa [prefixWord, tailWord_1783517, baseEnd_1783517] using wordTrace_append hprefix tailTrace_1783517
  have hstable : (prefixWord ++ tailWord_1783517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783517).length < 2 ^ (prefixWord ++ tailWord_1783517).sum := by decide
  have hdescent : baseEnd_1783517 < baseStart_1783517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783520 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3]
def baseStart_1783520 : Nat := 118140960795 + 1783520 * 2 ^ 59
def prefixEnd_1783520 : Nat := 4983230072969 + 3 ^ 40 * 1783520 * 2
def baseEnd_1783520 : Nat := 915803016906967203497747

theorem tailTrace_1783520 : CollatzResearch.WordTrace tailWord_1783520 prefixEnd_1783520 915803016906967203497747 := by
  unfold tailWord_1783520
  simp only [CollatzResearch.WordTrace]
  refine ⟨32525159249309557905294007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43366878999079410540392009 32525159249309557905294007)
  ·
    refine ⟨48787738873964336857941011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32525159249309557905294007 48787738873964336857941011)
    ·
      refine ⟨73181608310946505286911517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48787738873964336857941011 73181608310946505286911517)
      ·
        refine ⟨27443103116604939482591819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73181608310946505286911517 27443103116604939482591819)
        ·
          refine ⟨41164654674907409223887729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27443103116604939482591819 41164654674907409223887729)
          ·
            refine ⟨30873491006180556917915797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41164654674907409223887729 30873491006180556917915797)
            ·
              refine ⟨1447194890914713605527303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30873491006180556917915797 1447194890914713605527303)
              ·
                refine ⟨2170792336372070408290955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1447194890914713605527303 2170792336372070408290955)
                ·
                  refine ⟨3256188504558105612436433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2170792336372070408290955 3256188504558105612436433)
                  ·
                    refine ⟨2442141378418579209327325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3256188504558105612436433 2442141378418579209327325)
                    ·
                      refine ⟨915803016906967203497747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442141378418579209327325 915803016906967203497747)
                      ·
                        rfl

theorem cell23_1783520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_1783520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783520 prefixEnd_1783520 := by exact prefixLift 1783520
  have htrace : WordTrace (prefixWord ++ tailWord_1783520) baseStart_1783520 baseEnd_1783520 := by
    simpa [prefixWord, tailWord_1783520, baseEnd_1783520] using wordTrace_append hprefix tailTrace_1783520
  have hstable : (prefixWord ++ tailWord_1783520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783520).length < 2 ^ (prefixWord ++ tailWord_1783520).sum := by decide
  have hdescent : baseEnd_1783520 < baseStart_1783520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783543 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_1783543 : Nat := 118140960795 + 1783543 * 2 ^ 59
def prefixEnd_1783543 : Nat := 4983230072969 + 3 ^ 40 * 1783543 * 2
def baseEnd_1783543 : Nat := 915814826962020613510141

theorem tailTrace_1783543 : CollatzResearch.WordTrace tailWord_1783543 prefixEnd_1783543 915814826962020613510141 := by
  unfold tailWord_1783543
  simp only [CollatzResearch.WordTrace]
  refine ⟨65051157377535790738675283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43367438251690527159116855 65051157377535790738675283)
  ·
    refine ⟨97576736066303686108012925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65051157377535790738675283 97576736066303686108012925)
    ·
      refine ⟨36591276024863882290504847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97576736066303686108012925 36591276024863882290504847)
      ·
        refine ⟨54886914037295823435757271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36591276024863882290504847 54886914037295823435757271)
        ·
          refine ⟨82330371055943735153635907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54886914037295823435757271 82330371055943735153635907)
          ·
            refine ⟨123495556583915602730453861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82330371055943735153635907 123495556583915602730453861)
            ·
              refine ⟨23155416859484175511960099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123495556583915602730453861 23155416859484175511960099)
              ·
                refine ⟨34733125289226263267940149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23155416859484175511960099 34733125289226263267940149)
                ·
                  refine ⟨3256230495864962181369389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34733125289226263267940149 3256230495864962181369389)
                  ·
                    refine ⟨1221086435949360818013521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3256230495864962181369389 1221086435949360818013521)
                    ·
                      refine ⟨915814826962020613510141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221086435949360818013521 915814826962020613510141)
                      ·
                        rfl

theorem cell23_1783543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_1783543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783543 prefixEnd_1783543 := by exact prefixLift 1783543
  have htrace : WordTrace (prefixWord ++ tailWord_1783543) baseStart_1783543 baseEnd_1783543 := by
    simpa [prefixWord, tailWord_1783543, baseEnd_1783543] using wordTrace_append hprefix tailTrace_1783543
  have hstable : (prefixWord ++ tailWord_1783543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783543).length < 2 ^ (prefixWord ++ tailWord_1783543).sum := by decide
  have hdescent : baseEnd_1783543 < baseStart_1783543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783566 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 1, 8]
def baseStart_1783566 : Nat := 118140960795 + 1783566 * 2 ^ 59
def prefixEnd_1783566 : Nat := 4983230072969 + 3 ^ 40 * 1783566 * 2
def baseEnd_1783566 : Nat := 305275545672358007840845

theorem tailTrace_1783566 : CollatzResearch.WordTrace tailWord_1783566 prefixEnd_1783566 305275545672358007840845 := by
  unfold tailWord_1783566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131499532056558208345319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43367997504301643777841701 8131499532056558208345319)
  ·
    refine ⟨12197249298084837312517979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8131499532056558208345319 12197249298084837312517979)
    ·
      refine ⟨18295873947127255968776969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12197249298084837312517979 18295873947127255968776969)
      ·
        refine ⟨13721905460345441976582727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18295873947127255968776969 13721905460345441976582727)
        ·
          refine ⟨20582858190518162964874091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13721905460345441976582727 20582858190518162964874091)
          ·
            refine ⟨30874287285777244447311137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20582858190518162964874091 30874287285777244447311137)
            ·
              refine ⟨23155715464332933335483353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30874287285777244447311137 23155715464332933335483353)
              ·
                refine ⟨17366786598249700001612515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23155715464332933335483353 17366786598249700001612515)
                ·
                  refine ⟨26050179897374550002418773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17366786598249700001612515 26050179897374550002418773)
                  ·
                    refine ⟨305275545672358007840845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26050179897374550002418773 305275545672358007840845)
                    ·
                      rfl

theorem cell23_1783566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_1783566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783566 prefixEnd_1783566 := by exact prefixLift 1783566
  have htrace : WordTrace (prefixWord ++ tailWord_1783566) baseStart_1783566 baseEnd_1783566 := by
    simpa [prefixWord, tailWord_1783566, baseEnd_1783566] using wordTrace_append hprefix tailTrace_1783566
  have hstable : (prefixWord ++ tailWord_1783566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783566).length < 2 ^ (prefixWord ++ tailWord_1783566).sum := by decide
  have hdescent : baseEnd_1783566 < baseStart_1783566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783576 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1783576 : Nat := 118140960795 + 1783576 * 2 ^ 59
def prefixEnd_1783576 : Nat := 4983230072969 + 3 ^ 40 * 1783576 * 2
def baseEnd_1783576 : Nat := 915831771823618984397489

theorem tailTrace_1783576 : CollatzResearch.WordTrace tailWord_1783576 prefixEnd_1783576 915831771823618984397489 := by
  unfold tailWord_1783576
  simp only [CollatzResearch.WordTrace]
  refine ⟨32526180493208118687313291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43368240657610824916417721 32526180493208118687313291)
  ·
    refine ⟨48789270739812178030969937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32526180493208118687313291 48789270739812178030969937)
    ·
      refine ⟨36591953054859133523227453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48789270739812178030969937 36591953054859133523227453)
      ·
        refine ⟨13721982395572175071210295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36591953054859133523227453 13721982395572175071210295)
        ·
          refine ⟨20582973593358262606815443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13721982395572175071210295 20582973593358262606815443)
          ·
            refine ⟨30874460390037393910223165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20582973593358262606815443 30874460390037393910223165)
            ·
              refine ⟨11577922646264022716333687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30874460390037393910223165 11577922646264022716333687)
              ·
                refine ⟨17366883969396034074500531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11577922646264022716333687 17366883969396034074500531)
                ·
                  refine ⟨26050325954094051111750797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17366883969396034074500531 26050325954094051111750797)
                  ·
                    refine ⟨9768872232785269166906549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26050325954094051111750797 9768872232785269166906549)
                    ·
                      refine ⟨915831771823618984397489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9768872232785269166906549 915831771823618984397489)
                      ·
                        rfl

theorem cell23_1783576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1783576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783576 prefixEnd_1783576 := by exact prefixLift 1783576
  have htrace : WordTrace (prefixWord ++ tailWord_1783576) baseStart_1783576 baseEnd_1783576 := by
    simpa [prefixWord, tailWord_1783576, baseEnd_1783576] using wordTrace_append hprefix tailTrace_1783576
  have hstable : (prefixWord ++ tailWord_1783576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783576).length < 2 ^ (prefixWord ++ tailWord_1783576).sum := by decide
  have hdescent : baseEnd_1783576 < baseStart_1783576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783647 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 5]
def baseStart_1783647 : Nat := 118140960795 + 1783647 * 2 ^ 59
def prefixEnd_1783647 : Nat := 4983230072969 + 3 ^ 40 * 1783647 * 2
def baseEnd_1783647 : Nat := 101763136550009800734407

theorem tailTrace_1783647 : CollatzResearch.WordTrace tailWord_1783647 prefixEnd_1783647 101763136550009800734407 := by
  unfold tailWord_1783647
  simp only [CollatzResearch.WordTrace]
  refine ⟨65054950569159016500461195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43369967046106011000307463 65054950569159016500461195)
  ·
    refine ⟨97582425853738524750691793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65054950569159016500461195 97582425853738524750691793)
    ·
      refine ⟨73186819390303893563018845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97582425853738524750691793 73186819390303893563018845)
      ·
        refine ⟨27445057271363960086132067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73186819390303893563018845 27445057271363960086132067)
        ·
          refine ⟨41167585907045940129198101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27445057271363960086132067 41167585907045940129198101)
          ·
            refine ⟨1929730589392778443556161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41167585907045940129198101 1929730589392778443556161)
            ·
              refine ⟨1447297942044583832667121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1929730589392778443556161 1447297942044583832667121)
              ·
                refine ⟨1085473456533437874500341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447297942044583832667121 1085473456533437874500341)
                ·
                  refine ⟨101763136550009800734407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085473456533437874500341 101763136550009800734407)
                  ·
                    rfl

theorem cell23_1783647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 5].length) (baseStart_1783647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783647 prefixEnd_1783647 := by exact prefixLift 1783647
  have htrace : WordTrace (prefixWord ++ tailWord_1783647) baseStart_1783647 baseEnd_1783647 := by
    simpa [prefixWord, tailWord_1783647, baseEnd_1783647] using wordTrace_append hprefix tailTrace_1783647
  have hstable : (prefixWord ++ tailWord_1783647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783647).length < 2 ^ (prefixWord ++ tailWord_1783647).sum := by decide
  have hdescent : baseEnd_1783647 < baseStart_1783647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783703 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 8]
def baseStart_1783703 : Nat := 118140960795 + 1783703 * 2 ^ 59
def prefixEnd_1783703 : Nat := 4983230072969 + 3 ^ 40 * 1783703 * 2
def baseEnd_1783703 : Nat := 101766331540748887501045

theorem tailTrace_1783703 : CollatzResearch.WordTrace tailWord_1783703 prefixEnd_1783703 101766331540748887501045 := by
  unfold tailWord_1783703
  simp only [CollatzResearch.WordTrace]
  refine ⟨65056993056956138064499763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43371328704637425376333175 65056993056956138064499763)
  ·
    refine ⟨97585489585434207096749645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65056993056956138064499763 97585489585434207096749645)
    ·
      refine ⟨36594558594537827661281117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97585489585434207096749645 36594558594537827661281117)
      ·
        refine ⟨13722959472951685372980419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36594558594537827661281117 13722959472951685372980419)
        ·
          refine ⟨20584439209427528059470629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13722959472951685372980419 20584439209427528059470629)
          ·
            refine ⟨3859582351767661511150743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20584439209427528059470629 3859582351767661511150743)
            ·
              refine ⟨5789373527651492266726115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3859582351767661511150743 5789373527651492266726115)
              ·
                refine ⟨8684060291477238400089173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5789373527651492266726115 8684060291477238400089173)
                ·
                  refine ⟨101766331540748887501045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8684060291477238400089173 101766331540748887501045)
                  ·
                    rfl

theorem cell23_1783703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 8].length) (baseStart_1783703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783703 prefixEnd_1783703 := by exact prefixLift 1783703
  have htrace : WordTrace (prefixWord ++ tailWord_1783703) baseStart_1783703 baseEnd_1783703 := by
    simpa [prefixWord, tailWord_1783703, baseEnd_1783703] using wordTrace_append hprefix tailTrace_1783703
  have hstable : (prefixWord ++ tailWord_1783703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783703).length < 2 ^ (prefixWord ++ tailWord_1783703).sum := by decide
  have hdescent : baseEnd_1783703 < baseStart_1783703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783787 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 3, 2, 2]
def baseStart_1783787 : Nat := 118140960795 + 1783787 * 2 ^ 59
def prefixEnd_1783787 : Nat := 4983230072969 + 3 ^ 40 * 1783787 * 2
def baseEnd_1783787 : Nat := 915940116241717658859019

theorem tailTrace_1783787 : CollatzResearch.WordTrace tailWord_1783787 prefixEnd_1783787 915940116241717658859019 := by
  unfold tailWord_1783787
  simp only [CollatzResearch.WordTrace]
  refine ⟨65060056788651820410557615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43373371192434546940371743 65060056788651820410557615)
  ·
    refine ⟨97590085182977730615836423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65060056788651820410557615 97590085182977730615836423)
    ·
      refine ⟨146385127774466595923754635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97590085182977730615836423 146385127774466595923754635)
      ·
        refine ⟨219577691661699893885631953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146385127774466595923754635 219577691661699893885631953)
        ·
          refine ⟨164683268746274920414223965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219577691661699893885631953 164683268746274920414223965)
          ·
            refine ⟨61756225779853095155333987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164683268746274920414223965 61756225779853095155333987)
            ·
              refine ⟨92634338669779642733000981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61756225779853095155333987 92634338669779642733000981)
              ·
                refine ⟨4342234625145920753109421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 92634338669779642733000981 4342234625145920753109421)
                ·
                  refine ⟨1628337984429720282416033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4342234625145920753109421 1628337984429720282416033)
                  ·
                    refine ⟨1221253488322290211812025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628337984429720282416033 1221253488322290211812025)
                    ·
                      refine ⟨915940116241717658859019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221253488322290211812025 915940116241717658859019)
                      ·
                        rfl

theorem cell23_1783787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 2, 2].length) (baseStart_1783787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783787 prefixEnd_1783787 := by exact prefixLift 1783787
  have htrace : WordTrace (prefixWord ++ tailWord_1783787) baseStart_1783787 baseEnd_1783787 := by
    simpa [prefixWord, tailWord_1783787, baseEnd_1783787] using wordTrace_append hprefix tailTrace_1783787
  have hstable : (prefixWord ++ tailWord_1783787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783787).length < 2 ^ (prefixWord ++ tailWord_1783787).sum := by decide
  have hdescent : baseEnd_1783787 < baseStart_1783787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783820 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1783820 : Nat := 118140960795 + 1783820 * 2 ^ 59
def prefixEnd_1783820 : Nat := 4983230072969 + 3 ^ 40 * 1783820 * 2
def baseEnd_1783820 : Nat := 915957061103316029746367

theorem tailTrace_1783820 : CollatzResearch.WordTrace tailWord_1783820 prefixEnd_1783820 915957061103316029746367 := by
  unfold tailWord_1783820
  simp only [CollatzResearch.WordTrace]
  refine ⟨32530630198766133523254457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43374173598354844697672609 32530630198766133523254457)
  ·
    refine ⟨24397972649074600142440843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32530630198766133523254457 24397972649074600142440843)
    ·
      refine ⟨36596958973611900213661265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24397972649074600142440843 36596958973611900213661265)
      ·
        refine ⟨27447719230208925160245949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36596958973611900213661265 27447719230208925160245949)
        ·
          refine ⟨10292894711328346935092231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27447719230208925160245949 10292894711328346935092231)
          ·
            refine ⟨15439342066992520402638347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10292894711328346935092231 15439342066992520402638347)
            ·
              refine ⟨23159013100488780603957521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15439342066992520402638347 23159013100488780603957521)
              ·
                refine ⟨17369259825366585452968141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23159013100488780603957521 17369259825366585452968141)
                ·
                  refine ⟨6513472434512469544863053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17369259825366585452968141 6513472434512469544863053)
                  ·
                    refine ⟨2442552162942176079323645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6513472434512469544863053 2442552162942176079323645)
                    ·
                      refine ⟨915957061103316029746367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442552162942176079323645 915957061103316029746367)
                      ·
                        rfl

theorem cell23_1783820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1783820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783820 prefixEnd_1783820 := by exact prefixLift 1783820
  have htrace : WordTrace (prefixWord ++ tailWord_1783820) baseStart_1783820 baseEnd_1783820 := by
    simpa [prefixWord, tailWord_1783820, baseEnd_1783820] using wordTrace_append hprefix tailTrace_1783820
  have hstable : (prefixWord ++ tailWord_1783820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783820).length < 2 ^ (prefixWord ++ tailWord_1783820).sum := by decide
  have hdescent : baseEnd_1783820 < baseStart_1783820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783833 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_1783833 : Nat := 118140960795 + 1783833 * 2 ^ 59
def prefixEnd_1783833 : Nat := 4983230072969 + 3 ^ 40 * 1783833 * 2
def baseEnd_1783833 : Nat := 915963736351824478883807

theorem tailTrace_1783833 : CollatzResearch.WordTrace tailWord_1783833 prefixEnd_1783833 915963736351824478883807 := by
  unfold tailWord_1783833
  simp only [CollatzResearch.WordTrace]
  refine ⟨65061734546485170266732153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43374489697656780177821435 65061734546485170266732153)
  ·
    refine ⟨48796300909863877700049115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65061734546485170266732153 48796300909863877700049115)
    ·
      refine ⟨73194451364795816550073673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48796300909863877700049115 73194451364795816550073673)
      ·
        refine ⟨54895838523596862412555255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73194451364795816550073673 54895838523596862412555255)
        ·
          refine ⟨82343757785395293618832883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54895838523596862412555255 82343757785395293618832883)
          ·
            refine ⟨123515636678092940428249325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82343757785395293618832883 123515636678092940428249325)
            ·
              refine ⟨46318363754284852660593497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123515636678092940428249325 46318363754284852660593497)
              ·
                refine ⟨34738772815713639495445123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46318363754284852660593497 34738772815713639495445123)
                ·
                  refine ⟨52108159223570459243167685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34738772815713639495445123 52108159223570459243167685)
                  ·
                    refine ⟨9770279854419461108093941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52108159223570459243167685 9770279854419461108093941)
                    ·
                      refine ⟨915963736351824478883807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9770279854419461108093941 915963736351824478883807)
                      ·
                        rfl

theorem cell23_1783833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_1783833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783833 prefixEnd_1783833 := by exact prefixLift 1783833
  have htrace : WordTrace (prefixWord ++ tailWord_1783833) baseStart_1783833 baseEnd_1783833 := by
    simpa [prefixWord, tailWord_1783833, baseEnd_1783833] using wordTrace_append hprefix tailTrace_1783833
  have hstable : (prefixWord ++ tailWord_1783833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783833).length < 2 ^ (prefixWord ++ tailWord_1783833).sum := by decide
  have hdescent : baseEnd_1783833 < baseStart_1783833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783837 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1783837 : Nat := 118140960795 + 1783837 * 2 ^ 59
def prefixEnd_1783837 : Nat := 4983230072969 + 3 ^ 40 * 1783837 * 2
def baseEnd_1783837 : Nat := 915965790274442463233789

theorem tailTrace_1783837 : CollatzResearch.WordTrace tailWord_1783837 prefixEnd_1783837 915965790274442463233789 := by
  unfold tailWord_1783837
  simp only [CollatzResearch.WordTrace]
  refine ⟨65061880438470678949877765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43374586958980452633251843 65061880438470678949877765)
  ·
    refine ⟨12199102582213252303102081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65061880438470678949877765 12199102582213252303102081)
    ·
      refine ⟨9149326936659939227326561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12199102582213252303102081 9149326936659939227326561)
      ·
        refine ⟨6861995202494954420494921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9149326936659939227326561 6861995202494954420494921)
        ·
          refine ⟨5146496401871215815371191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6861995202494954420494921 5146496401871215815371191)
          ·
            refine ⟨7719744602806823723056787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5146496401871215815371191 7719744602806823723056787)
            ·
              refine ⟨11579616904210235584585181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7719744602806823723056787 11579616904210235584585181)
              ·
                refine ⟨4342356339078838344219443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11579616904210235584585181 4342356339078838344219443)
                ·
                  refine ⟨6513534508618257516329165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4342356339078838344219443 6513534508618257516329165)
                  ·
                    refine ⟨2442575440731846568623437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6513534508618257516329165 2442575440731846568623437)
                    ·
                      refine ⟨915965790274442463233789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442575440731846568623437 915965790274442463233789)
                      ·
                        rfl

theorem cell23_1783837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1783837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783837 prefixEnd_1783837 := by exact prefixLift 1783837
  have htrace : WordTrace (prefixWord ++ tailWord_1783837) baseStart_1783837 baseEnd_1783837 := by
    simpa [prefixWord, tailWord_1783837, baseEnd_1783837] using wordTrace_append hprefix tailTrace_1783837
  have hstable : (prefixWord ++ tailWord_1783837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783837).length < 2 ^ (prefixWord ++ tailWord_1783837).sum := by decide
  have hdescent : baseEnd_1783837 < baseStart_1783837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783880 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1783880 : Nat := 118140960795 + 1783880 * 2 ^ 59
def prefixEnd_1783880 : Nat := 4983230072969 + 3 ^ 40 * 1783880 * 2
def baseEnd_1783880 : Nat := 915987869942585794996091

theorem tailTrace_1783880 : CollatzResearch.WordTrace tailWord_1783880 prefixEnd_1783880 915987869942585794996091 := by
  unfold tailWord_1783880
  simp only [CollatzResearch.WordTrace]
  refine ⟨32531724388657448646846547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43375632518209931529128729 32531724388657448646846547)
  ·
    refine ⟨48797586582986172970269821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32531724388657448646846547 48797586582986172970269821)
    ·
      refine ⟨18299094968619814863851183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48797586582986172970269821 18299094968619814863851183)
      ·
        refine ⟨27448642452929722295776775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18299094968619814863851183 27448642452929722295776775)
        ·
          refine ⟨41172963679394583443665163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27448642452929722295776775 41172963679394583443665163)
          ·
            refine ⟨61759445519091875165497745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41172963679394583443665163 61759445519091875165497745)
            ·
              refine ⟨46319584139318906374123309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61759445519091875165497745 46319584139318906374123309)
              ·
                refine ⟨17369844052244589890296241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46319584139318906374123309 17369844052244589890296241)
                ·
                  refine ⟨13027383039183442417722181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17369844052244589890296241 13027383039183442417722181)
                  ·
                    refine ⟨2442634319846895453322909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13027383039183442417722181 2442634319846895453322909)
                    ·
                      refine ⟨915987869942585794996091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442634319846895453322909 915987869942585794996091)
                      ·
                        rfl

theorem cell23_1783880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1783880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783880 prefixEnd_1783880 := by exact prefixLift 1783880
  have htrace : WordTrace (prefixWord ++ tailWord_1783880) baseStart_1783880 baseEnd_1783880 := by
    simpa [prefixWord, tailWord_1783880, baseEnd_1783880] using wordTrace_append hprefix tailTrace_1783880
  have hstable : (prefixWord ++ tailWord_1783880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783880).length < 2 ^ (prefixWord ++ tailWord_1783880).sum := by decide
  have hdescent : baseEnd_1783880 < baseStart_1783880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783883 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 11]
def baseStart_1783883 : Nat := 118140960795 + 1783883 * 2 ^ 59
def prefixEnd_1783883 : Nat := 4983230072969 + 3 ^ 40 * 1783883 * 2
def baseEnd_1783883 : Nat := 101776601153838809250953

theorem tailTrace_1783883 : CollatzResearch.WordTrace tailWord_1783883 prefixEnd_1783883 101776601153838809250953 := by
  unfold tailWord_1783883
  simp only [CollatzResearch.WordTrace]
  refine ⟨65063558196304028806052303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43375705464202685870701535 65063558196304028806052303)
  ·
    refine ⟨97595337294456043209078455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65063558196304028806052303 97595337294456043209078455)
    ·
      refine ⟨146393005941684064813617683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97595337294456043209078455 146393005941684064813617683)
      ·
        refine ⟨219589508912526097220426525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146393005941684064813617683 219589508912526097220426525)
        ·
          refine ⟨82346065842197286457659947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 219589508912526097220426525 82346065842197286457659947)
          ·
            refine ⟨123519098763295929686489921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82346065842197286457659947 123519098763295929686489921)
            ·
              refine ⟨92639324072471947264867441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123519098763295929686489921 92639324072471947264867441)
              ·
                refine ⟨69479493054353960448650581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92639324072471947264867441 69479493054353960448650581)
                ·
                  refine ⟨101776601153838809250953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 69479493054353960448650581 101776601153838809250953)
                  ·
                    rfl

theorem cell23_1783883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 11].length) (baseStart_1783883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783883 prefixEnd_1783883 := by exact prefixLift 1783883
  have htrace : WordTrace (prefixWord ++ tailWord_1783883) baseStart_1783883 baseEnd_1783883 := by
    simpa [prefixWord, tailWord_1783883, baseEnd_1783883] using wordTrace_append hprefix tailTrace_1783883
  have hstable : (prefixWord ++ tailWord_1783883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783883).length < 2 ^ (prefixWord ++ tailWord_1783883).sum := by decide
  have hdescent : baseEnd_1783883 < baseStart_1783883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1783980 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1783980 : Nat := 118140960795 + 1783980 * 2 ^ 59
def prefixEnd_1783980 : Nat := 4983230072969 + 3 ^ 40 * 1783980 * 2
def baseEnd_1783980 : Nat := 916039218008035403745631

theorem tailTrace_1783980 : CollatzResearch.WordTrace tailWord_1783980 prefixEnd_1783980 916039218008035403745631 := by
  unfold tailWord_1783980
  simp only [CollatzResearch.WordTrace]
  refine ⟨32533548038476307186166697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43378064051301742914888929 32533548038476307186166697)
  ·
    refine ⟨24400161028857230389625023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32533548038476307186166697 24400161028857230389625023)
    ·
      refine ⟨36600241543285845584437535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24400161028857230389625023 36600241543285845584437535)
      ·
        refine ⟨54900362314928768376656303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36600241543285845584437535 54900362314928768376656303)
        ·
          refine ⟨82350543472393152564984455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54900362314928768376656303 82350543472393152564984455)
          ·
            refine ⟨123525815208589728847476683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82350543472393152564984455 123525815208589728847476683)
            ·
              refine ⟨185288722812884593271215025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123525815208589728847476683 185288722812884593271215025)
              ·
                refine ⟨138966542109663444953411269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185288722812884593271215025 138966542109663444953411269)
                ·
                  refine ⟨26056226645561895928764613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138966542109663444953411269 26056226645561895928764613)
                  ·
                    refine ⟨4885542496042855486643365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26056226645561895928764613 4885542496042855486643365)
                    ·
                      refine ⟨916039218008035403745631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4885542496042855486643365 916039218008035403745631)
                      ·
                        rfl

theorem cell23_1783980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1783980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1783980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1783980 prefixEnd_1783980 := by exact prefixLift 1783980
  have htrace : WordTrace (prefixWord ++ tailWord_1783980) baseStart_1783980 baseEnd_1783980 := by
    simpa [prefixWord, tailWord_1783980, baseEnd_1783980] using wordTrace_append hprefix tailTrace_1783980
  have hstable : (prefixWord ++ tailWord_1783980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1783980).length < 2 ^ (prefixWord ++ tailWord_1783980).sum := by decide
  have hdescent : baseEnd_1783980 < baseStart_1783980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1783980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784044 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_1784044 : Nat := 118140960795 + 1784044 * 2 ^ 59
def prefixEnd_1784044 : Nat := 4983230072969 + 3 ^ 40 * 1784044 * 2
def baseEnd_1784044 : Nat := 916072080769923153345337

theorem tailTrace_1784044 : CollatzResearch.WordTrace tailWord_1784044 prefixEnd_1784044 916072080769923153345337 := by
  unfold tailWord_1784044
  simp only [CollatzResearch.WordTrace]
  refine ⟨32534715174360376651331593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43379620232480502201775457 32534715174360376651331593)
  ·
    refine ⟨24401036380770282488498695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32534715174360376651331593 24401036380770282488498695)
    ·
      refine ⟨36601554571155423732748043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24401036380770282488498695 36601554571155423732748043)
      ·
        refine ⟨54902331856733135599122065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36601554571155423732748043 54902331856733135599122065)
        ·
          refine ⟨41176748892549851699341549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54902331856733135599122065 41176748892549851699341549)
          ·
            refine ⟨15441280834706194387253081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41176748892549851699341549 15441280834706194387253081)
            ·
              refine ⟨11580960626029645790439811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15441280834706194387253081 11580960626029645790439811)
              ·
                refine ⟨17371440939044468685659717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11580960626029645790439811 17371440939044468685659717)
                ·
                  refine ⟨3257145176070837878561197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17371440939044468685659717 3257145176070837878561197)
                  ·
                    refine ⟨1221429441026564204460449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3257145176070837878561197 1221429441026564204460449)
                    ·
                      refine ⟨916072080769923153345337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221429441026564204460449 916072080769923153345337)
                      ·
                        rfl

theorem cell23_1784044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_1784044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784044 prefixEnd_1784044 := by exact prefixLift 1784044
  have htrace : WordTrace (prefixWord ++ tailWord_1784044) baseStart_1784044 baseEnd_1784044 := by
    simpa [prefixWord, tailWord_1784044, baseEnd_1784044] using wordTrace_append hprefix tailTrace_1784044
  have hstable : (prefixWord ++ tailWord_1784044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784044).length < 2 ^ (prefixWord ++ tailWord_1784044).sum := by decide
  have hdescent : baseEnd_1784044 < baseStart_1784044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784051 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 1, 1, 3]
def baseStart_1784051 : Nat := 118140960795 + 1784051 * 2 ^ 59
def prefixEnd_1784051 : Nat := 4983230072969 + 3 ^ 40 * 1784051 * 2
def baseEnd_1784051 : Nat := 916075675134504625957805

theorem tailTrace_1784051 : CollatzResearch.WordTrace tailWord_1784051 prefixEnd_1784051 916075675134504625957805 := by
  unfold tailWord_1784051
  simp only [CollatzResearch.WordTrace]
  refine ⟨65069685659695393498168007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43379790439796928998778671 65069685659695393498168007)
  ·
    refine ⟨97604528489543090247252011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65069685659695393498168007 97604528489543090247252011)
    ·
      refine ⟨146406792734314635370878017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97604528489543090247252011 146406792734314635370878017)
      ·
        refine ⟨109805094550735976528158513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146406792734314635370878017 109805094550735976528158513)
        ·
          refine ⟨82353820913051982396118885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109805094550735976528158513 82353820913051982396118885)
          ·
            refine ⟨15441341421197246699272291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82353820913051982396118885 15441341421197246699272291)
            ·
              refine ⟨23162012131795870048908437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15441341421197246699272291 23162012131795870048908437)
              ·
                refine ⟨1085719318677931408542583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23162012131795870048908437 1085719318677931408542583)
                ·
                  refine ⟨1628578978016897112813875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085719318677931408542583 1628578978016897112813875)
                  ·
                    refine ⟨2442868467025345669220813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1628578978016897112813875 2442868467025345669220813)
                    ·
                      refine ⟨916075675134504625957805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442868467025345669220813 916075675134504625957805)
                      ·
                        rfl

theorem cell23_1784051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 1, 3].length) (baseStart_1784051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784051 prefixEnd_1784051 := by exact prefixLift 1784051
  have htrace : WordTrace (prefixWord ++ tailWord_1784051) baseStart_1784051 baseEnd_1784051 := by
    simpa [prefixWord, tailWord_1784051, baseEnd_1784051] using wordTrace_append hprefix tailTrace_1784051
  have hstable : (prefixWord ++ tailWord_1784051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784051).length < 2 ^ (prefixWord ++ tailWord_1784051).sum := by decide
  have hdescent : baseEnd_1784051 < baseStart_1784051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784057 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1784057 : Nat := 118140960795 + 1784057 * 2 ^ 59
def prefixEnd_1784057 : Nat := 4983230072969 + 3 ^ 40 * 1784057 * 2
def baseEnd_1784057 : Nat := 916078756018431602482777

theorem tailTrace_1784057 : CollatzResearch.WordTrace tailWord_1784057 prefixEnd_1784057 916078756018431602482777 := by
  unfold tailWord_1784057
  simp only [CollatzResearch.WordTrace]
  refine ⟨65069904497673656522886425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43379936331782437681924283 65069904497673656522886425)
  ·
    refine ⟨48802428373255242392164819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65069904497673656522886425 48802428373255242392164819)
    ·
      refine ⟨73203642559882863588247229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48802428373255242392164819 73203642559882863588247229)
      ·
        refine ⟨27451365959956073845592711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73203642559882863588247229 27451365959956073845592711)
        ·
          refine ⟨41177048939934110768389067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27451365959956073845592711 41177048939934110768389067)
          ·
            refine ⟨61765573409901166152583601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41177048939934110768389067 61765573409901166152583601)
            ·
              refine ⟨46324180057425874614437701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61765573409901166152583601 46324180057425874614437701)
              ·
                refine ⟨8685783760767351490207069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46324180057425874614437701 8685783760767351490207069)
                ·
                  refine ⟨3257168910287756808827651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8685783760767351490207069 3257168910287756808827651)
                  ·
                    refine ⟨4885753365431635213241477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257168910287756808827651 4885753365431635213241477)
                    ·
                      refine ⟨916078756018431602482777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4885753365431635213241477 916078756018431602482777)
                      ·
                        rfl

theorem cell23_1784057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1784057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784057 prefixEnd_1784057 := by exact prefixLift 1784057
  have htrace : WordTrace (prefixWord ++ tailWord_1784057) baseStart_1784057 baseEnd_1784057 := by
    simpa [prefixWord, tailWord_1784057, baseEnd_1784057] using wordTrace_append hprefix tailTrace_1784057
  have hstable : (prefixWord ++ tailWord_1784057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784057).length < 2 ^ (prefixWord ++ tailWord_1784057).sum := by decide
  have hdescent : baseEnd_1784057 < baseStart_1784057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784074 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1784074 : Nat := 118140960795 + 1784074 * 2 ^ 59
def prefixEnd_1784074 : Nat := 4983230072969 + 3 ^ 40 * 1784074 * 2
def baseEnd_1784074 : Nat := 916087485189558035970199

theorem tailTrace_1784074 : CollatzResearch.WordTrace tailWord_1784074 prefixEnd_1784074 916087485189558035970199 := by
  unfold tailWord_1784074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267631134653017106563819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43380349692408045617503517 16267631134653017106563819)
  ·
    refine ⟨24401446701979525659845729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16267631134653017106563819 24401446701979525659845729)
    ·
      refine ⟨18301085026484644244884297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24401446701979525659845729 18301085026484644244884297)
      ·
        refine ⟨13725813769863483183663223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18301085026484644244884297 13725813769863483183663223)
        ·
          refine ⟨20588720654795224775494835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13725813769863483183663223 20588720654795224775494835)
          ·
            refine ⟨30883080982192837163242253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20588720654795224775494835 30883080982192837163242253)
            ·
              refine ⟨11581155368322313936215845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30883080982192837163242253 11581155368322313936215845)
              ·
                refine ⟨2171466631560433863040471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11581155368322313936215845 2171466631560433863040471)
                ·
                  refine ⟨3257199947340650794560707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171466631560433863040471 3257199947340650794560707)
                  ·
                    refine ⟨4885799921010976191841061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257199947340650794560707 4885799921010976191841061)
                    ·
                      refine ⟨916087485189558035970199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4885799921010976191841061 916087485189558035970199)
                      ·
                        rfl

theorem cell23_1784074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1784074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784074 prefixEnd_1784074 := by exact prefixLift 1784074
  have htrace : WordTrace (prefixWord ++ tailWord_1784074) baseStart_1784074 baseEnd_1784074 := by
    simpa [prefixWord, tailWord_1784074, baseEnd_1784074] using wordTrace_append hprefix tailTrace_1784074
  have hstable : (prefixWord ++ tailWord_1784074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784074).length < 2 ^ (prefixWord ++ tailWord_1784074).sum := by decide
  have hdescent : baseEnd_1784074 < baseStart_1784074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784108 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 1, 2, 2]
def baseStart_1784108 : Nat := 118140960795 + 1784108 * 2 ^ 59
def prefixEnd_1784108 : Nat := 4983230072969 + 3 ^ 40 * 1784108 * 2
def baseEnd_1784108 : Nat := 916104943531810902945043

theorem tailTrace_1784108 : CollatzResearch.WordTrace tailWord_1784108 prefixEnd_1784108 916104943531810902945043 := by
  unfold tailWord_1784108
  simp only [CollatzResearch.WordTrace]
  refine ⟨32535882310244446116496489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43381176413659261488661985 32535882310244446116496489)
  ·
    refine ⟨24401911732683334587372367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32535882310244446116496489 24401911732683334587372367)
    ·
      refine ⟨36602867599025001881058551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24401911732683334587372367 36602867599025001881058551)
      ·
        refine ⟨54904301398537502821587827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36602867599025001881058551 54904301398537502821587827)
        ·
          refine ⟨82356452097806254232381741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54904301398537502821587827 82356452097806254232381741)
          ·
            refine ⟨30883669536677345337143153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82356452097806254232381741 30883669536677345337143153)
            ·
              refine ⟨23162752152508009002857365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30883669536677345337143153 23162752152508009002857365)
              ·
                refine ⟨1085754007148812922008939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23162752152508009002857365 1085754007148812922008939)
                ·
                  refine ⟨1628631010723219383013409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085754007148812922008939 1628631010723219383013409)
                  ·
                    refine ⟨1221473258042414537260057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628631010723219383013409 1221473258042414537260057)
                    ·
                      refine ⟨916104943531810902945043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221473258042414537260057 916104943531810902945043)
                      ·
                        rfl

theorem cell23_1784108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_1784108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784108 prefixEnd_1784108 := by exact prefixLift 1784108
  have htrace : WordTrace (prefixWord ++ tailWord_1784108) baseStart_1784108 baseEnd_1784108 := by
    simpa [prefixWord, tailWord_1784108, baseEnd_1784108] using wordTrace_append hprefix tailTrace_1784108
  have hstable : (prefixWord ++ tailWord_1784108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784108).length < 2 ^ (prefixWord ++ tailWord_1784108).sum := by decide
  have hdescent : baseEnd_1784108 < baseStart_1784108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784114 : List Nat := [3, 2, 1, 1, 5, 1, 2, 8]
def baseStart_1784114 : Nat := 118140960795 + 1784114 * 2 ^ 59
def prefixEnd_1784114 : Nat := 4983230072969 + 3 ^ 40 * 1784114 * 2
def baseEnd_1784114 : Nat := 33929926830212514054445

theorem tailTrace_1784114 : CollatzResearch.WordTrace tailWord_1784114 prefixEnd_1784114 33929926830212514054445 := by
  unfold tailWord_1784114
  simp only [CollatzResearch.WordTrace]
  refine ⟨16267995864616788814427849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43381322305644770171807597 16267995864616788814427849)
  ·
    refine ⟨12200996898462591610820887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16267995864616788814427849 12200996898462591610820887)
    ·
      refine ⟨18301495347693887416231331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12200996898462591610820887 18301495347693887416231331)
      ·
        refine ⟨27452243021540831124346997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18301495347693887416231331 27452243021540831124346997)
        ·
          refine ⟨2573647783269452917907531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27452243021540831124346997 2573647783269452917907531)
          ·
            refine ⟨3860471674904179376861297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573647783269452917907531 3860471674904179376861297)
            ·
              refine ⟨2895353756178134532645973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860471674904179376861297 2895353756178134532645973)
              ·
                refine ⟨33929926830212514054445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2895353756178134532645973 33929926830212514054445)
                ·
                  rfl

theorem cell23_1784114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_1784114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784114 prefixEnd_1784114 := by exact prefixLift 1784114
  have htrace : WordTrace (prefixWord ++ tailWord_1784114) baseStart_1784114 baseEnd_1784114 := by
    simpa [prefixWord, tailWord_1784114, baseEnd_1784114] using wordTrace_append hprefix tailTrace_1784114
  have hstable : (prefixWord ++ tailWord_1784114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784114).length < 2 ^ (prefixWord ++ tailWord_1784114).sum := by decide
  have hdescent : baseEnd_1784114 < baseStart_1784114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784117 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1784117 : Nat := 118140960795 + 1784117 * 2 ^ 59
def prefixEnd_1784117 : Nat := 4983230072969 + 3 ^ 40 * 1784117 * 2
def baseEnd_1784117 : Nat := 916109564857701367732501

theorem tailTrace_1784117 : CollatzResearch.WordTrace tailWord_1784117 prefixEnd_1784117 916109564857701367732501 := by
  unfold tailWord_1784117
  simp only [CollatzResearch.WordTrace]
  refine ⟨65072092877456286770070605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43381395251637524513380403 65072092877456286770070605)
  ·
    refine ⟨24402034829046107538776477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65072092877456286770070605 24402034829046107538776477)
    ·
      refine ⟨9150763060892290327041179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24402034829046107538776477 9150763060892290327041179)
      ·
        refine ⟨13726144591338435490561769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9150763060892290327041179 13726144591338435490561769)
        ·
          refine ⟨10294608443503826617921327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13726144591338435490561769 10294608443503826617921327)
          ·
            refine ⟨15441912665255739926881991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10294608443503826617921327 15441912665255739926881991)
            ·
              refine ⟨23162868997883609890322987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15441912665255739926881991 23162868997883609890322987)
              ·
                refine ⟨34744303496825414835484481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23162868997883609890322987 34744303496825414835484481)
                ·
                  refine ⟨26058227622619061126613361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34744303496825414835484481 26058227622619061126613361)
                  ·
                    refine ⟨19543670716964295844960021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26058227622619061126613361 19543670716964295844960021)
                    ·
                      refine ⟨916109564857701367732501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19543670716964295844960021 916109564857701367732501)
                      ·
                        rfl

theorem cell23_1784117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1784117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784117 prefixEnd_1784117 := by exact prefixLift 1784117
  have htrace : WordTrace (prefixWord ++ tailWord_1784117) baseStart_1784117 baseEnd_1784117 := by
    simpa [prefixWord, tailWord_1784117, baseEnd_1784117] using wordTrace_append hprefix tailTrace_1784117
  have hstable : (prefixWord ++ tailWord_1784117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784117).length < 2 ^ (prefixWord ++ tailWord_1784117).sum := by decide
  have hdescent : baseEnd_1784117 < baseStart_1784117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784124 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1784124 : Nat := 118140960795 + 1784124 * 2 ^ 59
def prefixEnd_1784124 : Nat := 4983230072969 + 3 ^ 40 * 1784124 * 2
def baseEnd_1784124 : Nat := 916113159222282840344969

theorem tailTrace_1784124 : CollatzResearch.WordTrace tailWord_1784124 prefixEnd_1784124 916113159222282840344969 := by
  unfold tailWord_1784124
  simp only [CollatzResearch.WordTrace]
  refine ⟨32536174094215463482787713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43381565458953951310383617 32536174094215463482787713)
  ·
    refine ⟨24402130570661597612090785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32536174094215463482787713 24402130570661597612090785)
    ·
      refine ⟨18301597927996198209068089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24402130570661597612090785 18301597927996198209068089)
      ·
        refine ⟨13726198445997148656801067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18301597927996198209068089 13726198445997148656801067)
        ·
          refine ⟨20589297668995722985201601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13726198445997148656801067 20589297668995722985201601)
          ·
            refine ⟨15441973251746792238901201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20589297668995722985201601 15441973251746792238901201)
            ·
              refine ⟨11581479938810094179175901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15441973251746792238901201 11581479938810094179175901)
              ·
                refine ⟨4343054977053785317190963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11581479938810094179175901 4343054977053785317190963)
                ·
                  refine ⟨6514582465580677975786445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4343054977053785317190963 6514582465580677975786445)
                  ·
                    refine ⟨2442968424592754240919917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6514582465580677975786445 2442968424592754240919917)
                    ·
                      refine ⟨916113159222282840344969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2442968424592754240919917 916113159222282840344969)
                      ·
                        rfl

theorem cell23_1784124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1784124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784124 prefixEnd_1784124 := by exact prefixLift 1784124
  have htrace : WordTrace (prefixWord ++ tailWord_1784124) baseStart_1784124 baseEnd_1784124 := by
    simpa [prefixWord, tailWord_1784124, baseEnd_1784124] using wordTrace_append hprefix tailTrace_1784124
  have hstable : (prefixWord ++ tailWord_1784124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784124).length < 2 ^ (prefixWord ++ tailWord_1784124).sum := by decide
  have hdescent : baseEnd_1784124 < baseStart_1784124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784187 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 9]
def baseStart_1784187 : Nat := 118140960795 + 1784187 * 2 ^ 59
def prefixEnd_1784187 : Nat := 4983230072969 + 3 ^ 40 * 1784187 * 2
def baseEnd_1784187 : Nat := 101793945389279565984131

theorem tailTrace_1784187 : CollatzResearch.WordTrace tailWord_1784187 prefixEnd_1784187 101793945389279565984131 := by
  unfold tailWord_1784187
  simp only [CollatzResearch.WordTrace]
  refine ⟨65074645987202688725118815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43383097324801792483412543 65074645987202688725118815)
  ·
    refine ⟨97611968980804033087678223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65074645987202688725118815 97611968980804033087678223)
    ·
      refine ⟨146417953471206049631517335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97611968980804033087678223 146417953471206049631517335)
      ·
        refine ⟨219626930206809074447276003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146417953471206049631517335 219626930206809074447276003)
        ·
          refine ⟨329440395310213611670914005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219626930206809074447276003 329440395310213611670914005)
          ·
            refine ⟨7721259265083131523537047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 329440395310213611670914005 7721259265083131523537047)
            ·
              refine ⟨11581888897624697285305571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7721259265083131523537047 11581888897624697285305571)
              ·
                refine ⟨17372833346437045927958357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11581888897624697285305571 17372833346437045927958357)
                ·
                  refine ⟨101793945389279565984131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17372833346437045927958357 101793945389279565984131)
                  ·
                    rfl

theorem cell23_1784187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 9].length) (baseStart_1784187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784187 prefixEnd_1784187 := by exact prefixLift 1784187
  have htrace : WordTrace (prefixWord ++ tailWord_1784187) baseStart_1784187 baseEnd_1784187 := by
    simpa [prefixWord, tailWord_1784187, baseEnd_1784187] using wordTrace_append hprefix tailTrace_1784187
  have hstable : (prefixWord ++ tailWord_1784187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784187).length < 2 ^ (prefixWord ++ tailWord_1784187).sum := by decide
  have hdescent : baseEnd_1784187 < baseStart_1784187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784197 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1784197 : Nat := 118140960795 + 1784197 * 2 ^ 59
def prefixEnd_1784197 : Nat := 4983230072969 + 3 ^ 40 * 1784197 * 2
def baseEnd_1784197 : Nat := 916150643310061054732133

theorem tailTrace_1784197 : CollatzResearch.WordTrace tailWord_1784197 prefixEnd_1784197 916150643310061054732133 := by
  unfold tailWord_1784197
  simp only [CollatzResearch.WordTrace]
  refine ⟨65075010717166460432982845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43383340478110973621988563 65075010717166460432982845)
  ·
    refine ⟨24403129018937422662368567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65075010717166460432982845 24403129018937422662368567)
    ·
      refine ⟨36604693528406133993552851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24403129018937422662368567 36604693528406133993552851)
      ·
        refine ⟨54907040292609200990329277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36604693528406133993552851 54907040292609200990329277)
        ·
          refine ⟨20590140109728450371373479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54907040292609200990329277 20590140109728450371373479)
          ·
            refine ⟨30885210164592675557060219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20590140109728450371373479 30885210164592675557060219)
            ·
              refine ⟨46327815246889013335590329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30885210164592675557060219 46327815246889013335590329)
              ·
                refine ⟨34745861435166760001692747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46327815246889013335590329 34745861435166760001692747)
                ·
                  refine ⟨52118792152750140002539121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34745861435166760001692747 52118792152750140002539121)
                  ·
                    refine ⟨39089094114562605001904341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52118792152750140002539121 39089094114562605001904341)
                    ·
                      refine ⟨916150643310061054732133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39089094114562605001904341 916150643310061054732133)
                      ·
                        rfl

theorem cell23_1784197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1784197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784197 prefixEnd_1784197 := by exact prefixLift 1784197
  have htrace : WordTrace (prefixWord ++ tailWord_1784197) baseStart_1784197 baseEnd_1784197 := by
    simpa [prefixWord, tailWord_1784197, baseEnd_1784197] using wordTrace_append hprefix tailTrace_1784197
  have hstable : (prefixWord ++ tailWord_1784197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784197).length < 2 ^ (prefixWord ++ tailWord_1784197).sum := by decide
  have hdescent : baseEnd_1784197 < baseStart_1784197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784221 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 7]
def baseStart_1784221 : Nat := 118140960795 + 1784221 * 2 ^ 59
def prefixEnd_1784221 : Nat := 4983230072969 + 3 ^ 40 * 1784221 * 2
def baseEnd_1784221 : Nat := 101795885205085440092447

theorem tailTrace_1784221 : CollatzResearch.WordTrace tailWord_1784221 prefixEnd_1784221 101795885205085440092447 := by
  unfold tailWord_1784221
  simp only [CollatzResearch.WordTrace]
  refine ⟨65075886069079512531856517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43383924046053008354571011 65075886069079512531856517)
  ·
    refine ⟨12201728637952408599723097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65075886069079512531856517 12201728637952408599723097)
    ·
      refine ⟨9151296478464306449792323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12201728637952408599723097 9151296478464306449792323)
      ·
        refine ⟨13726944717696459674688485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9151296478464306449792323 13726944717696459674688485)
        ·
          refine ⟨2573802134568086189004091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13726944717696459674688485 2573802134568086189004091)
          ·
            refine ⟨3860703201852129283506137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2573802134568086189004091 3860703201852129283506137)
            ·
              refine ⟨2895527401389096962629603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3860703201852129283506137 2895527401389096962629603)
              ·
                refine ⟨4343291102083645443944405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895527401389096962629603 4343291102083645443944405)
                ·
                  refine ⟨101795885205085440092447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4343291102083645443944405 101795885205085440092447)
                  ·
                    rfl

theorem cell23_1784221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_1784221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784221 prefixEnd_1784221 := by exact prefixLift 1784221
  have htrace : WordTrace (prefixWord ++ tailWord_1784221) baseStart_1784221 baseEnd_1784221 := by
    simpa [prefixWord, tailWord_1784221, baseEnd_1784221] using wordTrace_append hprefix tailTrace_1784221
  have hstable : (prefixWord ++ tailWord_1784221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784221).length < 2 ^ (prefixWord ++ tailWord_1784221).sum := by decide
  have hdescent : baseEnd_1784221 < baseStart_1784221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784231 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1784231 : Nat := 118140960795 + 1784231 * 2 ^ 59
def prefixEnd_1784231 : Nat := 4983230072969 + 3 ^ 40 * 1784231 * 2
def baseEnd_1784231 : Nat := 916168101652313921706977

theorem tailTrace_1784231 : CollatzResearch.WordTrace tailWord_1784231 prefixEnd_1784231 916168101652313921706977 := by
  unfold tailWord_1784231
  simp only [CollatzResearch.WordTrace]
  refine ⟨65076250799043284239720547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43384167199362189493147031 65076250799043284239720547)
  ·
    refine ⟨97614376198564926359580821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65076250799043284239720547 97614376198564926359580821)
    ·
      refine ⟨4575673884307730923105351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97614376198564926359580821 4575673884307730923105351)
      ·
        refine ⟨6863510826461596384658027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4575673884307730923105351 6863510826461596384658027)
        ·
          refine ⟨10295266239692394576987041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6863510826461596384658027 10295266239692394576987041)
          ·
            refine ⟨7721449679769295932740281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10295266239692394576987041 7721449679769295932740281)
            ·
              refine ⟨5791087259826971949555211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7721449679769295932740281 5791087259826971949555211)
              ·
                refine ⟨8686630889740457924332817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5791087259826971949555211 8686630889740457924332817)
                ·
                  refine ⟨6514973167305343443249613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8686630889740457924332817 6514973167305343443249613)
                  ·
                    refine ⟨2443114937739503791218605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6514973167305343443249613 2443114937739503791218605)
                    ·
                      refine ⟨916168101652313921706977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443114937739503791218605 916168101652313921706977)
                      ·
                        rfl

theorem cell23_1784231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1784231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784231 prefixEnd_1784231 := by exact prefixLift 1784231
  have htrace : WordTrace (prefixWord ++ tailWord_1784231) baseStart_1784231 baseEnd_1784231 := by
    simpa [prefixWord, tailWord_1784231, baseEnd_1784231] using wordTrace_append hprefix tailTrace_1784231
  have hstable : (prefixWord ++ tailWord_1784231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784231).length < 2 ^ (prefixWord ++ tailWord_1784231).sum := by decide
  have hdescent : baseEnd_1784231 < baseStart_1784231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784332 : List Nat := [2, 2, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_1784332 : Nat := 118140960795 + 1784332 * 2 ^ 59
def prefixEnd_1784332 : Nat := 4983230072969 + 3 ^ 40 * 1784332 * 2
def baseEnd_1784332 : Nat := 305406654399472675514671

theorem tailTrace_1784332 : CollatzResearch.WordTrace tailWord_1784332 prefixEnd_1784332 305406654399472675514671 := by
  unfold tailWord_1784332
  simp only [CollatzResearch.WordTrace]
  refine ⟨32539967285838689244573625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43386623047784918992764833 32539967285838689244573625)
  ·
    refine ⟨24404975464379016933430219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32539967285838689244573625 24404975464379016933430219)
    ·
      refine ⟨36607463196568525400145329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24404975464379016933430219 36607463196568525400145329)
      ·
        refine ⟨27455597397426394050108997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36607463196568525400145329 27455597397426394050108997)
        ·
          refine ⟨5147924512017448884395437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27455597397426394050108997 5147924512017448884395437)
          ·
            refine ⟨1930471692006543331648289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5147924512017448884395437 1930471692006543331648289)
            ·
              refine ⟨1447853769004907498736217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1930471692006543331648289 1447853769004907498736217)
              ·
                refine ⟨1085890326753680624052163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1447853769004907498736217 1085890326753680624052163)
                ·
                  refine ⟨1628835490130520936078245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085890326753680624052163 1628835490130520936078245)
                  ·
                    refine ⟨305406654399472675514671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1628835490130520936078245 305406654399472675514671)
                    ·
                      rfl

theorem cell23_1784332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_1784332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784332 prefixEnd_1784332 := by exact prefixLift 1784332
  have htrace : WordTrace (prefixWord ++ tailWord_1784332) baseStart_1784332 baseEnd_1784332 := by
    simpa [prefixWord, tailWord_1784332, baseEnd_1784332] using wordTrace_append hprefix tailTrace_1784332
  have hstable : (prefixWord ++ tailWord_1784332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784332).length < 2 ^ (prefixWord ++ tailWord_1784332).sum := by decide
  have hdescent : baseEnd_1784332 < baseStart_1784332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784359 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1784359 : Nat := 118140960795 + 1784359 * 2 ^ 59
def prefixEnd_1784359 : Nat := 4983230072969 + 3 ^ 40 * 1784359 * 2
def baseEnd_1784359 : Nat := 916233827176089420906389

theorem tailTrace_1784359 : CollatzResearch.WordTrace tailWord_1784359 prefixEnd_1784359 916233827176089420906389 := by
  unfold tailWord_1784359
  simp only [CollatzResearch.WordTrace]
  refine ⟨65080919342579562100380131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43387279561719708066920087 65080919342579562100380131)
  ·
    refine ⟨97621379013869343150570197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65080919342579562100380131 97621379013869343150570197)
    ·
      refine ⟨2288001070637562730091489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 97621379013869343150570197 2288001070637562730091489)
      ·
        refine ⟨1716000802978172047568617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288001070637562730091489 1716000802978172047568617)
        ·
          refine ⟨1287000602233629035676463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716000802978172047568617 1287000602233629035676463)
          ·
            refine ⟨1930500903350443553514695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287000602233629035676463 1930500903350443553514695)
            ·
              refine ⟨2895751355025665330272043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1930500903350443553514695 2895751355025665330272043)
              ·
                refine ⟨4343627032538497995408065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2895751355025665330272043 4343627032538497995408065)
                ·
                  refine ⟨3257720274403873496556049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4343627032538497995408065 3257720274403873496556049)
                  ·
                    refine ⟨2443290205802905122417037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3257720274403873496556049 2443290205802905122417037)
                    ·
                      refine ⟨916233827176089420906389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443290205802905122417037 916233827176089420906389)
                      ·
                        rfl

theorem cell23_1784359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1784359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784359 prefixEnd_1784359 := by exact prefixLift 1784359
  have htrace : WordTrace (prefixWord ++ tailWord_1784359) baseStart_1784359 baseEnd_1784359 := by
    simpa [prefixWord, tailWord_1784359, baseEnd_1784359] using wordTrace_append hprefix tailTrace_1784359
  have hstable : (prefixWord ++ tailWord_1784359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784359).length < 2 ^ (prefixWord ++ tailWord_1784359).sum := by decide
  have hdescent : baseEnd_1784359 < baseStart_1784359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784371 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 4, 4]
def baseStart_1784371 : Nat := 118140960795 + 1784371 * 2 ^ 59
def prefixEnd_1784371 : Nat := 4983230072969 + 3 ^ 40 * 1784371 * 2
def baseEnd_1784371 : Nat := 305413329647981124652111

theorem tailTrace_1784371 : CollatzResearch.WordTrace tailWord_1784371 prefixEnd_1784371 305413329647981124652111 := by
  unfold tailWord_1784371
  simp only [CollatzResearch.WordTrace]
  refine ⟨65081357018536088149816967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43387571345690725433211311 65081357018536088149816967)
  ·
    refine ⟨97622035527804132224725451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65081357018536088149816967 97622035527804132224725451)
    ·
      refine ⟨146433053291706198337088177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97622035527804132224725451 146433053291706198337088177)
      ·
        refine ⟨109824789968779648752816133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146433053291706198337088177 109824789968779648752816133)
        ·
          refine ⟨20592148119146184141153025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109824789968779648752816133 20592148119146184141153025)
          ·
            refine ⟨15444111089359638105864769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20592148119146184141153025 15444111089359638105864769)
            ·
              refine ⟨11583083317019728579398577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15444111089359638105864769 11583083317019728579398577)
              ·
                refine ⟨8687312487764796434548933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583083317019728579398577 8687312487764796434548933)
                ·
                  refine ⟨1628871091455899331477925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8687312487764796434548933 1628871091455899331477925)
                  ·
                    refine ⟨305413329647981124652111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1628871091455899331477925 305413329647981124652111)
                    ·
                      rfl

theorem cell23_1784371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 4].length) (baseStart_1784371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784371 prefixEnd_1784371 := by exact prefixLift 1784371
  have htrace : WordTrace (prefixWord ++ tailWord_1784371) baseStart_1784371 baseEnd_1784371 := by
    simpa [prefixWord, tailWord_1784371, baseEnd_1784371] using wordTrace_append hprefix tailTrace_1784371
  have hstable : (prefixWord ++ tailWord_1784371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784371).length < 2 ^ (prefixWord ++ tailWord_1784371).sum := by decide
  have hdescent : baseEnd_1784371 < baseStart_1784371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784378 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_1784378 : Nat := 118140960795 + 1784378 * 2 ^ 59
def prefixEnd_1784378 : Nat := 4983230072969 + 3 ^ 40 * 1784378 * 2
def baseEnd_1784378 : Nat := 916243583308524846568801

theorem tailTrace_1784378 : CollatzResearch.WordTrace tailWord_1784378 prefixEnd_1784378 916243583308524846568801 := by
  unfold tailWord_1784378
  simp only [CollatzResearch.WordTrace]
  refine ⟨16270403082377682086330447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43387741553007152230214525 16270403082377682086330447)
  ·
    refine ⟨24405604623566523129495671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16270403082377682086330447 24405604623566523129495671)
    ·
      refine ⟨36608406935349784694243507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24405604623566523129495671 36608406935349784694243507)
      ·
        refine ⟨54912610403024677041365261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36608406935349784694243507 54912610403024677041365261)
        ·
          refine ⟨20592228901134253890511973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54912610403024677041365261 20592228901134253890511973)
          ·
            refine ⟨3861042918962672604470995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20592228901134253890511973 3861042918962672604470995)
            ·
              refine ⟨5791564378444008906706493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861042918962672604470995 5791564378444008906706493)
              ·
                refine ⟨2171836641916503340014935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5791564378444008906706493 2171836641916503340014935)
                ·
                  refine ⟨3257754962874755010022403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2171836641916503340014935 3257754962874755010022403)
                  ·
                    refine ⟨4886632444312132515033605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3257754962874755010022403 4886632444312132515033605)
                    ·
                      refine ⟨916243583308524846568801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4886632444312132515033605 916243583308524846568801)
                      ·
                        rfl

theorem cell23_1784378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_1784378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784378 prefixEnd_1784378 := by exact prefixLift 1784378
  have htrace : WordTrace (prefixWord ++ tailWord_1784378) baseStart_1784378 baseEnd_1784378 := by
    simpa [prefixWord, tailWord_1784378, baseEnd_1784378] using wordTrace_append hprefix tailTrace_1784378
  have hstable : (prefixWord ++ tailWord_1784378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784378).length < 2 ^ (prefixWord ++ tailWord_1784378).sum := by decide
  have hdescent : baseEnd_1784378 < baseStart_1784378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784428 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_1784428 : Nat := 118140960795 + 1784428 * 2 ^ 59
def prefixEnd_1784428 : Nat := 4983230072969 + 3 ^ 40 * 1784428 * 2
def baseEnd_1784428 : Nat := 916269257341249650943571

theorem tailTrace_1784428 : CollatzResearch.WordTrace tailWord_1784428 prefixEnd_1784428 916269257341249650943571 := by
  unfold tailWord_1784428
  simp only [CollatzResearch.WordTrace]
  refine ⟨32541717989664793442320969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43388957319553057923094625 32541717989664793442320969)
  ·
    refine ⟨24406288492248595081740727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32541717989664793442320969 24406288492248595081740727)
    ·
      refine ⟨36609432738372892622611091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24406288492248595081740727 36609432738372892622611091)
      ·
        refine ⟨54914149107559338933916637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36609432738372892622611091 54914149107559338933916637)
        ·
          refine ⟨20592805915334752100218739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54914149107559338933916637 20592805915334752100218739)
          ·
            refine ⟨30889208873002128150328109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20592805915334752100218739 30889208873002128150328109)
            ·
              refine ⟨11583453327375798056373041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30889208873002128150328109 11583453327375798056373041)
              ·
                refine ⟨8687589995531848542279781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11583453327375798056373041 8687589995531848542279781)
                ·
                  refine ⟨1628923124162221601677459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8687589995531848542279781 1628923124162221601677459)
                  ·
                    refine ⟨2443384686243332402516189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1628923124162221601677459 2443384686243332402516189)
                    ·
                      refine ⟨916269257341249650943571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443384686243332402516189 916269257341249650943571)
                      ·
                        rfl

theorem cell23_1784428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_1784428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784428 prefixEnd_1784428 := by exact prefixLift 1784428
  have htrace : WordTrace (prefixWord ++ tailWord_1784428) baseStart_1784428 baseEnd_1784428 := by
    simpa [prefixWord, tailWord_1784428, baseEnd_1784428] using wordTrace_append hprefix tailTrace_1784428
  have hstable : (prefixWord ++ tailWord_1784428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784428).length < 2 ^ (prefixWord ++ tailWord_1784428).sum := by decide
  have hdescent : baseEnd_1784428 < baseStart_1784428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784429 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_1784429 : Nat := 118140960795 + 1784429 * 2 ^ 59
def prefixEnd_1784429 : Nat := 4983230072969 + 3 ^ 40 * 1784429 * 2
def baseEnd_1784429 : Nat := 916269770821904147031067

theorem tailTrace_1784429 : CollatzResearch.WordTrace tailWord_1784429 prefixEnd_1784429 916269770821904147031067 := by
  unfold tailWord_1784429
  simp only [CollatzResearch.WordTrace]
  refine ⟨65083472452325964055428341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43388981634883976036952227 65083472452325964055428341)
  ·
    refine ⟨6101575542405559130196407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65083472452325964055428341 6101575542405559130196407)
    ·
      refine ⟨9152363313608338695294611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6101575542405559130196407 9152363313608338695294611)
      ·
        refine ⟨13728544970412508042941917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9152363313608338695294611 13728544970412508042941917)
        ·
          refine ⟨5148204363904690516103219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13728544970412508042941917 5148204363904690516103219)
          ·
            refine ⟨7722306545857035774154829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148204363904690516103219 7722306545857035774154829)
            ·
              refine ⟨2895864954696388415308061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7722306545857035774154829 2895864954696388415308061)
              ·
                refine ⟨1085949358011145655740523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2895864954696388415308061 1085949358011145655740523)
                ·
                  refine ⟨1628924037016718483610785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1085949358011145655740523 1628924037016718483610785)
                  ·
                    refine ⟨1221693027762538862708089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1628924037016718483610785 1221693027762538862708089)
                    ·
                      refine ⟨916269770821904147031067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221693027762538862708089 916269770821904147031067)
                      ·
                        rfl

theorem cell23_1784429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_1784429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784429 prefixEnd_1784429 := by exact prefixLift 1784429
  have htrace : WordTrace (prefixWord ++ tailWord_1784429) baseStart_1784429 baseEnd_1784429 := by
    simpa [prefixWord, tailWord_1784429, baseEnd_1784429] using wordTrace_append hprefix tailTrace_1784429
  have hstable : (prefixWord ++ tailWord_1784429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784429).length < 2 ^ (prefixWord ++ tailWord_1784429).sum := by decide
  have hdescent : baseEnd_1784429 < baseStart_1784429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784471 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1784471 : Nat := 118140960795 + 1784471 * 2 ^ 59
def prefixEnd_1784471 : Nat := 4983230072969 + 3 ^ 40 * 1784471 * 2
def baseEnd_1784471 : Nat := 916291337009392982705873

theorem tailTrace_1784471 : CollatzResearch.WordTrace tailWord_1784471 prefixEnd_1784471 916291337009392982705873 := by
  unfold tailWord_1784471
  simp only [CollatzResearch.WordTrace]
  refine ⟨65085004318173805228457267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43390002878782536818971511 65085004318173805228457267)
  ·
    refine ⟨97627506477260707842685901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65085004318173805228457267 97627506477260707842685901)
    ·
      refine ⟨36610314928972765441007213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97627506477260707842685901 36610314928972765441007213)
      ·
        refine ⟨13728868098364787040377705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36610314928972765441007213 13728868098364787040377705)
        ·
          refine ⟨10296651073773590280283279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13728868098364787040377705 10296651073773590280283279)
          ·
            refine ⟨15444976610660385420424919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10296651073773590280283279 15444976610660385420424919)
            ·
              refine ⟨23167464915990578130637379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15444976610660385420424919 23167464915990578130637379)
              ·
                refine ⟨34751197373985867195956069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23167464915990578130637379 34751197373985867195956069)
                ·
                  refine ⟨6515849507622350099241763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34751197373985867195956069 6515849507622350099241763)
                  ·
                    refine ⟨9773774261433525148862645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6515849507622350099241763 9773774261433525148862645)
                    ·
                      refine ⟨916291337009392982705873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9773774261433525148862645 916291337009392982705873)
                      ·
                        rfl

theorem cell23_1784471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1784471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784471 prefixEnd_1784471 := by exact prefixLift 1784471
  have htrace : WordTrace (prefixWord ++ tailWord_1784471) baseStart_1784471 baseEnd_1784471 := by
    simpa [prefixWord, tailWord_1784471, baseEnd_1784471] using wordTrace_append hprefix tailTrace_1784471
  have hstable : (prefixWord ++ tailWord_1784471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784471).length < 2 ^ (prefixWord ++ tailWord_1784471).sum := by decide
  have hdescent : baseEnd_1784471 < baseStart_1784471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784601 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1784601 : Nat := 118140960795 + 1784601 * 2 ^ 59
def prefixEnd_1784601 : Nat := 4983230072969 + 3 ^ 40 * 1784601 * 2
def baseEnd_1784601 : Nat := 916358089494477474080275

theorem tailTrace_1784601 : CollatzResearch.WordTrace tailWord_1784601 prefixEnd_1784601 916358089494477474080275 := by
  unfold tailWord_1784601
  simp only [CollatzResearch.WordTrace]
  refine ⟨65089745807702837430689657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43393163871801891620459771 65089745807702837430689657)
  ·
    refine ⟨48817309355777128073017243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65089745807702837430689657 48817309355777128073017243)
    ·
      refine ⟨73225964033665692109525865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48817309355777128073017243 73225964033665692109525865)
      ·
        refine ⟨54919473025249269082144399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73225964033665692109525865 54919473025249269082144399)
        ·
          refine ⟨82379209537873903623216599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54919473025249269082144399 82379209537873903623216599)
          ·
            refine ⟨123568814306810855434824899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82379209537873903623216599 123568814306810855434824899)
            ·
              refine ⟨185353221460216283152237349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123568814306810855434824899 185353221460216283152237349)
              ·
                refine ⟨34753729023790553091044503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185353221460216283152237349 34753729023790553091044503)
                ·
                  refine ⟨52130593535685829636566755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34753729023790553091044503 52130593535685829636566755)
                  ·
                    refine ⟨78195890303528744454850133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52130593535685829636566755 78195890303528744454850133)
                    ·
                      refine ⟨916358089494477474080275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78195890303528744454850133 916358089494477474080275)
                      ·
                        rfl

theorem cell23_1784601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1784601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784601 prefixEnd_1784601 := by exact prefixLift 1784601
  have htrace : WordTrace (prefixWord ++ tailWord_1784601) baseStart_1784601 baseEnd_1784601 := by
    simpa [prefixWord, tailWord_1784601, baseEnd_1784601] using wordTrace_append hprefix tailTrace_1784601
  have hstable : (prefixWord ++ tailWord_1784601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784601).length < 2 ^ (prefixWord ++ tailWord_1784601).sum := by decide
  have hdescent : baseEnd_1784601 < baseStart_1784601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784612 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1784612 : Nat := 118140960795 + 1784612 * 2 ^ 59
def prefixEnd_1784612 : Nat := 4983230072969 + 3 ^ 40 * 1784612 * 2
def baseEnd_1784612 : Nat := 916363737781676931042725

theorem tailTrace_1784612 : CollatzResearch.WordTrace tailWord_1784612 prefixEnd_1784612 916363737781676931042725 := by
  unfold tailWord_1784612
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545073505331493154670045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43393431340441990872893393 32545073505331493154670045)
  ·
    refine ⟨12204402564499309933001267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32545073505331493154670045 12204402564499309933001267)
    ·
      refine ⟨18306603846748964899501901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12204402564499309933001267 18306603846748964899501901)
      ·
        refine ⟨6864976442530861837313213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18306603846748964899501901 6864976442530861837313213)
        ·
          refine ⟨2574366165949073188992455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6864976442530861837313213 2574366165949073188992455)
          ·
            refine ⟨3861549248923609783488683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574366165949073188992455 3861549248923609783488683)
            ·
              refine ⟨5792323873385414675233025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861549248923609783488683 5792323873385414675233025)
              ·
                refine ⟨4344242905039061006424769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792323873385414675233025 4344242905039061006424769)
                ·
                  refine ⟨3258182178779295754818577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344242905039061006424769 3258182178779295754818577)
                  ·
                    refine ⟨2443636634084471816113933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258182178779295754818577 2443636634084471816113933)
                    ·
                      refine ⟨916363737781676931042725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443636634084471816113933 916363737781676931042725)
                      ·
                        rfl

theorem cell23_1784612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1784612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784612 prefixEnd_1784612 := by exact prefixLift 1784612
  have htrace : WordTrace (prefixWord ++ tailWord_1784612) baseStart_1784612 baseEnd_1784612 := by
    simpa [prefixWord, tailWord_1784612, baseEnd_1784612] using wordTrace_append hprefix tailTrace_1784612
  have hstable : (prefixWord ++ tailWord_1784612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784612).length < 2 ^ (prefixWord ++ tailWord_1784612).sum := by decide
  have hdescent : baseEnd_1784612 < baseStart_1784612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784646 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1784646 : Nat := 118140960795 + 1784646 * 2 ^ 59
def prefixEnd_1784646 : Nat := 4983230072969 + 3 ^ 40 * 1784646 * 2
def baseEnd_1784646 : Nat := 916381196123929798017569

theorem tailTrace_1784646 : CollatzResearch.WordTrace tailWord_1784646 prefixEnd_1784646 916381196123929798017569 := by
  unfold tailWord_1784646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034105846641869066127431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43394258061693206744051861 2034105846641869066127431)
  ·
    refine ⟨3051158769962803599191147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034105846641869066127431 3051158769962803599191147)
    ·
      refine ⟨4576738154944205398786721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3051158769962803599191147 4576738154944205398786721)
      ·
        refine ⟨3432553616208154049090041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4576738154944205398786721 3432553616208154049090041)
        ·
          refine ⟨2574415212156115536817531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3432553616208154049090041 2574415212156115536817531)
          ·
            refine ⟨3861622818234173305226297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574415212156115536817531 3861622818234173305226297)
            ·
              refine ⟨2896217113675629978919723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3861622818234173305226297 2896217113675629978919723)
              ·
                refine ⟨4344325670513444968379585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896217113675629978919723 4344325670513444968379585)
                ·
                  refine ⟨3258244252885083726284689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344325670513444968379585 3258244252885083726284689)
                  ·
                    refine ⟨2443683189663812794713517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258244252885083726284689 2443683189663812794713517)
                    ·
                      refine ⟨916381196123929798017569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443683189663812794713517 916381196123929798017569)
                      ·
                        rfl

theorem cell23_1784646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1784646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784646 prefixEnd_1784646 := by exact prefixLift 1784646
  have htrace : WordTrace (prefixWord ++ tailWord_1784646) baseStart_1784646 baseEnd_1784646 := by
    simpa [prefixWord, tailWord_1784646, baseEnd_1784646] using wordTrace_append hprefix tailTrace_1784646
  have hstable : (prefixWord ++ tailWord_1784646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784646).length < 2 ^ (prefixWord ++ tailWord_1784646).sum := by decide
  have hdescent : baseEnd_1784646 < baseStart_1784646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784652 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_1784652 : Nat := 118140960795 + 1784652 * 2 ^ 59
def prefixEnd_1784652 : Nat := 4983230072969 + 3 ^ 40 * 1784652 * 2
def baseEnd_1784652 : Nat := 916384277007856774542541

theorem tailTrace_1784652 : CollatzResearch.WordTrace tailWord_1784652 prefixEnd_1784652 916384277007856774542541 := by
  unfold tailWord_1784652
  simp only [CollatzResearch.WordTrace]
  refine ⟨32545802965259036570398105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43394403953678715427197473 32545802965259036570398105)
  ·
    refine ⟨24409352223944277427798579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32545802965259036570398105 24409352223944277427798579)
    ·
      refine ⟨36614028335916416141697869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24409352223944277427798579 36614028335916416141697869)
      ·
        refine ⟨13730260625968656053136701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36614028335916416141697869 13730260625968656053136701)
        ·
          refine ⟨5148847734738246019926263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13730260625968656053136701 5148847734738246019926263)
          ·
            refine ⟨7723271602107369029889395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148847734738246019926263 7723271602107369029889395)
            ·
              refine ⟨11584907403161053544834093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7723271602107369029889395 11584907403161053544834093)
              ·
                refine ⟨4344340276185395079312785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11584907403161053544834093 4344340276185395079312785)
                ·
                  refine ⟨3258255207139046309484589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344340276185395079312785 3258255207139046309484589)
                  ·
                    refine ⟨1221845702677142366056721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3258255207139046309484589 1221845702677142366056721)
                    ·
                      refine ⟨916384277007856774542541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1221845702677142366056721 916384277007856774542541)
                      ·
                        rfl

theorem cell23_1784652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_1784652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784652 prefixEnd_1784652 := by exact prefixLift 1784652
  have htrace : WordTrace (prefixWord ++ tailWord_1784652) baseStart_1784652 baseEnd_1784652 := by
    simpa [prefixWord, tailWord_1784652, baseEnd_1784652] using wordTrace_append hprefix tailTrace_1784652
  have hstable : (prefixWord ++ tailWord_1784652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784652).length < 2 ^ (prefixWord ++ tailWord_1784652).sum := by decide
  have hdescent : baseEnd_1784652 < baseStart_1784652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784676 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_1784676 : Nat := 118140960795 + 1784676 * 2 ^ 59
def prefixEnd_1784676 : Nat := 4983230072969 + 3 ^ 40 * 1784676 * 2
def baseEnd_1784676 : Nat := 916396600543564680642431

theorem tailTrace_1784676 : CollatzResearch.WordTrace tailWord_1784676 prefixEnd_1784676 916396600543564680642431 := by
  unfold tailWord_1784676
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546240641215562619834941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43394987521620750159779921 32546240641215562619834941)
  ·
    refine ⟨12204840240455835982438103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32546240641215562619834941 12204840240455835982438103)
    ·
      refine ⟨18307260360683753973657155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12204840240455835982438103 18307260360683753973657155)
      ·
        refine ⟨27460890541025630960485733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18307260360683753973657155 27460890541025630960485733)
        ·
          refine ⟨5148916976442305805091075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27460890541025630960485733 5148916976442305805091075)
          ·
            refine ⟨7723375464663458707636613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5148916976442305805091075 7723375464663458707636613)
            ·
              refine ⟨1448132899624398507681865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7723375464663458707636613 1448132899624398507681865)
              ·
                refine ⟨1086099674718298880761399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448132899624398507681865 1086099674718298880761399)
                ·
                  refine ⟨1629149512077448321142099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086099674718298880761399 1629149512077448321142099)
                  ·
                    refine ⟨2443724268116172481713149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629149512077448321142099 2443724268116172481713149)
                    ·
                      refine ⟨916396600543564680642431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443724268116172481713149 916396600543564680642431)
                      ·
                        rfl

theorem cell23_1784676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_1784676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784676 prefixEnd_1784676 := by exact prefixLift 1784676
  have htrace : WordTrace (prefixWord ++ tailWord_1784676) baseStart_1784676 baseEnd_1784676 := by
    simpa [prefixWord, tailWord_1784676, baseEnd_1784676] using wordTrace_append hprefix tailTrace_1784676
  have hstable : (prefixWord ++ tailWord_1784676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784676).length < 2 ^ (prefixWord ++ tailWord_1784676).sum := by decide
  have hdescent : baseEnd_1784676 < baseStart_1784676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784688 : List Nat := [2, 1, 1, 1, 4, 1, 5, 8]
def baseStart_1784688 : Nat := 118140960795 + 1784688 * 2 ^ 59
def prefixEnd_1784688 : Nat := 4983230072969 + 3 ^ 40 * 1784688 * 2
def baseEnd_1784688 : Nat := 33940843048571060507125

theorem tailTrace_1784688 : CollatzResearch.WordTrace tailWord_1784688 prefixEnd_1784688 33940843048571060507125 := by
  unfold tailWord_1784688
  simp only [CollatzResearch.WordTrace]
  refine ⟨32546459479193825644553359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43395279305591767526071145 32546459479193825644553359)
  ·
    refine ⟨48819689218790738466830039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32546459479193825644553359 48819689218790738466830039)
    ·
      refine ⟨73229533828186107700245059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48819689218790738466830039 73229533828186107700245059)
      ·
        refine ⟨109844300742279161550367589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73229533828186107700245059 109844300742279161550367589)
        ·
          refine ⟨20595806389177342790693923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 109844300742279161550367589 20595806389177342790693923)
          ·
            refine ⟨30893709583766014186040885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20595806389177342790693923 30893709583766014186040885)
            ·
              refine ⟨2896285273478063829941333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30893709583766014186040885 2896285273478063829941333)
              ·
                refine ⟨33940843048571060507125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2896285273478063829941333 33940843048571060507125)
                ·
                  rfl

theorem cell23_1784688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 8].length) (baseStart_1784688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784688 prefixEnd_1784688 := by exact prefixLift 1784688
  have htrace : WordTrace (prefixWord ++ tailWord_1784688) baseStart_1784688 baseEnd_1784688 := by
    simpa [prefixWord, tailWord_1784688, baseEnd_1784688] using wordTrace_append hprefix tailTrace_1784688
  have hstable : (prefixWord ++ tailWord_1784688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784688).length < 2 ^ (prefixWord ++ tailWord_1784688).sum := by decide
  have hdescent : baseEnd_1784688 < baseStart_1784688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784715 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3]
def baseStart_1784715 : Nat := 118140960795 + 1784715 * 2 ^ 59
def prefixEnd_1784715 : Nat := 4983230072969 + 3 ^ 40 * 1784715 * 2
def baseEnd_1784715 : Nat := 916416626289090028054751

theorem tailTrace_1784715 : CollatzResearch.WordTrace tailWord_1784715 prefixEnd_1784715 916416626289090028054751 := by
  unfold tailWord_1784715
  simp only [CollatzResearch.WordTrace]
  refine ⟨65093903729289834900339599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43395935819526556600226399 65093903729289834900339599)
  ·
    refine ⟨97640855593934752350509399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65093903729289834900339599 97640855593934752350509399)
    ·
      refine ⟨146461283390902128525764099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97640855593934752350509399 146461283390902128525764099)
      ·
        refine ⟨219691925086353192788646149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146461283390902128525764099 219691925086353192788646149)
        ·
          refine ⟨41192235953691223647871153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 219691925086353192788646149 41192235953691223647871153)
          ·
            refine ⟨30894176965268417735903365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41192235953691223647871153 30894176965268417735903365)
            ·
              refine ⟨5792658180987828325481881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30894176965268417735903365 5792658180987828325481881)
              ·
                refine ⟨4344493635740871244111411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5792658180987828325481881 4344493635740871244111411)
                ·
                  refine ⟨6516740453611306866167117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4344493635740871244111411 6516740453611306866167117)
                  ·
                    refine ⟨2443777670104240074812669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6516740453611306866167117 2443777670104240074812669)
                    ·
                      refine ⟨916416626289090028054751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2443777670104240074812669 916416626289090028054751)
                      ·
                        rfl

theorem cell23_1784715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3].length) (baseStart_1784715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784715 prefixEnd_1784715 := by exact prefixLift 1784715
  have htrace : WordTrace (prefixWord ++ tailWord_1784715) baseStart_1784715 baseEnd_1784715 := by
    simpa [prefixWord, tailWord_1784715, baseEnd_1784715] using wordTrace_append hprefix tailTrace_1784715
  have hstable : (prefixWord ++ tailWord_1784715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784715).length < 2 ^ (prefixWord ++ tailWord_1784715).sum := by decide
  have hdescent : baseEnd_1784715 < baseStart_1784715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784726 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1784726 : Nat := 118140960795 + 1784726 * 2 ^ 59
def prefixEnd_1784726 : Nat := 4983230072969 + 3 ^ 40 * 1784726 * 2
def baseEnd_1784726 : Nat := 305474091525429828339067

theorem tailTrace_1784726 : CollatzResearch.WordTrace tailWord_1784726 prefixEnd_1784726 305474091525429828339067 := by
  unfold tailWord_1784726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4068394058265623986186877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43396203288166655852660021 4068394058265623986186877)
  ·
    refine ⟨1525647771849608994820079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4068394058265623986186877 1525647771849608994820079)
    ·
      refine ⟨2288471657774413492230119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1525647771849608994820079 2288471657774413492230119)
      ·
        refine ⟨3432707486661620238345179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288471657774413492230119 3432707486661620238345179)
        ·
          refine ⟨5149061229992430357517769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3432707486661620238345179 5149061229992430357517769)
          ·
            refine ⟨3861795922494322768138327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149061229992430357517769 3861795922494322768138327)
            ·
              refine ⟨5792693883741484152207491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3861795922494322768138327 5792693883741484152207491)
              ·
                refine ⟨8689040825612226228311237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5792693883741484152207491 8689040825612226228311237)
                ·
                  refine ⟨1629195154802292417808357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8689040825612226228311237 1629195154802292417808357)
                  ·
                    refine ⟨305474091525429828339067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1629195154802292417808357 305474091525429828339067)
                    ·
                      rfl

theorem cell23_1784726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1784726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784726 prefixEnd_1784726 := by exact prefixLift 1784726
  have htrace : WordTrace (prefixWord ++ tailWord_1784726) baseStart_1784726 baseEnd_1784726 := by
    simpa [prefixWord, tailWord_1784726, baseEnd_1784726] using wordTrace_append hprefix tailTrace_1784726
  have hstable : (prefixWord ++ tailWord_1784726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784726).length < 2 ^ (prefixWord ++ tailWord_1784726).sum := by decide
  have hdescent : baseEnd_1784726 < baseStart_1784726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784842 : List Nat := [3, 1, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1784842 : Nat := 118140960795 + 1784842 * 2 ^ 59
def prefixEnd_1784842 : Nat := 4983230072969 + 3 ^ 40 * 1784842 * 2
def baseEnd_1784842 : Nat := 305493946110737010388889

theorem tailTrace_1784842 : CollatzResearch.WordTrace tailWord_1784842 prefixEnd_1784842 305493946110737010388889 := by
  unfold tailWord_1784842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274633949957433897553195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43399023866553157060141853 16274633949957433897553195)
  ·
    refine ⟨24411950924936150846329793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16274633949957433897553195 24411950924936150846329793)
    ·
      refine ⟨18308963193702113134747345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24411950924936150846329793 18308963193702113134747345)
      ·
        refine ⟨13731722395276584851060509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18308963193702113134747345 13731722395276584851060509)
        ·
          refine ⟨5149395898228719319147691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13731722395276584851060509 5149395898228719319147691)
          ·
            refine ⟨7724093847343078978721537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149395898228719319147691 7724093847343078978721537)
            ·
              refine ⟨5793070385507309234041153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7724093847343078978721537 5793070385507309234041153)
              ·
                refine ⟨4344802789130481925530865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793070385507309234041153 4344802789130481925530865)
                ·
                  refine ⟨3258602091847861444148149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4344802789130481925530865 3258602091847861444148149)
                  ·
                    refine ⟨305493946110737010388889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3258602091847861444148149 305493946110737010388889)
                    ·
                      rfl

theorem cell23_1784842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1784842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784842 prefixEnd_1784842 := by exact prefixLift 1784842
  have htrace : WordTrace (prefixWord ++ tailWord_1784842) baseStart_1784842 baseEnd_1784842 := by
    simpa [prefixWord, tailWord_1784842, baseEnd_1784842] using wordTrace_append hprefix tailTrace_1784842
  have hstable : (prefixWord ++ tailWord_1784842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784842).length < 2 ^ (prefixWord ++ tailWord_1784842).sum := by decide
  have hdescent : baseEnd_1784842 < baseStart_1784842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784846 : List Nat := [4, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_1784846 : Nat := 118140960795 + 1784846 * 2 ^ 59
def prefixEnd_1784846 : Nat := 4983230072969 + 3 ^ 40 * 1784846 * 2
def baseEnd_1784846 : Nat := 101831543583869890612961

theorem tailTrace_1784846 : CollatzResearch.WordTrace tailWord_1784846 prefixEnd_1784846 101831543583869890612961 := by
  unfold tailWord_1784846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8137335211476905534169799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43399121127876829515572261 8137335211476905534169799)
  ·
    refine ⟨12206002817215358301254699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8137335211476905534169799 12206002817215358301254699)
    ·
      refine ⟨18309004225823037451882049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12206002817215358301254699 18309004225823037451882049)
      ·
        refine ⟨13731753169367278088911537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18309004225823037451882049 13731753169367278088911537)
        ·
          refine ⟨10298814877025458566683653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13731753169367278088911537 10298814877025458566683653)
          ·
            refine ⟨1931027789442273481253185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10298814877025458566683653 1931027789442273481253185)
            ·
              refine ⟨1448270842081705110939889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931027789442273481253185 1448270842081705110939889)
              ·
                refine ⟨1086203131561278833204917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448270842081705110939889 1086203131561278833204917)
                ·
                  refine ⟨101831543583869890612961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1086203131561278833204917 101831543583869890612961)
                  ·
                    rfl

theorem cell23_1784846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_1784846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784846 prefixEnd_1784846 := by exact prefixLift 1784846
  have htrace : WordTrace (prefixWord ++ tailWord_1784846) baseStart_1784846 baseEnd_1784846 := by
    simpa [prefixWord, tailWord_1784846, baseEnd_1784846] using wordTrace_append hprefix tailTrace_1784846
  have hstable : (prefixWord ++ tailWord_1784846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784846).length < 2 ^ (prefixWord ++ tailWord_1784846).sum := by decide
  have hdescent : baseEnd_1784846 < baseStart_1784846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784882 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1784882 : Nat := 118140960795 + 1784882 * 2 ^ 59
def prefixEnd_1784882 : Nat := 4983230072969 + 3 ^ 40 * 1784882 * 2
def baseEnd_1784882 : Nat := 916502377558390874666483

theorem tailTrace_1784882 : CollatzResearch.WordTrace tailWord_1784882 prefixEnd_1784882 916502377558390874666483 := by
  unfold tailWord_1784882
  simp only [CollatzResearch.WordTrace]
  refine ⟨16274998679921205605417225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43399996479789881614445933 16274998679921205605417225)
  ·
    refine ⟨12206249009940904204062919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16274998679921205605417225 12206249009940904204062919)
    ·
      refine ⟨18309373514911356306094379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12206249009940904204062919 18309373514911356306094379)
      ·
        refine ⟨27464060272367034459141569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18309373514911356306094379 27464060272367034459141569)
        ·
          refine ⟨20598045204275275844356177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27464060272367034459141569 20598045204275275844356177)
          ·
            refine ⟨15448533903206456883267133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20598045204275275844356177 15448533903206456883267133)
            ·
              refine ⟨5793200213702421331225175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15448533903206456883267133 5793200213702421331225175)
              ·
                refine ⟨8689800320553631996837763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793200213702421331225175 8689800320553631996837763)
                ·
                  refine ⟨13034700480830447995256645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8689800320553631996837763 13034700480830447995256645)
                  ·
                    refine ⟨2444006340155708999110621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13034700480830447995256645 2444006340155708999110621)
                    ·
                      refine ⟨916502377558390874666483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444006340155708999110621 916502377558390874666483)
                      ·
                        rfl

theorem cell23_1784882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1784882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784882 prefixEnd_1784882 := by exact prefixLift 1784882
  have htrace : WordTrace (prefixWord ++ tailWord_1784882) baseStart_1784882 baseEnd_1784882 := by
    simpa [prefixWord, tailWord_1784882, baseEnd_1784882] using wordTrace_append hprefix tailTrace_1784882
  have hstable : (prefixWord ++ tailWord_1784882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784882).length < 2 ^ (prefixWord ++ tailWord_1784882).sum := by decide
  have hdescent : baseEnd_1784882 < baseStart_1784882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784885 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 8]
def baseStart_1784885 : Nat := 118140960795 + 1784885 * 2 ^ 59
def prefixEnd_1784885 : Nat := 4983230072969 + 3 ^ 40 * 1784885 * 2
def baseEnd_1784885 : Nat := 101833768666706040325441

theorem tailTrace_1784885 : CollatzResearch.WordTrace tailWord_1784885 prefixEnd_1784885 101833768666706040325441 := by
  unfold tailWord_1784885
  simp only [CollatzResearch.WordTrace]
  refine ⟨65100104138673953934028109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43400069425782635956018739 65100104138673953934028109)
  ·
    refine ⟨24412539052002732725260541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65100104138673953934028109 24412539052002732725260541)
    ·
      refine ⟨9154702144501024771972703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24412539052002732725260541 9154702144501024771972703)
      ·
        refine ⟨13732053216751537157959055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9154702144501024771972703 13732053216751537157959055)
        ·
          refine ⟨20598079825127305736938583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13732053216751537157959055 20598079825127305736938583)
          ·
            refine ⟨30897119737690958605407875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20598079825127305736938583 30897119737690958605407875)
            ·
              refine ⟨46345679606536437908111813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30897119737690958605407875 46345679606536437908111813)
              ·
                refine ⟨8689814926225582107770965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46345679606536437908111813 8689814926225582107770965)
                ·
                  refine ⟨101833768666706040325441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8689814926225582107770965 101833768666706040325441)
                  ·
                    rfl

theorem cell23_1784885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_1784885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784885 prefixEnd_1784885 := by exact prefixLift 1784885
  have htrace : WordTrace (prefixWord ++ tailWord_1784885) baseStart_1784885 baseEnd_1784885 := by
    simpa [prefixWord, tailWord_1784885, baseEnd_1784885] using wordTrace_append hprefix tailTrace_1784885
  have hstable : (prefixWord ++ tailWord_1784885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784885).length < 2 ^ (prefixWord ++ tailWord_1784885).sum := by decide
  have hdescent : baseEnd_1784885 < baseStart_1784885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784929 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_1784929 : Nat := 118140960795 + 1784929 * 2 ^ 59
def prefixEnd_1784929 : Nat := 4983230072969 + 3 ^ 40 * 1784929 * 2
def baseEnd_1784929 : Nat := 916526511149152190778767

theorem tailTrace_1784929 : CollatzResearch.WordTrace tailWord_1784929 prefixEnd_1784929 916526511149152190778767 := by
  unfold tailWord_1784929
  simp only [CollatzResearch.WordTrace]
  refine ⟨65101708950514549448629841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43401139300343032965753227 65101708950514549448629841)
  ·
    refine ⟨48826281712885912086472381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65101708950514549448629841 48826281712885912086472381)
    ·
      refine ⟨18309855642332217032427143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48826281712885912086472381 18309855642332217032427143)
      ·
        refine ⟨27464783463498325548640715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18309855642332217032427143 27464783463498325548640715)
        ·
          refine ⟨41197175195247488322961073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27464783463498325548640715 41197175195247488322961073)
          ·
            refine ⟨30897881396435616242220805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41197175195247488322961073 30897881396435616242220805)
            ·
              refine ⟨5793352761831678045416401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30897881396435616242220805 5793352761831678045416401)
              ·
                refine ⟨4345014571373758534062301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793352761831678045416401 4345014571373758534062301)
                ·
                  refine ⟨1629380464265159450273363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4345014571373758534062301 1629380464265159450273363)
                  ·
                    refine ⟨2444070696397739175410045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629380464265159450273363 2444070696397739175410045)
                    ·
                      refine ⟨916526511149152190778767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444070696397739175410045 916526511149152190778767)
                      ·
                        rfl

theorem cell23_1784929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_1784929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784929 prefixEnd_1784929 := by exact prefixLift 1784929
  have htrace : WordTrace (prefixWord ++ tailWord_1784929) baseStart_1784929 baseEnd_1784929 := by
    simpa [prefixWord, tailWord_1784929, baseEnd_1784929] using wordTrace_append hprefix tailTrace_1784929
  have hstable : (prefixWord ++ tailWord_1784929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784929).length < 2 ^ (prefixWord ++ tailWord_1784929).sum := by decide
  have hdescent : baseEnd_1784929 < baseStart_1784929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784963 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 1, 1, 3]
def baseStart_1784963 : Nat := 118140960795 + 1784963 * 2 ^ 59
def prefixEnd_1784963 : Nat := 4983230072969 + 3 ^ 40 * 1784963 * 2
def baseEnd_1784963 : Nat := 916543969491405057753611

theorem tailTrace_1784963 : CollatzResearch.WordTrace tailWord_1784963 prefixEnd_1784963 916543969491405057753611 := by
  unfold tailWord_1784963
  simp only [CollatzResearch.WordTrace]
  refine ⟨65102949032391373255367543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43401966021594248836911695 65102949032391373255367543)
  ·
    refine ⟨97654423548587059883051315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65102949032391373255367543 97654423548587059883051315)
    ·
      refine ⟨146481635322880589824576973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97654423548587059883051315 146481635322880589824576973)
      ·
        refine ⟨54930613246080221184216365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146481635322880589824576973 54930613246080221184216365)
        ·
          refine ⟨20598979967280082944081137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54930613246080221184216365 20598979967280082944081137)
          ·
            refine ⟨15449234975460062208060853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20598979967280082944081137 15449234975460062208060853)
            ·
              refine ⟨1448365778949380832005705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15449234975460062208060853 1448365778949380832005705)
              ·
                refine ⟨1086274334212035624004279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448365778949380832005705 1086274334212035624004279)
                ·
                  refine ⟨1629411501318053436006419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086274334212035624004279 1629411501318053436006419)
                  ·
                    refine ⟨2444117251977080154009629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629411501318053436006419 2444117251977080154009629)
                    ·
                      refine ⟨916543969491405057753611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444117251977080154009629 916543969491405057753611)
                      ·
                        rfl

theorem cell23_1784963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_1784963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784963 prefixEnd_1784963 := by exact prefixLift 1784963
  have htrace : WordTrace (prefixWord ++ tailWord_1784963) baseStart_1784963 baseEnd_1784963 := by
    simpa [prefixWord, tailWord_1784963, baseEnd_1784963] using wordTrace_append hprefix tailTrace_1784963
  have hstable : (prefixWord ++ tailWord_1784963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784963).length < 2 ^ (prefixWord ++ tailWord_1784963).sum := by decide
  have hdescent : baseEnd_1784963 < baseStart_1784963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784986 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1784986 : Nat := 118140960795 + 1784986 * 2 ^ 59
def prefixEnd_1784986 : Nat := 4983230072969 + 3 ^ 40 * 1784986 * 2
def baseEnd_1784986 : Nat := 916555779546458467766005

theorem tailTrace_1784986 : CollatzResearch.WordTrace tailWord_1784986 prefixEnd_1784986 916555779546458467766005 := by
  unfold tailWord_1784986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16275946977827012045863703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43402525274205365455636541 16275946977827012045863703)
  ·
    refine ⟨24413920466740518068795555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16275946977827012045863703 24413920466740518068795555)
    ·
      refine ⟨36620880700110777103193333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24413920466740518068795555 36620880700110777103193333)
      ·
        refine ⟨3433207565635385353424375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36620880700110777103193333 3433207565635385353424375)
        ·
          refine ⟨5149811348453078030136563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433207565635385353424375 5149811348453078030136563)
          ·
            refine ⟨7724717022679617045204845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149811348453078030136563 7724717022679617045204845)
            ·
              refine ⟨2896768883504856391951817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7724717022679617045204845 2896768883504856391951817)
              ·
                refine ⟨2172576662628642293963863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2896768883504856391951817 2172576662628642293963863)
                ·
                  refine ⟨3258864993942963440945795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2172576662628642293963863 3258864993942963440945795)
                  ·
                    refine ⟨4888297490914445161418693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3258864993942963440945795 4888297490914445161418693)
                    ·
                      refine ⟨916555779546458467766005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4888297490914445161418693 916555779546458467766005)
                      ·
                        rfl

theorem cell23_1784986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1784986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784986 prefixEnd_1784986 := by exact prefixLift 1784986
  have htrace : WordTrace (prefixWord ++ tailWord_1784986) baseStart_1784986 baseEnd_1784986 := by
    simpa [prefixWord, tailWord_1784986, baseEnd_1784986] using wordTrace_append hprefix tailTrace_1784986
  have hstable : (prefixWord ++ tailWord_1784986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784986).length < 2 ^ (prefixWord ++ tailWord_1784986).sum := by decide
  have hdescent : baseEnd_1784986 < baseStart_1784986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784989 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1784989 : Nat := 118140960795 + 1784989 * 2 ^ 59
def prefixEnd_1784989 : Nat := 4983230072969 + 3 ^ 40 * 1784989 * 2
def baseEnd_1784989 : Nat := 916557319988421956028491

theorem tailTrace_1784989 : CollatzResearch.WordTrace tailWord_1784989 prefixEnd_1784989 916557319988421956028491 := by
  unfold tailWord_1784989
  simp only [CollatzResearch.WordTrace]
  refine ⟨65103897330297179695814021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43402598220198119797209347 65103897330297179695814021)
  ·
    refine ⟨12206980749430721192965129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65103897330297179695814021 12206980749430721192965129)
    ·
      refine ⟨9155235562073040894723847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12206980749430721192965129 9155235562073040894723847)
      ·
        refine ⟨13732853343109561342085771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155235562073040894723847 13732853343109561342085771)
        ·
          refine ⟨20599280014664342013128657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13732853343109561342085771 20599280014664342013128657)
          ·
            refine ⟨15449460010998256509846493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20599280014664342013128657 15449460010998256509846493)
            ·
              refine ⟨5793547504124346191192435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15449460010998256509846493 5793547504124346191192435)
              ·
                refine ⟨8690321256186519286788653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793547504124346191192435 8690321256186519286788653)
                ·
                  refine ⟨3258870471069944732545745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8690321256186519286788653 3258870471069944732545745)
                  ·
                    refine ⟨2444152853302458549409309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3258870471069944732545745 2444152853302458549409309)
                    ·
                      refine ⟨916557319988421956028491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444152853302458549409309 916557319988421956028491)
                      ·
                        rfl

theorem cell23_1784989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1784989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784989 prefixEnd_1784989 := by exact prefixLift 1784989
  have htrace : WordTrace (prefixWord ++ tailWord_1784989) baseStart_1784989 baseEnd_1784989 := by
    simpa [prefixWord, tailWord_1784989, baseEnd_1784989] using wordTrace_append hprefix tailTrace_1784989
  have hstable : (prefixWord ++ tailWord_1784989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784989).length < 2 ^ (prefixWord ++ tailWord_1784989).sum := by decide
  have hdescent : baseEnd_1784989 < baseStart_1784989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1784999 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1784999 : Nat := 118140960795 + 1784999 * 2 ^ 59
def prefixEnd_1784999 : Nat := 4983230072969 + 3 ^ 40 * 1784999 * 2
def baseEnd_1784999 : Nat := 916562454794966916903445

theorem tailTrace_1784999 : CollatzResearch.WordTrace tailWord_1784999 prefixEnd_1784999 916562454794966916903445 := by
  unfold tailWord_1784999
  simp only [CollatzResearch.WordTrace]
  refine ⟨65104262060260951403678051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43402841373507300935785367 65104262060260951403678051)
  ·
    refine ⟨97656393090391427105517077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65104262060260951403678051 97656393090391427105517077)
    ·
      refine ⟨4577643426112098145571113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 97656393090391427105517077 4577643426112098145571113)
      ·
        refine ⟨3433232569584073609178335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4577643426112098145571113 3433232569584073609178335)
        ·
          refine ⟨5149848854376110413767503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433232569584073609178335 5149848854376110413767503)
          ·
            refine ⟨7724773281564165620651255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5149848854376110413767503 7724773281564165620651255)
            ·
              refine ⟨11587159922346248430976883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7724773281564165620651255 11587159922346248430976883)
              ·
                refine ⟨17380739883519372646465325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11587159922346248430976883 17380739883519372646465325)
                ·
                  refine ⟨6517777456319764742424497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17380739883519372646465325 6517777456319764742424497)
                  ·
                    refine ⟨4888333092239823556818373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6517777456319764742424497 4888333092239823556818373)
                    ·
                      refine ⟨916562454794966916903445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4888333092239823556818373 916562454794966916903445)
                      ·
                        rfl

theorem cell23_1784999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1784999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1784999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1784999 prefixEnd_1784999 := by exact prefixLift 1784999
  have htrace : WordTrace (prefixWord ++ tailWord_1784999) baseStart_1784999 baseEnd_1784999 := by
    simpa [prefixWord, tailWord_1784999, baseEnd_1784999] using wordTrace_append hprefix tailTrace_1784999
  have hstable : (prefixWord ++ tailWord_1784999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1784999).length < 2 ^ (prefixWord ++ tailWord_1784999).sum := by decide
  have hdescent : baseEnd_1784999 < baseStart_1784999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1784999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785020 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_1785020 : Nat := 118140960795 + 1785020 * 2 ^ 59
def prefixEnd_1785020 : Nat := 4983230072969 + 3 ^ 40 * 1785020 * 2
def baseEnd_1785020 : Nat := 916573237888711334740849

theorem tailTrace_1785020 : CollatzResearch.WordTrace tailWord_1785020 prefixEnd_1785020 916573237888711334740849 := by
  unfold tailWord_1785020
  simp only [CollatzResearch.WordTrace]
  refine ⟨32552513996592435995096257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43403351995456581326795009 32552513996592435995096257)
  ·
    refine ⟨24414385497444326996322193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32552513996592435995096257 24414385497444326996322193)
    ·
      refine ⟨18310789123083245247241645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24414385497444326996322193 18310789123083245247241645)
      ·
        refine ⟨6866545921156216967715617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18310789123083245247241645 6866545921156216967715617)
        ·
          refine ⟨5149909440867162725786713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6866545921156216967715617 5149909440867162725786713)
          ·
            refine ⟨3862432080650372044340035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5149909440867162725786713 3862432080650372044340035)
            ·
              refine ⟨5793648120975558066510053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862432080650372044340035 5793648120975558066510053)
              ·
                refine ⟨1086309022682917137470635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5793648120975558066510053 1086309022682917137470635)
                ·
                  refine ⟨1629463534024375706205953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086309022682917137470635 1629463534024375706205953)
                  ·
                    refine ⟨1222097650518281779654465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1629463534024375706205953 1222097650518281779654465)
                    ·
                      refine ⟨916573237888711334740849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222097650518281779654465 916573237888711334740849)
                      ·
                        rfl

theorem cell23_1785020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_1785020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785020 prefixEnd_1785020 := by exact prefixLift 1785020
  have htrace : WordTrace (prefixWord ++ tailWord_1785020) baseStart_1785020 baseEnd_1785020 := by
    simpa [prefixWord, tailWord_1785020, baseEnd_1785020] using wordTrace_append hprefix tailTrace_1785020
  have hstable : (prefixWord ++ tailWord_1785020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785020).length < 2 ^ (prefixWord ++ tailWord_1785020).sum := by decide
  have hdescent : baseEnd_1785020 < baseStart_1785020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785030 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1785030 : Nat := 118140960795 + 1785030 * 2 ^ 59
def prefixEnd_1785030 : Nat := 4983230072969 + 3 ^ 40 * 1785030 * 2
def baseEnd_1785030 : Nat := 305526124231752098538601

theorem tailTrace_1785030 : CollatzResearch.WordTrace tailWord_1785030 prefixEnd_1785030 305526124231752098538601 := by
  unfold tailWord_1785030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2034543522598395115564267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 43403595148765762465371029 2034543522598395115564267)
  ·
    refine ⟨3051815283897592673346401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2034543522598395115564267 3051815283897592673346401)
    ·
      refine ⟨2288861462923194505009801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3051815283897592673346401 2288861462923194505009801)
      ·
        refine ⟨1716646097192395878757351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288861462923194505009801 1716646097192395878757351)
        ·
          refine ⟨2574969145788593818136027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716646097192395878757351 2574969145788593818136027)
          ·
            refine ⟨3862453718682890727204041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574969145788593818136027 3862453718682890727204041)
            ·
              refine ⟨2896840289012168045403031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862453718682890727204041 2896840289012168045403031)
              ·
                refine ⟨4345260433518252068104547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2896840289012168045403031 4345260433518252068104547)
                ·
                  refine ⟨6517890650277378102156821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4345260433518252068104547 6517890650277378102156821)
                  ·
                    refine ⟨305526124231752098538601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6517890650277378102156821 305526124231752098538601)
                    ·
                      rfl

theorem cell23_1785030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1785030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785030 prefixEnd_1785030 := by exact prefixLift 1785030
  have htrace : WordTrace (prefixWord ++ tailWord_1785030) baseStart_1785030 baseEnd_1785030 := by
    simpa [prefixWord, tailWord_1785030, baseEnd_1785030] using wordTrace_append hprefix tailTrace_1785030
  have hstable : (prefixWord ++ tailWord_1785030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785030).length < 2 ^ (prefixWord ++ tailWord_1785030).sum := by decide
  have hdescent : baseEnd_1785030 < baseStart_1785030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785037 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1785037 : Nat := 118140960795 + 1785037 * 2 ^ 59
def prefixEnd_1785037 : Nat := 4983230072969 + 3 ^ 40 * 1785037 * 2
def baseEnd_1785037 : Nat := 916581967059837768228271

theorem tailTrace_1785037 : CollatzResearch.WordTrace tailWord_1785037 prefixEnd_1785037 916581967059837768228271 := by
  unfold tailWord_1785037
  simp only [CollatzResearch.WordTrace]
  refine ⟨65105648034123283893561365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43403765356082189262374243 65105648034123283893561365)
  ·
    refine ⟨3051827251599528932510689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65105648034123283893561365 3051827251599528932510689)
    ·
      refine ⟨2288870438699646699383017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3051827251599528932510689 2288870438699646699383017)
      ·
        refine ⟨1716652829024735024537263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2288870438699646699383017 1716652829024735024537263)
        ·
          refine ⟨2574979243537102536805895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716652829024735024537263 2574979243537102536805895)
          ·
            refine ⟨3862468865305653805208843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2574979243537102536805895 3862468865305653805208843)
            ·
              refine ⟨5793703297958480707813265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862468865305653805208843 5793703297958480707813265)
              ·
                refine ⟨4345277473468860530859949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5793703297958480707813265 4345277473468860530859949)
                ·
                  refine ⟨1629479052550822699072481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4345277473468860530859949 1629479052550822699072481)
                  ·
                    refine ⟨1222109289413117024304361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1629479052550822699072481 1222109289413117024304361)
                    ·
                      refine ⟨916581967059837768228271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222109289413117024304361 916581967059837768228271)
                      ·
                        rfl

theorem cell23_1785037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1785037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785037 prefixEnd_1785037 := by exact prefixLift 1785037
  have htrace : WordTrace (prefixWord ++ tailWord_1785037) baseStart_1785037 baseEnd_1785037 := by
    simpa [prefixWord, tailWord_1785037, baseEnd_1785037] using wordTrace_append hprefix tailTrace_1785037
  have hstable : (prefixWord ++ tailWord_1785037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785037).length < 2 ^ (prefixWord ++ tailWord_1785037).sum := by decide
  have hdescent : baseEnd_1785037 < baseStart_1785037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785069 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1785069 : Nat := 118140960795 + 1785069 * 2 ^ 59
def prefixEnd_1785069 : Nat := 4983230072969 + 3 ^ 40 * 1785069 * 2
def baseEnd_1785069 : Nat := 305532799480260547676041

theorem tailTrace_1785069 : CollatzResearch.WordTrace tailWord_1785069 prefixEnd_1785069 305532799480260547676041 := by
  unfold tailWord_1785069
  simp only [CollatzResearch.WordTrace]
  refine ⟨65106815170007353358726261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43404543446671568905817507 65106815170007353358726261)
  ·
    refine ⟨6103763922188189377380587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65106815170007353358726261 6103763922188189377380587)
    ·
      refine ⟨9155645883282284066070881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6103763922188189377380587 9155645883282284066070881)
      ·
        refine ⟨6866734412461713049553161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9155645883282284066070881 6866734412461713049553161)
        ·
          refine ⟨5150050809346284787164871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6866734412461713049553161 5150050809346284787164871)
          ·
            refine ⟨7725076214019427180747307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5150050809346284787164871 7725076214019427180747307)
            ·
              refine ⟨11587614321029140771120961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7725076214019427180747307 11587614321029140771120961)
              ·
                refine ⟨8690710740771855578340721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11587614321029140771120961 8690710740771855578340721)
                ·
                  refine ⟨6518033055578891683755541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8690710740771855578340721 6518033055578891683755541)
                  ·
                    refine ⟨305532799480260547676041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6518033055578891683755541 305532799480260547676041)
                    ·
                      rfl

theorem cell23_1785069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1785069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785069 prefixEnd_1785069 := by exact prefixLift 1785069
  have htrace : WordTrace (prefixWord ++ tailWord_1785069) baseStart_1785069 baseEnd_1785069 := by
    simpa [prefixWord, tailWord_1785069, baseEnd_1785069] using wordTrace_append hprefix tailTrace_1785069
  have hstable : (prefixWord ++ tailWord_1785069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785069).length < 2 ^ (prefixWord ++ tailWord_1785069).sum := by decide
  have hdescent : baseEnd_1785069 < baseStart_1785069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785089 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1785089 : Nat := 118140960795 + 1785089 * 2 ^ 59
def prefixEnd_1785089 : Nat := 4983230072969 + 3 ^ 40 * 1785089 * 2
def baseEnd_1785089 : Nat := 916608668053871564778031

theorem tailTrace_1785089 : CollatzResearch.WordTrace tailWord_1785089 prefixEnd_1785089 916608668053871564778031 := by
  unfold tailWord_1785089
  simp only [CollatzResearch.WordTrace]
  refine ⟨65107544629934896774454321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43405029753289931182969547 65107544629934896774454321)
  ·
    refine ⟨48830658472451172580840741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65107544629934896774454321 48830658472451172580840741)
    ·
      refine ⟨9155748463584594858907639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48830658472451172580840741 9155748463584594858907639)
      ·
        refine ⟨13733622695376892288361459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155748463584594858907639 13733622695376892288361459)
        ·
          refine ⟨20600434043065338432542189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733622695376892288361459 20600434043065338432542189)
          ·
            refine ⟨7725162766149501912203321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20600434043065338432542189 7725162766149501912203321)
            ·
              refine ⟨5793872074612126434152491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7725162766149501912203321 5793872074612126434152491)
              ·
                refine ⟨8690808111918189651228737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5793872074612126434152491 8690808111918189651228737)
                ·
                  refine ⟨6518106083938642238421553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8690808111918189651228737 6518106083938642238421553)
                  ·
                    refine ⟨4888579562953981678816165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6518106083938642238421553 4888579562953981678816165)
                    ·
                      refine ⟨916608668053871564778031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4888579562953981678816165 916608668053871564778031)
                      ·
                        rfl

theorem cell23_1785089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1785089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785089 prefixEnd_1785089 := by exact prefixLift 1785089
  have htrace : WordTrace (prefixWord ++ tailWord_1785089) baseStart_1785089 baseEnd_1785089 := by
    simpa [prefixWord, tailWord_1785089, baseEnd_1785089] using wordTrace_append hprefix tailTrace_1785089
  have hstable : (prefixWord ++ tailWord_1785089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785089).length < 2 ^ (prefixWord ++ tailWord_1785089).sum := by decide
  have hdescent : baseEnd_1785089 < baseStart_1785089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785116 : List Nat := [2, 2, 3, 1, 1, 1, 5, 3, 5]
def baseStart_1785116 : Nat := 118140960795 + 1785116 * 2 ^ 59
def prefixEnd_1785116 : Nat := 4983230072969 + 3 ^ 40 * 1785116 * 2
def baseEnd_1785116 : Nat := 101846948003504773237823

theorem tailTrace_1785116 : CollatzResearch.WordTrace tailWord_1785116 prefixEnd_1785116 101846948003504773237823 := by
  unfold tailWord_1785116
  simp only [CollatzResearch.WordTrace]
  refine ⟨32554264700418540192843601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43405686267224720257124801 32554264700418540192843601)
  ·
    refine ⟨24415698525313905144632701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32554264700418540192843601 24415698525313905144632701)
    ·
      refine ⟨9155886946992714429237263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24415698525313905144632701 9155886946992714429237263)
      ·
        refine ⟨13733830420489071643855895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9155886946992714429237263 13733830420489071643855895)
        ·
          refine ⟨20600745630733607465783843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13733830420489071643855895 20600745630733607465783843)
          ·
            refine ⟨30901118446100411198675765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20600745630733607465783843 30901118446100411198675765)
            ·
              refine ⟨2896979854321913549875853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30901118446100411198675765 2896979854321913549875853)
              ·
                refine ⟨1086367445370717581203445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2896979854321913549875853 1086367445370717581203445)
                ·
                  refine ⟨101846948003504773237823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1086367445370717581203445 101846948003504773237823)
                  ·
                    rfl

theorem cell23_1785116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_1785116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785116 prefixEnd_1785116 := by exact prefixLift 1785116
  have htrace : WordTrace (prefixWord ++ tailWord_1785116) baseStart_1785116 baseEnd_1785116 := by
    simpa [prefixWord, tailWord_1785116, baseEnd_1785116] using wordTrace_append hprefix tailTrace_1785116
  have hstable : (prefixWord ++ tailWord_1785116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785116).length < 2 ^ (prefixWord ++ tailWord_1785116).sum := by decide
  have hdescent : baseEnd_1785116 < baseStart_1785116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785133 : List Nat := [1, 5, 3, 1, 1, 3, 1, 1, 7]
def baseStart_1785133 : Nat := 118140960795 + 1785133 * 2 ^ 59
def prefixEnd_1785133 : Nat := 4983230072969 + 3 ^ 40 * 1785133 * 2
def baseEnd_1785133 : Nat := 101847917911407710291981

theorem tailTrace_1785133 : CollatzResearch.WordTrace tailWord_1785133 prefixEnd_1785133 101847917911407710291981 := by
  unfold tailWord_1785133
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109149441775492289056053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43406099627850328192704035 65109149441775492289056053)
  ·
    refine ⟨6103982760166452402099005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65109149441775492289056053 6103982760166452402099005)
    ·
      refine ⟨2288993535062419650787127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6103982760166452402099005 2288993535062419650787127)
      ·
        refine ⟨3433490302593629476180691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2288993535062419650787127 3433490302593629476180691)
        ·
          refine ⟨5150235453890444214271037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433490302593629476180691 5150235453890444214271037)
          ·
            refine ⟨1931338295208916580351639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5150235453890444214271037 1931338295208916580351639)
            ·
              refine ⟨2897007442813374870527459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931338295208916580351639 2897007442813374870527459)
              ·
                refine ⟨4345511164220062305791189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897007442813374870527459 4345511164220062305791189)
                ·
                  refine ⟨101847917911407710291981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4345511164220062305791189 101847917911407710291981)
                  ·
                    rfl

theorem cell23_1785133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_1785133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785133 prefixEnd_1785133 := by exact prefixLift 1785133
  have htrace : WordTrace (prefixWord ++ tailWord_1785133) baseStart_1785133 baseEnd_1785133 := by
    simpa [prefixWord, tailWord_1785133, baseEnd_1785133] using wordTrace_append hprefix tailTrace_1785133
  have hstable : (prefixWord ++ tailWord_1785133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785133).length < 2 ^ (prefixWord ++ tailWord_1785133).sum := by decide
  have hdescent : baseEnd_1785133 < baseStart_1785133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785139 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5]
def baseStart_1785139 : Nat := 118140960795 + 1785139 * 2 ^ 59
def prefixEnd_1785139 : Nat := 4983230072969 + 3 ^ 40 * 1785139 * 2
def baseEnd_1785139 : Nat := 916634342086596369152801

theorem tailTrace_1785139 : CollatzResearch.WordTrace tailWord_1785139 prefixEnd_1785139 916634342086596369152801 := by
  unfold tailWord_1785139
  simp only [CollatzResearch.WordTrace]
  refine ⟨65109368279753755313774471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43406245519835836875849647 65109368279753755313774471)
  ·
    refine ⟨97664052419630632970661707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65109368279753755313774471 97664052419630632970661707)
    ·
      refine ⟨146496078629445949455992561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97664052419630632970661707 146496078629445949455992561)
      ·
        refine ⟨109872058972084462091994421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146496078629445949455992561 109872058972084462091994421)
        ·
          refine ⟨10300505528632918321124477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 109872058972084462091994421 10300505528632918321124477)
          ·
            refine ⟨3862689573237344370421679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10300505528632918321124477 3862689573237344370421679)
            ·
              refine ⟨5794034359856016555632519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3862689573237344370421679 5794034359856016555632519)
              ·
                refine ⟨8691051539784024833448779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5794034359856016555632519 8691051539784024833448779)
                ·
                  refine ⟨13036577309676037250173169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8691051539784024833448779 13036577309676037250173169)
                  ·
                    refine ⟨9777432982257027937629877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13036577309676037250173169 9777432982257027937629877)
                    ·
                      refine ⟨916634342086596369152801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9777432982257027937629877 916634342086596369152801)
                      ·
                        rfl

theorem cell23_1785139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_1785139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785139 prefixEnd_1785139 := by exact prefixLift 1785139
  have htrace : WordTrace (prefixWord ++ tailWord_1785139) baseStart_1785139 baseEnd_1785139 := by
    simpa [prefixWord, tailWord_1785139, baseEnd_1785139] using wordTrace_append hprefix tailTrace_1785139
  have hstable : (prefixWord ++ tailWord_1785139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785139).length < 2 ^ (prefixWord ++ tailWord_1785139).sum := by decide
  have hdescent : baseEnd_1785139 < baseStart_1785139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785166 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1785166 : Nat := 118140960795 + 1785166 * 2 ^ 59
def prefixEnd_1785166 : Nat := 4983230072969 + 3 ^ 40 * 1785166 * 2
def baseEnd_1785166 : Nat := 916648206064267763515177

theorem tailTrace_1785166 : CollatzResearch.WordTrace tailWord_1785166 prefixEnd_1785166 916648206064267763515177 := by
  unfold tailWord_1785166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138794131331992365625919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43406902033770625950004901 8138794131331992365625919)
  ·
    refine ⟨12208191196997988548438879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138794131331992365625919 12208191196997988548438879)
    ·
      refine ⟨18312286795496982822658319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12208191196997988548438879 18312286795496982822658319)
      ·
        refine ⟨27468430193245474233987479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18312286795496982822658319 27468430193245474233987479)
        ·
          refine ⟨41202645289868211350981219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27468430193245474233987479 41202645289868211350981219)
          ·
            refine ⟨61803967934802317026471829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41202645289868211350981219 61803967934802317026471829)
            ·
              refine ⟨2897060996943858610615867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61803967934802317026471829 2897060996943858610615867)
              ·
                refine ⟨4345591495415787915923801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897060996943858610615867 4345591495415787915923801)
                ·
                  refine ⟨3259193621561840936942851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4345591495415787915923801 3259193621561840936942851)
                  ·
                    refine ⟨4888790432342761405414277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259193621561840936942851 4888790432342761405414277)
                    ·
                      refine ⟨916648206064267763515177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4888790432342761405414277 916648206064267763515177)
                      ·
                        rfl

theorem cell23_1785166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1785166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785166 prefixEnd_1785166 := by exact prefixLift 1785166
  have htrace : WordTrace (prefixWord ++ tailWord_1785166) baseStart_1785166 baseEnd_1785166 := by
    simpa [prefixWord, tailWord_1785166, baseEnd_1785166] using wordTrace_append hprefix tailTrace_1785166
  have hstable : (prefixWord ++ tailWord_1785166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785166).length < 2 ^ (prefixWord ++ tailWord_1785166).sum := by decide
  have hdescent : baseEnd_1785166 < baseStart_1785166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785240 : List Nat := [2, 1, 2, 5, 3, 1, 1, 2, 6]
def baseStart_1785240 : Nat := 118140960795 + 1785240 * 2 ^ 59
def prefixEnd_1785240 : Nat := 4983230072969 + 3 ^ 40 * 1785240 * 2
def baseEnd_1785240 : Nat := 101854022625855608221093

theorem tailTrace_1785240 : CollatzResearch.WordTrace tailWord_1785240 prefixEnd_1785240 101854022625855608221093 := by
  unfold tailWord_1785240
  simp only [CollatzResearch.WordTrace]
  refine ⟨32556526026193924781600587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43408701368258566375467449 32556526026193924781600587)
  ·
    refine ⟨48834789039290887172400881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32556526026193924781600587 48834789039290887172400881)
    ·
      refine ⟨36626091779468165379300661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48834789039290887172400881 36626091779468165379300661)
      ·
        refine ⟨3433696104325140504309437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36626091779468165379300661 3433696104325140504309437)
        ·
          refine ⟨1287636039121927689116039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3433696104325140504309437 1287636039121927689116039)
          ·
            refine ⟨1931454058682891533674059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287636039121927689116039 1931454058682891533674059)
            ·
              refine ⟨2897181088024337300511089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931454058682891533674059 2897181088024337300511089)
              ·
                refine ⟨2172885816018252975383317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2897181088024337300511089 2172885816018252975383317)
                ·
                  refine ⟨101854022625855608221093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2172885816018252975383317 101854022625855608221093)
                  ·
                    rfl

theorem cell23_1785240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 6].length) (baseStart_1785240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785240 prefixEnd_1785240 := by exact prefixLift 1785240
  have htrace : WordTrace (prefixWord ++ tailWord_1785240) baseStart_1785240 baseEnd_1785240 := by
    simpa [prefixWord, tailWord_1785240, baseEnd_1785240] using wordTrace_append hprefix tailTrace_1785240
  have hstable : (prefixWord ++ tailWord_1785240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785240).length < 2 ^ (prefixWord ++ tailWord_1785240).sum := by decide
  have hdescent : baseEnd_1785240 < baseStart_1785240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785250 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1785250 : Nat := 118140960795 + 1785250 * 2 ^ 59
def prefixEnd_1785250 : Nat := 4983230072969 + 3 ^ 40 * 1785250 * 2
def baseEnd_1785250 : Nat := 916691338439245434864791

theorem tailTrace_1785250 : CollatzResearch.WordTrace tailWord_1785250 prefixEnd_1785250 916691338439245434864791 := by
  unfold tailWord_1785250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16278354195587905317766301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43408944521567747514043469 16278354195587905317766301)
  ·
    refine ⟨6104382823345464494162363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16278354195587905317766301 6104382823345464494162363)
    ·
      refine ⟨9156574235018196741243545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104382823345464494162363 9156574235018196741243545)
      ·
        refine ⟨6867430676263647555932659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9156574235018196741243545 6867430676263647555932659)
        ·
          refine ⟨10301146014395471333898989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6867430676263647555932659 10301146014395471333898989)
          ·
            refine ⟨3862929755398301750212121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10301146014395471333898989 3862929755398301750212121)
            ·
              refine ⟨2897197316548726312659091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3862929755398301750212121 2897197316548726312659091)
              ·
                refine ⟨4345795974823089468988637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897197316548726312659091 4345795974823089468988637)
                ·
                  refine ⟨1629673490558658550870739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4345795974823089468988637 1629673490558658550870739)
                  ·
                    refine ⟨2444510235837987826306109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629673490558658550870739 2444510235837987826306109)
                    ·
                      refine ⟨916691338439245434864791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444510235837987826306109 916691338439245434864791)
                      ·
                        rfl

theorem cell23_1785250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1785250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785250 prefixEnd_1785250 := by exact prefixLift 1785250
  have htrace : WordTrace (prefixWord ++ tailWord_1785250) baseStart_1785250 baseEnd_1785250 := by
    simpa [prefixWord, tailWord_1785250, baseEnd_1785250] using wordTrace_append hprefix tailTrace_1785250
  have hstable : (prefixWord ++ tailWord_1785250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785250).length < 2 ^ (prefixWord ++ tailWord_1785250).sum := by decide
  have hdescent : baseEnd_1785250 < baseStart_1785250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785284 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1785284 : Nat := 118140960795 + 1785284 * 2 ^ 59
def prefixEnd_1785284 : Nat := 4983230072969 + 3 ^ 40 * 1785284 * 2
def baseEnd_1785284 : Nat := 916708796781498301839635

theorem tailTrace_1785284 : CollatzResearch.WordTrace tailWord_1785284 prefixEnd_1785284 916708796781498301839635 := by
  unfold tailWord_1785284
  simp only [CollatzResearch.WordTrace]
  refine ⟨32557328432114222538901453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43409771242818963385201937 32557328432114222538901453)
  ·
    refine ⟨12208998162042833452088045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32557328432114222538901453 12208998162042833452088045)
    ·
      refine ⟨4578374310766062544533017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12208998162042833452088045 4578374310766062544533017)
      ·
        refine ⟨3433780733074546908399763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4578374310766062544533017 3433780733074546908399763)
        ·
          refine ⟨5150671099611820362599645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433780733074546908399763 5150671099611820362599645)
          ·
            refine ⟨1931501662354432635974867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5150671099611820362599645 1931501662354432635974867)
            ·
              refine ⟨2897252493531648953962301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931501662354432635974867 2897252493531648953962301)
              ·
                refine ⟨1086469685074368357735863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897252493531648953962301 1086469685074368357735863)
                ·
                  refine ⟨1629704527611552536603795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086469685074368357735863 1629704527611552536603795)
                  ·
                    refine ⟨2444556791417328804905693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629704527611552536603795 2444556791417328804905693)
                    ·
                      refine ⟨916708796781498301839635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444556791417328804905693 916708796781498301839635)
                      ·
                        rfl

theorem cell23_1785284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1785284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785284 prefixEnd_1785284 := by exact prefixLift 1785284
  have htrace : WordTrace (prefixWord ++ tailWord_1785284) baseStart_1785284 baseEnd_1785284 := by
    simpa [prefixWord, tailWord_1785284, baseEnd_1785284] using wordTrace_append hprefix tailTrace_1785284
  have hstable : (prefixWord ++ tailWord_1785284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785284).length < 2 ^ (prefixWord ++ tailWord_1785284).sum := by decide
  have hdescent : baseEnd_1785284 < baseStart_1785284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785317 : List Nat := [1, 3, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_1785317 : Nat := 118140960795 + 1785317 * 2 ^ 59
def prefixEnd_1785317 : Nat := 4983230072969 + 3 ^ 40 * 1785317 * 2
def baseEnd_1785317 : Nat := 305575247214365557575661

theorem tailTrace_1785317 : CollatzResearch.WordTrace tailWord_1785317 prefixEnd_1785317 305575247214365557575661 := by
  unfold tailWord_1785317
  simp only [CollatzResearch.WordTrace]
  refine ⟨65115860473108891713754205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43410573648739261142502803 65115860473108891713754205)
  ·
    refine ⟨24418447677415834392657827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65115860473108891713754205 24418447677415834392657827)
    ·
      refine ⟨36627671516123751588986741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24418447677415834392657827 36627671516123751588986741)
      ·
        refine ⟨3433844204636601711467507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36627671516123751588986741 3433844204636601711467507)
        ·
          refine ⟨5150766306954902567201261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3433844204636601711467507 5150766306954902567201261)
          ·
            refine ⟨1931537365108088462700473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5150766306954902567201261 1931537365108088462700473)
            ·
              refine ⟨1448653023831066347025355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931537365108088462700473 1448653023831066347025355)
              ·
                refine ⟨2172979535746599520538033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448653023831066347025355 2172979535746599520538033)
                ·
                  refine ⟨1629734651809949640403525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2172979535746599520538033 1629734651809949640403525)
                  ·
                    refine ⟨305575247214365557575661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1629734651809949640403525 305575247214365557575661)
                    ·
                      rfl

theorem cell23_1785317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_1785317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785317 prefixEnd_1785317 := by exact prefixLift 1785317
  have htrace : WordTrace (prefixWord ++ tailWord_1785317) baseStart_1785317 baseEnd_1785317 := by
    simpa [prefixWord, tailWord_1785317, baseEnd_1785317] using wordTrace_append hprefix tailTrace_1785317
  have hstable : (prefixWord ++ tailWord_1785317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785317).length < 2 ^ (prefixWord ++ tailWord_1785317).sum := by decide
  have hdescent : baseEnd_1785317 < baseStart_1785317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785339 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 1, 8]
def baseStart_1785339 : Nat := 118140960795 + 1785339 * 2 ^ 59
def prefixEnd_1785339 : Nat := 4983230072969 + 3 ^ 40 * 1785339 * 2
def baseEnd_1785339 : Nat := 305579012739165195550627

theorem tailTrace_1785339 : CollatzResearch.WordTrace tailWord_1785339 prefixEnd_1785339 305579012739165195550627 := by
  unfold tailWord_1785339
  simp only [CollatzResearch.WordTrace]
  refine ⟨65116662879029189471055071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43411108586019459647370047 65116662879029189471055071)
  ·
    refine ⟨97674994318543784206582607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65116662879029189471055071 97674994318543784206582607)
    ·
      refine ⟨146512491477815676309873911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97674994318543784206582607 146512491477815676309873911)
      ·
        refine ⟨219768737216723514464810867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146512491477815676309873911 219768737216723514464810867)
        ·
          refine ⟨329653105825085271697216301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219768737216723514464810867 329653105825085271697216301)
          ·
            refine ⟨123619914684406976886456113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329653105825085271697216301 123619914684406976886456113)
            ·
              refine ⟨92714936013305232664842085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123619914684406976886456113 92714936013305232664842085)
              ·
                refine ⟨17384050502494731124657891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92714936013305232664842085 17384050502494731124657891)
                ·
                  refine ⟨26076075753742096686986837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17384050502494731124657891 26076075753742096686986837)
                  ·
                    refine ⟨305579012739165195550627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26076075753742096686986837 305579012739165195550627)
                    ·
                      rfl

theorem cell23_1785339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_1785339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785339 prefixEnd_1785339 := by exact prefixLift 1785339
  have htrace : WordTrace (prefixWord ++ tailWord_1785339) baseStart_1785339 baseEnd_1785339 := by
    simpa [prefixWord, tailWord_1785339, baseEnd_1785339] using wordTrace_append hprefix tailTrace_1785339
  have hstable : (prefixWord ++ tailWord_1785339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785339).length < 2 ^ (prefixWord ++ tailWord_1785339).sum := by decide
  have hdescent : baseEnd_1785339 < baseStart_1785339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785358 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1785358 : Nat := 118140960795 + 1785358 * 2 ^ 59
def prefixEnd_1785358 : Nat := 4983230072969 + 3 ^ 40 * 1785358 * 2
def baseEnd_1785358 : Nat := 916746794349931012314295

theorem tailTrace_1785358 : CollatzResearch.WordTrace tailWord_1785358 prefixEnd_1785358 916746794349931012314295 := by
  unfold tailWord_1785358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8139669483245044464499591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43411570577306903810664485 8139669483245044464499591)
  ·
    refine ⟨12209504224867566696749387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8139669483245044464499591 12209504224867566696749387)
    ·
      refine ⟨18314256337301350045124081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12209504224867566696749387 18314256337301350045124081)
      ·
        refine ⟨13735692252976012533843061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18314256337301350045124081 13735692252976012533843061)
        ·
          refine ⟨1287721148716501175047787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13735692252976012533843061 1287721148716501175047787)
          ·
            refine ⟨1931581723074751762571681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287721148716501175047787 1931581723074751762571681)
            ·
              refine ⟨1448686292306063821928761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1931581723074751762571681 1448686292306063821928761)
              ·
                refine ⟨1086514719229547866446571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1448686292306063821928761 1086514719229547866446571)
                ·
                  refine ⟨1629772078844321799669857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086514719229547866446571 1629772078844321799669857)
                  ·
                    refine ⟨1222329059133241349752393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1629772078844321799669857 1222329059133241349752393)
                    ·
                      refine ⟨916746794349931012314295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222329059133241349752393 916746794349931012314295)
                      ·
                        rfl

theorem cell23_1785358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1785358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785358 prefixEnd_1785358 := by exact prefixLift 1785358
  have htrace : WordTrace (prefixWord ++ tailWord_1785358) baseStart_1785358 baseEnd_1785358 := by
    simpa [prefixWord, tailWord_1785358, baseEnd_1785358] using wordTrace_append hprefix tailTrace_1785358
  have hstable : (prefixWord ++ tailWord_1785358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785358).length < 2 ^ (prefixWord ++ tailWord_1785358).sum := by decide
  have hdescent : baseEnd_1785358 < baseStart_1785358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785454 : List Nat := [4, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_1785454 : Nat := 118140960795 + 1785454 * 2 ^ 59
def prefixEnd_1785454 : Nat := 4983230072969 + 3 ^ 40 * 1785454 * 2
def baseEnd_1785454 : Nat := 101866232054751404079317

theorem tailTrace_1785454 : CollatzResearch.WordTrace tailWord_1785454 prefixEnd_1785454 101866232054751404079317 := by
  unfold tailWord_1785454
  simp only [CollatzResearch.WordTrace]
  refine ⟨8140107159201570513936427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43413904849075042740994277 8140107159201570513936427)
  ·
    refine ⟨12210160738802355770904641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8140107159201570513936427 12210160738802355770904641)
    ·
      refine ⟨9157620554101766828178481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12210160738802355770904641 9157620554101766828178481)
      ·
        refine ⟨6868215415576325121133861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9157620554101766828178481 6868215415576325121133861)
        ·
          refine ⟨1287790390420560960212599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6868215415576325121133861 1287790390420560960212599)
          ·
            refine ⟨1931685585630841440318899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287790390420560960212599 1931685585630841440318899)
            ·
              refine ⟨2897528378446262160478349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931685585630841440318899 2897528378446262160478349)
              ·
                refine ⟨1086573141917348310179381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897528378446262160478349 1086573141917348310179381)
                ·
                  refine ⟨101866232054751404079317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1086573141917348310179381 101866232054751404079317)
                  ·
                    rfl

theorem cell23_1785454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_1785454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785454 prefixEnd_1785454 := by exact prefixLift 1785454
  have htrace : WordTrace (prefixWord ++ tailWord_1785454) baseStart_1785454 baseEnd_1785454 := by
    simpa [prefixWord, tailWord_1785454, baseEnd_1785454] using wordTrace_append hprefix tailTrace_1785454
  have hstable : (prefixWord ++ tailWord_1785454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785454).length < 2 ^ (prefixWord ++ tailWord_1785454).sum := by decide
  have hdescent : baseEnd_1785454 < baseStart_1785454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785466 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1785466 : Nat := 118140960795 + 1785466 * 2 ^ 59
def prefixEnd_1785466 : Nat := 4983230072969 + 3 ^ 40 * 1785466 * 2
def baseEnd_1785466 : Nat := 916802250260616589763797

theorem tailTrace_1785466 : CollatzResearch.WordTrace tailWord_1785466 prefixEnd_1785466 916802250260616589763797 := by
  unfold tailWord_1785466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16280323737392272540232063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43414196633046060107285501 16280323737392272540232063)
  ·
    refine ⟨24420485606088408810348095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16280323737392272540232063 24420485606088408810348095)
    ·
      refine ⟨36630728409132613215522143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24420485606088408810348095 36630728409132613215522143)
      ·
        refine ⟨54946092613698919823283215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36630728409132613215522143 54946092613698919823283215)
        ·
          refine ⟨82419138920548379734924823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54946092613698919823283215 82419138920548379734924823)
          ·
            refine ⟨123628708380822569602387235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82419138920548379734924823 123628708380822569602387235)
            ·
              refine ⟨185443062571233854403580853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123628708380822569602387235 185443062571233854403580853)
              ·
                refine ⟨17385287116053173850335705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 185443062571233854403580853 17385287116053173850335705)
                ·
                  refine ⟨13038965337039880387751779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17385287116053173850335705 13038965337039880387751779)
                  ·
                    refine ⟨19558448005559820581627669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13038965337039880387751779 19558448005559820581627669)
                    ·
                      refine ⟨916802250260616589763797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19558448005559820581627669 916802250260616589763797)
                      ·
                        rfl

theorem cell23_1785466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1785466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785466 prefixEnd_1785466 := by exact prefixLift 1785466
  have htrace : WordTrace (prefixWord ++ tailWord_1785466) baseStart_1785466 baseEnd_1785466 := by
    simpa [prefixWord, tailWord_1785466, baseEnd_1785466] using wordTrace_append hprefix tailTrace_1785466
  have hstable : (prefixWord ++ tailWord_1785466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785466).length < 2 ^ (prefixWord ++ tailWord_1785466).sum := by decide
  have hdescent : baseEnd_1785466 < baseStart_1785466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785516 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1785516 : Nat := 118140960795 + 1785516 * 2 ^ 59
def prefixEnd_1785516 : Nat := 4983230072969 + 3 ^ 40 * 1785516 * 2
def baseEnd_1785516 : Nat := 916827924293341394138567

theorem tailTrace_1785516 : CollatzResearch.WordTrace tailWord_1785516 prefixEnd_1785516 916827924293341394138567 := by
  unfold tailWord_1785516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32561559299693974350124201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43415412399591965800165601 32561559299693974350124201)
  ·
    refine ⟨24421169474770480762593151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32561559299693974350124201 24421169474770480762593151)
    ·
      refine ⟨36631754212155721143889727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24421169474770480762593151 36631754212155721143889727)
      ·
        refine ⟨54947631318233581715834591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36631754212155721143889727 54947631318233581715834591)
        ·
          refine ⟨82421446977350372573751887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54947631318233581715834591 82421446977350372573751887)
          ·
            refine ⟨123632170466025558860627831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82421446977350372573751887 123632170466025558860627831)
            ·
              refine ⟨185448255699038338290941747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123632170466025558860627831 185448255699038338290941747)
              ·
                refine ⟨278172383548557507436412621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185448255699038338290941747 278172383548557507436412621)
                ·
                  refine ⟨104314643830709065288654733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 278172383548557507436412621 104314643830709065288654733)
                  ·
                    refine ⟨39117991436515899483245525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104314643830709065288654733 39117991436515899483245525)
                    ·
                      refine ⟨916827924293341394138567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 39117991436515899483245525 916827924293341394138567)
                      ·
                        rfl

theorem cell23_1785516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1785516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785516 prefixEnd_1785516 := by exact prefixLift 1785516
  have htrace : WordTrace (prefixWord ++ tailWord_1785516) baseStart_1785516 baseEnd_1785516 := by
    simpa [prefixWord, tailWord_1785516, baseEnd_1785516] using wordTrace_append hprefix tailTrace_1785516
  have hstable : (prefixWord ++ tailWord_1785516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785516).length < 2 ^ (prefixWord ++ tailWord_1785516).sum := by decide
  have hdescent : baseEnd_1785516 < baseStart_1785516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785543 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1785543 : Nat := 118140960795 + 1785543 * 2 ^ 59
def prefixEnd_1785543 : Nat := 4983230072969 + 3 ^ 40 * 1785543 * 2
def baseEnd_1785543 : Nat := 916841788271012788500943

theorem tailTrace_1785543 : CollatzResearch.WordTrace tailWord_1785543 prefixEnd_1785543 916841788271012788500943 := by
  unfold tailWord_1785543
  simp only [CollatzResearch.WordTrace]
  refine ⟨65124103370290132311481283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43416068913526754874320855 65124103370290132311481283)
  ·
    refine ⟨97686155055435198467221925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65124103370290132311481283 97686155055435198467221925)
    ·
      refine ⟨18316154072894099712604111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97686155055435198467221925 18316154072894099712604111)
      ·
        refine ⟨27474231109341149568906167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18316154072894099712604111 27474231109341149568906167)
        ·
          refine ⟨41211346664011724353359251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27474231109341149568906167 41211346664011724353359251)
          ·
            refine ⟨61817019996017586530038877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41211346664011724353359251 61817019996017586530038877)
            ·
              refine ⟨23181382498506594948764579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61817019996017586530038877 23181382498506594948764579)
              ·
                refine ⟨34772073747759892423146869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23181382498506594948764579 34772073747759892423146869)
                ·
                  refine ⟨3259881913852489914670019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34772073747759892423146869 3259881913852489914670019)
                  ·
                    refine ⟨4889822870778734872005029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259881913852489914670019 4889822870778734872005029)
                    ·
                      refine ⟨916841788271012788500943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4889822870778734872005029 916841788271012788500943)
                      ·
                        rfl

theorem cell23_1785543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1785543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785543 prefixEnd_1785543 := by exact prefixLift 1785543
  have htrace : WordTrace (prefixWord ++ tailWord_1785543) baseStart_1785543 baseEnd_1785543 := by
    simpa [prefixWord, tailWord_1785543, baseEnd_1785543] using wordTrace_append hprefix tailTrace_1785543
  have hstable : (prefixWord ++ tailWord_1785543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785543).length < 2 ^ (prefixWord ++ tailWord_1785543).sum := by decide
  have hdescent : baseEnd_1785543 < baseStart_1785543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785553 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_1785553 : Nat := 118140960795 + 1785553 * 2 ^ 59
def prefixEnd_1785553 : Nat := 4983230072969 + 3 ^ 40 * 1785553 * 2
def baseEnd_1785553 : Nat := 305615641025852583125299

theorem tailTrace_1785553 : CollatzResearch.WordTrace tailWord_1785553 prefixEnd_1785553 305615641025852583125299 := by
  unfold tailWord_1785553
  simp only [CollatzResearch.WordTrace]
  refine ⟨65124468100253904019345313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43416312066835936012896875 65124468100253904019345313)
  ·
    refine ⟨48843351075190428014508985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65124468100253904019345313 48843351075190428014508985)
    ·
      refine ⟨36632513306392821010881739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48843351075190428014508985 36632513306392821010881739)
      ·
        refine ⟨54948769959589231516322609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36632513306392821010881739 54948769959589231516322609)
        ·
          refine ⟨41211577469691923637241957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54948769959589231516322609 41211577469691923637241957)
          ·
            refine ⟨7727170775567235681982867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41211577469691923637241957 7727170775567235681982867)
            ·
              refine ⟨11590756163350853522974301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7727170775567235681982867 11590756163350853522974301)
              ·
                refine ⟨4346533561256570071115363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11590756163350853522974301 4346533561256570071115363)
                ·
                  refine ⟨6519800341884855106673045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346533561256570071115363 6519800341884855106673045)
                  ·
                    refine ⟨305615641025852583125299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6519800341884855106673045 305615641025852583125299)
                    ·
                      rfl

theorem cell23_1785553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_1785553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785553 prefixEnd_1785553 := by exact prefixLift 1785553
  have htrace : WordTrace (prefixWord ++ tailWord_1785553) baseStart_1785553 baseEnd_1785553 := by
    simpa [prefixWord, tailWord_1785553, baseEnd_1785553] using wordTrace_append hprefix tailTrace_1785553
  have hstable : (prefixWord ++ tailWord_1785553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785553).length < 2 ^ (prefixWord ++ tailWord_1785553).sum := by decide
  have hdescent : baseEnd_1785553 < baseStart_1785553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785558 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1785558 : Nat := 118140960795 + 1785558 * 2 ^ 59
def prefixEnd_1785558 : Nat := 4983230072969 + 3 ^ 40 * 1785558 * 2
def baseEnd_1785558 : Nat := 916849490480830229813375

theorem tailTrace_1785558 : CollatzResearch.WordTrace tailWord_1785558 prefixEnd_1785558 916849490480830229813375 := by
  unfold tailWord_1785558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070290654077236867079833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43416433643490526582184885 4070290654077236867079833)
  ·
    refine ⟨3052717990557927650309875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4070290654077236867079833 3052717990557927650309875)
    ·
      refine ⟨4579076985836891475464813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3052717990557927650309875 4579076985836891475464813)
      ·
        refine ⟨1717153869688834303299305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4579076985836891475464813 1717153869688834303299305)
        ·
          refine ⟨1287865402266625727474479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1717153869688834303299305 1287865402266625727474479)
          ·
            refine ⟨1931798103399938591211719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287865402266625727474479 1931798103399938591211719)
            ·
              refine ⟨2897697155099907886817579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931798103399938591211719 2897697155099907886817579)
              ·
                refine ⟨4346545732649861830226369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2897697155099907886817579 4346545732649861830226369)
                ·
                  refine ⟨3259909299487396372669777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4346545732649861830226369 3259909299487396372669777)
                  ·
                    refine ⟨2444931974615547279502333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3259909299487396372669777 2444931974615547279502333)
                    ·
                      refine ⟨916849490480830229813375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444931974615547279502333 916849490480830229813375)
                      ·
                        rfl

theorem cell23_1785558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1785558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785558 prefixEnd_1785558 := by exact prefixLift 1785558
  have htrace : WordTrace (prefixWord ++ tailWord_1785558) baseStart_1785558 baseEnd_1785558 := by
    simpa [prefixWord, tailWord_1785558, baseEnd_1785558] using wordTrace_append hprefix tailTrace_1785558
  have hstable : (prefixWord ++ tailWord_1785558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785558).length < 2 ^ (prefixWord ++ tailWord_1785558).sum := by decide
  have hdescent : baseEnd_1785558 < baseStart_1785558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785560 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1785560 : Nat := 118140960795 + 1785560 * 2 ^ 59
def prefixEnd_1785560 : Nat := 4983230072969 + 3 ^ 40 * 1785560 * 2
def baseEnd_1785560 : Nat := 916850517442139221988365

theorem tailTrace_1785560 : CollatzResearch.WordTrace tailWord_1785560 prefixEnd_1785560 916850517442139221988365 := by
  unfold tailWord_1785560
  simp only [CollatzResearch.WordTrace]
  refine ⟨32562361705614272107425067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43416482274152362809900089 32562361705614272107425067)
  ·
    refine ⟨48843542558421408161137601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32562361705614272107425067 48843542558421408161137601)
    ·
      refine ⟨36632656918816056120853201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48843542558421408161137601 36632656918816056120853201)
      ·
        refine ⟨27474492689112042090639901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36632656918816056120853201 27474492689112042090639901)
        ·
          refine ⟨10302934758417015783989963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27474492689112042090639901 10302934758417015783989963)
          ·
            refine ⟨15454402137625523675984945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10302934758417015783989963 15454402137625523675984945)
            ·
              refine ⟨11590801603219142756988709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15454402137625523675984945 11590801603219142756988709)
              ·
                refine ⟨2173275300603589266935383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11590801603219142756988709 2173275300603589266935383)
                ·
                  refine ⟨3259912950905383900403075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173275300603589266935383 3259912950905383900403075)
                  ·
                    refine ⟨4889869426358075850604613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3259912950905383900403075 4889869426358075850604613)
                    ·
                      refine ⟨916850517442139221988365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4889869426358075850604613 916850517442139221988365)
                      ·
                        rfl

theorem cell23_1785560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1785560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785560 prefixEnd_1785560 := by exact prefixLift 1785560
  have htrace : WordTrace (prefixWord ++ tailWord_1785560) baseStart_1785560 baseEnd_1785560 := by
    simpa [prefixWord, tailWord_1785560, baseEnd_1785560] using wordTrace_append hprefix tailTrace_1785560
  have hstable : (prefixWord ++ tailWord_1785560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785560).length < 2 ^ (prefixWord ++ tailWord_1785560).sum := by decide
  have hdescent : baseEnd_1785560 < baseStart_1785560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785564 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1785564 : Nat := 118140960795 + 1785564 * 2 ^ 59
def prefixEnd_1785564 : Nat := 4983230072969 + 3 ^ 40 * 1785564 * 2
def baseEnd_1785564 : Nat := 916852571364757206338347

theorem tailTrace_1785564 : CollatzResearch.WordTrace tailWord_1785564 prefixEnd_1785564 916852571364757206338347 := by
  unfold tailWord_1785564
  simp only [CollatzResearch.WordTrace]
  refine ⟨32562434651607026448997873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43416579535476035265330497 32562434651607026448997873)
  ·
    refine ⟨24421825988705269836748405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32562434651607026448997873 24421825988705269836748405)
    ·
      refine ⟨2289546186441119047195163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24421825988705269836748405 2289546186441119047195163)
      ·
        refine ⟨3434319279661678570792745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289546186441119047195163 3434319279661678570792745)
        ·
          refine ⟨2575739459746258928094559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434319279661678570792745 2575739459746258928094559)
          ·
            refine ⟨3863609189619388392141839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575739459746258928094559 3863609189619388392141839)
            ·
              refine ⟨5795413784429082588212759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863609189619388392141839 5795413784429082588212759)
              ·
                refine ⟨8693120676643623882319139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795413784429082588212759 8693120676643623882319139)
                ·
                  refine ⟨13039681014965435823478709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8693120676643623882319139 13039681014965435823478709)
                  ·
                    refine ⟨1222470095153009608451129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13039681014965435823478709 1222470095153009608451129)
                    ·
                      refine ⟨916852571364757206338347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222470095153009608451129 916852571364757206338347)
                      ·
                        rfl

theorem cell23_1785564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1785564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785564 prefixEnd_1785564 := by exact prefixLift 1785564
  have htrace : WordTrace (prefixWord ++ tailWord_1785564) baseStart_1785564 baseEnd_1785564 := by
    simpa [prefixWord, tailWord_1785564, baseEnd_1785564] using wordTrace_append hprefix tailTrace_1785564
  have hstable : (prefixWord ++ tailWord_1785564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785564).length < 2 ^ (prefixWord ++ tailWord_1785564).sum := by decide
  have hdescent : baseEnd_1785564 < baseStart_1785564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785571 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1785571 : Nat := 118140960795 + 1785571 * 2 ^ 59
def prefixEnd_1785571 : Nat := 4983230072969 + 3 ^ 40 * 1785571 * 2
def baseEnd_1785571 : Nat := 916856165729338678950815

theorem tailTrace_1785571 : CollatzResearch.WordTrace tailWord_1785571 prefixEnd_1785571 916856165729338678950815 := by
  unfold tailWord_1785571
  simp only [CollatzResearch.WordTrace]
  refine ⟨65125124614188693093500567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43416749742792462062333711 65125124614188693093500567)
  ·
    refine ⟨97687686921283039640250851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65125124614188693093500567 97687686921283039640250851)
    ·
      refine ⟨146531530381924559460376277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97687686921283039640250851 146531530381924559460376277)
      ·
        refine ⟨3434332743326356862352569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 146531530381924559460376277 3434332743326356862352569)
        ·
          refine ⟨2575749557494767646764427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3434332743326356862352569 2575749557494767646764427)
          ·
            refine ⟨3863624336242151470146641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2575749557494767646764427 3863624336242151470146641)
            ·
              refine ⟨2897718252181613602609981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3863624336242151470146641 2897718252181613602609981)
              ·
                refine ⟨1086644344568105100978743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2897718252181613602609981 1086644344568105100978743)
                ·
                  refine ⟨1629966516852157651468115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086644344568105100978743 1629966516852157651468115)
                  ·
                    refine ⟨2444949775278236477202173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629966516852157651468115 2444949775278236477202173)
                    ·
                      refine ⟨916856165729338678950815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444949775278236477202173 916856165729338678950815)
                      ·
                        rfl

theorem cell23_1785571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1785571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785571 prefixEnd_1785571 := by exact prefixLift 1785571
  have htrace : WordTrace (prefixWord ++ tailWord_1785571) baseStart_1785571 baseEnd_1785571 := by
    simpa [prefixWord, tailWord_1785571, baseEnd_1785571] using wordTrace_append hprefix tailTrace_1785571
  have hstable : (prefixWord ++ tailWord_1785571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785571).length < 2 ^ (prefixWord ++ tailWord_1785571).sum := by decide
  have hdescent : baseEnd_1785571 < baseStart_1785571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785588 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1785588 : Nat := 118140960795 + 1785588 * 2 ^ 59
def prefixEnd_1785588 : Nat := 4983230072969 + 3 ^ 40 * 1785588 * 2
def baseEnd_1785588 : Nat := 916864894900465112438237

theorem tailTrace_1785588 : CollatzResearch.WordTrace tailWord_1785588 prefixEnd_1785588 916864894900465112438237 := by
  unfold tailWord_1785588
  simp only [CollatzResearch.WordTrace]
  refine ⟨32562872327563552498434709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43417163103418069997912945 32562872327563552498434709)
  ·
    refine ⟨1526384640354541523364127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32562872327563552498434709 1526384640354541523364127)
    ·
      refine ⟨2289576960531812285046191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526384640354541523364127 2289576960531812285046191)
      ·
        refine ⟨3434365440797718427569287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289576960531812285046191 3434365440797718427569287)
        ·
          refine ⟨5151548161196577641353931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434365440797718427569287 5151548161196577641353931)
          ·
            refine ⟨7727322241794866462030897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151548161196577641353931 7727322241794866462030897)
            ·
              refine ⟨5795491681346149846523173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7727322241794866462030897 5795491681346149846523173)
              ·
                refine ⟨1086654690252403096223095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5795491681346149846523173 1086654690252403096223095)
                ·
                  refine ⟨1629982035378604644334643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086654690252403096223095 1629982035378604644334643)
                  ·
                    refine ⟨2444973053067906966501965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1629982035378604644334643 2444973053067906966501965)
                    ·
                      refine ⟨916864894900465112438237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444973053067906966501965 916864894900465112438237)
                      ·
                        rfl

theorem cell23_1785588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1785588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785588 prefixEnd_1785588 := by exact prefixLift 1785588
  have htrace : WordTrace (prefixWord ++ tailWord_1785588) baseStart_1785588 baseEnd_1785588 := by
    simpa [prefixWord, tailWord_1785588, baseEnd_1785588] using wordTrace_append hprefix tailTrace_1785588
  have hstable : (prefixWord ++ tailWord_1785588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785588).length < 2 ^ (prefixWord ++ tailWord_1785588).sum := by decide
  have hdescent : baseEnd_1785588 < baseStart_1785588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785593 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1785593 : Nat := 118140960795 + 1785593 * 2 ^ 59
def prefixEnd_1785593 : Nat := 4983230072969 + 3 ^ 40 * 1785593 * 2
def baseEnd_1785593 : Nat := 916867462303737592875713

theorem tailTrace_1785593 : CollatzResearch.WordTrace tailWord_1785593 prefixEnd_1785593 916867462303737592875713 := by
  unfold tailWord_1785593
  simp only [CollatzResearch.WordTrace]
  refine ⟨65125927020108990850801433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43417284680072660567200955 65125927020108990850801433)
  ·
    refine ⟨48844445265081743138101075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65125927020108990850801433 48844445265081743138101075)
    ·
      refine ⟨73266667897622614707151613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48844445265081743138101075 73266667897622614707151613)
      ·
        refine ⟨27475000461608480515181855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73266667897622614707151613 27475000461608480515181855)
        ·
          refine ⟨41212500692412720772772783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27475000461608480515181855 41212500692412720772772783)
          ·
            refine ⟨61818751038619081159159175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41212500692412720772772783 61818751038619081159159175)
            ·
              refine ⟨92728126557928621738738763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61818751038619081159159175 92728126557928621738738763)
              ·
                refine ⟨139092189836892932608108145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92728126557928621738738763 139092189836892932608108145)
                ·
                  refine ⟨104319142377669699456081109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139092189836892932608108145 104319142377669699456081109)
                  ·
                    refine ⟨2444979899476633581001901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 104319142377669699456081109 2444979899476633581001901)
                    ·
                      refine ⟨916867462303737592875713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2444979899476633581001901 916867462303737592875713)
                      ·
                        rfl

theorem cell23_1785593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1785593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785593 prefixEnd_1785593 := by exact prefixLift 1785593
  have htrace : WordTrace (prefixWord ++ tailWord_1785593) baseStart_1785593 baseEnd_1785593 := by
    simpa [prefixWord, tailWord_1785593, baseEnd_1785593] using wordTrace_append hprefix tailTrace_1785593
  have hstable : (prefixWord ++ tailWord_1785593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785593).length < 2 ^ (prefixWord ++ tailWord_1785593).sum := by decide
  have hdescent : baseEnd_1785593 < baseStart_1785593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785604 : List Nat := [2, 3, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1785604 : Nat := 118140960795 + 1785604 * 2 ^ 59
def prefixEnd_1785604 : Nat := 4983230072969 + 3 ^ 40 * 1785604 * 2
def baseEnd_1785604 : Nat := 305624370196979016612721

theorem tailTrace_1785604 : CollatzResearch.WordTrace tailWord_1785604 prefixEnd_1785604 305624370196979016612721 := by
  unfold tailWord_1785604
  simp only [CollatzResearch.WordTrace]
  refine ⟨32563164111534569864725933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43417552148712759819634577 32563164111534569864725933)
  ·
    refine ⟨12211186541825463699272225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32563164111534569864725933 12211186541825463699272225)
    ·
      refine ⟨9158389906369097774454169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12211186541825463699272225 9158389906369097774454169)
      ·
        refine ⟨6868792429776823330840627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9158389906369097774454169 6868792429776823330840627)
        ·
          refine ⟨10303188644665234996260941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6868792429776823330840627 10303188644665234996260941)
          ·
            refine ⟨3863695741749463123597853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10303188644665234996260941 3863695741749463123597853)
            ·
              refine ⟨1448885903156048671349195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3863695741749463123597853 1448885903156048671349195)
              ·
                refine ⟨2173328854734073007023793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448885903156048671349195 2173328854734073007023793)
                ·
                  refine ⟨1629996641050554755267845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173328854734073007023793 1629996641050554755267845)
                  ·
                    refine ⟨305624370196979016612721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1629996641050554755267845 305624370196979016612721)
                    ·
                      rfl

theorem cell23_1785604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1785604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785604 prefixEnd_1785604 := by exact prefixLift 1785604
  have htrace : WordTrace (prefixWord ++ tailWord_1785604) baseStart_1785604 baseEnd_1785604 := by
    simpa [prefixWord, tailWord_1785604, baseEnd_1785604] using wordTrace_append hprefix tailTrace_1785604
  have hstable : (prefixWord ++ tailWord_1785604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785604).length < 2 ^ (prefixWord ++ tailWord_1785604).sum := by decide
  have hdescent : baseEnd_1785604 < baseStart_1785604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785661 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1785661 : Nat := 118140960795 + 1785661 * 2 ^ 59
def prefixEnd_1785661 : Nat := 4983230072969 + 3 ^ 40 * 1785661 * 2
def baseEnd_1785661 : Nat := 916902378988243326825401

theorem tailTrace_1785661 : CollatzResearch.WordTrace tailWord_1785661 prefixEnd_1785661 916902378988243326825401 := by
  unfold tailWord_1785661
  simp only [CollatzResearch.WordTrace]
  refine ⟨65128407183862638464276837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43418938122575092309517891 65128407183862638464276837)
  ·
    refine ⟨12211576346974244712051907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65128407183862638464276837 12211576346974244712051907)
    ·
      refine ⟨18317364520461367068077861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12211576346974244712051907 18317364520461367068077861)
      ·
        refine ⟨3434505847586506325264599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18317364520461367068077861 3434505847586506325264599)
        ·
          refine ⟨5151758771379759487896899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3434505847586506325264599 5151758771379759487896899)
          ·
            refine ⟨7727638157069639231845349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5151758771379759487896899 7727638157069639231845349)
            ·
              refine ⟨1448932154450557355971003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7727638157069639231845349 1448932154450557355971003)
              ·
                refine ⟨2173398231675836033956505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1448932154450557355971003 2173398231675836033956505)
                ·
                  refine ⟨1630048673756877025467379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173398231675836033956505 1630048673756877025467379)
                  ·
                    refine ⟨2445073010635315538201069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630048673756877025467379 2445073010635315538201069)
                    ·
                      refine ⟨916902378988243326825401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445073010635315538201069 916902378988243326825401)
                      ·
                        rfl

theorem cell23_1785661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1785661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785661 prefixEnd_1785661 := by exact prefixLift 1785661
  have htrace : WordTrace (prefixWord ++ tailWord_1785661) baseStart_1785661 baseEnd_1785661 := by
    simpa [prefixWord, tailWord_1785661, baseEnd_1785661] using wordTrace_append hprefix tailTrace_1785661
  have hstable : (prefixWord ++ tailWord_1785661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785661).length < 2 ^ (prefixWord ++ tailWord_1785661).sum := by decide
  have hdescent : baseEnd_1785661 < baseStart_1785661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785673 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 9]
def baseStart_1785673 : Nat := 118140960795 + 1785673 * 2 ^ 59
def prefixEnd_1785673 : Nat := 4983230072969 + 3 ^ 40 * 1785673 * 2
def baseEnd_1785673 : Nat := 101878726750677475541705

theorem tailTrace_1785673 : CollatzResearch.WordTrace tailWord_1785673 prefixEnd_1785673 101878726750677475541705 := by
  unfold tailWord_1785673
  simp only [CollatzResearch.WordTrace]
  refine ⟨65128844859819164513713673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43419229906546109675809115 65128844859819164513713673)
  ·
    refine ⟨48846633644864373385285255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65128844859819164513713673 48846633644864373385285255)
    ·
      refine ⟨73269950467296560077927883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48846633644864373385285255 73269950467296560077927883)
      ·
        refine ⟨109904925700944840116891825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73269950467296560077927883 109904925700944840116891825)
        ·
          refine ⟨82428694275708630087668869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109904925700944840116891825 82428694275708630087668869)
          ·
            refine ⟨15455380176695368141437913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82428694275708630087668869 15455380176695368141437913)
            ·
              refine ⟨11591535132521526106078435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15455380176695368141437913 11591535132521526106078435)
              ·
                refine ⟨17387302698782289159117653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11591535132521526106078435 17387302698782289159117653)
                ·
                  refine ⟨101878726750677475541705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17387302698782289159117653 101878726750677475541705)
                  ·
                    rfl

theorem cell23_1785673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_1785673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785673 prefixEnd_1785673 := by exact prefixLift 1785673
  have htrace : WordTrace (prefixWord ++ tailWord_1785673) baseStart_1785673 baseEnd_1785673 := by
    simpa [prefixWord, tailWord_1785673, baseEnd_1785673] using wordTrace_append hprefix tailTrace_1785673
  have hstable : (prefixWord ++ tailWord_1785673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785673).length < 2 ^ (prefixWord ++ tailWord_1785673).sum := by decide
  have hdescent : baseEnd_1785673 < baseStart_1785673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785684 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_1785684 : Nat := 118140960795 + 1785684 * 2 ^ 59
def prefixEnd_1785684 : Nat := 4983230072969 + 3 ^ 40 * 1785684 * 2
def baseEnd_1785684 : Nat := 916914189043296736837795

theorem tailTrace_1785684 : CollatzResearch.WordTrace tailWord_1785684 prefixEnd_1785684 916914189043296736837795 := by
  unfold tailWord_1785684
  simp only [CollatzResearch.WordTrace]
  refine ⟨32564623031389656696182053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43419497375186208928242737 32564623031389656696182053)
  ·
    refine ⟨6105866818385560630534135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32564623031389656696182053 6105866818385560630534135)
    ·
      refine ⟨9158800227578340945801203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6105866818385560630534135 9158800227578340945801203)
      ·
        refine ⟨13738200341367511418701805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9158800227578340945801203 13738200341367511418701805)
        ·
          refine ⟨5151825128012816782013177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13738200341367511418701805 5151825128012816782013177)
          ·
            refine ⟨3863868846009612586509883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5151825128012816782013177 3863868846009612586509883)
            ·
              refine ⟨5795803269014418879764825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3863868846009612586509883 5795803269014418879764825)
              ·
                refine ⟨4346852451760814159823619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5795803269014418879764825 4346852451760814159823619)
                ·
                  refine ⟨6520278677641221239735429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4346852451760814159823619 6520278677641221239735429)
                  ·
                    refine ⟨1222552252057728982450393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6520278677641221239735429 1222552252057728982450393)
                    ·
                      refine ⟨916914189043296736837795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222552252057728982450393 916914189043296736837795)
                      ·
                        rfl

theorem cell23_1785684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_1785684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785684 prefixEnd_1785684 := by exact prefixLift 1785684
  have htrace : WordTrace (prefixWord ++ tailWord_1785684) baseStart_1785684 baseEnd_1785684 := by
    simpa [prefixWord, tailWord_1785684, baseEnd_1785684] using wordTrace_append hprefix tailTrace_1785684
  have hstable : (prefixWord ++ tailWord_1785684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785684).length < 2 ^ (prefixWord ++ tailWord_1785684).sum := by decide
  have hdescent : baseEnd_1785684 < baseStart_1785684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785717 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1785717 : Nat := 118140960795 + 1785717 * 2 ^ 59
def prefixEnd_1785717 : Nat := 4983230072969 + 3 ^ 40 * 1785717 * 2
def baseEnd_1785717 : Nat := 916931133904895107725143

theorem tailTrace_1785717 : CollatzResearch.WordTrace tailWord_1785717 prefixEnd_1785717 916931133904895107725143 := by
  unfold tailWord_1785717
  simp only [CollatzResearch.WordTrace]
  refine ⟨65130449671659760028315405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43420299781106506685543603 65130449671659760028315405)
  ·
    refine ⟨24423918626872410010618277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65130449671659760028315405 24423918626872410010618277)
    ·
      refine ⟨4579484742538576876990927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24423918626872410010618277 4579484742538576876990927)
      ·
        refine ⟨6869227113807865315486391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579484742538576876990927 6869227113807865315486391)
        ·
          refine ⟨10303840670711797973229587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6869227113807865315486391 10303840670711797973229587)
          ·
            refine ⟨15455761006067696959844381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10303840670711797973229587 15455761006067696959844381)
            ·
              refine ⟨5795910377275386359941643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15455761006067696959844381 5795910377275386359941643)
              ·
                refine ⟨8693865565913079539912465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5795910377275386359941643 8693865565913079539912465)
                ·
                  refine ⟨6520399174434809654934349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8693865565913079539912465 6520399174434809654934349)
                  ·
                    refine ⟨2445149690413053620600381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6520399174434809654934349 2445149690413053620600381)
                    ·
                      refine ⟨916931133904895107725143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445149690413053620600381 916931133904895107725143)
                      ·
                        rfl

theorem cell23_1785717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1785717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785717 prefixEnd_1785717 := by exact prefixLift 1785717
  have htrace : WordTrace (prefixWord ++ tailWord_1785717) baseStart_1785717 baseEnd_1785717 := by
    simpa [prefixWord, tailWord_1785717, baseEnd_1785717] using wordTrace_append hprefix tailTrace_1785717
  have hstable : (prefixWord ++ tailWord_1785717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785717).length < 2 ^ (prefixWord ++ tailWord_1785717).sum := by decide
  have hdescent : baseEnd_1785717 < baseStart_1785717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785777 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1785777 : Nat := 118140960795 + 1785777 * 2 ^ 59
def prefixEnd_1785777 : Nat := 4983230072969 + 3 ^ 40 * 1785777 * 2
def baseEnd_1785777 : Nat := 916961942744164872974867

theorem tailTrace_1785777 : CollatzResearch.WordTrace tailWord_1785777 prefixEnd_1785777 916961942744164872974867 := by
  unfold tailWord_1785777
  simp only [CollatzResearch.WordTrace]
  refine ⟨65132638051442390275499585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43421758700961593516999723 65132638051442390275499585)
  ·
    refine ⟨48849478538581792706624689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65132638051442390275499585 48849478538581792706624689)
    ·
      refine ⟨36637108903936344529968517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48849478538581792706624689 36637108903936344529968517)
      ·
        refine ⟨6869457919488064599369097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36637108903936344529968517 6869457919488064599369097)
        ·
          refine ⟨5152093439616048449526823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6869457919488064599369097 5152093439616048449526823)
          ·
            refine ⟨7728140159424072674290235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152093439616048449526823 7728140159424072674290235)
            ·
              refine ⟨11592210239136109011435353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728140159424072674290235 11592210239136109011435353)
              ·
                refine ⟨8694157679352081758576515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11592210239136109011435353 8694157679352081758576515)
                ·
                  refine ⟨13041236519028122637864773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8694157679352081758576515 13041236519028122637864773)
                  ·
                    refine ⟨2445231847317772994599645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13041236519028122637864773 2445231847317772994599645)
                    ·
                      refine ⟨916961942744164872974867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445231847317772994599645 916961942744164872974867)
                      ·
                        rfl

theorem cell23_1785777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1785777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785777 prefixEnd_1785777 := by exact prefixLift 1785777
  have htrace : WordTrace (prefixWord ++ tailWord_1785777) baseStart_1785777 baseEnd_1785777 := by
    simpa [prefixWord, tailWord_1785777, baseEnd_1785777] using wordTrace_append hprefix tailTrace_1785777
  have hstable : (prefixWord ++ tailWord_1785777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785777).length < 2 ^ (prefixWord ++ tailWord_1785777).sum := by decide
  have hdescent : baseEnd_1785777 < baseStart_1785777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785818 : List Nat := [3, 1, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_1785818 : Nat := 118140960795 + 1785818 * 2 ^ 59
def prefixEnd_1785818 : Nat := 4983230072969 + 3 ^ 40 * 1785818 * 2
def baseEnd_1785818 : Nat := 305660998483666404187393

theorem tailTrace_1785818 : CollatzResearch.WordTrace tailWord_1785818 prefixEnd_1785818 305660998483666404187393 := by
  unfold tailWord_1785818
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283533361073463569435527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43422755629529236185161405 16283533361073463569435527)
  ·
    refine ⟨24425300041610195354153291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16283533361073463569435527 24425300041610195354153291)
    ·
      refine ⟨36637950062415293031229937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24425300041610195354153291 36637950062415293031229937)
      ·
        refine ⟨27478462546811469773422453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36637950062415293031229937 27478462546811469773422453)
        ·
          refine ⟨2576105863763575291258355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27478462546811469773422453 2576105863763575291258355)
          ·
            refine ⟨3864158795645362936887533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576105863763575291258355 3864158795645362936887533)
            ·
              refine ⟨1449059548367011101332825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3864158795645362936887533 1449059548367011101332825)
              ·
                refine ⟨1086794661275258325999619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449059548367011101332825 1086794661275258325999619)
                ·
                  refine ⟨1630191991912887488999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086794661275258325999619 1630191991912887488999429)
                  ·
                    refine ⟨305660998483666404187393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630191991912887488999429 305660998483666404187393)
                    ·
                      rfl

theorem cell23_1785818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_1785818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785818 prefixEnd_1785818 := by exact prefixLift 1785818
  have htrace : WordTrace (prefixWord ++ tailWord_1785818) baseStart_1785818 baseEnd_1785818 := by
    simpa [prefixWord, tailWord_1785818, baseEnd_1785818] using wordTrace_append hprefix tailTrace_1785818
  have hstable : (prefixWord ++ tailWord_1785818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785818).length < 2 ^ (prefixWord ++ tailWord_1785818).sum := by decide
  have hdescent : baseEnd_1785818 < baseStart_1785818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785831 : List Nat := [1, 1, 5, 2, 3, 2, 2, 1, 6]
def baseStart_1785831 : Nat := 118140960795 + 1785831 * 2 ^ 59
def prefixEnd_1785831 : Nat := 4983230072969 + 3 ^ 40 * 1785831 * 2
def baseEnd_1785831 : Nat := 101887741188834184633291

theorem tailTrace_1785831 : CollatzResearch.WordTrace tailWord_1785831 prefixEnd_1785831 101887741188834184633291 := by
  unfold tailWord_1785831
  simp only [CollatzResearch.WordTrace]
  refine ⟨65134607593246757497965347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43423071728831171665310231 65134607593246757497965347)
  ·
    refine ⟨97701911389870136246948021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65134607593246757497965347 97701911389870136246948021)
    ·
      refine ⟨9159554192800325273151377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 97701911389870136246948021 9159554192800325273151377)
      ·
        refine ⟨6869665644600243954863533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9159554192800325273151377 6869665644600243954863533)
        ·
          refine ⟨2576124616725091483073825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6869665644600243954863533 2576124616725091483073825)
          ·
            refine ⟨1932093462543818612305369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576124616725091483073825 1932093462543818612305369)
            ·
              refine ⟨1449070096907863959229027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932093462543818612305369 1449070096907863959229027)
              ·
                refine ⟨2173605145361795938843541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449070096907863959229027 2173605145361795938843541)
                ·
                  refine ⟨101887741188834184633291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2173605145361795938843541 101887741188834184633291)
                  ·
                    rfl

theorem cell23_1785831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 6].length) (baseStart_1785831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785831 prefixEnd_1785831 := by exact prefixLift 1785831
  have htrace : WordTrace (prefixWord ++ tailWord_1785831) baseStart_1785831 baseEnd_1785831 := by
    simpa [prefixWord, tailWord_1785831, baseEnd_1785831] using wordTrace_append hprefix tailTrace_1785831
  have hstable : (prefixWord ++ tailWord_1785831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785831).length < 2 ^ (prefixWord ++ tailWord_1785831).sum := by decide
  have hdescent : baseEnd_1785831 < baseStart_1785831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785834 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_1785834 : Nat := 118140960795 + 1785834 * 2 ^ 59
def prefixEnd_1785834 : Nat := 4983230072969 + 3 ^ 40 * 1785834 * 2
def baseEnd_1785834 : Nat := 916991211141471149962105

theorem tailTrace_1785834 : CollatzResearch.WordTrace tailWord_1785834 prefixEnd_1785834 916991211141471149962105 := by
  unfold tailWord_1785834
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283679253058972252581139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43423144674823926006883037 16283679253058972252581139)
  ·
    refine ⟨24425518879588458378871709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16283679253058972252581139 24425518879588458378871709)
    ·
      refine ⟨9159569579845671892076891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24425518879588458378871709 9159569579845671892076891)
      ·
        refine ⟨13739354369768507838115337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159569579845671892076891 13739354369768507838115337)
        ·
          refine ⟨10304515777326380878586503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13739354369768507838115337 10304515777326380878586503)
          ·
            refine ⟨15456773665989571317879755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304515777326380878586503 15456773665989571317879755)
            ·
              refine ⟨23185160498984356976819633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15456773665989571317879755 23185160498984356976819633)
              ·
                refine ⟨17388870374238267732614725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23185160498984356976819633 17388870374238267732614725)
                ·
                  refine ⟨3260413195169675199865261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17388870374238267732614725 3260413195169675199865261)
                  ·
                    refine ⟨1222654948188628199949473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3260413195169675199865261 1222654948188628199949473)
                    ·
                      refine ⟨916991211141471149962105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222654948188628199949473 916991211141471149962105)
                      ·
                        rfl

theorem cell23_1785834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_1785834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785834 prefixEnd_1785834 := by exact prefixLift 1785834
  have htrace : WordTrace (prefixWord ++ tailWord_1785834) baseStart_1785834 baseEnd_1785834 := by
    simpa [prefixWord, tailWord_1785834, baseEnd_1785834] using wordTrace_append hprefix tailTrace_1785834
  have hstable : (prefixWord ++ tailWord_1785834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785834).length < 2 ^ (prefixWord ++ tailWord_1785834).sum := by decide
  have hdescent : baseEnd_1785834 < baseStart_1785834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785850 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1785850 : Nat := 118140960795 + 1785850 * 2 ^ 59
def prefixEnd_1785850 : Nat := 4983230072969 + 3 ^ 40 * 1785850 * 2
def baseEnd_1785850 : Nat := 916999426831943087362031

theorem tailTrace_1785850 : CollatzResearch.WordTrace tailWord_1785850 prefixEnd_1785850 916999426831943087362031 := by
  unfold tailWord_1785850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16283825145044480935726751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43423533720118615828604669 16283825145044480935726751)
  ·
    refine ⟨24425737717566721403590127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16283825145044480935726751 24425737717566721403590127)
    ·
      refine ⟨36638606576350082105385191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24425737717566721403590127 36638606576350082105385191)
      ·
        refine ⟨54957909864525123158077787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36638606576350082105385191 54957909864525123158077787)
        ·
          refine ⟨82436864796787684737116681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54957909864525123158077787 82436864796787684737116681)
          ·
            refine ⟨61827648597590763552837511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82436864796787684737116681 61827648597590763552837511)
            ·
              refine ⟨92741472896386145329256267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61827648597590763552837511 92741472896386145329256267)
              ·
                refine ⟨139112209344579217993884401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92741472896386145329256267 139112209344579217993884401)
                ·
                  refine ⟨104334157008434413495413301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139112209344579217993884401 104334157008434413495413301)
                  ·
                    refine ⟨9781327219540726265194997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104334157008434413495413301 9781327219540726265194997)
                    ·
                      refine ⟨916999426831943087362031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9781327219540726265194997 916999426831943087362031)
                      ·
                        rfl

theorem cell23_1785850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1785850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785850 prefixEnd_1785850 := by exact prefixLift 1785850
  have htrace : WordTrace (prefixWord ++ tailWord_1785850) baseStart_1785850 baseEnd_1785850 := by
    simpa [prefixWord, tailWord_1785850, baseEnd_1785850] using wordTrace_append hprefix tailTrace_1785850
  have hstable : (prefixWord ++ tailWord_1785850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785850).length < 2 ^ (prefixWord ++ tailWord_1785850).sum := by decide
  have hdescent : baseEnd_1785850 < baseStart_1785850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785857 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1785857 : Nat := 118140960795 + 1785857 * 2 ^ 59
def prefixEnd_1785857 : Nat := 4983230072969 + 3 ^ 40 * 1785857 * 2
def baseEnd_1785857 : Nat := 305667673732174853324833

theorem tailTrace_1785857 : CollatzResearch.WordTrace tailWord_1785857 prefixEnd_1785857 305667673732174853324833 := by
  unfold tailWord_1785857
  simp only [CollatzResearch.WordTrace]
  refine ⟨65135555891152563938411825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43423703927435042625607883 65135555891152563938411825)
  ·
    refine ⟨48851666918364422953808869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65135555891152563938411825 48851666918364422953808869)
    ·
      refine ⟨9159687547193329303839163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48851666918364422953808869 9159687547193329303839163)
      ·
        refine ⟨13739531320789993955758745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159687547193329303839163 13739531320789993955758745)
        ·
          refine ⟨10304648490592495466819059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13739531320789993955758745 10304648490592495466819059)
          ·
            refine ⟨15456972735888743200228589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10304648490592495466819059 15456972735888743200228589)
            ·
              refine ⟨5796364775958278700085721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15456972735888743200228589 5796364775958278700085721)
              ·
                refine ⟨4347273581968709025064291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796364775958278700085721 4347273581968709025064291)
                ·
                  refine ⟨6520910372953063537596437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4347273581968709025064291 6520910372953063537596437)
                  ·
                    refine ⟨305667673732174853324833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6520910372953063537596437 305667673732174853324833)
                    ·
                      rfl

theorem cell23_1785857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1785857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785857 prefixEnd_1785857 := by exact prefixLift 1785857
  have htrace : WordTrace (prefixWord ++ tailWord_1785857) baseStart_1785857 baseEnd_1785857 := by
    simpa [prefixWord, tailWord_1785857, baseEnd_1785857] using wordTrace_append hprefix tailTrace_1785857
  have hstable : (prefixWord ++ tailWord_1785857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785857).length < 2 ^ (prefixWord ++ tailWord_1785857).sum := by decide
  have hdescent : baseEnd_1785857 < baseStart_1785857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785869 : List Nat := [1, 7, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1785869 : Nat := 118140960795 + 1785869 * 2 ^ 59
def prefixEnd_1785869 : Nat := 4983230072969 + 3 ^ 40 * 1785869 * 2
def baseEnd_1785869 : Nat := 305669727654792837674815

theorem tailTrace_1785869 : CollatzResearch.WordTrace tailWord_1785869 prefixEnd_1785869 305669727654792837674815 := by
  unfold tailWord_1785869
  simp only [CollatzResearch.WordTrace]
  refine ⟨65135993567109089987848661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43423995711406059991899107 65135993567109089987848661)
  ·
    refine ⟨1526624849229119296590203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 65135993567109089987848661 1526624849229119296590203)
    ·
      refine ⟨2289937273843678944885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526624849229119296590203 2289937273843678944885305)
      ·
        refine ⟨1717452955382759208663979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289937273843678944885305 1717452955382759208663979)
        ·
          refine ⟨2576179433074138812995969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717452955382759208663979 2576179433074138812995969)
          ·
            refine ⟨1932134574805604109746977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576179433074138812995969 1932134574805604109746977)
            ·
              refine ⟨1449100931104203082310233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932134574805604109746977 1449100931104203082310233)
              ·
                refine ⟨1086825698328152311732675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1449100931104203082310233 1086825698328152311732675)
                ·
                  refine ⟨1630238547492228467599013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086825698328152311732675 1630238547492228467599013)
                  ·
                    refine ⟨305669727654792837674815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630238547492228467599013 305669727654792837674815)
                    ·
                      rfl

theorem cell23_1785869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1785869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785869 prefixEnd_1785869 := by exact prefixLift 1785869
  have htrace : WordTrace (prefixWord ++ tailWord_1785869) baseStart_1785869 baseEnd_1785869 := by
    simpa [prefixWord, tailWord_1785869, baseEnd_1785869] using wordTrace_append hprefix tailTrace_1785869
  have hstable : (prefixWord ++ tailWord_1785869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785869).length < 2 ^ (prefixWord ++ tailWord_1785869).sum := by decide
  have hdescent : baseEnd_1785869 < baseStart_1785869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785884 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1785884 : Nat := 118140960795 + 1785884 * 2 ^ 59
def prefixEnd_1785884 : Nat := 4983230072969 + 3 ^ 40 * 1785884 * 2
def baseEnd_1785884 : Nat := 917016885174195954336875

theorem tailTrace_1785884 : CollatzResearch.WordTrace tailWord_1785884 prefixEnd_1785884 917016885174195954336875 := by
  unfold tailWord_1785884
  simp only [CollatzResearch.WordTrace]
  refine ⟨32568270331027373774822353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43424360441369831699763137 32568270331027373774822353)
  ·
    refine ⟨24426202748270530331116765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32568270331027373774822353 24426202748270530331116765)
    ·
      refine ⟨9159826030601448874168787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24426202748270530331116765 9159826030601448874168787)
      ·
        refine ⟨13739739045902173311253181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9159826030601448874168787 13739739045902173311253181)
        ·
          refine ⟨5152402142213314991719943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13739739045902173311253181 5152402142213314991719943)
          ·
            refine ⟨7728603213319972487579915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5152402142213314991719943 7728603213319972487579915)
            ·
              refine ⟨11592904819979958731369873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728603213319972487579915 11592904819979958731369873)
              ·
                refine ⟨8694678614984969048527405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11592904819979958731369873 8694678614984969048527405)
                ·
                  refine ⟨3260504480619363393197777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8694678614984969048527405 3260504480619363393197777)
                  ·
                    refine ⟨2445378360464522544898333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3260504480619363393197777 2445378360464522544898333)
                    ·
                      refine ⟨917016885174195954336875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445378360464522544898333 917016885174195954336875)
                      ·
                        rfl

theorem cell23_1785884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1785884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785884 prefixEnd_1785884 := by exact prefixLift 1785884
  have htrace : WordTrace (prefixWord ++ tailWord_1785884) baseStart_1785884 baseEnd_1785884 := by
    simpa [prefixWord, tailWord_1785884, baseEnd_1785884] using wordTrace_append hprefix tailTrace_1785884
  have hstable : (prefixWord ++ tailWord_1785884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785884).length < 2 ^ (prefixWord ++ tailWord_1785884).sum := by decide
  have hdescent : baseEnd_1785884 < baseStart_1785884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785898 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1785898 : Nat := 118140960795 + 1785898 * 2 ^ 59
def prefixEnd_1785898 : Nat := 4983230072969 + 3 ^ 40 * 1785898 * 2
def baseEnd_1785898 : Nat := 917024073903358899561811

theorem tailTrace_1785898 : CollatzResearch.WordTrace tailWord_1785898 prefixEnd_1785898 917024073903358899561811 := by
  unfold tailWord_1785898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284262821001006985163587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43424700856002685293769565 16284262821001006985163587)
  ·
    refine ⟨24426394231501510477745381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16284262821001006985163587 24426394231501510477745381)
    ·
      refine ⟨4579948918406533214577259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24426394231501510477745381 4579948918406533214577259)
      ·
        refine ⟨6869923377609799821865889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4579948918406533214577259 6869923377609799821865889)
        ·
          refine ⟨5152442533207349866399417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6869923377609799821865889 5152442533207349866399417)
          ·
            refine ⟨3864331899905512399799563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5152442533207349866399417 3864331899905512399799563)
            ·
              refine ⟨5796497849858268599699345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864331899905512399799563 5796497849858268599699345)
              ·
                refine ⟨4347373387393701449774509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5796497849858268599699345 4347373387393701449774509)
                ·
                  refine ⟨1630265020272638043665441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4347373387393701449774509 1630265020272638043665441)
                  ·
                    refine ⟨1222698765204478532749081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1630265020272638043665441 1222698765204478532749081)
                    ·
                      refine ⟨917024073903358899561811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222698765204478532749081 917024073903358899561811)
                      ·
                        rfl

theorem cell23_1785898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1785898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785898 prefixEnd_1785898 := by exact prefixLift 1785898
  have htrace : WordTrace (prefixWord ++ tailWord_1785898) baseStart_1785898 baseEnd_1785898 := by
    simpa [prefixWord, tailWord_1785898, baseEnd_1785898] using wordTrace_append hprefix tailTrace_1785898
  have hstable : (prefixWord ++ tailWord_1785898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785898).length < 2 ^ (prefixWord ++ tailWord_1785898).sum := by decide
  have hdescent : baseEnd_1785898 < baseStart_1785898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785914 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_1785914 : Nat := 118140960795 + 1785914 * 2 ^ 59
def prefixEnd_1785914 : Nat := 4983230072969 + 3 ^ 40 * 1785914 * 2
def baseEnd_1785914 : Nat := 917032289593830836961737

theorem tailTrace_1785914 : CollatzResearch.WordTrace tailWord_1785914 prefixEnd_1785914 917032289593830836961737 := by
  unfold tailWord_1785914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16284408712986515668309199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43425089901297375115491197 16284408712986515668309199)
  ·
    refine ⟨24426613069479773502463799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16284408712986515668309199 24426613069479773502463799)
    ·
      refine ⟨36639919604219660253695699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24426613069479773502463799 36639919604219660253695699)
      ·
        refine ⟨54959879406329490380543549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36639919604219660253695699 54959879406329490380543549)
        ·
          refine ⟨20609954777373558892703831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54959879406329490380543549 20609954777373558892703831)
          ·
            refine ⟨30914932166060338339055747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20609954777373558892703831 30914932166060338339055747)
            ·
              refine ⟨46372398249090507508583621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30914932166060338339055747 46372398249090507508583621)
              ·
                refine ⟨8694824671704470157859429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46372398249090507508583621 8694824671704470157859429)
                ·
                  refine ⟨1630279625944588154598643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8694824671704470157859429 1630279625944588154598643)
                  ·
                    refine ⟨2445419438916882231897965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630279625944588154598643 2445419438916882231897965)
                    ·
                      refine ⟨917032289593830836961737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445419438916882231897965 917032289593830836961737)
                      ·
                        rfl

theorem cell23_1785914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_1785914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785914 prefixEnd_1785914 := by exact prefixLift 1785914
  have htrace : WordTrace (prefixWord ++ tailWord_1785914) baseStart_1785914 baseEnd_1785914 := by
    simpa [prefixWord, tailWord_1785914, baseEnd_1785914] using wordTrace_append hprefix tailTrace_1785914
  have hstable : (prefixWord ++ tailWord_1785914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785914).length < 2 ^ (prefixWord ++ tailWord_1785914).sum := by decide
  have hdescent : baseEnd_1785914 < baseStart_1785914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785918 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1785918 : Nat := 118140960795 + 1785918 * 2 ^ 59
def prefixEnd_1785918 : Nat := 4983230072969 + 3 ^ 40 * 1785918 * 2
def baseEnd_1785918 : Nat := 917034343516448821311719

theorem tailTrace_1785918 : CollatzResearch.WordTrace tailWord_1785918 prefixEnd_1785918 917034343516448821311719 := by
  unfold tailWord_1785918
  simp only [CollatzResearch.WordTrace]
  refine ⟨8142222592991446419547801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43425187162621047570921605 8142222592991446419547801)
  ·
    refine ⟨6106666944743584814660851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8142222592991446419547801 6106666944743584814660851)
    ·
      refine ⟨9160000417115377221991277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106666944743584814660851 9160000417115377221991277)
      ·
        refine ⟨3435000156418266458246729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9160000417115377221991277 3435000156418266458246729)
        ·
          refine ⟨2576250117313699843685047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3435000156418266458246729 2576250117313699843685047)
          ·
            refine ⟨3864375175970549765527571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2576250117313699843685047 3864375175970549765527571)
            ·
              refine ⟨5796562763955824648291357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3864375175970549765527571 5796562763955824648291357)
              ·
                refine ⟨2173711036483434243109259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5796562763955824648291357 2173711036483434243109259)
                ·
                  refine ⟨3260566554725151364663889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2173711036483434243109259 3260566554725151364663889)
                  ·
                    refine ⟨2445424916043863523497917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3260566554725151364663889 2445424916043863523497917)
                    ·
                      refine ⟨917034343516448821311719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445424916043863523497917 917034343516448821311719)
                      ·
                        rfl

theorem cell23_1785918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1785918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785918 prefixEnd_1785918 := by exact prefixLift 1785918
  have htrace : WordTrace (prefixWord ++ tailWord_1785918) baseStart_1785918 baseEnd_1785918 := by
    simpa [prefixWord, tailWord_1785918, baseEnd_1785918] using wordTrace_append hprefix tailTrace_1785918
  have hstable : (prefixWord ++ tailWord_1785918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785918).length < 2 ^ (prefixWord ++ tailWord_1785918).sum := by decide
  have hdescent : baseEnd_1785918 < baseStart_1785918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785974 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1785974 : Nat := 118140960795 + 1785974 * 2 ^ 59
def prefixEnd_1785974 : Nat := 4983230072969 + 3 ^ 40 * 1785974 * 2
def baseEnd_1785974 : Nat := 917063098433100602211461

theorem tailTrace_1785974 : CollatzResearch.WordTrace tailWord_1785974 prefixEnd_1785974 917063098433100602211461 := by
  unfold tailWord_1785974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4071238951983043307526311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43426548821152461946947317 4071238951983043307526311)
  ·
    refine ⟨6106858427974564961289467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4071238951983043307526311 6106858427974564961289467)
    ·
      refine ⟨9160287641961847441934201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6106858427974564961289467 9160287641961847441934201)
      ·
        refine ⟨6870215731471385581450651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9160287641961847441934201 6870215731471385581450651)
        ·
          refine ⟨10305323597207078372175977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870215731471385581450651 10305323597207078372175977)
          ·
            refine ⟨7728992697905308779131983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305323597207078372175977 7728992697905308779131983)
            ·
              refine ⟨11593489046857963168697975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7728992697905308779131983 11593489046857963168697975)
              ·
                refine ⟨17390233570286944753046963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11593489046857963168697975 17390233570286944753046963)
                ·
                  refine ⟨26085350355430417129570445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17390233570286944753046963 26085350355430417129570445)
                  ·
                    refine ⟨9782006383286406423588917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26085350355430417129570445 9782006383286406423588917)
                    ·
                      refine ⟨917063098433100602211461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9782006383286406423588917 917063098433100602211461)
                      ·
                        rfl

theorem cell23_1785974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1785974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785974 prefixEnd_1785974 := by exact prefixLift 1785974
  have htrace : WordTrace (prefixWord ++ tailWord_1785974) baseStart_1785974 baseEnd_1785974 := by
    simpa [prefixWord, tailWord_1785974, baseEnd_1785974] using wordTrace_append hprefix tailTrace_1785974
  have hstable : (prefixWord ++ tailWord_1785974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785974).length < 2 ^ (prefixWord ++ tailWord_1785974).sum := by decide
  have hdescent : baseEnd_1785974 < baseStart_1785974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785988 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1785988 : Nat := 118140960795 + 1785988 * 2 ^ 59
def prefixEnd_1785988 : Nat := 4983230072969 + 3 ^ 40 * 1785988 * 2
def baseEnd_1785988 : Nat := 917070287162263547436397

theorem tailTrace_1785988 : CollatzResearch.WordTrace tailWord_1785988 prefixEnd_1785988 917070287162263547436397 := by
  unfold tailWord_1785988
  simp only [CollatzResearch.WordTrace]
  refine ⟨32570166926838986655715309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43426889235785315540953745 32570166926838986655715309)
  ·
    refine ⟨12213812597564619995893241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32570166926838986655715309 12213812597564619995893241)
    ·
      refine ⟨9160359448173464996919931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12213812597564619995893241 9160359448173464996919931)
      ·
        refine ⟨13740539172260197495379897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9160359448173464996919931 13740539172260197495379897)
        ·
          refine ⟨10305404379195148121534923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13740539172260197495379897 10305404379195148121534923)
          ·
            refine ⟨15458106568792722182302385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10305404379195148121534923 15458106568792722182302385)
            ·
              refine ⟨11593579926594541636726789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15458106568792722182302385 11593579926594541636726789)
              ·
                refine ⟨2173796236236476556886273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11593579926594541636726789 2173796236236476556886273)
                ·
                  refine ⟨1630347177177357417664705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2173796236236476556886273 1630347177177357417664705)
                  ·
                    refine ⟨1222760382883018063248529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1630347177177357417664705 1222760382883018063248529)
                    ·
                      refine ⟨917070287162263547436397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222760382883018063248529 917070287162263547436397)
                      ·
                        rfl

theorem cell23_1785988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1785988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785988 prefixEnd_1785988 := by exact prefixLift 1785988
  have htrace : WordTrace (prefixWord ++ tailWord_1785988) baseStart_1785988 baseEnd_1785988 := by
    simpa [prefixWord, tailWord_1785988, baseEnd_1785988] using wordTrace_append hprefix tailTrace_1785988
  have hstable : (prefixWord ++ tailWord_1785988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785988).length < 2 ^ (prefixWord ++ tailWord_1785988).sum := by decide
  have hdescent : baseEnd_1785988 < baseStart_1785988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1785994 : List Nat := [3, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_1785994 : Nat := 118140960795 + 1785994 * 2 ^ 59
def prefixEnd_1785994 : Nat := 4983230072969 + 3 ^ 40 * 1785994 * 2
def baseEnd_1785994 : Nat := 101897040894021169329041

theorem tailTrace_1785994 : CollatzResearch.WordTrace tailWord_1785994 prefixEnd_1785994 101897040894021169329041 := by
  unfold tailWord_1785994
  simp only [CollatzResearch.WordTrace]
  refine ⟨16285138172914059084037259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43427035127770824224099357 16285138172914059084037259)
  ·
    refine ⟨24427707259371088626055889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16285138172914059084037259 24427707259371088626055889)
    ·
      refine ⟨18320780444528316469541917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24427707259371088626055889 18320780444528316469541917)
      ·
        refine ⟨6870292666698118676078219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18320780444528316469541917 6870292666698118676078219)
        ·
          refine ⟨10305439000047178014117329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6870292666698118676078219 10305439000047178014117329)
          ·
            refine ⟨7729079250035383510587997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305439000047178014117329 7729079250035383510587997)
            ·
              refine ⟨2898404718763268816470499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7729079250035383510587997 2898404718763268816470499)
              ·
                refine ⟨4347607078144903224705749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898404718763268816470499 4347607078144903224705749)
                ·
                  refine ⟨101897040894021169329041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4347607078144903224705749 101897040894021169329041)
                  ·
                    rfl

theorem cell23_1785994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_1785994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1785994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1785994 prefixEnd_1785994 := by exact prefixLift 1785994
  have htrace : WordTrace (prefixWord ++ tailWord_1785994) baseStart_1785994 baseEnd_1785994 := by
    simpa [prefixWord, tailWord_1785994, baseEnd_1785994] using wordTrace_append hprefix tailTrace_1785994
  have hstable : (prefixWord ++ tailWord_1785994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1785994).length < 2 ^ (prefixWord ++ tailWord_1785994).sum := by decide
  have hdescent : baseEnd_1785994 < baseStart_1785994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1785994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786027 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4]
def baseStart_1786027 : Nat := 118140960795 + 1786027 * 2 ^ 59
def prefixEnd_1786027 : Nat := 4983230072969 + 3 ^ 40 * 1786027 * 2
def baseEnd_1786027 : Nat := 917090312907788894848717

theorem tailTrace_1786027 : CollatzResearch.WordTrace tailWord_1786027 prefixEnd_1786027 917090312907788894848717 := by
  unfold tailWord_1786027
  simp only [CollatzResearch.WordTrace]
  refine ⟨65141756300536682972100335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43427837533691121981400223 65141756300536682972100335)
  ·
    refine ⟨97712634450805024458150503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65141756300536682972100335 97712634450805024458150503)
    ·
      refine ⟨146568951676207536687225755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97712634450805024458150503 146568951676207536687225755)
      ·
        refine ⟨219853427514311305030838633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146568951676207536687225755 219853427514311305030838633)
        ·
          refine ⟨164890070635733478773128975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 219853427514311305030838633 164890070635733478773128975)
          ·
            refine ⟨247335105953600218159693463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164890070635733478773128975 247335105953600218159693463)
            ·
              refine ⟨371002658930400327239540195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247335105953600218159693463 371002658930400327239540195)
              ·
                refine ⟨556503988395600490859310293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371002658930400327239540195 556503988395600490859310293)
                ·
                  refine ⟨13043062228021886504515085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 556503988395600490859310293 13043062228021886504515085)
                  ·
                    refine ⟨4891148335508207439193157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13043062228021886504515085 4891148335508207439193157)
                    ·
                      refine ⟨917090312907788894848717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4891148335508207439193157 917090312907788894848717)
                      ·
                        rfl

theorem cell23_1786027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_1786027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786027 prefixEnd_1786027 := by exact prefixLift 1786027
  have htrace : WordTrace (prefixWord ++ tailWord_1786027) baseStart_1786027 baseEnd_1786027 := by
    simpa [prefixWord, tailWord_1786027, baseEnd_1786027] using wordTrace_append hprefix tailTrace_1786027
  have hstable : (prefixWord ++ tailWord_1786027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786027).length < 2 ^ (prefixWord ++ tailWord_1786027).sum := by decide
  have hdescent : baseEnd_1786027 < baseStart_1786027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786047 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1786047 : Nat := 118140960795 + 1786047 * 2 ^ 59
def prefixEnd_1786047 : Nat := 4983230072969 + 3 ^ 40 * 1786047 * 2
def baseEnd_1786047 : Nat := 917100582520878816598625

theorem tailTrace_1786047 : CollatzResearch.WordTrace tailWord_1786047 prefixEnd_1786047 917100582520878816598625 := by
  unfold tailWord_1786047
  simp only [CollatzResearch.WordTrace]
  refine ⟨65142485760464226387828395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43428323840309484258552263 65142485760464226387828395)
  ·
    refine ⟨97713728640696339581742593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65142485760464226387828395 97713728640696339581742593)
    ·
      refine ⟨73285296480522254686306945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97713728640696339581742593 73285296480522254686306945)
      ·
        refine ⟨54963972360391691014730209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73285296480522254686306945 54963972360391691014730209)
        ·
          refine ⟨41222979270293768261047657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54963972360391691014730209 41222979270293768261047657)
          ·
            refine ⟨30917234452720326195785743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41222979270293768261047657 30917234452720326195785743)
            ·
              refine ⟨46375851679080489293678615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30917234452720326195785743 46375851679080489293678615)
              ·
                refine ⟨69563777518620733940517923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46375851679080489293678615 69563777518620733940517923)
                ·
                  refine ⟨104345666277931100910776885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69563777518620733940517923 104345666277931100910776885)
                  ·
                    refine ⟨9782406213556040710385333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104345666277931100910776885 9782406213556040710385333)
                    ·
                      refine ⟨917100582520878816598625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9782406213556040710385333 917100582520878816598625)
                      ·
                        rfl

theorem cell23_1786047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1786047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786047 prefixEnd_1786047 := by exact prefixLift 1786047
  have htrace : WordTrace (prefixWord ++ tailWord_1786047) baseStart_1786047 baseEnd_1786047 := by
    simpa [prefixWord, tailWord_1786047, baseEnd_1786047] using wordTrace_append hprefix tailTrace_1786047
  have hstable : (prefixWord ++ tailWord_1786047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786047).length < 2 ^ (prefixWord ++ tailWord_1786047).sum := by decide
  have hdescent : baseEnd_1786047 < baseStart_1786047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786057 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_1786057 : Nat := 118140960795 + 1786057 * 2 ^ 59
def prefixEnd_1786057 : Nat := 4983230072969 + 3 ^ 40 * 1786057 * 2
def baseEnd_1786057 : Nat := 917105717327423777473579

theorem tailTrace_1786057 : CollatzResearch.WordTrace tailWord_1786057 prefixEnd_1786057 917105717327423777473579 := by
  unfold tailWord_1786057
  simp only [CollatzResearch.WordTrace]
  refine ⟨65142850490427998095692425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43428566993618665397128283 65142850490427998095692425)
  ·
    refine ⟨48857137867820998571769319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65142850490427998095692425 48857137867820998571769319)
    ·
      refine ⟨73285706801731497857653979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48857137867820998571769319 73285706801731497857653979)
      ·
        refine ⟨109928560202597246786480969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73285706801731497857653979 109928560202597246786480969)
        ·
          refine ⟨82446420151947935089860727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109928560202597246786480969 82446420151947935089860727)
          ·
            refine ⟨123669630227921902634791091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82446420151947935089860727 123669630227921902634791091)
            ·
              refine ⟨185504445341882853952186637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123669630227921902634791091 185504445341882853952186637)
              ·
                refine ⟨69564167003206070232069989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185504445341882853952186637 69564167003206070232069989)
                ·
                  refine ⟨13043281313101138168513123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69564167003206070232069989 13043281313101138168513123)
                  ·
                    refine ⟨19564921969651707252769685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13043281313101138168513123 19564921969651707252769685)
                    ·
                      refine ⟨917105717327423777473579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19564921969651707252769685 917105717327423777473579)
                      ·
                        rfl

theorem cell23_1786057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_1786057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786057 prefixEnd_1786057 := by exact prefixLift 1786057
  have htrace : WordTrace (prefixWord ++ tailWord_1786057) baseStart_1786057 baseEnd_1786057 := by
    simpa [prefixWord, tailWord_1786057, baseEnd_1786057] using wordTrace_append hprefix tailTrace_1786057
  have hstable : (prefixWord ++ tailWord_1786057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786057).length < 2 ^ (prefixWord ++ tailWord_1786057).sum := by decide
  have hdescent : baseEnd_1786057 < baseStart_1786057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786088 : List Nat := [2, 1, 4, 1, 2, 2, 1, 5, 1, 4]
def baseStart_1786088 : Nat := 118140960795 + 1786088 * 2 ^ 59
def prefixEnd_1786088 : Nat := 4983230072969 + 3 ^ 40 * 1786088 * 2
def baseEnd_1786088 : Nat := 305707211742571052061979

theorem tailTrace_1786088 : CollatzResearch.WordTrace tailWord_1786088 prefixEnd_1786088 305707211742571052061979 := by
  unfold tailWord_1786088
  simp only [CollatzResearch.WordTrace]
  refine ⟨32571990576657845195035459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43429320768877126926713945 32571990576657845195035459)
  ·
    refine ⟨48857985864986767792553189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32571990576657845195035459 48857985864986767792553189)
    ·
      refine ⟨9160872349685018961103723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48857985864986767792553189 9160872349685018961103723)
      ·
        refine ⟨13741308524527528441655585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9160872349685018961103723 13741308524527528441655585)
        ·
          refine ⟨10305981393395646331241689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13741308524527528441655585 10305981393395646331241689)
          ·
            refine ⟨7729486045046734748431267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10305981393395646331241689 7729486045046734748431267)
            ·
              refine ⟨11594229067570102122646901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729486045046734748431267 11594229067570102122646901)
              ·
                refine ⟨1086958975084697073998147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11594229067570102122646901 1086958975084697073998147)
                ·
                  refine ⟨1630438462627045610997221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086958975084697073998147 1630438462627045610997221)
                  ·
                    refine ⟨305707211742571052061979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630438462627045610997221 305707211742571052061979)
                    ·
                      rfl

theorem cell23_1786088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_1786088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786088 prefixEnd_1786088 := by exact prefixLift 1786088
  have htrace : WordTrace (prefixWord ++ tailWord_1786088) baseStart_1786088 baseEnd_1786088 := by
    simpa [prefixWord, tailWord_1786088, baseEnd_1786088] using wordTrace_append hprefix tailTrace_1786088
  have hstable : (prefixWord ++ tailWord_1786088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786088).length < 2 ^ (prefixWord ++ tailWord_1786088).sum := by decide
  have hdescent : baseEnd_1786088 < baseStart_1786088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786121 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 5, 2]
def baseStart_1786121 : Nat := 118140960795 + 1786121 * 2 ^ 59
def prefixEnd_1786121 : Nat := 4983230072969 + 3 ^ 40 * 1786121 * 2
def baseEnd_1786121 : Nat := 917138580089311527073285

theorem tailTrace_1786121 : CollatzResearch.WordTrace tailWord_1786121 prefixEnd_1786121 917138580089311527073285 := by
  unfold tailWord_1786121
  simp only [CollatzResearch.WordTrace]
  refine ⟨65145184762196137026022217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43430123174797424684014811 65145184762196137026022217)
  ·
    refine ⟨48858888571647102769516663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65145184762196137026022217 48858888571647102769516663)
    ·
      refine ⟨73288332857470654154274995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48858888571647102769516663 73288332857470654154274995)
      ·
        refine ⟨109932499286205981231412493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73288332857470654154274995 109932499286205981231412493)
        ·
          refine ⟨41224687232327242961779685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 109932499286205981231412493 41224687232327242961779685)
          ·
            refine ⟨7729628856061358055333691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41224687232327242961779685 7729628856061358055333691)
            ·
              refine ⟨11594443284092037083000537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7729628856061358055333691 11594443284092037083000537)
              ·
                refine ⟨8695832463069027812250403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11594443284092037083000537 8695832463069027812250403)
                ·
                  refine ⟨13043748694603541718375605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8695832463069027812250403 13043748694603541718375605)
                  ·
                    refine ⟨1222851440119082036097713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13043748694603541718375605 1222851440119082036097713)
                    ·
                      refine ⟨917138580089311527073285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222851440119082036097713 917138580089311527073285)
                      ·
                        rfl

theorem cell23_1786121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 5, 2].length) (baseStart_1786121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786121 prefixEnd_1786121 := by exact prefixLift 1786121
  have htrace : WordTrace (prefixWord ++ tailWord_1786121) baseStart_1786121 baseEnd_1786121 := by
    simpa [prefixWord, tailWord_1786121, baseEnd_1786121] using wordTrace_append hprefix tailTrace_1786121
  have hstable : (prefixWord ++ tailWord_1786121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786121).length < 2 ^ (prefixWord ++ tailWord_1786121).sum := by decide
  have hdescent : baseEnd_1786121 < baseStart_1786121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786145 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1786145 : Nat := 118140960795 + 1786145 * 2 ^ 59
def prefixEnd_1786145 : Nat := 4983230072969 + 3 ^ 40 * 1786145 * 2
def baseEnd_1786145 : Nat := 917150903625019433173175

theorem tailTrace_1786145 : CollatzResearch.WordTrace tailWord_1786145 prefixEnd_1786145 917150903625019433173175 := by
  unfold tailWord_1786145
  simp only [CollatzResearch.WordTrace]
  refine ⟨65146060114109189124895889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43430706742739459416597259 65146060114109189124895889)
  ·
    refine ⟨48859545085581891843671917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65146060114109189124895889 48859545085581891843671917)
    ·
      refine ⟨18322329407093209441376969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48859545085581891843671917 18322329407093209441376969)
      ·
        refine ⟨13741747055319907081032727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18322329407093209441376969 13741747055319907081032727)
        ·
          refine ⟨20612620582979860621549091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13741747055319907081032727 20612620582979860621549091)
          ·
            refine ⟨30918930874469790932323637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20612620582979860621549091 30918930874469790932323637)
            ·
              refine ⟨2898649769481542899905341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30918930874469790932323637 2898649769481542899905341)
              ·
                refine ⟨1086993663555578587464503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2898649769481542899905341 1086993663555578587464503)
                ·
                  refine ⟨1630490495333367881196755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1086993663555578587464503 1630490495333367881196755)
                  ·
                    refine ⟨2445735743000051821795133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630490495333367881196755 2445735743000051821795133)
                    ·
                      refine ⟨917150903625019433173175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445735743000051821795133 917150903625019433173175)
                      ·
                        rfl

theorem cell23_1786145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1786145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786145 prefixEnd_1786145 := by exact prefixLift 1786145
  have htrace : WordTrace (prefixWord ++ tailWord_1786145) baseStart_1786145 baseEnd_1786145 := by
    simpa [prefixWord, tailWord_1786145, baseEnd_1786145] using wordTrace_append hprefix tailTrace_1786145
  have hstable : (prefixWord ++ tailWord_1786145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786145).length < 2 ^ (prefixWord ++ tailWord_1786145).sum := by decide
  have hdescent : baseEnd_1786145 < baseStart_1786145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786162 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_1786162 : Nat := 118140960795 + 1786162 * 2 ^ 59
def prefixEnd_1786162 : Nat := 4983230072969 + 3 ^ 40 * 1786162 * 2
def baseEnd_1786162 : Nat := 917159632796145866660597

theorem tailTrace_1786162 : CollatzResearch.WordTrace tailWord_1786162 prefixEnd_1786162 917159632796145866660597 := by
  unfold tailWord_1786162
  simp only [CollatzResearch.WordTrace]
  refine ⟨16286670038761900257066185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43431120103365067352176493 16286670038761900257066185)
  ·
    refine ⟨12215002529071425192799639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16286670038761900257066185 12215002529071425192799639)
    ·
      refine ⟨18322503793607137789199459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12215002529071425192799639 18322503793607137789199459)
      ·
        refine ⟨27483755690410706683799189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18322503793607137789199459 27483755690410706683799189)
        ·
          refine ⟨1288301047988001875803087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27483755690410706683799189 1288301047988001875803087)
          ·
            refine ⟨1932451571982002813704631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288301047988001875803087 1932451571982002813704631)
            ·
              refine ⟨2898677357973004220556947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932451571982002813704631 2898677357973004220556947)
              ·
                refine ⟨4348016036959506330835421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2898677357973004220556947 4348016036959506330835421)
                ·
                  refine ⟨1630506013859814874063283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4348016036959506330835421 1630506013859814874063283)
                  ·
                    refine ⟨2445759020789722311094925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630506013859814874063283 2445759020789722311094925)
                    ·
                      refine ⟨917159632796145866660597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445759020789722311094925 917159632796145866660597)
                      ·
                        rfl

theorem cell23_1786162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_1786162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786162 prefixEnd_1786162 := by exact prefixLift 1786162
  have htrace : WordTrace (prefixWord ++ tailWord_1786162) baseStart_1786162 baseEnd_1786162 := by
    simpa [prefixWord, tailWord_1786162, baseEnd_1786162] using wordTrace_append hprefix tailTrace_1786162
  have hstable : (prefixWord ++ tailWord_1786162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786162).length < 2 ^ (prefixWord ++ tailWord_1786162).sum := by decide
  have hdescent : baseEnd_1786162 < baseStart_1786162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786269 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_1786269 : Nat := 118140960795 + 1786269 * 2 ^ 59
def prefixEnd_1786269 : Nat := 4983230072969 + 3 ^ 40 * 1786269 * 2
def baseEnd_1786269 : Nat := 917214575226176948022605

theorem tailTrace_1786269 : CollatzResearch.WordTrace tailWord_1786269 prefixEnd_1786269 917214575226176948022605 := by
  unfold tailWord_1786269
  simp only [CollatzResearch.WordTrace]
  refine ⟨65150582765659958302409861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43433721843773305534939907 65150582765659958302409861)
  ·
    refine ⟨12215734268561242181701849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65150582765659958302409861 12215734268561242181701849)
    ·
      refine ⟨9161800701420931636276387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12215734268561242181701849 9161800701420931636276387)
      ·
        refine ⟨13742701052131397454414581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9161800701420931636276387 13742701052131397454414581)
        ·
          refine ⟨1288378223637318511351367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13742701052131397454414581 1288378223637318511351367)
          ·
            refine ⟨1932567335455977767027051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288378223637318511351367 1932567335455977767027051)
            ·
              refine ⟨2898851003183966650540577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932567335455977767027051 2898851003183966650540577)
              ·
                refine ⟨2174138252387974987905433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2898851003183966650540577 2174138252387974987905433)
                ·
                  refine ⟨1630603689290981240929075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174138252387974987905433 1630603689290981240929075)
                  ·
                    refine ⟨2445905533936471861393613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630603689290981240929075 2445905533936471861393613)
                    ·
                      refine ⟨917214575226176948022605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2445905533936471861393613 917214575226176948022605)
                      ·
                        rfl

theorem cell23_1786269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_1786269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786269 prefixEnd_1786269 := by exact prefixLift 1786269
  have htrace : WordTrace (prefixWord ++ tailWord_1786269) baseStart_1786269 baseEnd_1786269 := by
    simpa [prefixWord, tailWord_1786269, baseEnd_1786269] using wordTrace_append hprefix tailTrace_1786269
  have hstable : (prefixWord ++ tailWord_1786269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786269).length < 2 ^ (prefixWord ++ tailWord_1786269).sum := by decide
  have hdescent : baseEnd_1786269 < baseStart_1786269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786271 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1786271 : Nat := 118140960795 + 1786271 * 2 ^ 59
def prefixEnd_1786271 : Nat := 4983230072969 + 3 ^ 40 * 1786271 * 2
def baseEnd_1786271 : Nat := 917215602187485940197595

theorem tailTrace_1786271 : CollatzResearch.WordTrace tailWord_1786271 prefixEnd_1786271 917215602187485940197595 := by
  unfold tailWord_1786271
  simp only [CollatzResearch.WordTrace]
  refine ⟨65150655711652712643982667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43433770474435141762655111 65150655711652712643982667)
  ·
    refine ⟨97725983567479068965974001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65150655711652712643982667 97725983567479068965974001)
    ·
      refine ⟨73294487675609301724480501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97725983567479068965974001 73294487675609301724480501)
      ·
        refine ⟨6871358219588372036670047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73294487675609301724480501 6871358219588372036670047)
        ·
          refine ⟨10307037329382558055005071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871358219588372036670047 10307037329382558055005071)
          ·
            refine ⟨15460555994073837082507607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307037329382558055005071 15460555994073837082507607)
            ·
              refine ⟨23190833991110755623761411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15460555994073837082507607 23190833991110755623761411)
              ·
                refine ⟨34786250986666133435642117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23190833991110755623761411 34786250986666133435642117)
                ·
                  refine ⟨6522422059999900019182897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34786250986666133435642117 6522422059999900019182897)
                  ·
                    refine ⟨4891816544999925014387173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6522422059999900019182897 4891816544999925014387173)
                    ·
                      refine ⟨917215602187485940197595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4891816544999925014387173 917215602187485940197595)
                      ·
                        rfl

theorem cell23_1786271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1786271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786271 prefixEnd_1786271 := by exact prefixLift 1786271
  have htrace : WordTrace (prefixWord ++ tailWord_1786271) baseStart_1786271 baseEnd_1786271 := by
    simpa [prefixWord, tailWord_1786271, baseEnd_1786271] using wordTrace_append hprefix tailTrace_1786271
  have hstable : (prefixWord ++ tailWord_1786271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786271).length < 2 ^ (prefixWord ++ tailWord_1786271).sum := by decide
  have hdescent : baseEnd_1786271 < baseStart_1786271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786275 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 4, 2, 2]
def baseStart_1786275 : Nat := 118140960795 + 1786275 * 2 ^ 59
def prefixEnd_1786275 : Nat := 4983230072969 + 3 ^ 40 * 1786275 * 2
def baseEnd_1786275 : Nat := 917217656110103924547577

theorem tailTrace_1786275 : CollatzResearch.WordTrace tailWord_1786275 prefixEnd_1786275 917217656110103924547577 := by
  unfold tailWord_1786275
  simp only [CollatzResearch.WordTrace]
  refine ⟨65150801603638221327128279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43433867735758814218085519 65150801603638221327128279)
  ·
    refine ⟨97726202405457331990692419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65150801603638221327128279 97726202405457331990692419)
    ·
      refine ⟨146589303608185997986038629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97726202405457331990692419 146589303608185997986038629)
      ·
        refine ⟨27485494426534874622382243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146589303608185997986038629 27485494426534874622382243)
        ·
          refine ⟨41228241639802311933573365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27485494426534874622382243 41228241639802311933573365)
          ·
            refine ⟨3865147653731466743772503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41228241639802311933573365 3865147653731466743772503)
            ·
              refine ⟨5797721480597200115658755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865147653731466743772503 5797721480597200115658755)
              ·
                refine ⟨8696582220895800173488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797721480597200115658755 8696582220895800173488133)
                ·
                  refine ⟨1630609166417962532529025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8696582220895800173488133 1630609166417962532529025)
                  ·
                    refine ⟨1222956874813471899396769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1630609166417962532529025 1222956874813471899396769)
                    ·
                      refine ⟨917217656110103924547577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222956874813471899396769 917217656110103924547577)
                      ·
                        rfl

theorem cell23_1786275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_1786275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786275 prefixEnd_1786275 := by exact prefixLift 1786275
  have htrace : WordTrace (prefixWord ++ tailWord_1786275) baseStart_1786275 baseEnd_1786275 := by
    simpa [prefixWord, tailWord_1786275, baseEnd_1786275] using wordTrace_append hprefix tailTrace_1786275
  have hstable : (prefixWord ++ tailWord_1786275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786275).length < 2 ^ (prefixWord ++ tailWord_1786275).sum := by decide
  have hdescent : baseEnd_1786275 < baseStart_1786275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786311 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 1, 7]
def baseStart_1786311 : Nat := 118140960795 + 1786311 * 2 ^ 59
def prefixEnd_1786311 : Nat := 4983230072969 + 3 ^ 40 * 1786311 * 2
def baseEnd_1786311 : Nat := 305745380471221927899137

theorem tailTrace_1786311 : CollatzResearch.WordTrace tailWord_1786311 prefixEnd_1786311 305745380471221927899137 := by
  unfold tailWord_1786311
  simp only [CollatzResearch.WordTrace]
  refine ⟨65152114631507799475438787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43434743087671866316959191 65152114631507799475438787)
  ·
    refine ⟨97728171947261699213158181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65152114631507799475438787 97728171947261699213158181)
    ·
      refine ⟨18324032240111568602467159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97728171947261699213158181 18324032240111568602467159)
      ·
        refine ⟨27486048360167352903700739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18324032240111568602467159 27486048360167352903700739)
        ·
          refine ⟨41229072540251029355551109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27486048360167352903700739 41229072540251029355551109)
          ·
            refine ⟨7730451101297068004165833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41229072540251029355551109 7730451101297068004165833)
            ·
              refine ⟨5797838325972801003124375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7730451101297068004165833 5797838325972801003124375)
              ·
                refine ⟨8696757488959201504686563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5797838325972801003124375 8696757488959201504686563)
                ·
                  refine ⟨13045136233438802257029845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8696757488959201504686563 13045136233438802257029845)
                  ·
                    refine ⟨305745380471221927899137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13045136233438802257029845 305745380471221927899137)
                    ·
                      rfl

theorem cell23_1786311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_1786311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786311 prefixEnd_1786311 := by exact prefixLift 1786311
  have htrace : WordTrace (prefixWord ++ tailWord_1786311) baseStart_1786311 baseEnd_1786311 := by
    simpa [prefixWord, tailWord_1786311, baseEnd_1786311] using wordTrace_append hprefix tailTrace_1786311
  have hstable : (prefixWord ++ tailWord_1786311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786311).length < 2 ^ (prefixWord ++ tailWord_1786311).sum := by decide
  have hdescent : baseEnd_1786311 < baseStart_1786311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786318 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2]
def baseStart_1786318 : Nat := 118140960795 + 1786318 * 2 ^ 59
def prefixEnd_1786318 : Nat := 4983230072969 + 3 ^ 40 * 1786318 * 2
def baseEnd_1786318 : Nat := 917239735778247256309879

theorem tailTrace_1786318 : CollatzResearch.WordTrace tailWord_1786318 prefixEnd_1786318 917239735778247256309879 := by
  unfold tailWord_1786318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8144046242810304958867951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43434913294988293113962405 8144046242810304958867951)
  ·
    refine ⟨12216069364215457438301927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8144046242810304958867951 12216069364215457438301927)
    ·
      refine ⟨18324104046323186157452891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12216069364215457438301927 18324104046323186157452891)
      ·
        refine ⟨27486156069484779236179337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18324104046323186157452891 27486156069484779236179337)
        ·
          refine ⟨20614617052113584427134503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27486156069484779236179337 20614617052113584427134503)
          ·
            refine ⟨30921925578170376640701755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20614617052113584427134503 30921925578170376640701755)
            ·
              refine ⟨46382888367255564961052633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30921925578170376640701755 46382888367255564961052633)
              ·
                refine ⟨34787166275441673720789475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46382888367255564961052633 34787166275441673720789475)
                ·
                  refine ⟨52180749413162510581184213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34787166275441673720789475 52180749413162510581184213)
                  ·
                    refine ⟨1222986314370996341746505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52180749413162510581184213 1222986314370996341746505)
                    ·
                      refine ⟨917239735778247256309879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1222986314370996341746505 917239735778247256309879)
                      ·
                        rfl

theorem cell23_1786318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_1786318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786318 prefixEnd_1786318 := by exact prefixLift 1786318
  have htrace : WordTrace (prefixWord ++ tailWord_1786318) baseStart_1786318 baseEnd_1786318 := by
    simpa [prefixWord, tailWord_1786318, baseEnd_1786318] using wordTrace_append hprefix tailTrace_1786318
  have hstable : (prefixWord ++ tailWord_1786318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786318).length < 2 ^ (prefixWord ++ tailWord_1786318).sum := by decide
  have hdescent : baseEnd_1786318 < baseStart_1786318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786348 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_1786348 : Nat := 118140960795 + 1786348 * 2 ^ 59
def prefixEnd_1786348 : Nat := 4983230072969 + 3 ^ 40 * 1786348 * 2
def baseEnd_1786348 : Nat := 917255140197882138934741

theorem tailTrace_1786348 : CollatzResearch.WordTrace tailWord_1786348 prefixEnd_1786348 917255140197882138934741 := by
  unfold tailWord_1786348
  simp only [CollatzResearch.WordTrace]
  refine ⟨32576732066186877397267849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43435642754915836529690465 32576732066186877397267849)
  ·
    refine ⟨24432549049640158047950887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32576732066186877397267849 24432549049640158047950887)
    ·
      refine ⟨36648823574460237071926331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24432549049640158047950887 36648823574460237071926331)
      ·
        refine ⟨54973235361690355607889497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36648823574460237071926331 54973235361690355607889497)
        ·
          refine ⟨41229926521267766705917123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54973235361690355607889497 41229926521267766705917123)
          ·
            refine ⟨61844889781901650058875685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41229926521267766705917123 61844889781901650058875685)
            ·
              refine ⟨11595916834106559386039191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61844889781901650058875685 11595916834106559386039191)
              ·
                refine ⟨17393875251159839079058787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11595916834106559386039191 17393875251159839079058787)
                ·
                  refine ⟨26090812876739758618588181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17393875251159839079058787 26090812876739758618588181)
                  ·
                    refine ⟨1223006853597176185246321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26090812876739758618588181 1223006853597176185246321)
                    ·
                      refine ⟨917255140197882138934741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223006853597176185246321 917255140197882138934741)
                      ·
                        rfl

theorem cell23_1786348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_1786348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786348 prefixEnd_1786348 := by exact prefixLift 1786348
  have htrace : WordTrace (prefixWord ++ tailWord_1786348) baseStart_1786348 baseEnd_1786348 := by
    simpa [prefixWord, tailWord_1786348, baseEnd_1786348] using wordTrace_append hprefix tailTrace_1786348
  have hstable : (prefixWord ++ tailWord_1786348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786348).length < 2 ^ (prefixWord ++ tailWord_1786348).sum := by decide
  have hdescent : baseEnd_1786348 < baseStart_1786348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786361 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1786361 : Nat := 118140960795 + 1786361 * 2 ^ 59
def prefixEnd_1786361 : Nat := 4983230072969 + 3 ^ 40 * 1786361 * 2
def baseEnd_1786361 : Nat := 917261815446390588072181

theorem tailTrace_1786361 : CollatzResearch.WordTrace tailWord_1786361 prefixEnd_1786361 917261815446390588072181 := by
  unfold tailWord_1786361
  simp only [CollatzResearch.WordTrace]
  refine ⟨65153938281326658014758937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43435958854217772009839291 65153938281326658014758937)
  ·
    refine ⟨48865453710994993511069203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65153938281326658014758937 48865453710994993511069203)
    ·
      refine ⟨73298180566492490266603805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48865453710994993511069203 73298180566492490266603805)
      ·
        refine ⟨27486817712434683849976427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73298180566492490266603805 27486817712434683849976427)
        ·
          refine ⟨41230226568652025774964641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27486817712434683849976427 41230226568652025774964641)
          ·
            refine ⟨30922669926489019331223481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41230226568652025774964641 30922669926489019331223481)
            ·
              refine ⟨23192002444866764498417611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30922669926489019331223481 23192002444866764498417611)
              ·
                refine ⟨34788003667300146747626417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23192002444866764498417611 34788003667300146747626417)
                ·
                  refine ⟨26091002750475110060719813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34788003667300146747626417 26091002750475110060719813)
                  ·
                    refine ⟨4892063015714083136384965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26091002750475110060719813 4892063015714083136384965)
                    ·
                      refine ⟨917261815446390588072181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4892063015714083136384965 917261815446390588072181)
                      ·
                        rfl

theorem cell23_1786361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1786361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786361 prefixEnd_1786361 := by exact prefixLift 1786361
  have htrace : WordTrace (prefixWord ++ tailWord_1786361) baseStart_1786361 baseEnd_1786361 := by
    simpa [prefixWord, tailWord_1786361, baseEnd_1786361] using wordTrace_append hprefix tailTrace_1786361
  have hstable : (prefixWord ++ tailWord_1786361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786361).length < 2 ^ (prefixWord ++ tailWord_1786361).sum := by decide
  have hdescent : baseEnd_1786361 < baseStart_1786361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786392 : List Nat := [2, 1, 2, 3, 3, 2, 1, 4, 1, 4]
def baseStart_1786392 : Nat := 118140960795 + 1786392 * 2 ^ 59
def prefixEnd_1786392 : Nat := 4983230072969 + 3 ^ 40 * 1786392 * 2
def baseEnd_1786392 : Nat := 305759244448893322261513

theorem tailTrace_1786392 : CollatzResearch.WordTrace tailWord_1786392 prefixEnd_1786392 305759244448893322261513 := by
  unfold tailWord_1786392
  simp only [CollatzResearch.WordTrace]
  refine ⟨32577534472107175154568715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43436712629476233539424953 32577534472107175154568715)
  ·
    refine ⟨48866301708160762731853073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32577534472107175154568715 48866301708160762731853073)
    ·
      refine ⟨36649726281120572048889805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48866301708160762731853073 36649726281120572048889805)
      ·
        refine ⟨13743647355420214518333677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36649726281120572048889805 13743647355420214518333677)
        ·
          refine ⟨5153867758282580444375129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13743647355420214518333677 5153867758282580444375129)
          ·
            refine ⟨3865400818711935333281347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5153867758282580444375129 3865400818711935333281347)
            ·
              refine ⟨5798101228067902999922021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3865400818711935333281347 5798101228067902999922021)
              ·
                refine ⟨1087143980262731812485379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5798101228067902999922021 1087143980262731812485379)
                ·
                  refine ⟨1630715970394097718728069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087143980262731812485379 1630715970394097718728069)
                  ·
                    refine ⟨305759244448893322261513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630715970394097718728069 305759244448893322261513)
                    ·
                      rfl

theorem cell23_1786392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_1786392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786392 prefixEnd_1786392 := by exact prefixLift 1786392
  have htrace : WordTrace (prefixWord ++ tailWord_1786392) baseStart_1786392 baseEnd_1786392 := by
    simpa [prefixWord, tailWord_1786392, baseEnd_1786392] using wordTrace_append hprefix tailTrace_1786392
  have hstable : (prefixWord ++ tailWord_1786392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786392).length < 2 ^ (prefixWord ++ tailWord_1786392).sum := by decide
  have hdescent : baseEnd_1786392 < baseStart_1786392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786418 : List Nat := [3, 2, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1786418 : Nat := 118140960795 + 1786418 * 2 ^ 59
def prefixEnd_1786418 : Nat := 4983230072969 + 3 ^ 40 * 1786418 * 2
def baseEnd_1786418 : Nat := 305763694614565621686473

theorem tailTrace_1786418 : CollatzResearch.WordTrace tailWord_1786418 prefixEnd_1786418 305763694614565621686473 := by
  unfold tailWord_1786418
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289004310530039187395977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43437344828080104499722605 16289004310530039187395977)
  ·
    refine ⟨12216753232897529390546983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16289004310530039187395977 12216753232897529390546983)
    ·
      refine ⟨18325129849346294085820475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12216753232897529390546983 18325129849346294085820475)
      ·
        refine ⟨27487694774019441128730713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325129849346294085820475 27487694774019441128730713)
        ·
          refine ⟨20615771080514580846548035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27487694774019441128730713 20615771080514580846548035)
          ·
            refine ⟨30923656620771871269822053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20615771080514580846548035 30923656620771871269822053)
            ·
              refine ⟨5798185616394725863091635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30923656620771871269822053 5798185616394725863091635)
              ·
                refine ⟨8697278424592088794637453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798185616394725863091635 8697278424592088794637453)
                ·
                  refine ⟨3261479409222033297989045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8697278424592088794637453 3261479409222033297989045)
                  ·
                    refine ⟨305763694614565621686473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3261479409222033297989045 305763694614565621686473)
                    ·
                      rfl

theorem cell23_1786418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1786418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786418 prefixEnd_1786418 := by exact prefixLift 1786418
  have htrace : WordTrace (prefixWord ++ tailWord_1786418) baseStart_1786418 baseEnd_1786418 := by
    simpa [prefixWord, tailWord_1786418, baseEnd_1786418] using wordTrace_append hprefix tailTrace_1786418
  have hstable : (prefixWord ++ tailWord_1786418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786418).length < 2 ^ (prefixWord ++ tailWord_1786418).sum := by decide
  have hdescent : baseEnd_1786418 < baseStart_1786418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786425 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1786425 : Nat := 118140960795 + 1786425 * 2 ^ 59
def prefixEnd_1786425 : Nat := 4983230072969 + 3 ^ 40 * 1786425 * 2
def baseEnd_1786425 : Nat := 917294678208278337671887

theorem tailTrace_1786425 : CollatzResearch.WordTrace tailWord_1786425 prefixEnd_1786425 917294678208278337671887 := by
  unfold tailWord_1786425
  simp only [CollatzResearch.WordTrace]
  refine ⟨65156272553094796945088729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43437515035396531296725819 65156272553094796945088729)
  ·
    refine ⟨48867204414821097708816547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65156272553094796945088729 48867204414821097708816547)
    ·
      refine ⟨73300806622231646563224821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48867204414821097708816547 73300806622231646563224821)
      ·
        refine ⟨6871950620834216865302327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73300806622231646563224821 6871950620834216865302327)
        ·
          refine ⟨10307925931251325297953491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6871950620834216865302327 10307925931251325297953491)
          ·
            refine ⟨15461888896876987946930237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10307925931251325297953491 15461888896876987946930237)
            ·
              refine ⟨5798208336328870480098839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15461888896876987946930237 5798208336328870480098839)
              ·
                refine ⟨8697312504493305720148259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798208336328870480098839 8697312504493305720148259)
                ·
                  refine ⟨13045968756739958580222389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697312504493305720148259 13045968756739958580222389)
                  ·
                    refine ⟨1223059570944371116895849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13045968756739958580222389 1223059570944371116895849)
                    ·
                      refine ⟨917294678208278337671887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223059570944371116895849 917294678208278337671887)
                      ·
                        rfl

theorem cell23_1786425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1786425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786425 prefixEnd_1786425 := by exact prefixLift 1786425
  have htrace : WordTrace (prefixWord ++ tailWord_1786425) baseStart_1786425 baseEnd_1786425 := by
    simpa [prefixWord, tailWord_1786425, baseEnd_1786425] using wordTrace_append hprefix tailTrace_1786425
  have hstable : (prefixWord ++ tailWord_1786425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786425).length < 2 ^ (prefixWord ++ tailWord_1786425).sum := by decide
  have hdescent : baseEnd_1786425 < baseStart_1786425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786432 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 1, 1, 3]
def baseStart_1786432 : Nat := 118140960795 + 1786432 * 2 ^ 59
def prefixEnd_1786432 : Nat := 4983230072969 + 3 ^ 40 * 1786432 * 2
def baseEnd_1786432 : Nat := 917298272572859810284355

theorem tailTrace_1786432 : CollatzResearch.WordTrace tailWord_1786432 prefixEnd_1786432 917298272572859810284355 := by
  unfold tailWord_1786432
  simp only [CollatzResearch.WordTrace]
  refine ⟨32578263932034718570296775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43437685242712958093729033 32578263932034718570296775)
  ·
    refine ⟨48867395898052077855445163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32578263932034718570296775 48867395898052077855445163)
    ·
      refine ⟨73301093847078116783167745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48867395898052077855445163 73301093847078116783167745)
      ·
        refine ⟨54975820385308587587375809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73301093847078116783167745 54975820385308587587375809)
        ·
          refine ⟨41231865288981440690531857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54975820385308587587375809 41231865288981440690531857)
          ·
            refine ⟨30923898966736080517898893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41231865288981440690531857 30923898966736080517898893)
            ·
              refine ⟨11596462112526030194212085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30923898966736080517898893 11596462112526030194212085)
              ·
                refine ⟨1087168323049315330707383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11596462112526030194212085 1087168323049315330707383)
                ·
                  refine ⟨1630752484573972996061075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087168323049315330707383 1630752484573972996061075)
                  ·
                    refine ⟨2446128726860959494091613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1630752484573972996061075 2446128726860959494091613)
                    ·
                      refine ⟨917298272572859810284355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2446128726860959494091613 917298272572859810284355)
                      ·
                        rfl

theorem cell23_1786432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_1786432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786432 prefixEnd_1786432 := by exact prefixLift 1786432
  have htrace : WordTrace (prefixWord ++ tailWord_1786432) baseStart_1786432 baseEnd_1786432 := by
    simpa [prefixWord, tailWord_1786432, baseEnd_1786432] using wordTrace_append hprefix tailTrace_1786432
  have hstable : (prefixWord ++ tailWord_1786432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786432).length < 2 ^ (prefixWord ++ tailWord_1786432).sum := by decide
  have hdescent : baseEnd_1786432 < baseStart_1786432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786465 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_1786465 : Nat := 118140960795 + 1786465 * 2 ^ 59
def prefixEnd_1786465 : Nat := 4983230072969 + 3 ^ 40 * 1786465 * 2
def baseEnd_1786465 : Nat := 305771739144819393723901

theorem tailTrace_1786465 : CollatzResearch.WordTrace tailWord_1786465 prefixEnd_1786465 305771739144819393723901 := by
  unfold tailWord_1786465
  simp only [CollatzResearch.WordTrace]
  refine ⟨65157731472949883776544849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43438487648633255851029899 65157731472949883776544849)
  ·
    refine ⟨48868298604712412832408637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65157731472949883776544849 48868298604712412832408637)
    ·
      refine ⟨18325611976767154812153239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48868298604712412832408637 18325611976767154812153239)
      ·
        refine ⟨27488417965150732218229859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325611976767154812153239 27488417965150732218229859)
        ·
          refine ⟨41232626947726098327344789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27488417965150732218229859 41232626947726098327344789)
          ·
            refine ⟨1932779388174660859094287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41232626947726098327344789 1932779388174660859094287)
            ·
              refine ⟨2899169082261991288641431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932779388174660859094287 2899169082261991288641431)
              ·
                refine ⟨4348753623392986932962147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899169082261991288641431 4348753623392986932962147)
                ·
                  refine ⟨6523130435089480399443221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4348753623392986932962147 6523130435089480399443221)
                  ·
                    refine ⟨305771739144819393723901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6523130435089480399443221 305771739144819393723901)
                    ·
                      rfl

theorem cell23_1786465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_1786465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786465 prefixEnd_1786465 := by exact prefixLift 1786465
  have htrace : WordTrace (prefixWord ++ tailWord_1786465) baseStart_1786465 baseEnd_1786465 := by
    simpa [prefixWord, tailWord_1786465, baseEnd_1786465] using wordTrace_append hprefix tailTrace_1786465
  have hstable : (prefixWord ++ tailWord_1786465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786465).length < 2 ^ (prefixWord ++ tailWord_1786465).sum := by decide
  have hdescent : baseEnd_1786465 < baseStart_1786465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786468 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1786468 : Nat := 118140960795 + 1786468 * 2 ^ 59
def prefixEnd_1786468 : Nat := 4983230072969 + 3 ^ 40 * 1786468 * 2
def baseEnd_1786468 : Nat := 917316757876421669434189

theorem tailTrace_1786468 : CollatzResearch.WordTrace tailWord_1786468 prefixEnd_1786468 917316757876421669434189 := by
  unfold tailWord_1786468
  simp only [CollatzResearch.WordTrace]
  refine ⟨32578920445969507644452029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43438560594626010192602705 32578920445969507644452029)
  ·
    refine ⟨12217095167238565366669511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32578920445969507644452029 12217095167238565366669511)
    ·
      refine ⟨18325642750857848050004267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217095167238565366669511 18325642750857848050004267)
      ·
        refine ⟨27488464126286772075006401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18325642750857848050004267 27488464126286772075006401)
        ·
          refine ⟨20616348094715079056254801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27488464126286772075006401 20616348094715079056254801)
          ·
            refine ⟨15462261071036309292191101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20616348094715079056254801 15462261071036309292191101)
            ·
              refine ⟨5798347901638615984571663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15462261071036309292191101 5798347901638615984571663)
              ·
                refine ⟨8697521852457923976857495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798347901638615984571663 8697521852457923976857495)
                ·
                  refine ⟨13046282778686885965286243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8697521852457923976857495 13046282778686885965286243)
                  ·
                    refine ⟨19569424168030328947929365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13046282778686885965286243 19569424168030328947929365)
                    ·
                      refine ⟨917316757876421669434189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 19569424168030328947929365 917316757876421669434189)
                      ·
                        rfl

theorem cell23_1786468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1786468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786468 prefixEnd_1786468 := by exact prefixLift 1786468
  have htrace : WordTrace (prefixWord ++ tailWord_1786468) baseStart_1786468 baseEnd_1786468 := by
    simpa [prefixWord, tailWord_1786468, baseEnd_1786468] using wordTrace_append hprefix tailTrace_1786468
  have hstable : (prefixWord ++ tailWord_1786468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786468).length < 2 ^ (prefixWord ++ tailWord_1786468).sum := by decide
  have hdescent : baseEnd_1786468 < baseStart_1786468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786506 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_1786506 : Nat := 118140960795 + 1786506 * 2 ^ 59
def prefixEnd_1786506 : Nat := 4983230072969 + 3 ^ 40 * 1786506 * 2
def baseEnd_1786506 : Nat := 917336270141292520759015

theorem tailTrace_1786506 : CollatzResearch.WordTrace tailWord_1786506 prefixEnd_1786506 917336270141292520759015 := by
  unfold tailWord_1786506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16289806716450336944696843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43439484577200898519191581 16289806716450336944696843)
  ·
    refine ⟨24434710074675505417045265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16289806716450336944696843 24434710074675505417045265)
    ·
      refine ⟨18326032556006629062783949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24434710074675505417045265 18326032556006629062783949)
      ·
        refine ⟨6872262208502485898543981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18326032556006629062783949 6872262208502485898543981)
        ·
          refine ⟨2577098328188432211953993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6872262208502485898543981 2577098328188432211953993)
          ·
            refine ⟨1932823746141324158965495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2577098328188432211953993 1932823746141324158965495)
            ·
              refine ⟨2899235619211986238448243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932823746141324158965495 2899235619211986238448243)
              ·
                refine ⟨4348853428817979357672365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899235619211986238448243 4348853428817979357672365)
                ·
                  refine ⟨1630820035806742259127137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4348853428817979357672365 1630820035806742259127137)
                  ·
                    refine ⟨1223115026855056694345353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1630820035806742259127137 1223115026855056694345353)
                    ·
                      refine ⟨917336270141292520759015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223115026855056694345353 917336270141292520759015)
                      ·
                        rfl

theorem cell23_1786506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_1786506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786506 prefixEnd_1786506 := by exact prefixLift 1786506
  have htrace : WordTrace (prefixWord ++ tailWord_1786506) baseStart_1786506 baseEnd_1786506 := by
    simpa [prefixWord, tailWord_1786506, baseEnd_1786506] using wordTrace_append hprefix tailTrace_1786506
  have hstable : (prefixWord ++ tailWord_1786506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786506).length < 2 ^ (prefixWord ++ tailWord_1786506).sum := by decide
  have hdescent : baseEnd_1786506 < baseStart_1786506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786515 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 5, 3, 2]
def baseStart_1786515 : Nat := 118140960795 + 1786515 * 2 ^ 59
def prefixEnd_1786515 : Nat := 4983230072969 + 3 ^ 40 * 1786515 * 2
def baseEnd_1786515 : Nat := 917340891467182985546473

theorem tailTrace_1786515 : CollatzResearch.WordTrace tailWord_1786515 prefixEnd_1786515 917340891467182985546473 := by
  unfold tailWord_1786515
  simp only [CollatzResearch.WordTrace]
  refine ⟨65159555122768742315864999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43439703415179161543909999 65159555122768742315864999)
  ·
    refine ⟨97739332684153113473797499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65159555122768742315864999 97739332684153113473797499)
    ·
      refine ⟨146608999026229670210696249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97739332684153113473797499 146608999026229670210696249)
      ·
        refine ⟨109956749269672252658022187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146608999026229670210696249 109956749269672252658022187)
        ·
          refine ⟨164935123904508378987033281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109956749269672252658022187 164935123904508378987033281)
          ·
            refine ⟨123701342928381284240274961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164935123904508378987033281 123701342928381284240274961)
            ·
              refine ⟨92776007196285963180206221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123701342928381284240274961 92776007196285963180206221)
              ·
                refine ⟨34791002698607236192577333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92776007196285963180206221 34791002698607236192577333)
                ·
                  refine ⟨3261656502994428393054125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34791002698607236192577333 3261656502994428393054125)
                  ·
                    refine ⟨1223121188622910647395297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261656502994428393054125 1223121188622910647395297)
                    ·
                      refine ⟨917340891467182985546473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223121188622910647395297 917340891467182985546473)
                      ·
                        rfl

theorem cell23_1786515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3, 2].length) (baseStart_1786515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786515 prefixEnd_1786515 := by exact prefixLift 1786515
  have htrace : WordTrace (prefixWord ++ tailWord_1786515) baseStart_1786515 baseEnd_1786515 := by
    simpa [prefixWord, tailWord_1786515, baseEnd_1786515] using wordTrace_append hprefix tailTrace_1786515
  have hstable : (prefixWord ++ tailWord_1786515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786515).length < 2 ^ (prefixWord ++ tailWord_1786515).sum := by decide
  have hdescent : baseEnd_1786515 < baseStart_1786515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786516 : List Nat := [2, 4, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1786516 : Nat := 118140960795 + 1786516 * 2 ^ 59
def prefixEnd_1786516 : Nat := 4983230072969 + 3 ^ 40 * 1786516 * 2
def baseEnd_1786516 : Nat := 305780468315945827211323

theorem tailTrace_1786516 : CollatzResearch.WordTrace tailWord_1786516 prefixEnd_1786516 305780468315945827211323 := by
  unfold tailWord_1786516
  simp only [CollatzResearch.WordTrace]
  refine ⟨32579795797882559743325701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43439727730510079657767601 32579795797882559743325701)
  ·
    refine ⟨6108711712102979951873569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32579795797882559743325701 6108711712102979951873569)
    ·
      refine ⟨4581533784077234963905177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6108711712102979951873569 4581533784077234963905177)
      ·
        refine ⟨3436150338057926222928883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4581533784077234963905177 3436150338057926222928883)
        ·
          refine ⟨5154225507086889334393325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436150338057926222928883 5154225507086889334393325)
          ·
            refine ⟨1932834565157583500397497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5154225507086889334393325 1932834565157583500397497)
            ·
              refine ⟨1449625923868187625298123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932834565157583500397497 1449625923868187625298123)
              ·
                refine ⟨2174438885802281437947185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449625923868187625298123 2174438885802281437947185)
                ·
                  refine ⟨1630829164351711078460389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174438885802281437947185 1630829164351711078460389)
                  ·
                    refine ⟨305780468315945827211323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1630829164351711078460389 305780468315945827211323)
                    ·
                      rfl

theorem cell23_1786516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1786516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786516 prefixEnd_1786516 := by exact prefixLift 1786516
  have htrace : WordTrace (prefixWord ++ tailWord_1786516) baseStart_1786516 baseEnd_1786516 := by
    simpa [prefixWord, tailWord_1786516, baseEnd_1786516] using wordTrace_append hprefix tailTrace_1786516
  have hstable : (prefixWord ++ tailWord_1786516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786516).length < 2 ^ (prefixWord ++ tailWord_1786516).sum := by decide
  have hdescent : baseEnd_1786516 < baseStart_1786516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786532 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_1786532 : Nat := 118140960795 + 1786532 * 2 ^ 59
def prefixEnd_1786532 : Nat := 4983230072969 + 3 ^ 40 * 1786532 * 2
def baseEnd_1786532 : Nat := 917349620638309419033895

theorem tailTrace_1786532 : CollatzResearch.WordTrace tailWord_1786532 prefixEnd_1786532 917349620638309419033895 := by
  unfold tailWord_1786532
  simp only [CollatzResearch.WordTrace]
  refine ⟨32580087581853577109616925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43440116775804769479489233 32580087581853577109616925)
  ·
    refine ⟨12217532843195091416106347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32580087581853577109616925 12217532843195091416106347)
    ·
      refine ⟨18326299264792637124159521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12217532843195091416106347 18326299264792637124159521)
      ·
        refine ⟨13744724448594477843119641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18326299264792637124159521 13744724448594477843119641)
        ·
          refine ⟨10308543336445858382339731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13744724448594477843119641 10308543336445858382339731)
          ·
            refine ⟨15462815004668787573509597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10308543336445858382339731 15462815004668787573509597)
            ·
              refine ⟨5798555626750795340066099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15462815004668787573509597 5798555626750795340066099)
              ·
                refine ⟨8697833440126193010099149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5798555626750795340066099 8697833440126193010099149)
                ·
                  refine ⟨3261687540047322378787181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8697833440126193010099149 3261687540047322378787181)
                  ·
                    refine ⟨1223132827517745892045193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3261687540047322378787181 1223132827517745892045193)
                    ·
                      refine ⟨917349620638309419033895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223132827517745892045193 917349620638309419033895)
                      ·
                        rfl

theorem cell23_1786532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_1786532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786532 prefixEnd_1786532 := by exact prefixLift 1786532
  have htrace : WordTrace (prefixWord ++ tailWord_1786532) baseStart_1786532 baseEnd_1786532 := by
    simpa [prefixWord, tailWord_1786532, baseEnd_1786532] using wordTrace_append hprefix tailTrace_1786532
  have hstable : (prefixWord ++ tailWord_1786532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786532).length < 2 ^ (prefixWord ++ tailWord_1786532).sum := by decide
  have hdescent : baseEnd_1786532 < baseStart_1786532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786653 : List Nat := [1, 4, 2, 4, 2, 1, 1, 3, 5]
def baseStart_1786653 : Nat := 118140960795 + 1786653 * 2 ^ 59
def prefixEnd_1786653 : Nat := 4983230072969 + 3 ^ 40 * 1786653 * 2
def baseEnd_1786653 : Nat := 101934639088611493957871

theorem tailTrace_1786653 : CollatzResearch.WordTrace tailWord_1786653 prefixEnd_1786653 101934639088611493957871 := by
  unfold tailWord_1786653
  simp only [CollatzResearch.WordTrace]
  refine ⟨65164588396268791884388613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43443058930845861256259075 65164588396268791884388613)
  ·
    refine ⟨12218360324300398478322865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65164588396268791884388613 12218360324300398478322865)
    ·
      refine ⟨9163770243225298858742149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12218360324300398478322865 9163770243225298858742149)
      ·
        refine ⟨1718206920604743536014153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9163770243225298858742149 1718206920604743536014153)
        ·
          refine ⟨1288655190453557652010615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1718206920604743536014153 1288655190453557652010615)
          ·
            refine ⟨1932982785680336478015923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288655190453557652010615 1932982785680336478015923)
            ·
              refine ⟨2899474178520504717023885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1932982785680336478015923 2899474178520504717023885)
              ·
                refine ⟨1087302816945189268883957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2899474178520504717023885 1087302816945189268883957)
                ·
                  refine ⟨101934639088611493957871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1087302816945189268883957 101934639088611493957871)
                  ·
                    rfl

theorem cell23_1786653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_1786653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786653 prefixEnd_1786653 := by exact prefixLift 1786653
  have htrace : WordTrace (prefixWord ++ tailWord_1786653) baseStart_1786653 baseEnd_1786653 := by
    simpa [prefixWord, tailWord_1786653, baseEnd_1786653] using wordTrace_append hprefix tailTrace_1786653
  have hstable : (prefixWord ++ tailWord_1786653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786653).length < 2 ^ (prefixWord ++ tailWord_1786653).sum := by decide
  have hdescent : baseEnd_1786653 < baseStart_1786653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786675 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 8]
def baseStart_1786675 : Nat := 118140960795 + 1786675 * 2 ^ 59
def prefixEnd_1786675 : Nat := 4983230072969 + 3 ^ 40 * 1786675 * 2
def baseEnd_1786675 : Nat := 101935894263544706616193

theorem tailTrace_1786675 : CollatzResearch.WordTrace tailWord_1786675 prefixEnd_1786675 101935894263544706616193 := by
  unfold tailWord_1786675
  simp only [CollatzResearch.WordTrace]
  refine ⟨65165390802189089641689479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43443593868126059761126319 65165390802189089641689479)
  ·
    refine ⟨97748086203283634462534219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65165390802189089641689479 97748086203283634462534219)
    ·
      refine ⟨146622129304925451693801329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97748086203283634462534219 146622129304925451693801329)
      ·
        refine ⟨109966596978694088770350997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146622129304925451693801329 109966596978694088770350997)
        ·
          refine ⟨5154684233376285411110203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 109966596978694088770350997 5154684233376285411110203)
          ·
            refine ⟨7732026350064428116665305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5154684233376285411110203 7732026350064428116665305)
            ·
              refine ⟨5799019762548321087498979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7732026350064428116665305 5799019762548321087498979)
              ·
                refine ⟨8698529643822481631248469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799019762548321087498979 8698529643822481631248469)
                ·
                  refine ⟨101935894263544706616193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8698529643822481631248469 101935894263544706616193)
                  ·
                    rfl

theorem cell23_1786675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 8].length) (baseStart_1786675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786675 prefixEnd_1786675 := by exact prefixLift 1786675
  have htrace : WordTrace (prefixWord ++ tailWord_1786675) baseStart_1786675 baseEnd_1786675 := by
    simpa [prefixWord, tailWord_1786675, baseEnd_1786675] using wordTrace_append hprefix tailTrace_1786675
  have hstable : (prefixWord ++ tailWord_1786675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786675).length < 2 ^ (prefixWord ++ tailWord_1786675).sum := by decide
  have hdescent : baseEnd_1786675 < baseStart_1786675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786712 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2]
def baseStart_1786712 : Nat := 118140960795 + 1786712 * 2 ^ 59
def prefixEnd_1786712 : Nat := 4983230072969 + 3 ^ 40 * 1786712 * 2
def baseEnd_1786712 : Nat := 917442047156118714783067

theorem tailTrace_1786712 : CollatzResearch.WordTrace tailWord_1786712 prefixEnd_1786712 917442047156118714783067 := by
  unfold tailWord_1786712
  simp only [CollatzResearch.WordTrace]
  refine ⟨32583370151527522480393195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43444493535370029973857593 32583370151527522480393195)
  ·
    refine ⟨48875055227291283720589793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32583370151527522480393195 48875055227291283720589793)
    ·
      refine ⟨36656291420468462790442345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48875055227291283720589793 36656291420468462790442345)
      ·
        refine ⟨27492218565351347092831759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36656291420468462790442345 27492218565351347092831759)
        ·
          refine ⟨41238327848027020639247639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27492218565351347092831759 41238327848027020639247639)
          ·
            refine ⟨61857491772040530958871459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41238327848027020639247639 61857491772040530958871459)
            ·
              refine ⟨92786237658060796438307189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61857491772040530958871459 92786237658060796438307189)
              ·
                refine ⟨8698709780443199666091299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92786237658060796438307189 8698709780443199666091299)
                ·
                  refine ⟨13048064670664799499136949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8698709780443199666091299 13048064670664799499136949)
                  ·
                    refine ⟨1223256062874824953044089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13048064670664799499136949 1223256062874824953044089)
                    ·
                      refine ⟨917442047156118714783067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223256062874824953044089 917442047156118714783067)
                      ·
                        rfl

theorem cell23_1786712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_1786712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786712 prefixEnd_1786712 := by exact prefixLift 1786712
  have htrace : WordTrace (prefixWord ++ tailWord_1786712) baseStart_1786712 baseEnd_1786712 := by
    simpa [prefixWord, tailWord_1786712, baseEnd_1786712] using wordTrace_append hprefix tailTrace_1786712
  have hstable : (prefixWord ++ tailWord_1786712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786712).length < 2 ^ (prefixWord ++ tailWord_1786712).sum := by decide
  have hdescent : baseEnd_1786712 < baseStart_1786712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786770 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1786770 : Nat := 118140960795 + 1786770 * 2 ^ 59
def prefixEnd_1786770 : Nat := 4983230072969 + 3 ^ 40 * 1786770 * 2
def baseEnd_1786770 : Nat := 917471829034079487857801

theorem tailTrace_1786770 : CollatzResearch.WordTrace tailWord_1786770 prefixEnd_1786770 917471829034079487857801 := by
  unfold tailWord_1786770
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292213934211230216599441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43445903824563280577598509 16292213934211230216599441)
  ·
    refine ⟨12219160450658422662449581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16292213934211230216599441 12219160450658422662449581)
    ·
      refine ⟨4582185168996908498418593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12219160450658422662449581 4582185168996908498418593)
      ·
        refine ⟨3436638876747681373813945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4582185168996908498418593 3436638876747681373813945)
        ·
          refine ⟨2577479157560761030360459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436638876747681373813945 2577479157560761030360459)
          ·
            refine ⟨3866218736341141545540689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2577479157560761030360459 3866218736341141545540689)
            ·
              refine ⟨2899664052255856159155517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3866218736341141545540689 2899664052255856159155517)
              ·
                refine ⟨1087374019595946059683319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2899664052255856159155517 1087374019595946059683319)
                ·
                  refine ⟨1631061029393919089524979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1087374019595946059683319 1631061029393919089524979)
                  ·
                    refine ⟨2446591544090878634287469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1631061029393919089524979 2446591544090878634287469)
                    ·
                      refine ⟨917471829034079487857801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2446591544090878634287469 917471829034079487857801)
                      ·
                        rfl

theorem cell23_1786770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1786770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786770 prefixEnd_1786770 := by exact prefixLift 1786770
  have htrace : WordTrace (prefixWord ++ tailWord_1786770) baseStart_1786770 baseEnd_1786770 := by
    simpa [prefixWord, tailWord_1786770, baseEnd_1786770] using wordTrace_append hprefix tailTrace_1786770
  have hstable : (prefixWord ++ tailWord_1786770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786770).length < 2 ^ (prefixWord ++ tailWord_1786770).sum := by decide
  have hdescent : baseEnd_1786770 < baseStart_1786770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786786 : List Nat := [3, 3, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1786786 : Nat := 118140960795 + 1786786 * 2 ^ 59
def prefixEnd_1786786 : Nat := 4983230072969 + 3 ^ 40 * 1786786 * 2
def baseEnd_1786786 : Nat := 305826681574850475085909

theorem tailTrace_1786786 : CollatzResearch.WordTrace tailWord_1786786 prefixEnd_1786786 305826681574850475085909 := by
  unfold tailWord_1786786
  simp only [CollatzResearch.WordTrace]
  refine ⟨16292359826196738899745053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 43446292869857970399320141 16292359826196738899745053)
  ·
    refine ⟨6109634934823777087404395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16292359826196738899745053 6109634934823777087404395)
    ·
      refine ⟨9164452402235665631106593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109634934823777087404395 9164452402235665631106593)
      ·
        refine ⟨6873339301676749223329945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9164452402235665631106593 6873339301676749223329945)
        ·
          refine ⟨5155004476257561917497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6873339301676749223329945 5155004476257561917497459)
          ·
            refine ⟨7732506714386342876246189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5155004476257561917497459 7732506714386342876246189)
            ·
              refine ⟨2899690017894878578592321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732506714386342876246189 2899690017894878578592321)
              ·
                refine ⟨2174767513421158933944241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899690017894878578592321 2174767513421158933944241)
                ·
                  refine ⟨1631075635065869200458181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2174767513421158933944241 1631075635065869200458181)
                  ·
                    refine ⟨305826681574850475085909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1631075635065869200458181 305826681574850475085909)
                    ·
                      rfl

theorem cell23_1786786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1786786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786786 prefixEnd_1786786 := by exact prefixLift 1786786
  have htrace : WordTrace (prefixWord ++ tailWord_1786786) baseStart_1786786 baseEnd_1786786 := by
    simpa [prefixWord, tailWord_1786786, baseEnd_1786786] using wordTrace_append hprefix tailTrace_1786786
  have hstable : (prefixWord ++ tailWord_1786786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786786).length < 2 ^ (prefixWord ++ tailWord_1786786).sum := by decide
  have hdescent : baseEnd_1786786 < baseStart_1786786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786809 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1786809 : Nat := 118140960795 + 1786809 * 2 ^ 59
def prefixEnd_1786809 : Nat := 4983230072969 + 3 ^ 40 * 1786809 * 2
def baseEnd_1786809 : Nat := 917491854779604835270121

theorem tailTrace_1786809 : CollatzResearch.WordTrace tailWord_1786809 prefixEnd_1786809 917491854779604835270121 := by
  unfold tailWord_1786809
  simp only [CollatzResearch.WordTrace]
  refine ⟨65170278183703630527067481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43446852122469087018044987 65170278183703630527067481)
  ·
    refine ⟨48877708637777722895300611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65170278183703630527067481 48877708637777722895300611)
    ·
      refine ⟨73316562956666584342950917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48877708637777722895300611 73316562956666584342950917)
      ·
        refine ⟨13746855554374984564303297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73316562956666584342950917 13746855554374984564303297)
        ·
          refine ⟨10310141665781238423227473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13746855554374984564303297 10310141665781238423227473)
          ·
            refine ⟨7732606249335928817420605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10310141665781238423227473 7732606249335928817420605)
            ·
              refine ⟨2899727343500973306532727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7732606249335928817420605 2899727343500973306532727)
              ·
                refine ⟨4349591015251459959799091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899727343500973306532727 4349591015251459959799091)
                ·
                  refine ⟨6524386522877189939698637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4349591015251459959799091 6524386522877189939698637)
                  ·
                    refine ⟨2446644946078946227386989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6524386522877189939698637 2446644946078946227386989)
                    ·
                      refine ⟨917491854779604835270121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2446644946078946227386989 917491854779604835270121)
                      ·
                        rfl

theorem cell23_1786809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1786809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786809 prefixEnd_1786809 := by exact prefixLift 1786809
  have htrace : WordTrace (prefixWord ++ tailWord_1786809) baseStart_1786809 baseEnd_1786809 := by
    simpa [prefixWord, tailWord_1786809, baseEnd_1786809] using wordTrace_append hprefix tailTrace_1786809
  have hstable : (prefixWord ++ tailWord_1786809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786809).length < 2 ^ (prefixWord ++ tailWord_1786809).sum := by decide
  have hdescent : baseEnd_1786809 < baseStart_1786809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786815 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1786815 : Nat := 118140960795 + 1786815 * 2 ^ 59
def prefixEnd_1786815 : Nat := 4983230072969 + 3 ^ 40 * 1786815 * 2
def baseEnd_1786815 : Nat := 917494935663531811795093

theorem tailTrace_1786815 : CollatzResearch.WordTrace tailWord_1786815 prefixEnd_1786815 917494935663531811795093 := by
  unfold tailWord_1786815
  simp only [CollatzResearch.WordTrace]
  refine ⟨65170497021681893551785899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 43446998014454595701190599 65170497021681893551785899)
  ·
    refine ⟨97755745532522840327678849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65170497021681893551785899 97755745532522840327678849)
    ·
      refine ⟨73316809149392130245759137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97755745532522840327678849 73316809149392130245759137)
      ·
        refine ⟨54987606862044097684319353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73316809149392130245759137 54987606862044097684319353)
        ·
          refine ⟨41240705146533073263239515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54987606862044097684319353 41240705146533073263239515)
          ·
            refine ⟨61861057719799609894859273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41240705146533073263239515 61861057719799609894859273)
            ·
              refine ⟨46395793289849707421144455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61861057719799609894859273 46395793289849707421144455)
              ·
                refine ⟨69593689934774561131716683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46395793289849707421144455 69593689934774561131716683)
                ·
                  refine ⟨104390534902161841697575025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69593689934774561131716683 104390534902161841697575025)
                  ·
                    refine ⟨78292901176621381273181269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104390534902161841697575025 78292901176621381273181269)
                    ·
                      refine ⟨917494935663531811795093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 78292901176621381273181269 917494935663531811795093)
                      ·
                        rfl

theorem cell23_1786815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1786815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786815 prefixEnd_1786815 := by exact prefixLift 1786815
  have htrace : WordTrace (prefixWord ++ tailWord_1786815) baseStart_1786815 baseEnd_1786815 := by
    simpa [prefixWord, tailWord_1786815, baseEnd_1786815] using wordTrace_append hprefix tailTrace_1786815
  have hstable : (prefixWord ++ tailWord_1786815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786815).length < 2 ^ (prefixWord ++ tailWord_1786815).sum := by decide
  have hdescent : baseEnd_1786815 < baseStart_1786815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786870 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_1786870 : Nat := 118140960795 + 1786870 * 2 ^ 59
def prefixEnd_1786870 : Nat := 4983230072969 + 3 ^ 40 * 1786870 * 2
def baseEnd_1786870 : Nat := 917523177099529096607341

theorem tailTrace_1786870 : CollatzResearch.WordTrace tailWord_1786870 prefixEnd_1786870 917523177099529096607341 := by
  unfold tailWord_1786870
  simp only [CollatzResearch.WordTrace]
  refine ⟨4073281439780164871564879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 43448335357655091963358709 4073281439780164871564879)
  ·
    refine ⟨6109922159670247307347319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4073281439780164871564879 6109922159670247307347319)
    ·
      refine ⟨9164883239505370961020979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109922159670247307347319 9164883239505370961020979)
      ·
        refine ⟨13747324859258056441531469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9164883239505370961020979 13747324859258056441531469)
        ·
          refine ⟨5155246822221771165574301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13747324859258056441531469 5155246822221771165574301)
          ·
            refine ⟨1933217558333164187090363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5155246822221771165574301 1933217558333164187090363)
            ·
              refine ⟨2899826337499746280635545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933217558333164187090363 2899826337499746280635545)
              ·
                refine ⟨2174869753124809710476659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899826337499746280635545 2174869753124809710476659)
                ·
                  refine ⟨3262304629687214565714989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2174869753124809710476659 3262304629687214565714989)
                  ·
                    refine ⟨1223364236132705462143121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3262304629687214565714989 1223364236132705462143121)
                    ·
                      refine ⟨917523177099529096607341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223364236132705462143121 917523177099529096607341)
                      ·
                        rfl

theorem cell23_1786870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_1786870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786870 prefixEnd_1786870 := by exact prefixLift 1786870
  have htrace : WordTrace (prefixWord ++ tailWord_1786870) baseStart_1786870 baseEnd_1786870 := by
    simpa [prefixWord, tailWord_1786870, baseEnd_1786870] using wordTrace_append hprefix tailTrace_1786870
  have hstable : (prefixWord ++ tailWord_1786870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786870).length < 2 ^ (prefixWord ++ tailWord_1786870).sum := by decide
  have hdescent : baseEnd_1786870 < baseStart_1786870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786916 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1786916 : Nat := 118140960795 + 1786916 * 2 ^ 59
def prefixEnd_1786916 : Nat := 4983230072969 + 3 ^ 40 * 1786916 * 2
def baseEnd_1786916 : Nat := 917546797209635916632129

theorem tailTrace_1786916 : CollatzResearch.WordTrace tailWord_1786916 prefixEnd_1786916 917546797209635916632129 := by
  unfold tailWord_1786916
  simp only [CollatzResearch.WordTrace]
  refine ⟨32587090397157993900606301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43449453862877325200808401 32587090397157993900606301)
  ·
    refine ⟨12220158898934247712727363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32587090397157993900606301 12220158898934247712727363)
    ·
      refine ⟨18330238348401371569091045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12220158898934247712727363 18330238348401371569091045)
      ·
        refine ⟨3436919690325257169204571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18330238348401371569091045 3436919690325257169204571)
        ·
          refine ⟨5155379535487885753806857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3436919690325257169204571 5155379535487885753806857)
          ·
            refine ⟨3866534651615914315355143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5155379535487885753806857 3866534651615914315355143)
            ·
              refine ⟨5799801977423871473032715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3866534651615914315355143 5799801977423871473032715)
              ·
                refine ⟨8699702966135807209549073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5799801977423871473032715 8699702966135807209549073)
                ·
                  refine ⟨6524777224601855407161805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8699702966135807209549073 6524777224601855407161805)
                  ·
                    refine ⟨2446791459225695777685677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6524777224601855407161805 2446791459225695777685677)
                    ·
                      refine ⟨917546797209635916632129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2446791459225695777685677 917546797209635916632129)
                      ·
                        rfl

theorem cell23_1786916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1786916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786916 prefixEnd_1786916 := by exact prefixLift 1786916
  have htrace : WordTrace (prefixWord ++ tailWord_1786916) baseStart_1786916 baseEnd_1786916 := by
    simpa [prefixWord, tailWord_1786916, baseEnd_1786916] using wordTrace_append hprefix tailTrace_1786916
  have hstable : (prefixWord ++ tailWord_1786916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786916).length < 2 ^ (prefixWord ++ tailWord_1786916).sum := by decide
  have hdescent : baseEnd_1786916 < baseStart_1786916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786926 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1786926 : Nat := 118140960795 + 1786926 * 2 ^ 59
def prefixEnd_1786926 : Nat := 4983230072969 + 3 ^ 40 * 1786926 * 2
def baseEnd_1786926 : Nat := 917551932016180877507083

theorem tailTrace_1786926 : CollatzResearch.WordTrace tailWord_1786926 prefixEnd_1786926 917551932016180877507083 := by
  unfold tailWord_1786926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8146818190534969938634579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 43449697016186506339384421 8146818190534969938634579)
  ·
    refine ⟨12220227285802454907951869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8146818190534969938634579 12220227285802454907951869)
    ·
      refine ⟨4582585232175920590481951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12220227285802454907951869 4582585232175920590481951)
      ·
        refine ⟨6873877848263880885722927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4582585232175920590481951 6873877848263880885722927)
        ·
          refine ⟨10310816772395821328584391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6873877848263880885722927 10310816772395821328584391)
          ·
            refine ⟨15466225158593731992876587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10310816772395821328584391 15466225158593731992876587)
            ·
              refine ⟨23199337737890597989314881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15466225158593731992876587 23199337737890597989314881)
              ·
                refine ⟨17399503303417948491986161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23199337737890597989314881 17399503303417948491986161)
                ·
                  refine ⟨13049627477563461368989621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17399503303417948491986161 13049627477563461368989621)
                  ·
                    refine ⟨1223402576021574503342777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13049627477563461368989621 1223402576021574503342777)
                    ·
                      refine ⟨917551932016180877507083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1223402576021574503342777 917551932016180877507083)
                      ·
                        rfl

theorem cell23_1786926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1786926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786926 prefixEnd_1786926 := by exact prefixLift 1786926
  have htrace : WordTrace (prefixWord ++ tailWord_1786926) baseStart_1786926 baseEnd_1786926 := by
    simpa [prefixWord, tailWord_1786926, baseEnd_1786926] using wordTrace_append hprefix tailTrace_1786926
  have hstable : (prefixWord ++ tailWord_1786926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786926).length < 2 ^ (prefixWord ++ tailWord_1786926).sum := by decide
  have hdescent : baseEnd_1786926 < baseStart_1786926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1786936 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_1786936 : Nat := 118140960795 + 1786936 * 2 ^ 59
def prefixEnd_1786936 : Nat := 4983230072969 + 3 ^ 40 * 1786936 * 2
def baseEnd_1786936 : Nat := 305852355607575279460679

theorem tailTrace_1786936 : CollatzResearch.WordTrace tailWord_1786936 prefixEnd_1786936 305852355607575279460679 := by
  unfold tailWord_1786936
  simp only [CollatzResearch.WordTrace]
  refine ⟨32587455127121765608470331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 43449940169495687477960441 32587455127121765608470331)
  ·
    refine ⟨48881182690682648412705497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32587455127121765608470331 48881182690682648412705497)
    ·
      refine ⟨36660887018011986309529123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48881182690682648412705497 36660887018011986309529123)
      ·
        refine ⟨54991330527017979464293685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36660887018011986309529123 54991330527017979464293685)
        ·
          refine ⟨5155437236907935574777533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54991330527017979464293685 5155437236907935574777533)
          ·
            refine ⟨1933288963840475840541575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5155437236907935574777533 1933288963840475840541575)
            ·
              refine ⟨2899933445760713760812363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933288963840475840541575 2899933445760713760812363)
              ·
                refine ⟨4349900168641070641218545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2899933445760713760812363 4349900168641070641218545)
                ·
                  refine ⟨3262425126480802980913909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4349900168641070641218545 3262425126480802980913909)
                  ·
                    refine ⟨305852355607575279460679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3262425126480802980913909 305852355607575279460679)
                    ·
                      rfl

theorem cell23_1786936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_1786936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1786936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1786936 prefixEnd_1786936 := by exact prefixLift 1786936
  have htrace : WordTrace (prefixWord ++ tailWord_1786936) baseStart_1786936 baseEnd_1786936 := by
    simpa [prefixWord, tailWord_1786936, baseEnd_1786936] using wordTrace_append hprefix tailTrace_1786936
  have hstable : (prefixWord ++ tailWord_1786936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1786936).length < 2 ^ (prefixWord ++ tailWord_1786936).sum := by decide
  have hdescent : baseEnd_1786936 < baseStart_1786936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1786936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
