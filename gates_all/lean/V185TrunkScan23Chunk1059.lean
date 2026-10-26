import V185TrunkScan23Chunk1058

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6269118 : List Nat := [4, 2, 1, 1, 4, 1, 10]
def baseStart_6269118 : Nat := 118140960795 + 6269118 * 2 ^ 59
def prefixEnd_6269118 : Nat := 4983230072969 + 3 ^ 40 * 6269118 * 2
def baseEnd_6269118 : Nat := 39741614984608744206097

theorem tailTrace_6269118 : CollatzResearch.WordTrace tailWord_6269118 prefixEnd_6269118 39741614984608744206097 := by
  unfold tailWord_6269118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28581689762757955119789001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152435678734709093972208005 28581689762757955119789001)
  ·
    refine ⟨21436267322068466339841751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28581689762757955119789001 21436267322068466339841751)
    ·
      refine ⟨32154400983102699509762627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21436267322068466339841751 32154400983102699509762627)
      ·
        refine ⟨48231601474654049264643941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32154400983102699509762627 48231601474654049264643941)
        ·
          refine ⟨9043425276497634237120739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48231601474654049264643941 9043425276497634237120739)
          ·
            refine ⟨13565137914746451355681109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043425276497634237120739 13565137914746451355681109)
            ·
              refine ⟨39741614984608744206097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13565137914746451355681109 39741614984608744206097)
              ·
                rfl

theorem cell23_6269118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 10].length) (baseStart_6269118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269118 prefixEnd_6269118 := by exact prefixLift 6269118
  have htrace : WordTrace (prefixWord ++ tailWord_6269118) baseStart_6269118 baseEnd_6269118 := by
    simpa [prefixWord, tailWord_6269118, baseEnd_6269118] using wordTrace_append hprefix tailTrace_6269118
  have hstable : (prefixWord ++ tailWord_6269118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269118).length < 2 ^ (prefixWord ++ tailWord_6269118).sum := by decide
  have hdescent : baseEnd_6269118 < baseStart_6269118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269142 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_6269142 : Nat := 118140960795 + 6269142 * 2 ^ 59
def prefixEnd_6269142 : Nat := 4983230072969 + 3 ^ 40 * 6269142 * 2
def baseEnd_6269142 : Nat := 3219083137289016186793747

theorem tailTrace_6269142 : CollatzResearch.WordTrace tailWord_6269142 prefixEnd_6269142 3219083137289016186793747 := by
  unfold tailWord_6269142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14290899590873543316074105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152436262302651128704790453 14290899590873543316074105)
  ·
    refine ⟨10718174693155157487055579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14290899590873543316074105 10718174693155157487055579)
    ·
      refine ⟨16077262039732736230583369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718174693155157487055579 16077262039732736230583369)
      ·
        refine ⟨12057946529799552172937527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16077262039732736230583369 12057946529799552172937527)
        ·
          refine ⟨18086919794699328259406291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12057946529799552172937527 18086919794699328259406291)
          ·
            refine ⟨27130379692048992389109437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18086919794699328259406291 27130379692048992389109437)
            ·
              refine ⟨10173892384518372145916039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27130379692048992389109437 10173892384518372145916039)
              ·
                refine ⟨15260838576777558218874059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173892384518372145916039 15260838576777558218874059)
                ·
                  refine ⟨22891257865166337328311089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15260838576777558218874059 22891257865166337328311089)
                  ·
                    refine ⟨17168443398874752996233317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22891257865166337328311089 17168443398874752996233317)
                    ·
                      refine ⟨3219083137289016186793747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17168443398874752996233317 3219083137289016186793747)
                      ·
                        rfl

theorem cell23_6269142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_6269142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269142 prefixEnd_6269142 := by exact prefixLift 6269142
  have htrace : WordTrace (prefixWord ++ tailWord_6269142) baseStart_6269142 baseEnd_6269142 := by
    simpa [prefixWord, tailWord_6269142, baseEnd_6269142] using wordTrace_append hprefix tailTrace_6269142
  have hstable : (prefixWord ++ tailWord_6269142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269142).length < 2 ^ (prefixWord ++ tailWord_6269142).sum := by decide
  have hdescent : baseEnd_6269142 < baseStart_6269142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269145 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 3]
def baseStart_6269145 : Nat := 118140960795 + 6269145 * 2 ^ 59
def prefixEnd_6269145 : Nat := 4983230072969 + 3 ^ 40 * 6269145 * 2
def baseEnd_6269145 : Nat := 3219084677730979675056233

theorem tailTrace_6269145 : CollatzResearch.WordTrace tailWord_6269145 prefixEnd_6269145 3219084677730979675056233 := by
  unfold tailWord_6269145
  simp only [CollatzResearch.WordTrace]
  refine ⟨228654502872965824569544889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152436335248643883046363259 228654502872965824569544889)
  ·
    refine ⟨171490877154724368427158667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228654502872965824569544889 171490877154724368427158667)
    ·
      refine ⟨257236315732086552640738001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171490877154724368427158667 257236315732086552640738001)
      ·
        refine ⟨192927236799064914480553501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257236315732086552640738001 192927236799064914480553501)
        ·
          refine ⟨72347713799649342930207563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192927236799064914480553501 72347713799649342930207563)
          ·
            refine ⟨108521570699474014395311345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72347713799649342930207563 108521570699474014395311345)
            ·
              refine ⟨81391178024605510796483509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108521570699474014395311345 81391178024605510796483509)
              ·
                refine ⟨7630422939806766637170329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81391178024605510796483509 7630422939806766637170329)
                ·
                  refine ⟨5722817204855074977877747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7630422939806766637170329 5722817204855074977877747)
                  ·
                    refine ⟨8584225807282612466816621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5722817204855074977877747 8584225807282612466816621)
                    ·
                      refine ⟨3219084677730979675056233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584225807282612466816621 3219084677730979675056233)
                      ·
                        rfl

theorem cell23_6269145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_6269145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269145 prefixEnd_6269145 := by exact prefixLift 6269145
  have htrace : WordTrace (prefixWord ++ tailWord_6269145) baseStart_6269145 baseEnd_6269145 := by
    simpa [prefixWord, tailWord_6269145, baseEnd_6269145] using wordTrace_append hprefix tailTrace_6269145
  have hstable : (prefixWord ++ tailWord_6269145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269145).length < 2 ^ (prefixWord ++ tailWord_6269145).sum := by decide
  have hdescent : baseEnd_6269145 < baseStart_6269145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269198 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6269198 : Nat := 118140960795 + 6269198 * 2 ^ 59
def prefixEnd_6269198 : Nat := 4983230072969 + 3 ^ 40 * 6269198 * 2
def baseEnd_6269198 : Nat := 3219111892205667967693489

theorem tailTrace_6269198 : CollatzResearch.WordTrace tailWord_6269198 prefixEnd_6269198 3219111892205667967693489 := by
  unfold tailWord_6269198
  simp only [CollatzResearch.WordTrace]
  refine ⟨28582054492721726827653031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152437623961182543080816165 28582054492721726827653031)
  ·
    refine ⟨42873081739082590241479547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28582054492721726827653031 42873081739082590241479547)
    ·
      refine ⟨64309622608623885362219321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42873081739082590241479547 64309622608623885362219321)
      ·
        refine ⟨48232216956467914021664491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64309622608623885362219321 48232216956467914021664491)
        ·
          refine ⟨72348325434701871032496737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48232216956467914021664491 72348325434701871032496737)
          ·
            refine ⟨54261244076026403274372553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72348325434701871032496737 54261244076026403274372553)
            ·
              refine ⟨40695933057019802455779415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54261244076026403274372553 40695933057019802455779415)
              ·
                refine ⟨61043899585529703683669123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40695933057019802455779415 61043899585529703683669123)
                ·
                  refine ⟨91565849378294555525503685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61043899585529703683669123 91565849378294555525503685)
                  ·
                    refine ⟨17168596758430229161031941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91565849378294555525503685 17168596758430229161031941)
                    ·
                      refine ⟨3219111892205667967693489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17168596758430229161031941 3219111892205667967693489)
                      ·
                        rfl

theorem cell23_6269198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6269198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269198 prefixEnd_6269198 := by exact prefixLift 6269198
  have htrace : WordTrace (prefixWord ++ tailWord_6269198) baseStart_6269198 baseEnd_6269198 := by
    simpa [prefixWord, tailWord_6269198, baseEnd_6269198] using wordTrace_append hprefix tailTrace_6269198
  have hstable : (prefixWord ++ tailWord_6269198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269198).length < 2 ^ (prefixWord ++ tailWord_6269198).sum := by decide
  have hdescent : baseEnd_6269198 < baseStart_6269198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269236 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_6269236 : Nat := 118140960795 + 6269236 * 2 ^ 59
def prefixEnd_6269236 : Nat := 4983230072969 + 3 ^ 40 * 6269236 * 2
def baseEnd_6269236 : Nat := 3219131404470538819018315

theorem tailTrace_6269236 : CollatzResearch.WordTrace tailWord_6269236 prefixEnd_6269236 3219131404470538819018315 := by
  unfold tailWord_6269236
  simp only [CollatzResearch.WordTrace]
  refine ⟨114328910957818073555553781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152438547943757431407405041 114328910957818073555553781)
  ·
    refine ⟨10718335402295444395833167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114328910957818073555553781 10718335402295444395833167)
    ·
      refine ⟨16077503103443166593749751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718335402295444395833167 16077503103443166593749751)
      ·
        refine ⟨24116254655164749890624627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16077503103443166593749751 24116254655164749890624627)
        ·
          refine ⟨36174381982747124835936941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24116254655164749890624627 36174381982747124835936941)
          ·
            refine ⟨13565393243530171813476353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36174381982747124835936941 13565393243530171813476353)
            ·
              refine ⟨10174044932647628860107265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13565393243530171813476353 10174044932647628860107265)
              ·
                refine ⟨7630533699485721645080449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10174044932647628860107265 7630533699485721645080449)
                ·
                  refine ⟨5722900274614291233810337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7630533699485721645080449 5722900274614291233810337)
                  ·
                    refine ⟨4292175205960718425357753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5722900274614291233810337 4292175205960718425357753)
                    ·
                      refine ⟨3219131404470538819018315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292175205960718425357753 3219131404470538819018315)
                      ·
                        rfl

theorem cell23_6269236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_6269236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269236 prefixEnd_6269236 := by exact prefixLift 6269236
  have htrace : WordTrace (prefixWord ++ tailWord_6269236) baseStart_6269236 baseEnd_6269236 := by
    simpa [prefixWord, tailWord_6269236, baseEnd_6269236] using wordTrace_append hprefix tailTrace_6269236
  have hstable : (prefixWord ++ tailWord_6269236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269236).length < 2 ^ (prefixWord ++ tailWord_6269236).sum := by decide
  have hdescent : baseEnd_6269236 < baseStart_6269236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269242 : List Nat := [3, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_6269242 : Nat := 118140960795 + 6269242 * 2 ^ 59
def prefixEnd_6269242 : Nat := 4983230072969 + 3 ^ 40 * 6269242 * 2
def baseEnd_6269242 : Nat := 357681609483829532838143

theorem tailTrace_6269242 : CollatzResearch.WordTrace tailWord_6269242 prefixEnd_6269242 357681609483829532838143 := by
  unfold tailWord_6269242
  simp only [CollatzResearch.WordTrace]
  refine ⟨57164510188403602533956495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152438693835742940090550653 57164510188403602533956495)
  ·
    refine ⟨85746765282605403800934743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57164510188403602533956495 85746765282605403800934743)
    ·
      refine ⟨128620147923908105701402115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85746765282605403800934743 128620147923908105701402115)
      ·
        refine ⟨192930221885862158552103173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128620147923908105701402115 192930221885862158552103173)
        ·
          refine ⟨36174416603599154728519345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192930221885862158552103173 36174416603599154728519345)
          ·
            refine ⟨27130812452699366046389509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36174416603599154728519345 27130812452699366046389509)
            ·
              refine ⟨5087027334881131133698033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27130812452699366046389509 5087027334881131133698033)
              ·
                refine ⟨3815270501160848350273525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087027334881131133698033 3815270501160848350273525)
                ·
                  refine ⟨357681609483829532838143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3815270501160848350273525 357681609483829532838143)
                  ·
                    rfl

theorem cell23_6269242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_6269242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269242 prefixEnd_6269242 := by exact prefixLift 6269242
  have htrace : WordTrace (prefixWord ++ tailWord_6269242) baseStart_6269242 baseEnd_6269242 := by
    simpa [prefixWord, tailWord_6269242, baseEnd_6269242] using wordTrace_append hprefix tailTrace_6269242
  have hstable : (prefixWord ++ tailWord_6269242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269242).length < 2 ^ (prefixWord ++ tailWord_6269242).sum := by decide
  have hdescent : baseEnd_6269242 < baseStart_6269242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269336 : List Nat := [2, 1, 2, 5, 1, 3, 1, 3, 1, 4]
def baseStart_6269336 : Nat := 118140960795 + 6269336 * 2 ^ 59
def prefixEnd_6269336 : Nat := 4983230072969 + 3 ^ 40 * 6269336 * 2
def baseEnd_6269336 : Nat := 1073060917511996142589285

theorem tailTrace_6269336 : CollatzResearch.WordTrace tailWord_6269336 prefixEnd_6269336 1073060917511996142589285 := by
  unfold tailWord_6269336
  simp only [CollatzResearch.WordTrace]
  refine ⟨114330734607636932094873931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152440979476849242793165241 114330734607636932094873931)
  ·
    refine ⟨171496101911455398142310897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114330734607636932094873931 171496101911455398142310897)
    ·
      refine ⟨128622076433591548606733173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171496101911455398142310897 128622076433591548606733173)
      ·
        refine ⟨12058319665649207681881235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128622076433591548606733173 12058319665649207681881235)
        ·
          refine ⟨18087479498473811522821853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12058319665649207681881235 18087479498473811522821853)
          ·
            refine ⟨6782804811927679321058195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18087479498473811522821853 6782804811927679321058195)
            ·
              refine ⟨10174207217891518981587293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782804811927679321058195 10174207217891518981587293)
              ·
                refine ⟨3815327706709319618095235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10174207217891518981587293 3815327706709319618095235)
                ·
                  refine ⟨5722991560063979427142853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815327706709319618095235 5722991560063979427142853)
                  ·
                    refine ⟨1073060917511996142589285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5722991560063979427142853 1073060917511996142589285)
                    ·
                      rfl

theorem cell23_6269336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_6269336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269336 prefixEnd_6269336 := by exact prefixLift 6269336
  have htrace : WordTrace (prefixWord ++ tailWord_6269336) baseStart_6269336 baseEnd_6269336 := by
    simpa [prefixWord, tailWord_6269336, baseEnd_6269336] using wordTrace_append hprefix tailTrace_6269336
  have hstable : (prefixWord ++ tailWord_6269336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269336).length < 2 ^ (prefixWord ++ tailWord_6269336).sum := by decide
  have hdescent : baseEnd_6269336 < baseStart_6269336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269410 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6269410 : Nat := 118140960795 + 6269410 * 2 ^ 59
def prefixEnd_6269410 : Nat := 4983230072969 + 3 ^ 40 * 6269410 * 2
def baseEnd_6269410 : Nat := 3219220750104421138242515

theorem tailTrace_6269410 : CollatzResearch.WordTrace tailWord_6269410 prefixEnd_6269410 3219220750104421138242515 := by
  unfold tailWord_6269410
  simp only [CollatzResearch.WordTrace]
  refine ⟨57166042054251443706985421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152442778811337183218627789 57166042054251443706985421)
  ·
    refine ⟨21437265770344291390119533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57166042054251443706985421 21437265770344291390119533)
    ·
      refine ⟨8038974663879109271294825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21437265770344291390119533 8038974663879109271294825)
      ·
        refine ⟨6029230997909331953471119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038974663879109271294825 6029230997909331953471119)
        ·
          refine ⟨9043846496863997930206679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029230997909331953471119 9043846496863997930206679)
          ·
            refine ⟨13565769745295996895310019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043846496863997930206679 13565769745295996895310019)
            ·
              refine ⟨20348654617943995342965029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565769745295996895310019 20348654617943995342965029)
              ·
                refine ⟨3815372740864499126805943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20348654617943995342965029 3815372740864499126805943)
                ·
                  refine ⟨5723059111296748690208915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815372740864499126805943 5723059111296748690208915)
                  ·
                    refine ⟨8584588666945123035313373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723059111296748690208915 8584588666945123035313373)
                    ·
                      refine ⟨3219220750104421138242515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584588666945123035313373 3219220750104421138242515)
                      ·
                        rfl

theorem cell23_6269410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6269410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269410 prefixEnd_6269410 := by exact prefixLift 6269410
  have htrace : WordTrace (prefixWord ++ tailWord_6269410) baseStart_6269410 baseEnd_6269410 := by
    simpa [prefixWord, tailWord_6269410, baseEnd_6269410] using wordTrace_append hprefix tailTrace_6269410
  have hstable : (prefixWord ++ tailWord_6269410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269410).length < 2 ^ (prefixWord ++ tailWord_6269410).sum := by decide
  have hdescent : baseEnd_6269410 < baseStart_6269410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269422 : List Nat := [4, 1, 2, 1, 2, 4, 1, 8]
def baseStart_6269422 : Nat := 118140960795 + 6269422 * 2 ^ 59
def prefixEnd_6269422 : Nat := 4983230072969 + 3 ^ 40 * 6269422 * 2
def baseEnd_6269422 : Nat := 119230626365639818196017

theorem tailTrace_6269422 : CollatzResearch.WordTrace tailWord_6269422 prefixEnd_6269422 119230626365639818196017 := by
  unfold tailWord_6269422
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583075736620287609672315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152443070595308200584919013 28583075736620287609672315)
  ·
    refine ⟨42874613604930431414508473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28583075736620287609672315 42874613604930431414508473)
    ·
      refine ⟨32155960203697823560881355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42874613604930431414508473 32155960203697823560881355)
      ·
        refine ⟨48233940305546735341322033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32155960203697823560881355 48233940305546735341322033)
        ·
          refine ⟨36175455229160051505991525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48233940305546735341322033 36175455229160051505991525)
          ·
            refine ⟨6782897855467509657373411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36175455229160051505991525 6782897855467509657373411)
            ·
              refine ⟨10174346783201264486060117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6782897855467509657373411 10174346783201264486060117)
              ·
                refine ⟨119230626365639818196017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10174346783201264486060117 119230626365639818196017)
                ·
                  rfl

theorem cell23_6269422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_6269422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269422 prefixEnd_6269422 := by exact prefixLift 6269422
  have htrace : WordTrace (prefixWord ++ tailWord_6269422) baseStart_6269422 baseEnd_6269422 := by
    simpa [prefixWord, tailWord_6269422, baseEnd_6269422] using wordTrace_append hprefix tailTrace_6269422
  have hstable : (prefixWord ++ tailWord_6269422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269422).length < 2 ^ (prefixWord ++ tailWord_6269422).sum := by decide
  have hdescent : baseEnd_6269422 < baseStart_6269422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269432 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_6269432 : Nat := 118140960795 + 6269432 * 2 ^ 59
def prefixEnd_6269432 : Nat := 4983230072969 + 3 ^ 40 * 6269432 * 2
def baseEnd_6269432 : Nat := 3219232046678820052167413

theorem tailTrace_6269432 : CollatzResearch.WordTrace tailWord_6269432 prefixEnd_6269432 3219232046678820052167413 := by
  unfold tailWord_6269432
  simp only [CollatzResearch.WordTrace]
  refine ⟨114332485311463036292621275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152443313748617381723495033 114332485311463036292621275)
  ·
    refine ⟨171498727967194554438931913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114332485311463036292621275 171498727967194554438931913)
    ·
      refine ⟨128624045975395915829198935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171498727967194554438931913 128624045975395915829198935)
      ·
        refine ⟨192936068963093873743798403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128624045975395915829198935 192936068963093873743798403)
        ·
          refine ⟨289404103444640810615697605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192936068963093873743798403 289404103444640810615697605)
          ·
            refine ⟨54263269395870151990443301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289404103444640810615697605 54263269395870151990443301)
            ·
              refine ⟨10174363011725653498208119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54263269395870151990443301 10174363011725653498208119)
              ·
                refine ⟨15261544517588480247312179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174363011725653498208119 15261544517588480247312179)
                ·
                  refine ⟨22892316776382720370968269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15261544517588480247312179 22892316776382720370968269)
                  ·
                    refine ⟨8584618791143520139113101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22892316776382720370968269 8584618791143520139113101)
                    ·
                      refine ⟨3219232046678820052167413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584618791143520139113101 3219232046678820052167413)
                      ·
                        rfl

theorem cell23_6269432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_6269432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269432 prefixEnd_6269432 := by exact prefixLift 6269432
  have htrace : WordTrace (prefixWord ++ tailWord_6269432) baseStart_6269432 baseEnd_6269432 := by
    simpa [prefixWord, tailWord_6269432, baseEnd_6269432] using wordTrace_append hprefix tailTrace_6269432
  have hstable : (prefixWord ++ tailWord_6269432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269432).length < 2 ^ (prefixWord ++ tailWord_6269432).sum := by decide
  have hdescent : baseEnd_6269432 < baseStart_6269432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269453 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6269453 : Nat := 118140960795 + 6269453 * 2 ^ 59
def prefixEnd_6269453 : Nat := 4983230072969 + 3 ^ 40 * 6269453 * 2
def baseEnd_6269453 : Nat := 3219242829772564470004817

theorem tailTrace_6269453 : CollatzResearch.WordTrace tailWord_6269453 prefixEnd_6269453 3219242829772564470004817 := by
  unfold tailWord_6269453
  simp only [CollatzResearch.WordTrace]
  refine ⟨228665736555849993171757013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152443824370566662114504675 228665736555849993171757013)
  ·
    refine ⟨5359353200527734214963055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 228665736555849993171757013 5359353200527734214963055)
    ·
      refine ⟨8039029800791601322444583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359353200527734214963055 8039029800791601322444583)
      ·
        refine ⟨12058544701187401983666875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8039029800791601322444583 12058544701187401983666875)
        ·
          refine ⟨18087817051781102975500313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12058544701187401983666875 18087817051781102975500313)
          ·
            refine ⟨13565862788835827231625235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18087817051781102975500313 13565862788835827231625235)
            ·
              refine ⟨20348794183253740847437853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13565862788835827231625235 20348794183253740847437853)
              ·
                refine ⟨7630797818720152817789195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20348794183253740847437853 7630797818720152817789195)
                ·
                  refine ⟨11446196728080229226683793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630797818720152817789195 11446196728080229226683793)
                  ·
                    refine ⟨8584647546060171920012845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11446196728080229226683793 8584647546060171920012845)
                    ·
                      refine ⟨3219242829772564470004817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584647546060171920012845 3219242829772564470004817)
                      ·
                        rfl

theorem cell23_6269453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6269453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269453 prefixEnd_6269453 := by exact prefixLift 6269453
  have htrace : WordTrace (prefixWord ++ tailWord_6269453) baseStart_6269453 baseEnd_6269453 := by
    simpa [prefixWord, tailWord_6269453, baseEnd_6269453] using wordTrace_append hprefix tailTrace_6269453
  have hstable : (prefixWord ++ tailWord_6269453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269453).length < 2 ^ (prefixWord ++ tailWord_6269453).sum := by decide
  have hdescent : baseEnd_6269453 < baseStart_6269453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269459 : List Nat := [1, 1, 1, 2, 1, 5, 3, 3, 1, 3, 2]
def baseStart_6269459 : Nat := 118140960795 + 6269459 * 2 ^ 59
def prefixEnd_6269459 : Nat := 4983230072969 + 3 ^ 40 * 6269459 * 2
def baseEnd_6269459 : Nat := 3219245910656491446529789

theorem tailTrace_6269459 : CollatzResearch.WordTrace tailWord_6269459 prefixEnd_6269459 3219245910656491446529789 := by
  unfold tailWord_6269459
  simp only [CollatzResearch.WordTrace]
  refine ⟨228665955393828256196475431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152443970262552170797650287 228665955393828256196475431)
  ·
    refine ⟨342998933090742384294713147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228665955393828256196475431 342998933090742384294713147)
    ·
      refine ⟨514498399636113576442069721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342998933090742384294713147 514498399636113576442069721)
      ·
        refine ⟨385873799727085182331552291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514498399636113576442069721 385873799727085182331552291)
        ·
          refine ⟨578810699590627773497328437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385873799727085182331552291 578810699590627773497328437)
          ·
            refine ⟨54263503086621353765374541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 578810699590627773497328437 54263503086621353765374541)
            ·
              refine ⟨20348813657483007662015453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54263503086621353765374541 20348813657483007662015453)
              ·
                refine ⟨7630805121556127873255795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20348813657483007662015453 7630805121556127873255795)
                ·
                  refine ⟨11446207682334191809883693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7630805121556127873255795 11446207682334191809883693)
                  ·
                    refine ⟨4292327880875321928706385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11446207682334191809883693 4292327880875321928706385)
                    ·
                      refine ⟨3219245910656491446529789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292327880875321928706385 3219245910656491446529789)
                      ·
                        rfl

theorem cell23_6269459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 3, 2].length) (baseStart_6269459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269459 prefixEnd_6269459 := by exact prefixLift 6269459
  have htrace : WordTrace (prefixWord ++ tailWord_6269459) baseStart_6269459 baseEnd_6269459 := by
    simpa [prefixWord, tailWord_6269459, baseEnd_6269459] using wordTrace_append hprefix tailTrace_6269459
  have hstable : (prefixWord ++ tailWord_6269459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269459).length < 2 ^ (prefixWord ++ tailWord_6269459).sum := by decide
  have hdescent : baseEnd_6269459 < baseStart_6269459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269482 : List Nat := [3, 1, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_6269482 : Nat := 118140960795 + 6269482 * 2 ^ 59
def prefixEnd_6269482 : Nat := 4983230072969 + 3 ^ 40 * 6269482 * 2
def baseEnd_6269482 : Nat := 1073085906903848285514061

theorem tailTrace_6269482 : CollatzResearch.WordTrace tailWord_6269482 prefixEnd_6269482 1073085906903848285514061 := by
  unfold tailWord_6269482
  simp only [CollatzResearch.WordTrace]
  refine ⟨57166698568186232781140675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152444529515163287416375133 57166698568186232781140675)
  ·
    refine ⟨85750047852279349171711013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57166698568186232781140675 85750047852279349171711013)
    ·
      refine ⟨16078133972302377969695815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85750047852279349171711013 16078133972302377969695815)
      ·
        refine ⟨24117200958453566954543723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16078133972302377969695815 24117200958453566954543723)
        ·
          refine ⟨36175801437680350431815585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24117200958453566954543723 36175801437680350431815585)
          ·
            refine ⟨27131851078260262823861689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36175801437680350431815585 27131851078260262823861689)
            ·
              refine ⟨20348888308695197117896267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27131851078260262823861689 20348888308695197117896267)
              ·
                refine ⟨30523332463042795676844401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20348888308695197117896267 30523332463042795676844401)
                ·
                  refine ⟨22892499347282096757633301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30523332463042795676844401 22892499347282096757633301)
                  ·
                    refine ⟨1073085906903848285514061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22892499347282096757633301 1073085906903848285514061)
                    ·
                      rfl

theorem cell23_6269482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_6269482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269482 prefixEnd_6269482 := by exact prefixLift 6269482
  have htrace : WordTrace (prefixWord ++ tailWord_6269482) baseStart_6269482 baseEnd_6269482 := by
    simpa [prefixWord, tailWord_6269482, baseEnd_6269482] using wordTrace_append hprefix tailTrace_6269482
  have hstable : (prefixWord ++ tailWord_6269482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269482).length < 2 ^ (prefixWord ++ tailWord_6269482).sum := by decide
  have hdescent : baseEnd_6269482 < baseStart_6269482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269489 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_6269489 : Nat := 118140960795 + 6269489 * 2 ^ 59
def prefixEnd_6269489 : Nat := 4983230072969 + 3 ^ 40 * 6269489 * 2
def baseEnd_6269489 : Nat := 3219261315076126329154651

theorem tailTrace_6269489 : CollatzResearch.WordTrace tailWord_6269489 prefixEnd_6269489 3219261315076126329154651 := by
  unfold tailWord_6269489
  simp only [CollatzResearch.WordTrace]
  refine ⟨228667049583719571320067521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152444699722479714213378347 228667049583719571320067521)
  ·
    refine ⟨171500287187789678490050641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228667049583719571320067521 171500287187789678490050641)
    ·
      refine ⟨128625215390842258867537981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171500287187789678490050641 128625215390842258867537981)
      ·
        refine ⟨48234455771565847075326743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128625215390842258867537981 48234455771565847075326743)
        ·
          refine ⟨72351683657348770612990115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48234455771565847075326743 72351683657348770612990115)
          ·
            refine ⟨108527525486023155919485173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72351683657348770612990115 108527525486023155919485173)
            ·
              refine ⟨10174455514314670867451735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108527525486023155919485173 10174455514314670867451735)
              ·
                refine ⟨15261683271472006301177603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174455514314670867451735 15261683271472006301177603)
                ·
                  refine ⟨22892524907208009451766405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15261683271472006301177603 22892524907208009451766405)
                  ·
                    refine ⟨4292348420101501772206201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22892524907208009451766405 4292348420101501772206201)
                    ·
                      refine ⟨3219261315076126329154651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292348420101501772206201 3219261315076126329154651)
                      ·
                        rfl

theorem cell23_6269489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_6269489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269489 prefixEnd_6269489 := by exact prefixLift 6269489
  have htrace : WordTrace (prefixWord ++ tailWord_6269489) baseStart_6269489 baseEnd_6269489 := by
    simpa [prefixWord, tailWord_6269489, baseEnd_6269489] using wordTrace_append hprefix tailTrace_6269489
  have hstable : (prefixWord ++ tailWord_6269489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269489).length < 2 ^ (prefixWord ++ tailWord_6269489).sum := by decide
  have hdescent : baseEnd_6269489 < baseStart_6269489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269495 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 7]
def baseStart_6269495 : Nat := 118140960795 + 6269495 * 2 ^ 59
def prefixEnd_6269495 : Nat := 4983230072969 + 3 ^ 40 * 6269495 * 2
def baseEnd_6269495 : Nat := 357696043995561478408847

theorem tailTrace_6269495 : CollatzResearch.WordTrace tailWord_6269495 prefixEnd_6269495 357696043995561478408847 := by
  unfold tailWord_6269495
  simp only [CollatzResearch.WordTrace]
  refine ⟨228667268421697834344785939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152444845614465222896523959 228667268421697834344785939)
  ·
    refine ⟨343000902632546751517178909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228667268421697834344785939 343000902632546751517178909)
    ·
      refine ⟨128625338487205031818942091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343000902632546751517178909 128625338487205031818942091)
      ·
        refine ⟨192938007730807547728413137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128625338487205031818942091 192938007730807547728413137)
        ·
          refine ⟨144703505798105660796309853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192938007730807547728413137 144703505798105660796309853)
          ·
            refine ⟨54263814674289622798616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144703505798105660796309853 54263814674289622798616195)
            ·
              refine ⟨81395722011434434197924293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54263814674289622798616195 81395722011434434197924293)
              ·
                refine ⟨15261697877143956412110805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81395722011434434197924293 15261697877143956412110805)
                ·
                  refine ⟨357696043995561478408847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15261697877143956412110805 357696043995561478408847)
                  ·
                    rfl

theorem cell23_6269495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 7].length) (baseStart_6269495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269495 prefixEnd_6269495 := by exact prefixLift 6269495
  have htrace : WordTrace (prefixWord ++ tailWord_6269495) baseStart_6269495 baseEnd_6269495 := by
    simpa [prefixWord, tailWord_6269495, baseEnd_6269495] using wordTrace_append hprefix tailTrace_6269495
  have hstable : (prefixWord ++ tailWord_6269495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269495).length < 2 ^ (prefixWord ++ tailWord_6269495).sum := by decide
  have hdescent : baseEnd_6269495 < baseStart_6269495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269534 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6269534 : Nat := 118140960795 + 6269534 * 2 ^ 59
def prefixEnd_6269534 : Nat := 4983230072969 + 3 ^ 40 * 6269534 * 2
def baseEnd_6269534 : Nat := 3219284421705578653091945

theorem tailTrace_6269534 : CollatzResearch.WordTrace tailWord_6269534 prefixEnd_6269534 3219284421705578653091945 := by
  unfold tailWord_6269534
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583586358569568000681957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152445793912371029336970437 28583586358569568000681957)
  ·
    refine ⟨5359422442231794000127867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28583586358569568000681957 5359422442231794000127867)
    ·
      refine ⟨8039133663347691000191801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359422442231794000127867 8039133663347691000191801)
      ·
        refine ⟨6029350247510768250143851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8039133663347691000191801 6029350247510768250143851)
        ·
          refine ⟨9044025371266152375215777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029350247510768250143851 9044025371266152375215777)
          ·
            refine ⟨6783019028449614281411833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044025371266152375215777 6783019028449614281411833)
            ·
              refine ⟨5087264271337210711058875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6783019028449614281411833 5087264271337210711058875)
              ·
                refine ⟨7630896407005816066588313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087264271337210711058875 7630896407005816066588313)
                ·
                  refine ⟨5723172305254362049941235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7630896407005816066588313 5723172305254362049941235)
                  ·
                    refine ⟨8584758457881543074911853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723172305254362049941235 8584758457881543074911853)
                    ·
                      refine ⟨3219284421705578653091945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584758457881543074911853 3219284421705578653091945)
                      ·
                        rfl

theorem cell23_6269534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6269534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269534 prefixEnd_6269534 := by exact prefixLift 6269534
  have htrace : WordTrace (prefixWord ++ tailWord_6269534) baseStart_6269534 baseEnd_6269534 := by
    simpa [prefixWord, tailWord_6269534, baseEnd_6269534] using wordTrace_append hprefix tailTrace_6269534
  have hstable : (prefixWord ++ tailWord_6269534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269534).length < 2 ^ (prefixWord ++ tailWord_6269534).sum := by decide
  have hdescent : baseEnd_6269534 < baseStart_6269534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269582 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6269582 : Nat := 118140960795 + 6269582 * 2 ^ 59
def prefixEnd_6269582 : Nat := 4983230072969 + 3 ^ 40 * 6269582 * 2
def baseEnd_6269582 : Nat := 3219309068776994465291723

theorem tailTrace_6269582 : CollatzResearch.WordTrace tailWord_6269582 prefixEnd_6269582 3219309068776994465291723 := by
  unfold tailWord_6269582
  simp only [CollatzResearch.WordTrace]
  refine ⟨28583805196547831025400375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152446961048255098802135333 28583805196547831025400375)
  ·
    refine ⟨42875707794821746538100563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28583805196547831025400375 42875707794821746538100563)
    ·
      refine ⟨64313561692232619807150845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42875707794821746538100563 64313561692232619807150845)
      ·
        refine ⟨24117585634587232427681567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64313561692232619807150845 24117585634587232427681567)
        ·
          refine ⟨36176378451880848641522351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24117585634587232427681567 36176378451880848641522351)
          ·
            refine ⟨54264567677821272962283527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36176378451880848641522351 54264567677821272962283527)
            ·
              refine ⟨81396851516731909443425291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54264567677821272962283527 81396851516731909443425291)
              ·
                refine ⟨122095277275097864165137937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81396851516731909443425291 122095277275097864165137937)
                ·
                  refine ⟨91571457956323398123853453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122095277275097864165137937 91571457956323398123853453)
                  ·
                    refine ⟨34339296733621274296445045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91571457956323398123853453 34339296733621274296445045)
                    ·
                      refine ⟨3219309068776994465291723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34339296733621274296445045 3219309068776994465291723)
                      ·
                        rfl

theorem cell23_6269582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6269582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269582 prefixEnd_6269582 := by exact prefixLift 6269582
  have htrace : WordTrace (prefixWord ++ tailWord_6269582) baseStart_6269582 baseEnd_6269582 := by
    simpa [prefixWord, tailWord_6269582, baseEnd_6269582] using wordTrace_append hprefix tailTrace_6269582
  have hstable : (prefixWord ++ tailWord_6269582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269582).length < 2 ^ (prefixWord ++ tailWord_6269582).sum := by decide
  have hdescent : baseEnd_6269582 < baseStart_6269582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269585 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 12]
def baseStart_6269585 : Nat := 118140960795 + 6269585 * 2 ^ 59
def prefixEnd_6269585 : Nat := 4983230072969 + 3 ^ 40 * 6269585 * 2
def baseEnd_6269585 : Nat := 357701178802106439283801

theorem tailTrace_6269585 : CollatzResearch.WordTrace tailWord_6269585 prefixEnd_6269585 357701178802106439283801 := by
  unfold tailWord_6269585
  simp only [CollatzResearch.WordTrace]
  refine ⟨228670550991371779715562209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152447033994247853143708139 228670550991371779715562209)
  ·
    refine ⟨171502913243528834786671657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228670550991371779715562209 171502913243528834786671657)
    ·
      refine ⟨128627184932646626090003743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171502913243528834786671657 128627184932646626090003743)
      ·
        refine ⟨192940777398969939135005615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128627184932646626090003743 192940777398969939135005615)
        ·
          refine ⟨289411166098454908702508423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192940777398969939135005615 289411166098454908702508423)
          ·
            refine ⟨434116749147682363053762635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289411166098454908702508423 434116749147682363053762635)
            ·
              refine ⟨651175123721523544580643953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434116749147682363053762635 651175123721523544580643953)
              ·
                refine ⟨488381342791142658435482965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651175123721523544580643953 488381342791142658435482965)
                ·
                  refine ⟨357701178802106439283801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 488381342791142658435482965 357701178802106439283801)
                  ·
                    rfl

theorem cell23_6269585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_6269585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269585 prefixEnd_6269585 := by exact prefixLift 6269585
  have htrace : WordTrace (prefixWord ++ tailWord_6269585) baseStart_6269585 baseEnd_6269585 := by
    simpa [prefixWord, tailWord_6269585, baseEnd_6269585] using wordTrace_append hprefix tailTrace_6269585
  have hstable : (prefixWord ++ tailWord_6269585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269585).length < 2 ^ (prefixWord ++ tailWord_6269585).sum := by decide
  have hdescent : baseEnd_6269585 < baseStart_6269585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_6269595 : Nat := 118140960795 + 6269595 * 2 ^ 59
def prefixEnd_6269595 : Nat := 4983230072969 + 3 ^ 40 * 6269595 * 2
def baseEnd_6269595 : Nat := 3219315744025502914429163

theorem tailTrace_6269595 : CollatzResearch.WordTrace tailWord_6269595 prefixEnd_6269595 3219315744025502914429163 := by
  unfold tailWord_6269595
  simp only [CollatzResearch.WordTrace]
  refine ⟨228670915721335551423426239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152447277147557034282284159 228670915721335551423426239)
  ·
    refine ⟨343006373582003327135139359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228670915721335551423426239 343006373582003327135139359)
    ·
      refine ⟨514509560373004990702709039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343006373582003327135139359 514509560373004990702709039)
      ·
        refine ⟨771764340559507486054063559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514509560373004990702709039 771764340559507486054063559)
        ·
          refine ⟨1157646510839261229081095339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771764340559507486054063559 1157646510839261229081095339)
          ·
            refine ⟨1736469766258891843621643009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157646510839261229081095339 1736469766258891843621643009)
            ·
              refine ⟨1302352324694168882716232257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736469766258891843621643009 1302352324694168882716232257)
              ·
                refine ⟨976764243520626662037174193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302352324694168882716232257 976764243520626662037174193)
                ·
                  refine ⟨732573182640469996527880645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 976764243520626662037174193 732573182640469996527880645)
                  ·
                    refine ⟨137357471745088124348977621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732573182640469996527880645 137357471745088124348977621)
                    ·
                      refine ⟨3219315744025502914429163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137357471745088124348977621 3219315744025502914429163)
                      ·
                        rfl

theorem cell23_6269595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_6269595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269595 prefixEnd_6269595 := by exact prefixLift 6269595
  have htrace : WordTrace (prefixWord ++ tailWord_6269595) baseStart_6269595 baseEnd_6269595 := by
    simpa [prefixWord, tailWord_6269595, baseEnd_6269595] using wordTrace_append hprefix tailTrace_6269595
  have hstable : (prefixWord ++ tailWord_6269595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269595).length < 2 ^ (prefixWord ++ tailWord_6269595).sum := by decide
  have hdescent : baseEnd_6269595 < baseStart_6269595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269596 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6269596 : Nat := 118140960795 + 6269596 * 2 ^ 59
def prefixEnd_6269596 : Nat := 4983230072969 + 3 ^ 40 * 6269596 * 2
def baseEnd_6269596 : Nat := 3219316257506157410516659

theorem tailTrace_6269596 : CollatzResearch.WordTrace tailWord_6269596 prefixEnd_6269596 3219316257506157410516659 := by
  unfold tailWord_6269596
  simp only [CollatzResearch.WordTrace]
  refine ⟨114335476097165964297106321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152447301462887952396141761 114335476097165964297106321)
  ·
    refine ⟨85751607072874473222829741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114335476097165964297106321 85751607072874473222829741)
    ·
      refine ⟨32156852652327927458561153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85751607072874473222829741 32156852652327927458561153)
      ·
        refine ⟨24117639489245945593920865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32156852652327927458561153 24117639489245945593920865)
        ·
          refine ⟨18088229616934459195440649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24117639489245945593920865 18088229616934459195440649)
          ·
            refine ⟨13566172212700844396580487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18088229616934459195440649 13566172212700844396580487)
            ·
              refine ⟨20349258319051266594870731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13566172212700844396580487 20349258319051266594870731)
              ·
                refine ⟨30523887478576899892306097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20349258319051266594870731 30523887478576899892306097)
                ·
                  refine ⟨22892915608932674919229573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30523887478576899892306097 22892915608932674919229573)
                  ·
                    refine ⟨4292421676674876547355545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22892915608932674919229573 4292421676674876547355545)
                    ·
                      refine ⟨3219316257506157410516659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292421676674876547355545 3219316257506157410516659)
                      ·
                        rfl

theorem cell23_6269596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6269596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269596 prefixEnd_6269596 := by exact prefixLift 6269596
  have htrace : WordTrace (prefixWord ++ tailWord_6269596) baseStart_6269596 baseEnd_6269596 := by
    simpa [prefixWord, tailWord_6269596, baseEnd_6269596] using wordTrace_append hprefix tailTrace_6269596
  have hstable : (prefixWord ++ tailWord_6269596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269596).length < 2 ^ (prefixWord ++ tailWord_6269596).sum := by decide
  have hdescent : baseEnd_6269596 < baseStart_6269596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269610 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_6269610 : Nat := 118140960795 + 6269610 * 2 ^ 59
def prefixEnd_6269610 : Nat := 4983230072969 + 3 ^ 40 * 6269610 * 2
def baseEnd_6269610 : Nat := 1073107815411773451913865

theorem tailTrace_6269610 : CollatzResearch.WordTrace tailWord_6269610 prefixEnd_6269610 1073107815411773451913865 := by
  unfold tailWord_6269610
  simp only [CollatzResearch.WordTrace]
  refine ⟨57167865704070302246305571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152447641877520805990148189 57167865704070302246305571)
  ·
    refine ⟨85751798556105453369458357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57167865704070302246305571 85751798556105453369458357)
    ·
      refine ⟨8039231114634886253386721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85751798556105453369458357 8039231114634886253386721)
      ·
        refine ⟨6029423335976164690040041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8039231114634886253386721 6029423335976164690040041)
        ·
          refine ⟨4522067501982123517530031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6029423335976164690040041 4522067501982123517530031)
          ·
            refine ⟨6783101252973185276295047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522067501982123517530031 6783101252973185276295047)
            ·
              refine ⟨10174651879459777914442571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783101252973185276295047 10174651879459777914442571)
              ·
                refine ⟨15261977819189666871663857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10174651879459777914442571 15261977819189666871663857)
                ·
                  refine ⟨11446483364392250153747893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15261977819189666871663857 11446483364392250153747893)
                  ·
                    refine ⟨1073107815411773451913865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11446483364392250153747893 1073107815411773451913865)
                    ·
                      rfl

theorem cell23_6269610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_6269610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269610 prefixEnd_6269610 := by exact prefixLift 6269610
  have htrace : WordTrace (prefixWord ++ tailWord_6269610) baseStart_6269610 baseEnd_6269610 := by
    simpa [prefixWord, tailWord_6269610, baseEnd_6269610] using wordTrace_append hprefix tailTrace_6269610
  have hstable : (prefixWord ++ tailWord_6269610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269610).length < 2 ^ (prefixWord ++ tailWord_6269610).sum := by decide
  have hdescent : baseEnd_6269610 < baseStart_6269610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269623 : List Nat := [1, 1, 3, 1, 6, 1, 2, 3, 1, 4]
def baseStart_6269623 : Nat := 118140960795 + 6269623 * 2 ^ 59
def prefixEnd_6269623 : Nat := 4983230072969 + 3 ^ 40 * 6269623 * 2
def baseEnd_6269623 : Nat := 1073110040494609601626345

theorem tailTrace_6269623 : CollatzResearch.WordTrace tailWord_6269623 prefixEnd_6269623 1073110040494609601626345 := by
  unfold tailWord_6269623
  simp only [CollatzResearch.WordTrace]
  refine ⟨228671936965234112205445523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152447957976822741470297015 228671936965234112205445523)
  ·
    refine ⟨343007905447851168308168285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228671936965234112205445523 343007905447851168308168285)
    ·
      refine ⟨128627964542944188115563107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343007905447851168308168285 128627964542944188115563107)
      ·
        refine ⟨192941946814416282173344661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128627964542944188115563107 192941946814416282173344661)
        ·
          refine ⟨9044153756925763226875531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192941946814416282173344661 9044153756925763226875531)
          ·
            refine ⟨13566230635388644840313297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044153756925763226875531 13566230635388644840313297)
            ·
              refine ⟨10174672976541483630234973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13566230635388644840313297 10174672976541483630234973)
              ·
                refine ⟨3815502366203056361338115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10174672976541483630234973 3815502366203056361338115)
                ·
                  refine ⟨5723253549304584542007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815502366203056361338115 5723253549304584542007173)
                  ·
                    refine ⟨1073110040494609601626345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723253549304584542007173 1073110040494609601626345)
                    ·
                      rfl

theorem cell23_6269623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_6269623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269623 prefixEnd_6269623 := by exact prefixLift 6269623
  have htrace : WordTrace (prefixWord ++ tailWord_6269623) baseStart_6269623 baseEnd_6269623 := by
    simpa [prefixWord, tailWord_6269623, baseEnd_6269623] using wordTrace_append hprefix tailTrace_6269623
  have hstable : (prefixWord ++ tailWord_6269623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269623).length < 2 ^ (prefixWord ++ tailWord_6269623).sum := by decide
  have hdescent : baseEnd_6269623 < baseStart_6269623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269636 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 6]
def baseStart_6269636 : Nat := 118140960795 + 6269636 * 2 ^ 59
def prefixEnd_6269636 : Nat := 4983230072969 + 3 ^ 40 * 6269636 * 2
def baseEnd_6269636 : Nat := 357704088525815250446275

theorem tailTrace_6269636 : CollatzResearch.WordTrace tailWord_6269636 prefixEnd_6269636 357704088525815250446275 := by
  unfold tailWord_6269636
  simp only [CollatzResearch.WordTrace]
  refine ⟨114336205557093507712834381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152448274076124676950445841 114336205557093507712834381)
  ·
    refine ⟨42876077083910065392312893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114336205557093507712834381 42876077083910065392312893)
    ·
      refine ⟨16078528906466274522117335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42876077083910065392312893 16078528906466274522117335)
      ·
        refine ⟨24117793359699411783176003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16078528906466274522117335 24117793359699411783176003)
        ·
          refine ⟨36176690039549117674764005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24117793359699411783176003 36176690039549117674764005)
          ·
            refine ⟨6783129382415459564018251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36176690039549117674764005 6783129382415459564018251)
            ·
              refine ⟨10174694073623189346027377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783129382415459564018251 10174694073623189346027377)
              ·
                refine ⟨7631020555217392009520533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10174694073623189346027377 7631020555217392009520533)
                ·
                  refine ⟨357704088525815250446275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7631020555217392009520533 357704088525815250446275)
                  ·
                    rfl

theorem cell23_6269636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_6269636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269636 prefixEnd_6269636 := by exact prefixLift 6269636
  have htrace : WordTrace (prefixWord ++ tailWord_6269636) baseStart_6269636 baseEnd_6269636 := by
    simpa [prefixWord, tailWord_6269636, baseEnd_6269636] using wordTrace_append hprefix tailTrace_6269636
  have hstable : (prefixWord ++ tailWord_6269636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269636).length < 2 ^ (prefixWord ++ tailWord_6269636).sum := by decide
  have hdescent : baseEnd_6269636 < baseStart_6269636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269646 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_6269646 : Nat := 118140960795 + 6269646 * 2 ^ 59
def prefixEnd_6269646 : Nat := 4983230072969 + 3 ^ 40 * 6269646 * 2
def baseEnd_6269646 : Nat := 3219341931538882214891429

theorem tailTrace_6269646 : CollatzResearch.WordTrace tailWord_6269646 prefixEnd_6269646 3219341931538882214891429 := by
  unfold tailWord_6269646
  simp only [CollatzResearch.WordTrace]
  refine ⟨28584096980518848391691599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152448517229433858089021861 28584096980518848391691599)
  ·
    refine ⟨42876145470778272587537399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28584096980518848391691599 42876145470778272587537399)
    ·
      refine ⟨64314218206167408881306099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42876145470778272587537399 64314218206167408881306099)
      ·
        refine ⟨96471327309251113321959149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64314218206167408881306099 96471327309251113321959149)
        ·
          refine ⟨36176747740969167495734681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96471327309251113321959149 36176747740969167495734681)
          ·
            refine ⟨27132560805726875621801011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36176747740969167495734681 27132560805726875621801011)
            ·
              refine ⟨40698841208590313432701517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27132560805726875621801011 40698841208590313432701517)
              ·
                refine ⟨15262065453221367537263069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40698841208590313432701517 15262065453221367537263069)
                ·
                  refine ⟨5723274544958012826473651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15262065453221367537263069 5723274544958012826473651)
                  ·
                    refine ⟨8584911817437019239710477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723274544958012826473651 8584911817437019239710477)
                    ·
                      refine ⟨3219341931538882214891429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8584911817437019239710477 3219341931538882214891429)
                      ·
                        rfl

theorem cell23_6269646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_6269646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269646 prefixEnd_6269646 := by exact prefixLift 6269646
  have htrace : WordTrace (prefixWord ++ tailWord_6269646) baseStart_6269646 baseEnd_6269646 := by
    simpa [prefixWord, tailWord_6269646, baseEnd_6269646] using wordTrace_append hprefix tailTrace_6269646
  have hstable : (prefixWord ++ tailWord_6269646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269646).length < 2 ^ (prefixWord ++ tailWord_6269646).sum := by decide
  have hdescent : baseEnd_6269646 < baseStart_6269646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269653 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 6]
def baseStart_6269653 : Nat := 118140960795 + 6269653 * 2 ^ 59
def prefixEnd_6269653 : Nat := 4983230072969 + 3 ^ 40 * 6269653 * 2
def baseEnd_6269653 : Nat := 357705058433718187500433

theorem tailTrace_6269653 : CollatzResearch.WordTrace tailWord_6269653 prefixEnd_6269653 357705058433718187500433 := by
  unfold tailWord_6269653
  simp only [CollatzResearch.WordTrace]
  refine ⟨228673031155125427329037613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152448687436750284886025075 228673031155125427329037613)
  ·
    refine ⟨85752386683172035248389105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228673031155125427329037613 85752386683172035248389105)
    ·
      refine ⟨64314290012379026436291829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85752386683172035248389105 64314290012379026436291829)
      ·
        refine ⟨6029464688660533728402359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64314290012379026436291829 6029464688660533728402359)
        ·
          refine ⟨9044197032990800592603539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029464688660533728402359 9044197032990800592603539)
          ·
            refine ⟨13566295549486200888905309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044197032990800592603539 13566295549486200888905309)
            ·
              refine ⟨5087360831057325333339491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13566295549486200888905309 5087360831057325333339491)
              ·
                refine ⟨7631041246585988000009237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087360831057325333339491 7631041246585988000009237)
                ·
                  refine ⟨357705058433718187500433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7631041246585988000009237 357705058433718187500433)
                  ·
                    rfl

theorem cell23_6269653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_6269653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269653 prefixEnd_6269653 := by exact prefixLift 6269653
  have htrace : WordTrace (prefixWord ++ tailWord_6269653) baseStart_6269653 baseEnd_6269653 := by
    simpa [prefixWord, tailWord_6269653, baseEnd_6269653] using wordTrace_append hprefix tailTrace_6269653
  have hstable : (prefixWord ++ tailWord_6269653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269653).length < 2 ^ (prefixWord ++ tailWord_6269653).sum := by decide
  have hdescent : baseEnd_6269653 < baseStart_6269653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269679 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 4, 4]
def baseStart_6269679 : Nat := 118140960795 + 6269679 * 2 ^ 59
def prefixEnd_6269679 : Nat := 4983230072969 + 3 ^ 40 * 6269679 * 2
def baseEnd_6269679 : Nat := 1073119625466826861926259

theorem tailTrace_6269679 : CollatzResearch.WordTrace tailWord_6269679 prefixEnd_6269679 1073119625466826861926259 := by
  unfold tailWord_6269679
  simp only [CollatzResearch.WordTrace]
  refine ⟨228673979453031233769484091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152449319635354155846322727 228673979453031233769484091)
  ·
    refine ⟨343010969179546850654226137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228673979453031233769484091 343010969179546850654226137)
    ·
      refine ⟨257258226884660137990669603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343010969179546850654226137 257258226884660137990669603)
      ·
        refine ⟨385887340326990206986004405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257258226884660137990669603 385887340326990206986004405)
        ·
          refine ⟨36176938155655331904937913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 385887340326990206986004405 36176938155655331904937913)
          ·
            refine ⟨27132703616741498928703435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36176938155655331904937913 27132703616741498928703435)
            ·
              refine ⟨40699055425112248393055153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27132703616741498928703435 40699055425112248393055153)
              ·
                refine ⟨30524291568834186294791365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40699055425112248393055153 30524291568834186294791365)
                ·
                  refine ⟨5723304669156409930273381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30524291568834186294791365 5723304669156409930273381)
                  ·
                    refine ⟨1073119625466826861926259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723304669156409930273381 1073119625466826861926259)
                    ·
                      rfl

theorem cell23_6269679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 4].length) (baseStart_6269679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269679 prefixEnd_6269679 := by exact prefixLift 6269679
  have htrace : WordTrace (prefixWord ++ tailWord_6269679) baseStart_6269679 baseEnd_6269679 := by
    simpa [prefixWord, tailWord_6269679, baseEnd_6269679] using wordTrace_append hprefix tailTrace_6269679
  have hstable : (prefixWord ++ tailWord_6269679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269679).length < 2 ^ (prefixWord ++ tailWord_6269679).sum := by decide
  have hdescent : baseEnd_6269679 < baseStart_6269679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269686 : List Nat := [5, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6269686 : Nat := 118140960795 + 6269686 * 2 ^ 59
def prefixEnd_6269686 : Nat := 4983230072969 + 3 ^ 40 * 6269686 * 2
def baseEnd_6269686 : Nat := 3219362470765062058391245

theorem tailTrace_6269686 : CollatzResearch.WordTrace tailWord_6269686 prefixEnd_6269686 3219362470765062058391245 := by
  unfold tailWord_6269686
  simp only [CollatzResearch.WordTrace]
  refine ⟨14292139672750367122811807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152449489842670582643325941 14292139672750367122811807)
  ·
    refine ⟨21438209509125550684217711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14292139672750367122811807 21438209509125550684217711)
    ·
      refine ⟨32157314263688326026326567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21438209509125550684217711 32157314263688326026326567)
      ·
        refine ⟨48235971395532489039489851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32157314263688326026326567 48235971395532489039489851)
        ·
          refine ⟨72353957093298733559234777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48235971395532489039489851 72353957093298733559234777)
          ·
            refine ⟨54265467819974050169426083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72353957093298733559234777 54265467819974050169426083)
            ·
              refine ⟨81398201729961075254139125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54265467819974050169426083 81398201729961075254139125)
              ·
                refine ⟨7631081412183850805075543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81398201729961075254139125 7631081412183850805075543)
                ·
                  refine ⟨11446622118275776207613315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631081412183850805075543 11446622118275776207613315)
                  ·
                    refine ⟨17169933177413664311419973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11446622118275776207613315 17169933177413664311419973)
                    ·
                      refine ⟨3219362470765062058391245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17169933177413664311419973 3219362470765062058391245)
                      ·
                        rfl

theorem cell23_6269686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6269686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269686 prefixEnd_6269686 := by exact prefixLift 6269686
  have htrace : WordTrace (prefixWord ++ tailWord_6269686) baseStart_6269686 baseEnd_6269686 := by
    simpa [prefixWord, tailWord_6269686, baseEnd_6269686] using wordTrace_append hprefix tailTrace_6269686
  have hstable : (prefixWord ++ tailWord_6269686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269686).length < 2 ^ (prefixWord ++ tailWord_6269686).sum := by decide
  have hdescent : baseEnd_6269686 < baseStart_6269686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269692 : List Nat := [2, 2, 2, 1, 3, 2, 11]
def baseStart_6269692 : Nat := 118140960795 + 6269692 * 2 ^ 59
def prefixEnd_6269692 : Nat := 4983230072969 + 3 ^ 40 * 6269692 * 2
def baseEnd_6269692 : Nat := 39745253724061593023657

theorem tailTrace_6269692 : CollatzResearch.WordTrace tailWord_6269692 prefixEnd_6269692 39745253724061593023657 := by
  unfold tailWord_6269692
  simp only [CollatzResearch.WordTrace]
  refine ⟨114337226800992068494853665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152449635734656091326471553 114337226800992068494853665)
  ·
    refine ⟨85752920100744051371140249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114337226800992068494853665 85752920100744051371140249)
    ·
      refine ⟨64314690075558038528355187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85752920100744051371140249 64314690075558038528355187)
      ·
        refine ⟨96472035113337057792532781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64314690075558038528355187 96472035113337057792532781)
        ·
          refine ⟨36177013167501396672199793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96472035113337057792532781 36177013167501396672199793)
          ·
            refine ⟨27132759875626047504149845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36177013167501396672199793 27132759875626047504149845)
            ·
              refine ⟨39745253724061593023657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27132759875626047504149845 39745253724061593023657)
              ·
                rfl

theorem cell23_6269692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 11].length) (baseStart_6269692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269692 prefixEnd_6269692 := by exact prefixLift 6269692
  have htrace : WordTrace (prefixWord ++ tailWord_6269692) baseStart_6269692 baseEnd_6269692 := by
    simpa [prefixWord, tailWord_6269692, baseEnd_6269692] using wordTrace_append hprefix tailTrace_6269692
  have hstable : (prefixWord ++ tailWord_6269692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269692).length < 2 ^ (prefixWord ++ tailWord_6269692).sum := by decide
  have hdescent : baseEnd_6269692 < baseStart_6269692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269736 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_6269736 : Nat := 118140960795 + 6269736 * 2 ^ 59
def prefixEnd_6269736 : Nat := 4983230072969 + 3 ^ 40 * 6269736 * 2
def baseEnd_6269736 : Nat := 3219388144797786862766015

theorem tailTrace_6269736 : CollatzResearch.WordTrace tailWord_6269736 prefixEnd_6269736 3219388144797786862766015 := by
  unfold tailWord_6269736
  simp only [CollatzResearch.WordTrace]
  refine ⟨114338029206912366252154531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152450705609216488336206041 114338029206912366252154531)
  ·
    refine ⟨171507043810368549378231797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114338029206912366252154531 171507043810368549378231797)
    ·
      refine ⟨16078785357222051504209231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171507043810368549378231797 16078785357222051504209231)
      ·
        refine ⟨24118178035833077256313847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16078785357222051504209231 24118178035833077256313847)
        ·
          refine ⟨36177267053749615884470771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24118178035833077256313847 36177267053749615884470771)
          ·
            refine ⟨54265900580624423826706157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36177267053749615884470771 54265900580624423826706157)
            ·
              refine ⟨20349712717734158935014809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54265900580624423826706157 20349712717734158935014809)
              ·
                refine ⟨15262284538300619201261107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20349712717734158935014809 15262284538300619201261107)
                ·
                  refine ⟨22893426807450928801891661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15262284538300619201261107 22893426807450928801891661)
                  ·
                    refine ⟨8585035052794098300709373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22893426807450928801891661 8585035052794098300709373)
                    ·
                      refine ⟨3219388144797786862766015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585035052794098300709373 3219388144797786862766015)
                      ·
                        rfl

theorem cell23_6269736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_6269736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269736 prefixEnd_6269736 := by exact prefixLift 6269736
  have htrace : WordTrace (prefixWord ++ tailWord_6269736) baseStart_6269736 baseEnd_6269736 := by
    simpa [prefixWord, tailWord_6269736, baseEnd_6269736] using wordTrace_append hprefix tailTrace_6269736
  have hstable : (prefixWord ++ tailWord_6269736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269736).length < 2 ^ (prefixWord ++ tailWord_6269736).sum := by decide
  have hdescent : baseEnd_6269736 < baseStart_6269736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269754 : List Nat := [3, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2]
def baseStart_6269754 : Nat := 118140960795 + 6269754 * 2 ^ 59
def prefixEnd_6269754 : Nat := 4983230072969 + 3 ^ 40 * 6269754 * 2
def baseEnd_6269754 : Nat := 3219397387449567792340933

theorem tailTrace_6269754 : CollatzResearch.WordTrace tailWord_6269754 prefixEnd_6269754 3219397387449567792340933 := by
  unfold tailWord_6269754
  simp only [CollatzResearch.WordTrace]
  refine ⟨57169178731939880394616079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152451143285173014385642877 57169178731939880394616079)
  ·
    refine ⟨85753768097909820591924119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57169178731939880394616079 85753768097909820591924119)
    ·
      refine ⟨128630652146864730887886179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85753768097909820591924119 128630652146864730887886179)
      ·
        refine ⟨192945978220297096331829269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128630652146864730887886179 192945978220297096331829269)
        ·
          refine ⟨9044342729076426390554497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 192945978220297096331829269 9044342729076426390554497)
          ·
            refine ⟨6783257046807319792915873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044342729076426390554497 6783257046807319792915873)
            ·
              refine ⟨5087442785105489844686905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6783257046807319792915873 5087442785105489844686905)
              ·
                refine ⟨3815582088829117383515179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087442785105489844686905 3815582088829117383515179)
                ·
                  refine ⟨5723373133243676075272769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815582088829117383515179 5723373133243676075272769)
                  ·
                    refine ⟨4292529849932757056454577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723373133243676075272769 4292529849932757056454577)
                    ·
                      refine ⟨3219397387449567792340933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292529849932757056454577 3219397387449567792340933)
                      ·
                        rfl

theorem cell23_6269754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_6269754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269754 prefixEnd_6269754 := by exact prefixLift 6269754
  have htrace : WordTrace (prefixWord ++ tailWord_6269754) baseStart_6269754 baseEnd_6269754 := by
    simpa [prefixWord, tailWord_6269754, baseEnd_6269754] using wordTrace_append hprefix tailTrace_6269754
  have hstable : (prefixWord ++ tailWord_6269754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269754).length < 2 ^ (prefixWord ++ tailWord_6269754).sum := by decide
  have hdescent : baseEnd_6269754 < baseStart_6269754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269759 : List Nat := [1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_6269759 : Nat := 118140960795 + 6269759 * 2 ^ 59
def prefixEnd_6269759 : Nat := 4983230072969 + 3 ^ 40 * 6269759 * 2
def baseEnd_6269759 : Nat := 3219399954852840272778409

theorem tailTrace_6269759 : CollatzResearch.WordTrace tailWord_6269759 prefixEnd_6269759 3219399954852840272778409 := by
  unfold tailWord_6269759
  simp only [CollatzResearch.WordTrace]
  refine ⟨228676897292741407432396331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152451264861827604954930887 228676897292741407432396331)
  ·
    refine ⟨343015345939112111148594497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228676897292741407432396331 343015345939112111148594497)
    ·
      refine ⟨257261509454334083361445873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343015345939112111148594497 257261509454334083361445873)
      ·
        refine ⟨192946132090750562521084405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257261509454334083361445873 192946132090750562521084405)
        ·
          refine ⟨18088699883507865236351663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192946132090750562521084405 18088699883507865236351663)
          ·
            refine ⟨27133049825261797854527495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18088699883507865236351663 27133049825261797854527495)
            ·
              refine ⟨40699574737892696781791243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27133049825261797854527495 40699574737892696781791243)
              ·
                refine ⟨61049362106839045172686865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40699574737892696781791243 61049362106839045172686865)
                ·
                  refine ⟨45787021580129283879515149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61049362106839045172686865 45787021580129283879515149)
                  ·
                    refine ⟨17170133092548481454818181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45787021580129283879515149 17170133092548481454818181)
                    ·
                      refine ⟨3219399954852840272778409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17170133092548481454818181 3219399954852840272778409)
                      ·
                        rfl

theorem cell23_6269759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_6269759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269759 prefixEnd_6269759 := by exact prefixLift 6269759
  have htrace : WordTrace (prefixWord ++ tailWord_6269759) baseStart_6269759 baseEnd_6269759 := by
    simpa [prefixWord, tailWord_6269759, baseEnd_6269759] using wordTrace_append hprefix tailTrace_6269759
  have hstable : (prefixWord ++ tailWord_6269759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269759).length < 2 ^ (prefixWord ++ tailWord_6269759).sum := by decide
  have hdescent : baseEnd_6269759 < baseStart_6269759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269769 : List Nat := [1, 2, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_6269769 : Nat := 118140960795 + 6269769 * 2 ^ 59
def prefixEnd_6269769 : Nat := 4983230072969 + 3 ^ 40 * 6269769 * 2
def baseEnd_6269769 : Nat := 1073135029886461744551121

theorem tailTrace_6269769 : CollatzResearch.WordTrace tailWord_6269769 prefixEnd_6269769 1073135029886461744551121 := by
  unfold tailWord_6269769
  simp only [CollatzResearch.WordTrace]
  refine ⟨228677262022705179140260361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152451508015136786093506907 228677262022705179140260361)
  ·
    refine ⟨171507946517028884355195271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228677262022705179140260361 171507946517028884355195271)
    ·
      refine ⟨257261919775543326532792907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171507946517028884355195271 257261919775543326532792907)
      ·
        refine ⟨385892879663314989799189361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257261919775543326532792907 385892879663314989799189361)
        ·
          refine ⟨289419659747486242349392021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385892879663314989799189361 289419659747486242349392021)
          ·
            refine ⟨13566546550663417610127751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 289419659747486242349392021 13566546550663417610127751)
            ·
              refine ⟨20349819825995126415191627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13566546550663417610127751 20349819825995126415191627)
              ·
                refine ⟨30524729738992689622787441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20349819825995126415191627 30524729738992689622787441)
                ·
                  refine ⟨22893547304244517217090581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30524729738992689622787441 22893547304244517217090581)
                  ·
                    refine ⟨1073135029886461744551121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22893547304244517217090581 1073135029886461744551121)
                    ·
                      rfl

theorem cell23_6269769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_6269769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269769 prefixEnd_6269769 := by exact prefixLift 6269769
  have htrace : WordTrace (prefixWord ++ tailWord_6269769) baseStart_6269769 baseEnd_6269769 := by
    simpa [prefixWord, tailWord_6269769, baseEnd_6269769] using wordTrace_append hprefix tailTrace_6269769
  have hstable : (prefixWord ++ tailWord_6269769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269769).length < 2 ^ (prefixWord ++ tailWord_6269769).sum := by decide
  have hdescent : baseEnd_6269769 < baseStart_6269769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269776 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2]
def baseStart_6269776 : Nat := 118140960795 + 6269776 * 2 ^ 59
def prefixEnd_6269776 : Nat := 4983230072969 + 3 ^ 40 * 6269776 * 2
def baseEnd_6269776 : Nat := 3219408684023966706265831

theorem tailTrace_6269776 : CollatzResearch.WordTrace tailWord_6269776 prefixEnd_6269776 3219408684023966706265831 := by
  unfold tailWord_6269776
  simp only [CollatzResearch.WordTrace]
  refine ⟨114338758666839909667882591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152451678222453212890510121 114338758666839909667882591)
  ·
    refine ⟨171508138000259864501823887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114338758666839909667882591 171508138000259864501823887)
    ·
      refine ⟨257262207000389796752735831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171508138000259864501823887 257262207000389796752735831)
      ·
        refine ⟨385893310500584695129103747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257262207000389796752735831 385893310500584695129103747)
        ·
          refine ⟨578839965750877042693655621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385893310500584695129103747 578839965750877042693655621)
          ·
            refine ⟨108532493578289445505060429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 578839965750877042693655621 108532493578289445505060429)
            ·
              refine ⟨40699685091858542064397661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108532493578289445505060429 40699685091858542064397661)
              ·
                refine ⟨15262381909446953274149123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40699685091858542064397661 15262381909446953274149123)
                ·
                  refine ⟨22893572864170429911223685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15262381909446953274149123 22893572864170429911223685)
                  ·
                    refine ⟨4292544912031955608354441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22893572864170429911223685 4292544912031955608354441)
                    ·
                      refine ⟨3219408684023966706265831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292544912031955608354441 3219408684023966706265831)
                      ·
                        rfl

theorem cell23_6269776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 1, 4, 2].length) (baseStart_6269776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269776 prefixEnd_6269776 := by exact prefixLift 6269776
  have htrace : WordTrace (prefixWord ++ tailWord_6269776) baseStart_6269776 baseEnd_6269776 := by
    simpa [prefixWord, tailWord_6269776, baseEnd_6269776] using wordTrace_append hprefix tailTrace_6269776
  have hstable : (prefixWord ++ tailWord_6269776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269776).length < 2 ^ (prefixWord ++ tailWord_6269776).sum := by decide
  have hdescent : baseEnd_6269776 < baseStart_6269776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269810 : List Nat := [3, 2, 1, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6269810 : Nat := 118140960795 + 6269810 * 2 ^ 59
def prefixEnd_6269810 : Nat := 4983230072969 + 3 ^ 40 * 6269810 * 2
def baseEnd_6269810 : Nat := 3219426142366219573240675

theorem tailTrace_6269810 : CollatzResearch.WordTrace tailWord_6269810 prefixEnd_6269810 3219426142366219573240675 := by
  unfold tailWord_6269810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57169689353889160785625721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152452504943704428761668589 57169689353889160785625721)
  ·
    refine ⟨42877267015416870589219291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57169689353889160785625721 42877267015416870589219291)
    ·
      refine ⟨64315900523125305883828937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42877267015416870589219291 64315900523125305883828937)
      ·
        refine ⟨48236925392343979412871703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64315900523125305883828937 48236925392343979412871703)
        ·
          refine ⟨72355388088515969119307555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48236925392343979412871703 72355388088515969119307555)
          ·
            refine ⟨108533082132773953678961333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72355388088515969119307555 108533082132773953678961333)
            ·
              refine ⟨10174976449947558157402625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108533082132773953678961333 10174976449947558157402625)
              ·
                refine ⟨7631232337460668618051969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10174976449947558157402625 7631232337460668618051969)
                ·
                  refine ⟨5723424253095501463538977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631232337460668618051969 5723424253095501463538977)
                  ·
                    refine ⟨4292568189821626097654233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723424253095501463538977 4292568189821626097654233)
                    ·
                      refine ⟨3219426142366219573240675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292568189821626097654233 3219426142366219573240675)
                      ·
                        rfl

theorem cell23_6269810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6269810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269810 prefixEnd_6269810 := by exact prefixLift 6269810
  have htrace : WordTrace (prefixWord ++ tailWord_6269810) baseStart_6269810 baseEnd_6269810 := by
    simpa [prefixWord, tailWord_6269810, baseEnd_6269810] using wordTrace_append hprefix tailTrace_6269810
  have hstable : (prefixWord ++ tailWord_6269810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269810).length < 2 ^ (prefixWord ++ tailWord_6269810).sum := by decide
  have hdescent : baseEnd_6269810 < baseStart_6269810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269829 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_6269829 : Nat := 118140960795 + 6269829 * 2 ^ 59
def prefixEnd_6269829 : Nat := 4983230072969 + 3 ^ 40 * 6269829 * 2
def baseEnd_6269829 : Nat := 1073145299499551666301029

theorem tailTrace_6269829 : CollatzResearch.WordTrace tailWord_6269829 prefixEnd_6269829 1073145299499551666301029 := by
  unfold tailWord_6269829
  simp only [CollatzResearch.WordTrace]
  refine ⟨228679450402487809387444541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152452966934991872924963027 228679450402487809387444541)
  ·
    refine ⟨85754793900932928520291703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228679450402487809387444541 85754793900932928520291703)
    ·
      refine ⟨128632190851399392780437555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85754793900932928520291703 128632190851399392780437555)
      ·
        refine ⟨192948286277099089170656333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128632190851399392780437555 192948286277099089170656333)
        ·
          refine ⟨72355607353912158438996125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192948286277099089170656333 72355607353912158438996125)
          ·
            refine ⟨27133352757717059414623547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72355607353912158438996125 27133352757717059414623547)
            ·
              refine ⟨40700029136575589121935321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27133352757717059414623547 40700029136575589121935321)
              ·
                refine ⟨30525021852431691841451491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40700029136575589121935321 30525021852431691841451491)
                ·
                  refine ⟨45787532778647537762177237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30525021852431691841451491 45787532778647537762177237)
                  ·
                    refine ⟨1073145299499551666301029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45787532778647537762177237 1073145299499551666301029)
                    ·
                      rfl

theorem cell23_6269829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_6269829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269829 prefixEnd_6269829 := by exact prefixLift 6269829
  have htrace : WordTrace (prefixWord ++ tailWord_6269829) baseStart_6269829 baseEnd_6269829 := by
    simpa [prefixWord, tailWord_6269829, baseEnd_6269829] using wordTrace_append hprefix tailTrace_6269829
  have hstable : (prefixWord ++ tailWord_6269829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269829).length < 2 ^ (prefixWord ++ tailWord_6269829).sum := by decide
  have hdescent : baseEnd_6269829 < baseStart_6269829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269836 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 2, 5, 2]
def baseStart_6269836 : Nat := 118140960795 + 6269836 * 2 ^ 59
def prefixEnd_6269836 : Nat := 4983230072969 + 3 ^ 40 * 6269836 * 2
def baseEnd_6269836 : Nat := 3219439492863236471515555

theorem tailTrace_6269836 : CollatzResearch.WordTrace tailWord_6269836 prefixEnd_6269836 3219439492863236471515555 := by
  unfold tailWord_6269836
  simp only [CollatzResearch.WordTrace]
  refine ⟨114339852856731224791474681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152453137142308299721966241 114339852856731224791474681)
  ·
    refine ⟨85754889642548418593606011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114339852856731224791474681 85754889642548418593606011)
    ·
      refine ⟨128632334463822627890409017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85754889642548418593606011 128632334463822627890409017)
      ·
        refine ⟨96474250847866970917806763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128632334463822627890409017 96474250847866970917806763)
        ·
          refine ⟨144711376271800456376710145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96474250847866970917806763 144711376271800456376710145)
          ·
            refine ⟨108533532203850342282532609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144711376271800456376710145 108533532203850342282532609)
            ·
              refine ⟨81400149152887756711899457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108533532203850342282532609 81400149152887756711899457)
              ·
                refine ⟨61050111864665817533924593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81400149152887756711899457 61050111864665817533924593)
                ·
                  refine ⟨45787583898499363150443445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61050111864665817533924593 45787583898499363150443445)
                  ·
                    refine ⟨4292585990484315295354073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45787583898499363150443445 4292585990484315295354073)
                    ·
                      refine ⟨3219439492863236471515555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292585990484315295354073 3219439492863236471515555)
                      ·
                        rfl

theorem cell23_6269836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_6269836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269836 prefixEnd_6269836 := by exact prefixLift 6269836
  have htrace : WordTrace (prefixWord ++ tailWord_6269836) baseStart_6269836 baseEnd_6269836 := by
    simpa [prefixWord, tailWord_6269836, baseEnd_6269836] using wordTrace_append hprefix tailTrace_6269836
  have hstable : (prefixWord ++ tailWord_6269836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269836).length < 2 ^ (prefixWord ++ tailWord_6269836).sum := by decide
  have hdescent : baseEnd_6269836 < baseStart_6269836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269850 : List Nat := [3, 1, 1, 4, 3, 2, 1, 3, 5]
def baseStart_6269850 : Nat := 118140960795 + 6269850 * 2 ^ 59
def prefixEnd_6269850 : Nat := 4983230072969 + 3 ^ 40 * 6269850 * 2
def baseEnd_6269850 : Nat := 357716297954711046304499

theorem tailTrace_6269850 : CollatzResearch.WordTrace tailWord_6269850 prefixEnd_6269850 357716297954711046304499 := by
  unfold tailWord_6269850
  simp only [CollatzResearch.WordTrace]
  refine ⟨57170054083852932493489751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152453477556941153315972669 57170054083852932493489751)
  ·
    refine ⟨85755081125779398740234627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57170054083852932493489751 85755081125779398740234627)
    ·
      refine ⟨128632621688669098110351941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85755081125779398740234627 128632621688669098110351941)
      ·
        refine ⟨24118616566625455895690989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128632621688669098110351941 24118616566625455895690989)
        ·
          refine ⟨9044481212484545960884121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24118616566625455895690989 9044481212484545960884121)
          ·
            refine ⟨6783360909363409470663091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044481212484545960884121 6783360909363409470663091)
            ·
              refine ⟨10175041364045114205994637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783360909363409470663091 10175041364045114205994637)
              ·
                refine ⟨3815640511516917827247989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10175041364045114205994637 3815640511516917827247989)
                ·
                  refine ⟨357716297954711046304499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3815640511516917827247989 357716297954711046304499)
                  ·
                    rfl

theorem cell23_6269850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_6269850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269850 prefixEnd_6269850 := by exact prefixLift 6269850
  have htrace : WordTrace (prefixWord ++ tailWord_6269850) baseStart_6269850 baseEnd_6269850 := by
    simpa [prefixWord, tailWord_6269850, baseEnd_6269850] using wordTrace_append hprefix tailTrace_6269850
  have hstable : (prefixWord ++ tailWord_6269850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269850).length < 2 ^ (prefixWord ++ tailWord_6269850).sum := by decide
  have hdescent : baseEnd_6269850 < baseStart_6269850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269863 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 2, 5]
def baseStart_6269863 : Nat := 118140960795 + 6269863 * 2 ^ 59
def prefixEnd_6269863 : Nat := 4983230072969 + 3 ^ 40 * 6269863 * 2
def baseEnd_6269863 : Nat := 1073151118946969288625977

theorem tailTrace_6269863 : CollatzResearch.WordTrace tailWord_6269863 prefixEnd_6269863 1073151118946969288625977 := by
  unfold tailWord_6269863
  simp only [CollatzResearch.WordTrace]
  refine ⟨228680690484364633194182243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152453793656243088796121495 228680690484364633194182243)
  ·
    refine ⟨343021035726546949791273365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228680690484364633194182243 343021035726546949791273365)
    ·
      refine ⟨16079111049681888271465939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 343021035726546949791273365 16079111049681888271465939)
      ·
        refine ⟨24118666574522832407198909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079111049681888271465939 24118666574522832407198909)
        ·
          refine ⟨9044499965446062152699591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24118666574522832407198909 9044499965446062152699591)
          ·
            refine ⟨13566749948169093229049387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044499965446062152699591 13566749948169093229049387)
            ·
              refine ⟨20350124922253639843574081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13566749948169093229049387 20350124922253639843574081)
              ·
                refine ⟨15262593691690229882680561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20350124922253639843574081 15262593691690229882680561)
                ·
                  refine ⟨11446945268767672412010421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15262593691690229882680561 11446945268767672412010421)
                  ·
                    refine ⟨1073151118946969288625977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11446945268767672412010421 1073151118946969288625977)
                    ·
                      rfl

theorem cell23_6269863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_6269863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269863 prefixEnd_6269863 := by exact prefixLift 6269863
  have htrace : WordTrace (prefixWord ++ tailWord_6269863) baseStart_6269863 baseEnd_6269863 := by
    simpa [prefixWord, tailWord_6269863, baseEnd_6269863] using wordTrace_append hprefix tailTrace_6269863
  have hstable : (prefixWord ++ tailWord_6269863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269863).length < 2 ^ (prefixWord ++ tailWord_6269863).sum := by decide
  have hdescent : baseEnd_6269863 < baseStart_6269863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269879 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_6269879 : Nat := 118140960795 + 6269879 * 2 ^ 59
def prefixEnd_6269879 : Nat := 4983230072969 + 3 ^ 40 * 6269879 * 2
def baseEnd_6269879 : Nat := 3219461572531379803277857

theorem tailTrace_6269879 : CollatzResearch.WordTrace tailWord_6269879 prefixEnd_6269879 3219461572531379803277857 := by
  unfold tailWord_6269879
  simp only [CollatzResearch.WordTrace]
  refine ⟨228681274052306667926764691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152454182701537778617843127 228681274052306667926764691)
  ·
    refine ⟨343021911078460001890147037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228681274052306667926764691 343021911078460001890147037)
    ·
      refine ⟨128633216654422500708805139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343021911078460001890147037 128633216654422500708805139)
      ·
        refine ⟨192949824981633751063207709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128633216654422500708805139 192949824981633751063207709)
        ·
          refine ⟨72356184368112656648702891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192949824981633751063207709 72356184368112656648702891)
          ·
            refine ⟨108534276552168984973054337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72356184368112656648702891 108534276552168984973054337)
            ·
              refine ⟨81400707414126738729790753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108534276552168984973054337 81400707414126738729790753)
              ·
                refine ⟨61050530560595054047343065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81400707414126738729790753 61050530560595054047343065)
                ·
                  refine ⟨45787897920446290535507299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61050530560595054047343065 45787897920446290535507299)
                  ·
                    refine ⟨68681846880669435803260949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45787897920446290535507299 68681846880669435803260949)
                    ·
                      refine ⟨3219461572531379803277857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68681846880669435803260949 3219461572531379803277857)
                      ·
                        rfl

theorem cell23_6269879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_6269879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269879 prefixEnd_6269879 := by exact prefixLift 6269879
  have htrace : WordTrace (prefixWord ++ tailWord_6269879) baseStart_6269879 baseEnd_6269879 := by
    simpa [prefixWord, tailWord_6269879, baseEnd_6269879] using wordTrace_append hprefix tailTrace_6269879
  have hstable : (prefixWord ++ tailWord_6269879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269879).length < 2 ^ (prefixWord ++ tailWord_6269879).sum := by decide
  have hdescent : baseEnd_6269879 < baseStart_6269879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269903 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3]
def baseStart_6269903 : Nat := 118140960795 + 6269903 * 2 ^ 59
def prefixEnd_6269903 : Nat := 4983230072969 + 3 ^ 40 * 6269903 * 2
def baseEnd_6269903 : Nat := 3219473896067087709377747

theorem tailTrace_6269903 : CollatzResearch.WordTrace tailWord_6269903 prefixEnd_6269903 3219473896067087709377747 := by
  unfold tailWord_6269903
  simp only [CollatzResearch.WordTrace]
  refine ⟨228682149404219720025638363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152454766269479813350425575 228682149404219720025638363)
  ·
    refine ⟨343023224106329580038457545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228682149404219720025638363 343023224106329580038457545)
    ·
      refine ⟨257267418079747185028843159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343023224106329580038457545 257267418079747185028843159)
      ·
        refine ⟨385901127119620777543264739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257267418079747185028843159 385901127119620777543264739)
        ·
          refine ⟨578851690679431166314897109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385901127119620777543264739 578851690679431166314897109)
          ·
            refine ⟨13566836500299167960505401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 578851690679431166314897109 13566836500299167960505401)
            ·
              refine ⟨10175127375224375970379051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13566836500299167960505401 10175127375224375970379051)
              ·
                refine ⟨15262691062836563955568577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175127375224375970379051 15262691062836563955568577)
                ·
                  refine ⟨11447018297127422966676433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15262691062836563955568577 11447018297127422966676433)
                  ·
                    refine ⟨8585263722845567225007325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11447018297127422966676433 8585263722845567225007325)
                    ·
                      refine ⟨3219473896067087709377747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585263722845567225007325 3219473896067087709377747)
                      ·
                        rfl

theorem cell23_6269903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_6269903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269903 prefixEnd_6269903 := by exact prefixLift 6269903
  have htrace : WordTrace (prefixWord ++ tailWord_6269903) baseStart_6269903 baseEnd_6269903 := by
    simpa [prefixWord, tailWord_6269903, baseEnd_6269903] using wordTrace_append hprefix tailTrace_6269903
  have hstable : (prefixWord ++ tailWord_6269903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269903).length < 2 ^ (prefixWord ++ tailWord_6269903).sum := by decide
  have hdescent : baseEnd_6269903 < baseStart_6269903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269927 : List Nat := [1, 1, 5, 2, 2, 1, 4, 2, 1, 4]
def baseStart_6269927 : Nat := 118140960795 + 6269927 * 2 ^ 59
def prefixEnd_6269927 : Nat := 4983230072969 + 3 ^ 40 * 6269927 * 2
def baseEnd_6269927 : Nat := 1073162073200931871825879

theorem tailTrace_6269927 : CollatzResearch.WordTrace tailWord_6269927 prefixEnd_6269927 1073162073200931871825879 := by
  unfold tailWord_6269927
  simp only [CollatzResearch.WordTrace]
  refine ⟨228683024756132772124512035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152455349837421848083008023 228683024756132772124512035)
  ·
    refine ⟨343024537134199158186768053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228683024756132772124512035 343024537134199158186768053)
    ·
      refine ⟨32158550356331171080009505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343024537134199158186768053 32158550356331171080009505)
      ·
        refine ⟨24118912767248378310007129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32158550356331171080009505 24118912767248378310007129)
        ·
          refine ⟨18089184575436283732505347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24118912767248378310007129 18089184575436283732505347)
          ·
            refine ⟨27133776863154425598758021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18089184575436283732505347 27133776863154425598758021)
            ·
              refine ⟨5087583161841454799767129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27133776863154425598758021 5087583161841454799767129)
              ·
                refine ⟨3815687371381091099825347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087583161841454799767129 3815687371381091099825347)
                ·
                  refine ⟨5723531057071636649738021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815687371381091099825347 5723531057071636649738021)
                  ·
                    refine ⟨1073162073200931871825879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723531057071636649738021 1073162073200931871825879)
                    ·
                      rfl

theorem cell23_6269927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_6269927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269927 prefixEnd_6269927 := by exact prefixLift 6269927
  have htrace : WordTrace (prefixWord ++ tailWord_6269927) baseStart_6269927 baseEnd_6269927 := by
    simpa [prefixWord, tailWord_6269927, baseEnd_6269927] using wordTrace_append hprefix tailTrace_6269927
  have hstable : (prefixWord ++ tailWord_6269927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269927).length < 2 ^ (prefixWord ++ tailWord_6269927).sum := by decide
  have hdescent : baseEnd_6269927 < baseStart_6269927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269929 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_6269929 : Nat := 118140960795 + 6269929 * 2 ^ 59
def prefixEnd_6269929 : Nat := 4983230072969 + 3 ^ 40 * 6269929 * 2
def baseEnd_6269929 : Nat := 3219487246564104607652627

theorem tailTrace_6269929 : CollatzResearch.WordTrace tailWord_6269929 prefixEnd_6269929 3219487246564104607652627 := by
  unfold tailWord_6269929
  simp only [CollatzResearch.WordTrace]
  refine ⟨228683097702125526466084841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152455398468083684310723227 228683097702125526466084841)
  ·
    refine ⟨171512323276594144849563631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228683097702125526466084841 171512323276594144849563631)
    ·
      refine ⟨257268484914891217274345447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171512323276594144849563631 257268484914891217274345447)
      ·
        refine ⟨385902727372336825911518171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257268484914891217274345447 385902727372336825911518171)
        ·
          refine ⟨578854091058505238867277257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385902727372336825911518171 578854091058505238867277257)
          ·
            refine ⟨434140568293878929150457943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578854091058505238867277257 434140568293878929150457943)
            ·
              refine ⟨651210852440818393725686915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434140568293878929150457943 651210852440818393725686915)
              ·
                refine ⟨976816278661227590588530373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651210852440818393725686915 976816278661227590588530373)
                ·
                  refine ⟨183153052248980173235349445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976816278661227590588530373 183153052248980173235349445)
                  ·
                    refine ⟨34341197296683782481628021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183153052248980173235349445 34341197296683782481628021)
                    ·
                      refine ⟨3219487246564104607652627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34341197296683782481628021 3219487246564104607652627)
                      ·
                        rfl

theorem cell23_6269929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_6269929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269929 prefixEnd_6269929 := by exact prefixLift 6269929
  have htrace : WordTrace (prefixWord ++ tailWord_6269929) baseStart_6269929 baseEnd_6269929 := by
    simpa [prefixWord, tailWord_6269929, baseEnd_6269929] using wordTrace_append hprefix tailTrace_6269929
  have hstable : (prefixWord ++ tailWord_6269929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269929).length < 2 ^ (prefixWord ++ tailWord_6269929).sum := by decide
  have hdescent : baseEnd_6269929 < baseStart_6269929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269954 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_6269954 : Nat := 118140960795 + 6269954 * 2 ^ 59
def prefixEnd_6269954 : Nat := 4983230072969 + 3 ^ 40 * 6269954 * 2
def baseEnd_6269954 : Nat := 3219500083580467009840013

theorem tailTrace_6269954 : CollatzResearch.WordTrace tailWord_6269954 prefixEnd_6269954 3219500083580467009840013 := by
  unfold tailWord_6269954
  simp only [CollatzResearch.WordTrace]
  refine ⟨57171002381758738933936229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152456006351356637157163277 57171002381758738933936229)
  ·
    refine ⟨10719562946579763550113043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57171002381758738933936229 10719562946579763550113043)
    ·
      refine ⟨16079344419869645325169565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719562946579763550113043 16079344419869645325169565)
      ·
        refine ⟨6029754157451116996938587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16079344419869645325169565 6029754157451116996938587)
        ·
          refine ⟨9044631236176675495407881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029754157451116996938587 9044631236176675495407881)
          ·
            refine ⟨6783473427132506621555911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9044631236176675495407881 6783473427132506621555911)
            ·
              refine ⟨10175210140698759932333867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783473427132506621555911 10175210140698759932333867)
              ·
                refine ⟨15262815211048139898500801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175210140698759932333867 15262815211048139898500801)
                ·
                  refine ⟨11447111408286104923875601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15262815211048139898500801 11447111408286104923875601)
                  ·
                    refine ⟨8585333556214578692906701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11447111408286104923875601 8585333556214578692906701)
                    ·
                      refine ⟨3219500083580467009840013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585333556214578692906701 3219500083580467009840013)
                      ·
                        rfl

theorem cell23_6269954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_6269954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269954 prefixEnd_6269954 := by exact prefixLift 6269954
  have htrace : WordTrace (prefixWord ++ tailWord_6269954) baseStart_6269954 baseEnd_6269954 := by
    simpa [prefixWord, tailWord_6269954, baseEnd_6269954] using wordTrace_append hprefix tailTrace_6269954
  have hstable : (prefixWord ++ tailWord_6269954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269954).length < 2 ^ (prefixWord ++ tailWord_6269954).sum := by decide
  have hdescent : baseEnd_6269954 < baseStart_6269954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269960 : List Nat := [2, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2]
def baseStart_6269960 : Nat := 118140960795 + 6269960 * 2 ^ 59
def prefixEnd_6269960 : Nat := 4983230072969 + 3 ^ 40 * 6269960 * 2
def baseEnd_6269960 : Nat := 3219503164464393986364985

theorem tailTrace_6269960 : CollatzResearch.WordTrace tailWord_6269960 prefixEnd_6269960 3219503164464393986364985 := by
  unfold tailWord_6269960
  simp only [CollatzResearch.WordTrace]
  refine ⟨114342114182506609380231667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152456152243342145840308889 114342114182506609380231667)
  ·
    refine ⟨171513171273759914070347501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114342114182506609380231667 171513171273759914070347501)
    ·
      refine ⟨64317439227659967776380313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171513171273759914070347501 64317439227659967776380313)
      ·
        refine ⟨48238079420744975832285235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64317439227659967776380313 48238079420744975832285235)
        ·
          refine ⟨72357119131117463748427853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48238079420744975832285235 72357119131117463748427853)
          ·
            refine ⟨27133919674169048905660445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72357119131117463748427853 27133919674169048905660445)
            ·
              refine ⟨10175219877813393339622667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27133919674169048905660445 10175219877813393339622667)
              ·
                refine ⟨15262829816720090009434001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175219877813393339622667 15262829816720090009434001)
                ·
                  refine ⟨11447122362540067507075501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15262829816720090009434001 11447122362540067507075501)
                  ·
                    refine ⟨4292670885952525315153313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11447122362540067507075501 4292670885952525315153313)
                    ·
                      refine ⟨3219503164464393986364985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292670885952525315153313 3219503164464393986364985)
                      ·
                        rfl

theorem cell23_6269960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_6269960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269960 prefixEnd_6269960 := by exact prefixLift 6269960
  have htrace : WordTrace (prefixWord ++ tailWord_6269960) baseStart_6269960 baseEnd_6269960 := by
    simpa [prefixWord, tailWord_6269960, baseEnd_6269960] using wordTrace_append hprefix tailTrace_6269960
  have hstable : (prefixWord ++ tailWord_6269960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269960).length < 2 ^ (prefixWord ++ tailWord_6269960).sum := by decide
  have hdescent : baseEnd_6269960 < baseStart_6269960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6269983 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 4, 4]
def baseStart_6269983 : Nat := 118140960795 + 6269983 * 2 ^ 59
def prefixEnd_6269983 : Nat := 4983230072969 + 3 ^ 40 * 6269983 * 2
def baseEnd_6269983 : Nat := 1073171658173149132125793

theorem tailTrace_6269983 : CollatzResearch.WordTrace tailWord_6269983 prefixEnd_6269983 1073171658173149132125793 := by
  unfold tailWord_6269983
  simp only [CollatzResearch.WordTrace]
  refine ⟨228685067243929893688550603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152456711495953262459033735 228685067243929893688550603)
  ·
    refine ⟨343027600865894840532825905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228685067243929893688550603 343027600865894840532825905)
    ·
      refine ⟨257270700649421130399619429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343027600865894840532825905 257270700649421130399619429)
      ·
        refine ⟨48238256371766461949928643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257270700649421130399619429 48238256371766461949928643)
        ·
          refine ⟨72357384557649692924892965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48238256371766461949928643 72357384557649692924892965)
          ·
            refine ⟨13567009604559317423417431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72357384557649692924892965 13567009604559317423417431)
            ·
              refine ⟨20350514406838976135126147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13567009604559317423417431 20350514406838976135126147)
              ·
                refine ⟨30525771610258464202689221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20350514406838976135126147 30525771610258464202689221)
                ·
                  refine ⟨5723582176923462038004229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30525771610258464202689221 5723582176923462038004229)
                  ·
                    refine ⟨1073171658173149132125793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723582176923462038004229 1073171658173149132125793)
                    ·
                      rfl

theorem cell23_6269983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 4].length) (baseStart_6269983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6269983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6269983 prefixEnd_6269983 := by exact prefixLift 6269983
  have htrace : WordTrace (prefixWord ++ tailWord_6269983) baseStart_6269983 baseEnd_6269983 := by
    simpa [prefixWord, tailWord_6269983, baseEnd_6269983] using wordTrace_append hprefix tailTrace_6269983
  have hstable : (prefixWord ++ tailWord_6269983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6269983).length < 2 ^ (prefixWord ++ tailWord_6269983).sum := by decide
  have hdescent : baseEnd_6269983 < baseStart_6269983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6269983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270000 : List Nat := [2, 1, 1, 1, 2, 4, 5, 1, 2, 4]
def baseStart_6270000 : Nat := 118140960795 + 6270000 * 2 ^ 59
def prefixEnd_6270000 : Nat := 4983230072969 + 3 ^ 40 * 6270000 * 2
def baseEnd_6270000 : Nat := 1073174567896857943288267

theorem tailTrace_6270000 : CollatzResearch.WordTrace tailWord_6270000 prefixEnd_6270000 1073174567896857943288267 := by
  unfold tailWord_6270000
  simp only [CollatzResearch.WordTrace]
  refine ⟨114342843642434152795959727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152457124856578870394612969 114342843642434152795959727)
  ·
    refine ⟨171514265463651229193939591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114342843642434152795959727 171514265463651229193939591)
    ·
      refine ⟨257271398195476843790909387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171514265463651229193939591 257271398195476843790909387)
      ·
        refine ⟨385907097293215265686364081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257271398195476843790909387 385907097293215265686364081)
        ·
          refine ⟨289430322969911449264773061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385907097293215265686364081 289430322969911449264773061)
          ·
            refine ⟨54268185556858396737144949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289430322969911449264773061 54268185556858396737144949)
            ·
              refine ⟨5087642395955474694107339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54268185556858396737144949 5087642395955474694107339)
              ·
                refine ⟨7631463593933212041161009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087642395955474694107339 7631463593933212041161009)
                ·
                  refine ⟨5723597695449909030870757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631463593933212041161009 5723597695449909030870757)
                  ·
                    refine ⟨1073174567896857943288267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723597695449909030870757 1073174567896857943288267)
                    ·
                      rfl

theorem cell23_6270000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 5, 1, 2, 4].length) (baseStart_6270000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270000 prefixEnd_6270000 := by exact prefixLift 6270000
  have htrace : WordTrace (prefixWord ++ tailWord_6270000) baseStart_6270000 baseEnd_6270000 := by
    simpa [prefixWord, tailWord_6270000, baseEnd_6270000] using wordTrace_append hprefix tailTrace_6270000
  have hstable : (prefixWord ++ tailWord_6270000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270000).length < 2 ^ (prefixWord ++ tailWord_6270000).sum := by decide
  have hdescent : baseEnd_6270000 < baseStart_6270000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270013 : List Nat := [1, 4, 1, 3, 1, 2, 4, 7]
def baseStart_6270013 : Nat := 118140960795 + 6270013 * 2 ^ 59
def prefixEnd_6270013 : Nat := 4983230072969 + 3 ^ 40 * 6270013 * 2
def baseEnd_6270013 : Nat := 119241865886632677000083

theorem tailTrace_6270013 : CollatzResearch.WordTrace tailWord_6270013 prefixEnd_6270013 119241865886632677000083 := by
  unfold tailWord_6270013
  simp only [CollatzResearch.WordTrace]
  refine ⟨228686161433821208812142693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152457440955880805874761795 228686161433821208812142693)
  ·
    refine ⟨42878655268841476652276755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228686161433821208812142693 42878655268841476652276755)
    ·
      refine ⟨64317982903262214978415133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42878655268841476652276755 64317982903262214978415133)
      ·
        refine ⟨24119243588723330616905675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64317982903262214978415133 24119243588723330616905675)
        ·
          refine ⟨36178865383084995925358513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24119243588723330616905675 36178865383084995925358513)
          ·
            refine ⟨27134149037313746944018885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36178865383084995925358513 27134149037313746944018885)
            ·
              refine ⟨5087652944496327552003541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27134149037313746944018885 5087652944496327552003541)
              ·
                refine ⟨119241865886632677000083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5087652944496327552003541 119241865886632677000083)
                ·
                  rfl

theorem cell23_6270013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 7].length) (baseStart_6270013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270013 prefixEnd_6270013 := by exact prefixLift 6270013
  have htrace : WordTrace (prefixWord ++ tailWord_6270013) baseStart_6270013 baseEnd_6270013 := by
    simpa [prefixWord, tailWord_6270013, baseEnd_6270013] using wordTrace_append hprefix tailTrace_6270013
  have hstable : (prefixWord ++ tailWord_6270013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270013).length < 2 ^ (prefixWord ++ tailWord_6270013).sum := by decide
  have hdescent : baseEnd_6270013 < baseStart_6270013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270040 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_6270040 : Nat := 118140960795 + 6270040 * 2 ^ 59
def prefixEnd_6270040 : Nat := 4983230072969 + 3 ^ 40 * 6270040 * 2
def baseEnd_6270040 : Nat := 3219544242916753673364617

theorem tailTrace_6270040 : CollatzResearch.WordTrace tailWord_6270040 prefixEnd_6270040 3219544242916753673364617 := by
  unfold tailWord_6270040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114343573102361696211687787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152458097469815594948917049 114343573102361696211687787)
  ·
    refine ⟨171515359653542544317531681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114343573102361696211687787 171515359653542544317531681)
    ·
      refine ⟨128636519740156908238148761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171515359653542544317531681 128636519740156908238148761)
      ·
        refine ⟨96477389805117681178611571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128636519740156908238148761 96477389805117681178611571)
        ·
          refine ⟨144716084707676521767917357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96477389805117681178611571 144716084707676521767917357)
          ·
            refine ⟨54268531765378695662969009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144716084707676521767917357 54268531765378695662969009)
            ·
              refine ⟨40701398824034021747226757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54268531765378695662969009 40701398824034021747226757)
              ·
                refine ⟨7631512279506379077605017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40701398824034021747226757 7631512279506379077605017)
                ·
                  refine ⟨5723634209629784308203763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631512279506379077605017 5723634209629784308203763)
                  ·
                    refine ⟨8585451314444676462305645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723634209629784308203763 8585451314444676462305645)
                    ·
                      refine ⟨3219544242916753673364617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585451314444676462305645 3219544242916753673364617)
                      ·
                        rfl

theorem cell23_6270040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_6270040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270040 prefixEnd_6270040 := by exact prefixLift 6270040
  have htrace : WordTrace (prefixWord ++ tailWord_6270040) baseStart_6270040 baseEnd_6270040 := by
    simpa [prefixWord, tailWord_6270040, baseEnd_6270040] using wordTrace_append hprefix tailTrace_6270040
  have hstable : (prefixWord ++ tailWord_6270040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270040).length < 2 ^ (prefixWord ++ tailWord_6270040).sum := by decide
  have hdescent : baseEnd_6270040 < baseStart_6270040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270057 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 2, 1, 3]
def baseStart_6270057 : Nat := 118140960795 + 6270057 * 2 ^ 59
def prefixEnd_6270057 : Nat := 4983230072969 + 3 ^ 40 * 6270057 * 2
def baseEnd_6270057 : Nat := 3219552972087880106852039

theorem tailTrace_6270057 : CollatzResearch.WordTrace tailWord_6270057 prefixEnd_6270057 3219552972087880106852039 := by
  unfold tailWord_6270057
  simp only [CollatzResearch.WordTrace]
  refine ⟨228687766245661804326744425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152458510830441202884496283 228687766245661804326744425)
  ·
    refine ⟨171515824684246353245058319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228687766245661804326744425 171515824684246353245058319)
    ·
      refine ⟨257273737026369529867587479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171515824684246353245058319 257273737026369529867587479)
      ·
        refine ⟨385910605539554294801381219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257273737026369529867587479 385910605539554294801381219)
        ·
          refine ⟨578865908309331442202071829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385910605539554294801381219 578865908309331442202071829)
          ·
            refine ⟨27134339451999911353222117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 578865908309331442202071829 27134339451999911353222117)
            ·
              refine ⟨5087688647249983378729147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27134339451999911353222117 5087688647249983378729147)
              ·
                refine ⟨7631532970874975068093721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087688647249983378729147 7631532970874975068093721)
                ·
                  refine ⟨5723649728156231301070291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631532970874975068093721 5723649728156231301070291)
                  ·
                    refine ⟨8585474592234346951605437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723649728156231301070291 8585474592234346951605437)
                    ·
                      refine ⟨3219552972087880106852039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585474592234346951605437 3219552972087880106852039)
                      ·
                        rfl

theorem cell23_6270057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 1, 3].length) (baseStart_6270057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270057 prefixEnd_6270057 := by exact prefixLift 6270057
  have htrace : WordTrace (prefixWord ++ tailWord_6270057) baseStart_6270057 baseEnd_6270057 := by
    simpa [prefixWord, tailWord_6270057, baseEnd_6270057] using wordTrace_append hprefix tailTrace_6270057
  have hstable : (prefixWord ++ tailWord_6270057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270057).length < 2 ^ (prefixWord ++ tailWord_6270057).sum := by decide
  have hdescent : baseEnd_6270057 < baseStart_6270057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270078 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6270078 : Nat := 118140960795 + 6270078 * 2 ^ 59
def prefixEnd_6270078 : Nat := 4983230072969 + 3 ^ 40 * 6270078 * 2
def baseEnd_6270078 : Nat := 3219563755181624524689443

theorem tailTrace_6270078 : CollatzResearch.WordTrace tailWord_6270078 prefixEnd_6270078 3219563755181624524689443 := by
  unfold tailWord_6270078
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586066522323215614157361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152459021452390483275505925 28586066522323215614157361)
  ·
    refine ⟨21439549891742411710618021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28586066522323215614157361 21439549891742411710618021)
    ·
      refine ⟨4019915604701702195740879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21439549891742411710618021 4019915604701702195740879)
      ·
        refine ⟨6029873407052553293611319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019915604701702195740879 6029873407052553293611319)
        ·
          refine ⟨9044810110578829940416979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6029873407052553293611319 9044810110578829940416979)
          ·
            refine ⟨13567215165868244910625469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044810110578829940416979 13567215165868244910625469)
            ·
              refine ⟨5087705687200591841484551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13567215165868244910625469 5087705687200591841484551)
              ·
                refine ⟨7631558530800887762226827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087705687200591841484551 7631558530800887762226827)
                ·
                  refine ⟨11447337796201331643340241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631558530800887762226827 11447337796201331643340241)
                  ·
                    refine ⟨8585503347150998732505181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11447337796201331643340241 8585503347150998732505181)
                    ·
                      refine ⟨3219563755181624524689443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585503347150998732505181 3219563755181624524689443)
                      ·
                        rfl

theorem cell23_6270078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6270078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270078 prefixEnd_6270078 := by exact prefixLift 6270078
  have htrace : WordTrace (prefixWord ++ tailWord_6270078) baseStart_6270078 baseEnd_6270078 := by
    simpa [prefixWord, tailWord_6270078, baseEnd_6270078] using wordTrace_append hprefix tailTrace_6270078
  have hstable : (prefixWord ++ tailWord_6270078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270078).length < 2 ^ (prefixWord ++ tailWord_6270078).sum := by decide
  have hdescent : baseEnd_6270078 < baseStart_6270078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270080 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2]
def baseStart_6270080 : Nat := 118140960795 + 6270080 * 2 ^ 59
def prefixEnd_6270080 : Nat := 4983230072969 + 3 ^ 40 * 6270080 * 2
def baseEnd_6270080 : Nat := 3219564782142933516864433

theorem tailTrace_6270080 : CollatzResearch.WordTrace tailWord_6270080 prefixEnd_6270080 3219564782142933516864433 := by
  unfold tailWord_6270080
  simp only [CollatzResearch.WordTrace]
  refine ⟨114344302562289239627415847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152459070083052319503221129 114344302562289239627415847)
  ·
    refine ⟨171516453843433859441123771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114344302562289239627415847 171516453843433859441123771)
    ·
      refine ⟨257274680765150789161685657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171516453843433859441123771 257274680765150789161685657)
      ·
        refine ⟨192956010573863091871264243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257274680765150789161685657 192956010573863091871264243)
        ·
          refine ⟨289434015860794637806896365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192956010573863091871264243 289434015860794637806896365)
          ·
            refine ⟨108537755947797989177586137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289434015860794637806896365 108537755947797989177586137)
            ·
              refine ⟨81403316960848491883189603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108537755947797989177586137 81403316960848491883189603)
              ·
                refine ⟨122104975441272737824784405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81403316960848491883189603 122104975441272737824784405)
                ·
                  refine ⟨5723670723809659585536769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122104975441272737824784405 5723670723809659585536769)
                  ·
                    refine ⟨4292753042857244689152577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723670723809659585536769 4292753042857244689152577)
                    ·
                      refine ⟨3219564782142933516864433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292753042857244689152577 3219564782142933516864433)
                      ·
                        rfl

theorem cell23_6270080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_6270080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270080 prefixEnd_6270080 := by exact prefixLift 6270080
  have htrace : WordTrace (prefixWord ++ tailWord_6270080) baseStart_6270080 baseEnd_6270080 := by
    simpa [prefixWord, tailWord_6270080, baseEnd_6270080] using wordTrace_append hprefix tailTrace_6270080
  have hstable : (prefixWord ++ tailWord_6270080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270080).length < 2 ^ (prefixWord ++ tailWord_6270080).sum := by decide
  have hdescent : baseEnd_6270080 < baseStart_6270080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270084 : List Nat := [2, 3, 2, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_6270084 : Nat := 118140960795 + 6270084 * 2 ^ 59
def prefixEnd_6270084 : Nat := 4983230072969 + 3 ^ 40 * 6270084 * 2
def baseEnd_6270084 : Nat := 3219566836065551501214415

theorem tailTrace_6270084 : CollatzResearch.WordTrace tailWord_6270084 prefixEnd_6270084 3219566836065551501214415 := by
  unfold tailWord_6270084
  simp only [CollatzResearch.WordTrace]
  refine ⟨114344375508281993968988653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152459167344375991958651537 114344375508281993968988653)
  ·
    refine ⟨42879140815605747738370745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114344375508281993968988653 42879140815605747738370745)
    ·
      refine ⟨32159355611704310803778059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42879140815605747738370745 32159355611704310803778059)
      ·
        refine ⟨48239033417556466205667089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32159355611704310803778059 48239033417556466205667089)
        ·
          refine ⟨36179275063167349654250317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48239033417556466205667089 36179275063167349654250317)
          ·
            refine ⟨13567228148687756120343869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36179275063167349654250317 13567228148687756120343869)
            ·
              refine ⟨5087710555757908545128951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13567228148687756120343869 5087710555757908545128951)
              ·
                refine ⟨7631565833636862817693427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087710555757908545128951 7631565833636862817693427)
                ·
                  refine ⟨11447348750455294226540141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631565833636862817693427 11447348750455294226540141)
                  ·
                    refine ⟨4292755781420735334952553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11447348750455294226540141 4292755781420735334952553)
                    ·
                      refine ⟨3219566836065551501214415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292755781420735334952553 3219566836065551501214415)
                      ·
                        rfl

theorem cell23_6270084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_6270084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270084 prefixEnd_6270084 := by exact prefixLift 6270084
  have htrace : WordTrace (prefixWord ++ tailWord_6270084) baseStart_6270084 baseEnd_6270084 := by
    simpa [prefixWord, tailWord_6270084, baseEnd_6270084] using wordTrace_append hprefix tailTrace_6270084
  have hstable : (prefixWord ++ tailWord_6270084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270084).length < 2 ^ (prefixWord ++ tailWord_6270084).sum := by decide
  have hdescent : baseEnd_6270084 < baseStart_6270084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270110 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6270110 : Nat := 118140960795 + 6270110 * 2 ^ 59
def prefixEnd_6270110 : Nat := 4983230072969 + 3 ^ 40 * 6270110 * 2
def baseEnd_6270110 : Nat := 3219580186562568399489295

theorem tailTrace_6270110 : CollatzResearch.WordTrace tailWord_6270110 prefixEnd_6270110 3219580186562568399489295 := by
  unfold tailWord_6270110
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586212414308724297302973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152459799542979862918949189 28586212414308724297302973)
  ·
    refine ⟨10719829655365771611488615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28586212414308724297302973 10719829655365771611488615)
    ·
      refine ⟨16079744483048657417232923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10719829655365771611488615 16079744483048657417232923)
      ·
        refine ⟨24119616724572986125849385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079744483048657417232923 24119616724572986125849385)
        ·
          refine ⟨18089712543429739594387039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24119616724572986125849385 18089712543429739594387039)
          ·
            refine ⟨27134568815144609391580559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18089712543429739594387039 27134568815144609391580559)
            ·
              refine ⟨40701853222716914087370839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27134568815144609391580559 40701853222716914087370839)
              ·
                refine ⟨61052779834075371131056259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40701853222716914087370839 61052779834075371131056259)
                ·
                  refine ⟨91579169751113056696584389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61052779834075371131056259 91579169751113056696584389)
                  ·
                    refine ⟨17171094328333698130609573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91579169751113056696584389 17171094328333698130609573)
                    ·
                      refine ⟨3219580186562568399489295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17171094328333698130609573 3219580186562568399489295)
                      ·
                        rfl

theorem cell23_6270110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6270110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270110 prefixEnd_6270110 := by exact prefixLift 6270110
  have htrace : WordTrace (prefixWord ++ tailWord_6270110) baseStart_6270110 baseEnd_6270110 := by
    simpa [prefixWord, tailWord_6270110, baseEnd_6270110] using wordTrace_append hprefix tailTrace_6270110
  have hstable : (prefixWord ++ tailWord_6270110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270110).length < 2 ^ (prefixWord ++ tailWord_6270110).sum := by decide
  have hdescent : baseEnd_6270110 < baseStart_6270110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270114 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6270114 : Nat := 118140960795 + 6270114 * 2 ^ 59
def prefixEnd_6270114 : Nat := 4983230072969 + 3 ^ 40 * 6270114 * 2
def baseEnd_6270114 : Nat := 3219582240485186383839277

theorem tailTrace_6270114 : CollatzResearch.WordTrace tailWord_6270114 prefixEnd_6270114 3219582240485186383839277 := by
  unfold tailWord_6270114
  simp only [CollatzResearch.WordTrace]
  refine ⟨57172461301613825765392349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152459896804303535374379597 57172461301613825765392349)
  ·
    refine ⟨21439672988105184662022131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57172461301613825765392349 21439672988105184662022131)
    ·
      refine ⟨32159509482157776993033197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21439672988105184662022131 32159509482157776993033197)
      ·
        refine ⟨12059816055809166372387449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32159509482157776993033197 12059816055809166372387449)
        ·
          refine ⟨9044862041856874779290587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12059816055809166372387449 9044862041856874779290587)
          ·
            refine ⟨13567293062785312168935881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9044862041856874779290587 13567293062785312168935881)
            ·
              refine ⟨10175469797088984126701911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13567293062785312168935881 10175469797088984126701911)
              ·
                refine ⟨15263204695633476190052867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175469797088984126701911 15263204695633476190052867)
                ·
                  refine ⟨22894807043450214285079301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15263204695633476190052867 22894807043450214285079301)
                  ·
                    refine ⟨4292776320646915178452369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22894807043450214285079301 4292776320646915178452369)
                    ·
                      refine ⟨3219582240485186383839277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292776320646915178452369 3219582240485186383839277)
                      ·
                        rfl

theorem cell23_6270114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6270114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270114 prefixEnd_6270114 := by exact prefixLift 6270114
  have htrace : WordTrace (prefixWord ++ tailWord_6270114) baseStart_6270114 baseEnd_6270114 := by
    simpa [prefixWord, tailWord_6270114, baseEnd_6270114] using wordTrace_append hprefix tailTrace_6270114
  have hstable : (prefixWord ++ tailWord_6270114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270114).length < 2 ^ (prefixWord ++ tailWord_6270114).sum := by decide
  have hdescent : baseEnd_6270114 < baseStart_6270114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270148 : List Nat := [2, 3, 3, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_6270148 : Nat := 118140960795 + 6270148 * 2 ^ 59
def prefixEnd_6270148 : Nat := 4983230072969 + 3 ^ 40 * 6270148 * 2
def baseEnd_6270148 : Nat := 3219599698827439250814121

theorem tailTrace_6270148 : CollatzResearch.WordTrace tailWord_6270148 prefixEnd_6270148 3219599698827439250814121 := by
  unfold tailWord_6270148
  simp only [CollatzResearch.WordTrace]
  refine ⟨114345542644166063434153549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152460723525554751245538065 114345542644166063434153549)
  ·
    refine ⟨42879578491562273787807581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114345542644166063434153549 42879578491562273787807581)
    ·
      refine ⟨16079841934335852670427843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42879578491562273787807581 16079841934335852670427843)
      ·
        refine ⟨24119762901503779005641765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16079841934335852670427843 24119762901503779005641765)
        ·
          refine ⟨4522455544031958563557831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24119762901503779005641765 4522455544031958563557831)
          ·
            refine ⟨6783683316047937845336747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522455544031958563557831 6783683316047937845336747)
            ·
              refine ⟨10175524974071906768005121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783683316047937845336747 10175524974071906768005121)
              ·
                refine ⟨7631643730553930076003841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10175524974071906768005121 7631643730553930076003841)
                ·
                  refine ⟨5723732797915447557002881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631643730553930076003841 5723732797915447557002881)
                  ·
                    refine ⟨4292799598436585667752161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723732797915447557002881 4292799598436585667752161)
                    ·
                      refine ⟨3219599698827439250814121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292799598436585667752161 3219599698827439250814121)
                      ·
                        rfl

theorem cell23_6270148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_6270148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270148 prefixEnd_6270148 := by exact prefixLift 6270148
  have htrace : WordTrace (prefixWord ++ tailWord_6270148) baseStart_6270148 baseEnd_6270148 := by
    simpa [prefixWord, tailWord_6270148, baseEnd_6270148] using wordTrace_append hprefix tailTrace_6270148
  have hstable : (prefixWord ++ tailWord_6270148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270148).length < 2 ^ (prefixWord ++ tailWord_6270148).sum := by decide
  have hdescent : baseEnd_6270148 < baseStart_6270148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270163 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 7, 4]
def baseStart_6270163 : Nat := 118140960795 + 6270163 * 2 ^ 59
def prefixEnd_6270163 : Nat := 4983230072969 + 3 ^ 40 * 6270163 * 2
def baseEnd_6270163 : Nat := 1073202467012418897375517

theorem tailTrace_6270163 : CollatzResearch.WordTrace tailWord_6270163 prefixEnd_6270163 1073202467012418897375517 := by
  unfold tailWord_6270163
  simp only [CollatzResearch.WordTrace]
  refine ⟨228691632383277784430103143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152461088255518522953402095 228691632383277784430103143)
  ·
    refine ⟨343037448574916676645154715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228691632383277784430103143 343037448574916676645154715)
    ·
      refine ⟨514556172862375014967732073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343037448574916676645154715 514556172862375014967732073)
      ·
        refine ⟨385917129646781261225799055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514556172862375014967732073 385917129646781261225799055)
        ·
          refine ⟨578875694470171891838698583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385917129646781261225799055 578875694470171891838698583)
          ·
            refine ⟨868313541705257837758047875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578875694470171891838698583 868313541705257837758047875)
            ·
              refine ⟨1302470312557886756637071813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868313541705257837758047875 1302470312557886756637071813)
              ·
                refine ⟨244213183604603766869450965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1302470312557886756637071813 244213183604603766869450965)
                ·
                  refine ⟨5723746490732900786002757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244213183604603766869450965 5723746490732900786002757)
                  ·
                    refine ⟨1073202467012418897375517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723746490732900786002757 1073202467012418897375517)
                    ·
                      rfl

theorem cell23_6270163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 4].length) (baseStart_6270163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270163 prefixEnd_6270163 := by exact prefixLift 6270163
  have htrace : WordTrace (prefixWord ++ tailWord_6270163) baseStart_6270163 baseEnd_6270163 := by
    simpa [prefixWord, tailWord_6270163, baseEnd_6270163] using wordTrace_append hprefix tailTrace_6270163
  have hstable : (prefixWord ++ tailWord_6270163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270163).length < 2 ^ (prefixWord ++ tailWord_6270163).sum := by decide
  have hdescent : baseEnd_6270163 < baseStart_6270163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270180 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_6270180 : Nat := 118140960795 + 6270180 * 2 ^ 59
def prefixEnd_6270180 : Nat := 4983230072969 + 3 ^ 40 * 6270180 * 2
def baseEnd_6270180 : Nat := 1073205376736127708537991

theorem tailTrace_6270180 : CollatzResearch.WordTrace tailWord_6270180 prefixEnd_6270180 1073205376736127708537991 := by
  unfold tailWord_6270180
  simp only [CollatzResearch.WordTrace]
  refine ⟨114346126212108098166735997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152461501616144130888981329 114346126212108098166735997)
  ·
    refine ⟨42879797329540536812525999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114346126212108098166735997 42879797329540536812525999)
    ·
      refine ⟨64319695994310805218788999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42879797329540536812525999 64319695994310805218788999)
      ·
        refine ⟨96479543991466207828183499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64319695994310805218788999 96479543991466207828183499)
        ·
          refine ⟨144719315987199311742275249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96479543991466207828183499 144719315987199311742275249)
          ·
            refine ⟨108539486990399483806706437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144719315987199311742275249 108539486990399483806706437)
            ·
              refine ⟨20351153810699903213757457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108539486990399483806706437 20351153810699903213757457)
              ·
                refine ⟨15263365358024927410318093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20351153810699903213757457 15263365358024927410318093)
                ·
                  refine ⟨5723762009259347778869285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15263365358024927410318093 5723762009259347778869285)
                  ·
                    refine ⟨1073205376736127708537991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723762009259347778869285 1073205376736127708537991)
                    ·
                      rfl

theorem cell23_6270180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_6270180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270180 prefixEnd_6270180 := by exact prefixLift 6270180
  have htrace : WordTrace (prefixWord ++ tailWord_6270180) baseStart_6270180 baseEnd_6270180 := by
    simpa [prefixWord, tailWord_6270180, baseEnd_6270180] using wordTrace_append hprefix tailTrace_6270180
  have hstable : (prefixWord ++ tailWord_6270180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270180).length < 2 ^ (prefixWord ++ tailWord_6270180).sum := by decide
  have hdescent : baseEnd_6270180 < baseStart_6270180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270190 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_6270190 : Nat := 118140960795 + 6270190 * 2 ^ 59
def prefixEnd_6270190 : Nat := 4983230072969 + 3 ^ 40 * 6270190 * 2
def baseEnd_6270190 : Nat := 3219621265014928086488927

theorem tailTrace_6270190 : CollatzResearch.WordTrace tailWord_6270190 prefixEnd_6270190 3219621265014928086488927 := by
  unfold tailWord_6270190
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586577144272496005167003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152461744769453312027557349 28586577144272496005167003)
  ·
    refine ⟨42879865716408744007750505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28586577144272496005167003 42879865716408744007750505)
    ·
      refine ⟨32159899287306558005812879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42879865716408744007750505 32159899287306558005812879)
      ·
        refine ⟨48239848930959837008719319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32159899287306558005812879 48239848930959837008719319)
        ·
          refine ⟨72359773396439755513078979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48239848930959837008719319 72359773396439755513078979)
          ·
            refine ⟨108539660094659633269618469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72359773396439755513078979 108539660094659633269618469)
            ·
              refine ⟨20351186267748681238053463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108539660094659633269618469 20351186267748681238053463)
              ·
                refine ⟨30526779401623021857080195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20351186267748681238053463 30526779401623021857080195)
                ·
                  refine ⟨45790169102434532785620293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30526779401623021857080195 45790169102434532785620293)
                  ·
                    refine ⟨8585656706706474897303805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45790169102434532785620293 8585656706706474897303805)
                    ·
                      refine ⟨3219621265014928086488927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585656706706474897303805 3219621265014928086488927)
                      ·
                        rfl

theorem cell23_6270190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_6270190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270190 prefixEnd_6270190 := by exact prefixLift 6270190
  have htrace : WordTrace (prefixWord ++ tailWord_6270190) baseStart_6270190 baseEnd_6270190 := by
    simpa [prefixWord, tailWord_6270190, baseEnd_6270190] using wordTrace_append hprefix tailTrace_6270190
  have hstable : (prefixWord ++ tailWord_6270190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270190).length < 2 ^ (prefixWord ++ tailWord_6270190).sum := by decide
  have hdescent : baseEnd_6270190 < baseStart_6270190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270270 : List Nat := [4, 2, 1, 2, 1, 1, 1, 2, 3, 6]
def baseStart_6270270 : Nat := 118140960795 + 6270270 * 2 ^ 59
def prefixEnd_6270270 : Nat := 4983230072969 + 3 ^ 40 * 6270270 * 2
def baseEnd_6270270 : Nat := 1073220781155762591162853

theorem tailTrace_6270270 : CollatzResearch.WordTrace tailWord_6270270 prefixEnd_6270270 1073220781155762591162853 := by
  unfold tailWord_6270270
  simp only [CollatzResearch.WordTrace]
  refine ⟨28586941874236267713031033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152463689995926761136165509 28586941874236267713031033)
  ·
    refine ⟨21440206405677200784773275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28586941874236267713031033 21440206405677200784773275)
    ·
      refine ⟨32160309608515801177159913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21440206405677200784773275 32160309608515801177159913)
      ·
        refine ⟨24120232206386850882869935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32160309608515801177159913 24120232206386850882869935)
        ·
          refine ⟨36180348309580276324304903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120232206386850882869935 36180348309580276324304903)
          ·
            refine ⟨54270522464370414486457355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36180348309580276324304903 54270522464370414486457355)
            ·
              refine ⟨81405783696555621729686033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54270522464370414486457355 81405783696555621729686033)
              ·
                refine ⟨61054337772416716297264525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81405783696555621729686033 61054337772416716297264525)
                ·
                  refine ⟨22895376664656268611474197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61054337772416716297264525 22895376664656268611474197)
                  ·
                    refine ⟨1073220781155762591162853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22895376664656268611474197 1073220781155762591162853)
                    ·
                      rfl

theorem cell23_6270270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_6270270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270270 prefixEnd_6270270 := by exact prefixLift 6270270
  have htrace : WordTrace (prefixWord ++ tailWord_6270270) baseStart_6270270 baseEnd_6270270 := by
    simpa [prefixWord, tailWord_6270270, baseEnd_6270270] using wordTrace_append hprefix tailTrace_6270270
  have hstable : (prefixWord ++ tailWord_6270270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270270).length < 2 ^ (prefixWord ++ tailWord_6270270).sum := by decide
  have hdescent : baseEnd_6270270 < baseStart_6270270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270271 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 1, 1, 3]
def baseStart_6270271 : Nat := 118140960795 + 6270271 * 2 ^ 59
def prefixEnd_6270271 : Nat := 4983230072969 + 3 ^ 40 * 6270271 * 2
def baseEnd_6270271 : Nat := 3219662856947942269576055

theorem tailTrace_6270271 : CollatzResearch.WordTrace tailWord_6270271 prefixEnd_6270271 3219662856947942269576055 := by
  unfold tailWord_6270271
  simp only [CollatzResearch.WordTrace]
  refine ⟨228695571466886518875034667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152463714311257679250023111 228695571466886518875034667)
  ·
    refine ⟨343043357200329778312552001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228695571466886518875034667 343043357200329778312552001)
    ·
      refine ⟨257282517900247333734414001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343043357200329778312552001 257282517900247333734414001)
      ·
        refine ⟨192961888425185500300810501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257282517900247333734414001 192961888425185500300810501)
        ·
          refine ⟨36180354079722281306401969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192961888425185500300810501 36180354079722281306401969)
          ·
            refine ⟨27135265559791710979801477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36180354079722281306401969 27135265559791710979801477)
            ·
              refine ⟨5087862292460945808712777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27135265559791710979801477 5087862292460945808712777)
              ·
                refine ⟨3815896719345709356534583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5087862292460945808712777 3815896719345709356534583)
                ·
                  refine ⟨5723845079018564034801875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3815896719345709356534583 5723845079018564034801875)
                  ·
                    refine ⟨8585767618527846052202813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723845079018564034801875 8585767618527846052202813)
                    ·
                      refine ⟨3219662856947942269576055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585767618527846052202813 3219662856947942269576055)
                      ·
                        rfl

theorem cell23_6270271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_6270271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270271 prefixEnd_6270271 := by exact prefixLift 6270271
  have htrace : WordTrace (prefixWord ++ tailWord_6270271) baseStart_6270271 baseEnd_6270271 := by
    simpa [prefixWord, tailWord_6270271, baseEnd_6270271] using wordTrace_append hprefix tailTrace_6270271
  have hstable : (prefixWord ++ tailWord_6270271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270271).length < 2 ^ (prefixWord ++ tailWord_6270271).sum := by decide
  have hdescent : baseEnd_6270271 < baseStart_6270271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270277 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_6270277 : Nat := 118140960795 + 6270277 * 2 ^ 59
def prefixEnd_6270277 : Nat := 4983230072969 + 3 ^ 40 * 6270277 * 2
def baseEnd_6270277 : Nat := 3219665937831869246101027

theorem tailTrace_6270277 : CollatzResearch.WordTrace tailWord_6270277 prefixEnd_6270277 3219665937831869246101027 := by
  unfold tailWord_6270277
  simp only [CollatzResearch.WordTrace]
  refine ⟨228695790304864781899753085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152463860203243187933168723 228695790304864781899753085)
  ·
    refine ⟨85760921364324293212407407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228695790304864781899753085 85760921364324293212407407)
    ·
      refine ⟨128641382046486439818611111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85760921364324293212407407 128641382046486439818611111)
      ·
        refine ⟨192962073069729659727916667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128641382046486439818611111 192962073069729659727916667)
        ·
          refine ⟨289443109604594489591875001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192962073069729659727916667 289443109604594489591875001)
          ·
            refine ⟨217082332203445867193906251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289443109604594489591875001 217082332203445867193906251)
            ·
              refine ⟨325623498305168800790859377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217082332203445867193906251 325623498305168800790859377)
              ·
                refine ⟨244217623728876600593144533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325623498305168800790859377 244217623728876600593144533)
                ·
                  refine ⟨5723850556145545326401825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244217623728876600593144533 5723850556145545326401825)
                  ·
                    refine ⟨4292887917109158994801369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5723850556145545326401825 4292887917109158994801369)
                    ·
                      refine ⟨3219665937831869246101027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4292887917109158994801369 3219665937831869246101027)
                      ·
                        rfl

theorem cell23_6270277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_6270277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270277 prefixEnd_6270277 := by exact prefixLift 6270277
  have htrace : WordTrace (prefixWord ++ tailWord_6270277) baseStart_6270277 baseEnd_6270277 := by
    simpa [prefixWord, tailWord_6270277, baseEnd_6270277] using wordTrace_append hprefix tailTrace_6270277
  have hstable : (prefixWord ++ tailWord_6270277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270277).length < 2 ^ (prefixWord ++ tailWord_6270277).sum := by decide
  have hdescent : baseEnd_6270277 < baseStart_6270277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270311 : List Nat := [1, 1, 5, 1, 4, 2, 2, 1, 1, 1, 4]
def baseStart_6270311 : Nat := 118140960795 + 6270311 * 2 ^ 59
def prefixEnd_6270311 : Nat := 4983230072969 + 3 ^ 40 * 6270311 * 2
def baseEnd_6270311 : Nat := 3219683396174122113075871

theorem tailTrace_6270311 : CollatzResearch.WordTrace tailWord_6270311 prefixEnd_6270311 3219683396174122113075871 := by
  unfold tailWord_6270311
  simp only [CollatzResearch.WordTrace]
  refine ⟨228697030386741605706490787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152464686924494403804327191 228697030386741605706490787)
  ·
    refine ⟨343045545580112408559736181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228697030386741605706490787 343045545580112408559736181)
    ·
      refine ⟨32160519898135538302475267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343045545580112408559736181 32160519898135538302475267)
      ·
        refine ⟨48240779847203307453712901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32160519898135538302475267 48240779847203307453712901)
        ·
          refine ⟨9045146221350620147571169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48240779847203307453712901 9045146221350620147571169)
          ·
            refine ⟨6783859666012965110678377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9045146221350620147571169 6783859666012965110678377)
            ·
              refine ⟨5087894749509723833008783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6783859666012965110678377 5087894749509723833008783)
              ·
                refine ⟨7631842124264585749513175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087894749509723833008783 7631842124264585749513175)
                ·
                  refine ⟨11447763186396878624269763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7631842124264585749513175 11447763186396878624269763)
                  ·
                    refine ⟨17171644779595317936404645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11447763186396878624269763 17171644779595317936404645)
                    ·
                      refine ⟨3219683396174122113075871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17171644779595317936404645 3219683396174122113075871)
                      ·
                        rfl

theorem cell23_6270311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_6270311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270311 prefixEnd_6270311 := by exact prefixLift 6270311
  have htrace : WordTrace (prefixWord ++ tailWord_6270311) baseStart_6270311 baseEnd_6270311 := by
    simpa [prefixWord, tailWord_6270311, baseEnd_6270311] using wordTrace_append hprefix tailTrace_6270311
  have hstable : (prefixWord ++ tailWord_6270311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270311).length < 2 ^ (prefixWord ++ tailWord_6270311).sum := by decide
  have hdescent : baseEnd_6270311 < baseStart_6270311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270313 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_6270313 : Nat := 118140960795 + 6270313 * 2 ^ 59
def prefixEnd_6270313 : Nat := 4983230072969 + 3 ^ 40 * 6270313 * 2
def baseEnd_6270313 : Nat := 1073228141045143701750287

theorem tailTrace_6270313 : CollatzResearch.WordTrace tailWord_6270313 prefixEnd_6270313 1073228141045143701750287 := by
  unfold tailWord_6270313
  simp only [CollatzResearch.WordTrace]
  refine ⟨228697103332734360048063593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152464735555156240032042395 228697103332734360048063593)
  ·
    refine ⟨171522827499550770036047695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228697103332734360048063593 171522827499550770036047695)
    ·
      refine ⟨257284241249326155054071543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171522827499550770036047695 257284241249326155054071543)
      ·
        refine ⟨385926361873989232581107315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257284241249326155054071543 385926361873989232581107315)
        ·
          refine ⟨578889542810983848871660973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385926361873989232581107315 578889542810983848871660973)
          ·
            refine ⟨217083578554118943326872865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 578889542810983848871660973 217083578554118943326872865)
            ·
              refine ⟨162812683915589207495154649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217083578554118943326872865 162812683915589207495154649)
              ·
                refine ⟨122109512936691905621365987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162812683915589207495154649 122109512936691905621365987)
                ·
                  refine ⟨183164269405037858432048981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122109512936691905621365987 183164269405037858432048981)
                  ·
                    refine ⟨1073228141045143701750287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 183164269405037858432048981 1073228141045143701750287)
                    ·
                      rfl

theorem cell23_6270313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_6270313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270313 prefixEnd_6270313 := by exact prefixLift 6270313
  have htrace : WordTrace (prefixWord ++ tailWord_6270313) baseStart_6270313 baseEnd_6270313 := by
    simpa [prefixWord, tailWord_6270313, baseEnd_6270313] using wordTrace_append hprefix tailTrace_6270313
  have hstable : (prefixWord ++ tailWord_6270313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270313).length < 2 ^ (prefixWord ++ tailWord_6270313).sum := by decide
  have hdescent : baseEnd_6270313 < baseStart_6270313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270323 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_6270323 : Nat := 118140960795 + 6270323 * 2 ^ 59
def prefixEnd_6270323 : Nat := 4983230072969 + 3 ^ 40 * 6270323 * 2
def baseEnd_6270323 : Nat := 3219689557941976066125815

theorem tailTrace_6270323 : CollatzResearch.WordTrace tailWord_6270323 prefixEnd_6270323 3219689557941976066125815 := by
  unfold tailWord_6270323
  simp only [CollatzResearch.WordTrace]
  refine ⟨228697468062698131755927623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152464978708465421170618415 228697468062698131755927623)
  ·
    refine ⟨343046202094047197633891435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228697468062698131755927623 343046202094047197633891435)
    ·
      refine ⟨514569303141070796450837153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343046202094047197633891435 514569303141070796450837153)
      ·
        refine ⟨385926977355803097338127865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514569303141070796450837153 385926977355803097338127865)
        ·
          refine ⟨289445233016852323003595899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385926977355803097338127865 289445233016852323003595899)
          ·
            refine ⟨434167849525278484505393849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289445233016852323003595899 434167849525278484505393849)
            ·
              refine ⟨325625887143958863379045387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434167849525278484505393849 325625887143958863379045387)
              ·
                refine ⟨488438830715938295068568081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325625887143958863379045387 488438830715938295068568081)
                ·
                  refine ⟨366329123036953721301426061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488438830715938295068568081 366329123036953721301426061)
                  ·
                    refine ⟨137373421138857645488034773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 366329123036953721301426061 137373421138857645488034773)
                    ·
                      refine ⟨3219689557941976066125815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137373421138857645488034773 3219689557941976066125815)
                      ·
                        rfl

theorem cell23_6270323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_6270323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270323 prefixEnd_6270323 := by exact prefixLift 6270323
  have htrace : WordTrace (prefixWord ++ tailWord_6270323) baseStart_6270323 baseEnd_6270323 := by
    simpa [prefixWord, tailWord_6270323, baseEnd_6270323] using wordTrace_append hprefix tailTrace_6270323
  have hstable : (prefixWord ++ tailWord_6270323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270323).length < 2 ^ (prefixWord ++ tailWord_6270323).sum := by decide
  have hdescent : baseEnd_6270323 < baseStart_6270323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270327 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 3]
def baseStart_6270327 : Nat := 118140960795 + 6270327 * 2 ^ 59
def prefixEnd_6270327 : Nat := 4983230072969 + 3 ^ 40 * 6270327 * 2
def baseEnd_6270327 : Nat := 3219691611864594050475797

theorem tailTrace_6270327 : CollatzResearch.WordTrace tailWord_6270327 prefixEnd_6270327 3219691611864594050475797 := by
  unfold tailWord_6270327
  simp only [CollatzResearch.WordTrace]
  refine ⟨228697613954683640439073235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152465075969789093626048823 228697613954683640439073235)
  ·
    refine ⟨343046420932025460658609853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228697613954683640439073235 343046420932025460658609853)
    ·
      refine ⟨128642407849509547746978695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343046420932025460658609853 128642407849509547746978695)
      ·
        refine ⟨192963611774264321620468043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128642407849509547746978695 192963611774264321620468043)
        ·
          refine ⟨289445417661396482430702065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192963611774264321620468043 289445417661396482430702065)
          ·
            refine ⟨217084063246047361823026549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289445417661396482430702065 217084063246047361823026549)
            ·
              refine ⟨20351630929316940170908739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 217084063246047361823026549 20351630929316940170908739)
              ·
                refine ⟨30527446393975410256363109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20351630929316940170908739 30527446393975410256363109)
                ·
                  refine ⟨5723896198870389423068083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30527446393975410256363109 5723896198870389423068083)
                  ·
                    refine ⟨8585844298305584134602125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5723896198870389423068083 8585844298305584134602125)
                    ·
                      refine ⟨3219691611864594050475797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585844298305584134602125 3219691611864594050475797)
                      ·
                        rfl

theorem cell23_6270327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_6270327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270327 prefixEnd_6270327 := by exact prefixLift 6270327
  have htrace : WordTrace (prefixWord ++ tailWord_6270327) baseStart_6270327 baseEnd_6270327 := by
    simpa [prefixWord, tailWord_6270327, baseEnd_6270327] using wordTrace_append hprefix tailTrace_6270327
  have hstable : (prefixWord ++ tailWord_6270327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270327).length < 2 ^ (prefixWord ++ tailWord_6270327).sum := by decide
  have hdescent : baseEnd_6270327 < baseStart_6270327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270338 : List Nat := [3, 4, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_6270338 : Nat := 118140960795 + 6270338 * 2 ^ 59
def prefixEnd_6270338 : Nat := 4983230072969 + 3 ^ 40 * 6270338 * 2
def baseEnd_6270338 : Nat := 1073232420050597835812749

theorem tailTrace_6270338 : CollatzResearch.WordTrace tailWord_6270338 prefixEnd_6270338 1073232420050597835812749 := by
  unfold tailWord_6270338
  simp only [CollatzResearch.WordTrace]
  refine ⟨57174503789410947329430917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152465343438429192878482445 57174503789410947329430917)
  ·
    refine ⟨10720219460514552624268297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57174503789410947329430917 10720219460514552624268297)
    ·
      refine ⟨8040164595385914468201223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10720219460514552624268297 8040164595385914468201223)
      ·
        refine ⟨12060246893078871702301835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040164595385914468201223 12060246893078871702301835)
        ·
          refine ⟨18090370339618307553452753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12060246893078871702301835 18090370339618307553452753)
          ·
            refine ⟨13567777754713730665089565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18090370339618307553452753 13567777754713730665089565)
            ·
              refine ⟨5087916658017648999408587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13567777754713730665089565 5087916658017648999408587)
              ·
                refine ⟨7631874987026473499112881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5087916658017648999408587 7631874987026473499112881)
                ·
                  refine ⟨5723906240269855124334661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7631874987026473499112881 5723906240269855124334661)
                  ·
                    refine ⟨1073232420050597835812749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5723906240269855124334661 1073232420050597835812749)
                    ·
                      rfl

theorem cell23_6270338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_6270338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270338 prefixEnd_6270338 := by exact prefixLift 6270338
  have htrace : WordTrace (prefixWord ++ tailWord_6270338) baseStart_6270338 baseEnd_6270338 := by
    simpa [prefixWord, tailWord_6270338, baseEnd_6270338] using wordTrace_append hprefix tailTrace_6270338
  have hstable : (prefixWord ++ tailWord_6270338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270338).length < 2 ^ (prefixWord ++ tailWord_6270338).sum := by decide
  have hdescent : baseEnd_6270338 < baseStart_6270338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270344 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_6270344 : Nat := 118140960795 + 6270344 * 2 ^ 59
def prefixEnd_6270344 : Nat := 4983230072969 + 3 ^ 40 * 6270344 * 2
def baseEnd_6270344 : Nat := 3219700341035720483963219

theorem tailTrace_6270344 : CollatzResearch.WordTrace tailWord_6270344 prefixEnd_6270344 3219700341035720483963219 := by
  unfold tailWord_6270344
  simp only [CollatzResearch.WordTrace]
  refine ⟨114349116997811026171221043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152465489330414701561628057 114349116997811026171221043)
  ·
    refine ⟨171523675496716539256831565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114349116997811026171221043 171523675496716539256831565)
    ·
      refine ⟨64321378311268702221311837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171523675496716539256831565 64321378311268702221311837)
      ·
        refine ⟨24120516866725763332991939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64321378311268702221311837 24120516866725763332991939)
        ·
          refine ⟨36180775300088644999487909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24120516866725763332991939 36180775300088644999487909)
          ·
            refine ⟨6783895368766620937403983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36180775300088644999487909 6783895368766620937403983)
            ·
              refine ⟨10175843053149931406105975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6783895368766620937403983 10175843053149931406105975)
              ·
                refine ⟨15263764579724897109158963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10175843053149931406105975 15263764579724897109158963)
                ·
                  refine ⟨22895646869587345663738445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15263764579724897109158963 22895646869587345663738445)
                  ·
                    refine ⟨8585867576095254623901917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22895646869587345663738445 8585867576095254623901917)
                    ·
                      refine ⟨3219700341035720483963219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8585867576095254623901917 3219700341035720483963219)
                      ·
                        rfl

theorem cell23_6270344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_6270344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270344 prefixEnd_6270344 := by exact prefixLift 6270344
  have htrace : WordTrace (prefixWord ++ tailWord_6270344) baseStart_6270344 baseEnd_6270344 := by
    simpa [prefixWord, tailWord_6270344, baseEnd_6270344] using wordTrace_append hprefix tailTrace_6270344
  have hstable : (prefixWord ++ tailWord_6270344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270344).length < 2 ^ (prefixWord ++ tailWord_6270344).sum := by decide
  have hdescent : baseEnd_6270344 < baseStart_6270344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270380 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_6270380 : Nat := 118140960795 + 6270380 * 2 ^ 59
def prefixEnd_6270380 : Nat := 4983230072969 + 3 ^ 40 * 6270380 * 2
def baseEnd_6270380 : Nat := 3219718826339282343113053

theorem tailTrace_6270380 : CollatzResearch.WordTrace tailWord_6270380 prefixEnd_6270380 3219718826339282343113053 := by
  unfold tailWord_6270380
  simp only [CollatzResearch.WordTrace]
  refine ⟨114349773511745815245376297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152466364682327753660501729 114349773511745815245376297)
  ·
    refine ⟨85762330133809361434032223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114349773511745815245376297 85762330133809361434032223)
    ·
      refine ⟨128643495200714042151048335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85762330133809361434032223 128643495200714042151048335)
      ·
        refine ⟨192965242801071063226572503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128643495200714042151048335 192965242801071063226572503)
        ·
          refine ⟨289447864201606594839858755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192965242801071063226572503 289447864201606594839858755)
          ·
            refine ⟨434171796302409892259788133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289447864201606594839858755 434171796302409892259788133)
            ·
              refine ⟨81407211806701854798710275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 434171796302409892259788133 81407211806701854798710275)
              ·
                refine ⟨122110817710052782198065413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81407211806701854798710275 122110817710052782198065413)
                ·
                  refine ⟨22895778320634896662137265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122110817710052782198065413 22895778320634896662137265)
                  ·
                    refine ⟨17171833740476172496602949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22895778320634896662137265 17171833740476172496602949)
                    ·
                      refine ⟨3219718826339282343113053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17171833740476172496602949 3219718826339282343113053)
                      ·
                        rfl

theorem cell23_6270380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_6270380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270380 prefixEnd_6270380 := by exact prefixLift 6270380
  have htrace : WordTrace (prefixWord ++ tailWord_6270380) baseStart_6270380 baseEnd_6270380 := by
    simpa [prefixWord, tailWord_6270380, baseEnd_6270380] using wordTrace_append hprefix tailTrace_6270380
  have hstable : (prefixWord ++ tailWord_6270380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270380).length < 2 ^ (prefixWord ++ tailWord_6270380).sum := by decide
  have hdescent : baseEnd_6270380 < baseStart_6270380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270474 : List Nat := [3, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_6270474 : Nat := 118140960795 + 6270474 * 2 ^ 59
def prefixEnd_6270474 : Nat := 4983230072969 + 3 ^ 40 * 6270474 * 2
def baseEnd_6270474 : Nat := 3219767093520804975337621

theorem tailTrace_6270474 : CollatzResearch.WordTrace tailWord_6270474 prefixEnd_6270474 3219767093520804975337621 := by
  unfold tailWord_6270474
  simp only [CollatzResearch.WordTrace]
  refine ⟨57175743871287771136168619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152468650323434056363116317 57175743871287771136168619)
  ·
    refine ⟨85763615806931656704252929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57175743871287771136168619 85763615806931656704252929)
    ·
      refine ⟨64322711855198742528189697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85763615806931656704252929 64322711855198742528189697)
      ·
        refine ⟨48242033891399056896142273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64322711855198742528189697 48242033891399056896142273)
        ·
          refine ⟨36181525418549292672106705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48242033891399056896142273 36181525418549292672106705)
          ·
            refine ⟨27136144063911969504080029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36181525418549292672106705 27136144063911969504080029)
            ·
              refine ⟨10176054023966988564030011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27136144063911969504080029 10176054023966988564030011)
              ·
                refine ⟨15264081035950482846045017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10176054023966988564030011 15264081035950482846045017)
                ·
                  refine ⟨11448060776962862134533763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15264081035950482846045017 11448060776962862134533763)
                  ·
                    refine ⟨17172091165444293201800645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11448060776962862134533763 17172091165444293201800645)
                    ·
                      refine ⟨3219767093520804975337621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17172091165444293201800645 3219767093520804975337621)
                      ·
                        rfl

theorem cell23_6270474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_6270474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270474 prefixEnd_6270474 := by exact prefixLift 6270474
  have htrace : WordTrace (prefixWord ++ tailWord_6270474) baseStart_6270474 baseEnd_6270474 := by
    simpa [prefixWord, tailWord_6270474, baseEnd_6270474] using wordTrace_append hprefix tailTrace_6270474
  have hstable : (prefixWord ++ tailWord_6270474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270474).length < 2 ^ (prefixWord ++ tailWord_6270474).sum := by decide
  have hdescent : baseEnd_6270474 < baseStart_6270474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270497 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 8]
def baseStart_6270497 : Nat := 118140960795 + 6270497 * 2 ^ 59
def prefixEnd_6270497 : Nat := 4983230072969 + 3 ^ 40 * 6270497 * 2
def baseEnd_6270497 : Nat := 357753211508428709483335

theorem tailTrace_6270497 : CollatzResearch.WordTrace tailWord_6270497 prefixEnd_6270497 357753211508428709483335 := by
  unfold tailWord_6270497
  simp only [CollatzResearch.WordTrace]
  refine ⟨228703814364067759472761745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152469209576045172981841163 228703814364067759472761745)
  ·
    refine ⟨171527860773050819604571309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228703814364067759472761745 171527860773050819604571309)
    ·
      refine ⟨64322947789894057351714241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171527860773050819604571309 64322947789894057351714241)
      ·
        refine ⟨48242210842420543013785681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64322947789894057351714241 48242210842420543013785681)
        ·
          refine ⟨36181658131815407260339261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48242210842420543013785681 36181658131815407260339261)
          ·
            refine ⟨13568121799430777722627223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36181658131815407260339261 13568121799430777722627223)
            ·
              refine ⟨20352182699146166583940835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13568121799430777722627223 20352182699146166583940835)
              ·
                refine ⟨30528274048719249875911253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20352182699146166583940835 30528274048719249875911253)
                ·
                  refine ⟨357753211508428709483335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30528274048719249875911253 357753211508428709483335)
                  ·
                    rfl

theorem cell23_6270497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_6270497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270497 prefixEnd_6270497 := by exact prefixLift 6270497
  have htrace : WordTrace (prefixWord ++ tailWord_6270497) baseStart_6270497 baseEnd_6270497 := by
    simpa [prefixWord, tailWord_6270497, baseEnd_6270497] using wordTrace_append hprefix tailTrace_6270497
  have hstable : (prefixWord ++ tailWord_6270497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270497).length < 2 ^ (prefixWord ++ tailWord_6270497).sum := by decide
  have hdescent : baseEnd_6270497 < baseStart_6270497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270535 : List Nat := [1, 1, 4, 1, 6, 1, 1, 3, 1, 4]
def baseStart_6270535 : Nat := 118140960795 + 6270535 * 2 ^ 59
def prefixEnd_6270535 : Nat := 4983230072969 + 3 ^ 40 * 6270535 * 2
def baseEnd_6270535 : Nat := 1073266138613576412224947

theorem tailTrace_6270535 : CollatzResearch.WordTrace tailWord_6270535 prefixEnd_6270535 1073266138613576412224947 := by
  unfold tailWord_6270535
  simp only [CollatzResearch.WordTrace]
  refine ⟨228705200337930091962645059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152470133558620061308430039 228705200337930091962645059)
  ·
    refine ⟨343057800506895137943967589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228705200337930091962645059 343057800506895137943967589)
    ·
      refine ⟨64323337595042838364493923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343057800506895137943967589 64323337595042838364493923)
      ·
        refine ⟨96485006392564257546740885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64323337595042838364493923 96485006392564257546740885)
        ·
          refine ⟨4522734674651449572503479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96485006392564257546740885 4522734674651449572503479)
          ·
            refine ⟨6784102011977174358755219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522734674651449572503479 6784102011977174358755219)
            ·
              refine ⟨10176153017965761538132829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784102011977174358755219 10176153017965761538132829)
              ·
                refine ⟨3816057381737160576799811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10176153017965761538132829 3816057381737160576799811)
                ·
                  refine ⟨5724086072605740865199717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816057381737160576799811 5724086072605740865199717)
                  ·
                    refine ⟨1073266138613576412224947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724086072605740865199717 1073266138613576412224947)
                    ·
                      rfl

theorem cell23_6270535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_6270535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270535 prefixEnd_6270535 := by exact prefixLift 6270535
  have htrace : WordTrace (prefixWord ++ tailWord_6270535) baseStart_6270535 baseEnd_6270535 := by
    simpa [prefixWord, tailWord_6270535, baseEnd_6270535] using wordTrace_append hprefix tailTrace_6270535
  have hstable : (prefixWord ++ tailWord_6270535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270535).length < 2 ^ (prefixWord ++ tailWord_6270535).sum := by decide
  have hdescent : baseEnd_6270535 < baseStart_6270535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270551 : List Nat := [1, 1, 3, 2, 2, 4, 1, 2, 2, 3, 2]
def baseStart_6270551 : Nat := 118140960795 + 6270551 * 2 ^ 59
def prefixEnd_6270551 : Nat := 4983230072969 + 3 ^ 40 * 6270551 * 2
def baseEnd_6270551 : Nat := 3219806631531201174074767

theorem tailTrace_6270551 : CollatzResearch.WordTrace tailWord_6270551 prefixEnd_6270551 3219806631531201174074767 := by
  unfold tailWord_6270551
  simp only [CollatzResearch.WordTrace]
  refine ⟨228705783905872126695227507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152470522603914751130151671 228705783905872126695227507)
  ·
    refine ⟨343058675858808190042841261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228705783905872126695227507 343058675858808190042841261)
    ·
      refine ⟨128647003447053071266065473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343058675858808190042841261 128647003447053071266065473)
      ·
        refine ⟨96485252585289803449549105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128647003447053071266065473 96485252585289803449549105)
        ·
          refine ⟨72363939438967352587161829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96485252585289803449549105 72363939438967352587161829)
          ·
            refine ⟨13568238644806378610092843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72363939438967352587161829 13568238644806378610092843)
            ·
              refine ⟨20352357967209567915139265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13568238644806378610092843 20352357967209567915139265)
              ·
                refine ⟨15264268475407175936354449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20352357967209567915139265 15264268475407175936354449)
                ·
                  refine ⟨11448201356555381952265837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15264268475407175936354449 11448201356555381952265837)
                  ·
                    refine ⟨4293075508708268232099689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11448201356555381952265837 4293075508708268232099689)
                    ·
                      refine ⟨3219806631531201174074767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293075508708268232099689 3219806631531201174074767)
                      ·
                        rfl

theorem cell23_6270551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_6270551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270551 prefixEnd_6270551 := by exact prefixLift 6270551
  have htrace : WordTrace (prefixWord ++ tailWord_6270551) baseStart_6270551 baseEnd_6270551 := by
    simpa [prefixWord, tailWord_6270551, baseEnd_6270551] using wordTrace_append hprefix tailTrace_6270551
  have hstable : (prefixWord ++ tailWord_6270551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270551).length < 2 ^ (prefixWord ++ tailWord_6270551).sum := by decide
  have hdescent : baseEnd_6270551 < baseStart_6270551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270577 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_6270577 : Nat := 118140960795 + 6270577 * 2 ^ 59
def prefixEnd_6270577 : Nat := 4983230072969 + 3 ^ 40 * 6270577 * 2
def baseEnd_6270577 : Nat := 3219819982028218072349647

theorem tailTrace_6270577 : CollatzResearch.WordTrace tailWord_6270577 prefixEnd_6270577 3219819982028218072349647 := by
  unfold tailWord_6270577
  simp only [CollatzResearch.WordTrace]
  refine ⟨228706732203777933135673985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152471154802518622090449323 228706732203777933135673985)
  ·
    refine ⟨171530049152833449851755489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228706732203777933135673985 171530049152833449851755489)
    ·
      refine ⟨128647536864625087388816617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171530049152833449851755489 128647536864625087388816617)
      ·
        refine ⟨96485652648468815541612463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128647536864625087388816617 96485652648468815541612463)
        ·
          refine ⟨144728478972703223312418695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96485652648468815541612463 144728478972703223312418695)
          ·
            refine ⟨217092718459054834968628043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144728478972703223312418695 217092718459054834968628043)
            ·
              refine ⟨325639077688582252452942065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217092718459054834968628043 325639077688582252452942065)
              ·
                refine ⟨244229308266436689339706549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325639077688582252452942065 244229308266436689339706549)
                ·
                  refine ⟨22896497649978439625597489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 244229308266436689339706549 22896497649978439625597489)
                  ·
                    refine ⟨17172373237483829719198117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22896497649978439625597489 17172373237483829719198117)
                    ·
                      refine ⟨3219819982028218072349647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17172373237483829719198117 3219819982028218072349647)
                      ·
                        rfl

theorem cell23_6270577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_6270577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270577 prefixEnd_6270577 := by exact prefixLift 6270577
  have htrace : WordTrace (prefixWord ++ tailWord_6270577) baseStart_6270577 baseEnd_6270577 := by
    simpa [prefixWord, tailWord_6270577, baseEnd_6270577] using wordTrace_append hprefix tailTrace_6270577
  have hstable : (prefixWord ++ tailWord_6270577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270577).length < 2 ^ (prefixWord ++ tailWord_6270577).sum := by decide
  have hdescent : baseEnd_6270577 < baseStart_6270577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270581 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6270581 : Nat := 118140960795 + 6270581 * 2 ^ 59
def prefixEnd_6270581 : Nat := 4983230072969 + 3 ^ 40 * 6270581 * 2
def baseEnd_6270581 : Nat := 3219822035950836056699629

theorem tailTrace_6270581 : CollatzResearch.WordTrace tailWord_6270581 prefixEnd_6270581 3219822035950836056699629 := by
  unfold tailWord_6270581
  simp only [CollatzResearch.WordTrace]
  refine ⟨228706878095763441818819597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152471252063842294545879731 228706878095763441818819597)
  ·
    refine ⟨85765079285911290682057349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228706878095763441818819597 85765079285911290682057349)
    ·
      refine ⟨16080952366108367002885753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85765079285911290682057349 16080952366108367002885753)
      ·
        refine ⟨12060714274581275252164315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16080952366108367002885753 12060714274581275252164315)
        ·
          refine ⟨18091071411871912878246473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12060714274581275252164315 18091071411871912878246473)
          ·
            refine ⟨13568303558903934658684855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18091071411871912878246473 13568303558903934658684855)
            ·
              refine ⟨20352455338355901988027283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13568303558903934658684855 20352455338355901988027283)
              ·
                refine ⟨30528683007533852982040925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20352455338355901988027283 30528683007533852982040925)
                ·
                  refine ⟨11448256127825194868265347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30528683007533852982040925 11448256127825194868265347)
                  ·
                    refine ⟨17172384191737792302398021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11448256127825194868265347 17172384191737792302398021)
                    ·
                      refine ⟨3219822035950836056699629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17172384191737792302398021 3219822035950836056699629)
                      ·
                        rfl

theorem cell23_6270581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6270581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270581 prefixEnd_6270581 := by exact prefixLift 6270581
  have htrace : WordTrace (prefixWord ++ tailWord_6270581) baseStart_6270581 baseEnd_6270581 := by
    simpa [prefixWord, tailWord_6270581, baseEnd_6270581] using wordTrace_append hprefix tailTrace_6270581
  have hstable : (prefixWord ++ tailWord_6270581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270581).length < 2 ^ (prefixWord ++ tailWord_6270581).sum := by decide
  have hdescent : baseEnd_6270581 < baseStart_6270581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270615 : List Nat := [1, 1, 3, 3, 2, 3, 1, 4, 1, 2, 2]
def baseStart_6270615 : Nat := 118140960795 + 6270615 * 2 ^ 59
def prefixEnd_6270615 : Nat := 4983230072969 + 3 ^ 40 * 6270615 * 2
def baseEnd_6270615 : Nat := 3219839494293088923674473

theorem tailTrace_6270615 : CollatzResearch.WordTrace tailWord_6270615 prefixEnd_6270615 3219839494293088923674473 := by
  unfold tailWord_6270615
  simp only [CollatzResearch.WordTrace]
  refine ⟨228708118177640265625557299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152472078785093510417038199 228708118177640265625557299)
  ·
    refine ⟨343062177266460398438335949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228708118177640265625557299 343062177266460398438335949)
    ·
      refine ⟨128648316474922649414375981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343062177266460398438335949 128648316474922649414375981)
      ·
        refine ⟨48243118678095993530390993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128648316474922649414375981 48243118678095993530390993)
        ·
          refine ⟨36182339008571995147793245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48243118678095993530390993 36182339008571995147793245)
          ·
            refine ⟨13568377128214498180422467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36182339008571995147793245 13568377128214498180422467)
            ·
              refine ⟨20352565692321747270633701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13568377128214498180422467 20352565692321747270633701)
              ·
                refine ⟨3816106067310327613243819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20352565692321747270633701 3816106067310327613243819)
                ·
                  refine ⟨5724159100965491419865729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816106067310327613243819 5724159100965491419865729)
                  ·
                    refine ⟨4293119325724118564899297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5724159100965491419865729 4293119325724118564899297)
                    ·
                      refine ⟨3219839494293088923674473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293119325724118564899297 3219839494293088923674473)
                      ·
                        rfl

theorem cell23_6270615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_6270615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270615 prefixEnd_6270615 := by exact prefixLift 6270615
  have htrace : WordTrace (prefixWord ++ tailWord_6270615) baseStart_6270615 baseEnd_6270615 := by
    simpa [prefixWord, tailWord_6270615, baseEnd_6270615] using wordTrace_append hprefix tailTrace_6270615
  have hstable : (prefixWord ++ tailWord_6270615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270615).length < 2 ^ (prefixWord ++ tailWord_6270615).sum := by decide
  have hdescent : baseEnd_6270615 < baseStart_6270615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270638 : List Nat := [4, 1, 4, 1, 2, 1, 3, 7]
def baseStart_6270638 : Nat := 118140960795 + 6270638 * 2 ^ 59
def prefixEnd_6270638 : Nat := 4983230072969 + 3 ^ 40 * 6270638 * 2
def baseEnd_6270638 : Nat := 119253752012894160506921

theorem tailTrace_6270638 : CollatzResearch.WordTrace tailWord_6270638 prefixEnd_6270638 119253752012894160506921 := by
  unfold tailWord_6270638
  simp only [CollatzResearch.WordTrace]
  refine ⟨28588619632069617569205571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152472638037704627035763045 28588619632069617569205571)
  ·
    refine ⟨42882929448104426353808357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28588619632069617569205571 42882929448104426353808357)
    ·
      refine ⟨8040549271519579941339067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42882929448104426353808357 8040549271519579941339067)
      ·
        refine ⟨12060823907279369912008601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040549271519579941339067 12060823907279369912008601)
        ·
          refine ⟨9045617930459527434006451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12060823907279369912008601 9045617930459527434006451)
          ·
            refine ⟨13568426895689291151009677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9045617930459527434006451 13568426895689291151009677)
            ·
              refine ⟨5088160085883484181628629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13568426895689291151009677 5088160085883484181628629)
              ·
                refine ⟨119253752012894160506921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5088160085883484181628629 119253752012894160506921)
                ·
                  rfl

theorem cell23_6270638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_6270638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270638 prefixEnd_6270638 := by exact prefixLift 6270638
  have htrace : WordTrace (prefixWord ++ tailWord_6270638) baseStart_6270638 baseEnd_6270638 := by
    simpa [prefixWord, tailWord_6270638, baseEnd_6270638] using wordTrace_append hprefix tailTrace_6270638
  have hstable : (prefixWord ++ tailWord_6270638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270638).length < 2 ^ (prefixWord ++ tailWord_6270638).sum := by decide
  have hdescent : baseEnd_6270638 < baseStart_6270638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270688 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2]
def baseStart_6270688 : Nat := 118140960795 + 6270688 * 2 ^ 59
def prefixEnd_6270688 : Nat := 4983230072969 + 3 ^ 40 * 6270688 * 2
def baseEnd_6270688 : Nat := 3219876978380867138061637

theorem tailTrace_6270688 : CollatzResearch.WordTrace tailWord_6270688 prefixEnd_6270688 3219876978380867138061637 := by
  unfold tailWord_6270688
  simp only [CollatzResearch.WordTrace]
  refine ⟨114355390353187899546482359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152473853804250532728643145 114355390353187899546482359)
  ·
    refine ⟨171533085529781849319723539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114355390353187899546482359 171533085529781849319723539)
    ·
      refine ⟨257299628294672773979585309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171533085529781849319723539 257299628294672773979585309)
      ·
        refine ⟨96487360610502290242344491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257299628294672773979585309 96487360610502290242344491)
        ·
          refine ⟨144731040915753435363516737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96487360610502290242344491 144731040915753435363516737)
          ·
            refine ⟨108548280686815076522637553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144731040915753435363516737 108548280686815076522637553)
            ·
              refine ⟨81411210515111307391978165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108548280686815076522637553 81411210515111307391978165)
              ·
                refine ⟨7632300985791685067997953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81411210515111307391978165 7632300985791685067997953)
                ·
                  refine ⟨5724225739343763800998465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7632300985791685067997953 5724225739343763800998465)
                  ·
                    refine ⟨4293169304507822850748849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5724225739343763800998465 4293169304507822850748849)
                    ·
                      refine ⟨3219876978380867138061637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293169304507822850748849 3219876978380867138061637)
                      ·
                        rfl

theorem cell23_6270688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_6270688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270688 prefixEnd_6270688 := by exact prefixLift 6270688
  have htrace : WordTrace (prefixWord ++ tailWord_6270688) baseStart_6270688 baseEnd_6270688 := by
    simpa [prefixWord, tailWord_6270688, baseEnd_6270688] using wordTrace_append hprefix tailTrace_6270688
  have hstable : (prefixWord ++ tailWord_6270688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270688).length < 2 ^ (prefixWord ++ tailWord_6270688).sum := by decide
  have hdescent : baseEnd_6270688 < baseStart_6270688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270704 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_6270704 : Nat := 118140960795 + 6270704 * 2 ^ 59
def prefixEnd_6270704 : Nat := 4983230072969 + 3 ^ 40 * 6270704 * 2
def baseEnd_6270704 : Nat := 3219885194071339075461563

theorem tailTrace_6270704 : CollatzResearch.WordTrace tailWord_6270704 prefixEnd_6270704 3219885194071339075461563 := by
  unfold tailWord_6270704
  simp only [CollatzResearch.WordTrace]
  refine ⟨114355682137158916912773583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152474242849545222550364777 114355682137158916912773583)
  ·
    refine ⟨171533523205738375369160375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114355682137158916912773583 171533523205738375369160375)
    ·
      refine ⟨257300284808607563053740563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171533523205738375369160375 257300284808607563053740563)
      ·
        refine ⟨385950427212911344580610845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257300284808607563053740563 385950427212911344580610845)
        ·
          refine ⟨144731410204841754217729067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385950427212911344580610845 144731410204841754217729067)
          ·
            refine ⟨217097115307262631326593601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144731410204841754217729067 217097115307262631326593601)
            ·
              refine ⟨162822836480446973494945201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217097115307262631326593601 162822836480446973494945201)
              ·
                refine ⟨122117127360335230121208901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162822836480446973494945201 122117127360335230121208901)
                ·
                  refine ⟨22896961380062855647726669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122117127360335230121208901 22896961380062855647726669)
                  ·
                    refine ⟨8586360517523570867897501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22896961380062855647726669 8586360517523570867897501)
                    ·
                      refine ⟨3219885194071339075461563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8586360517523570867897501 3219885194071339075461563)
                      ·
                        rfl

theorem cell23_6270704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_6270704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270704 prefixEnd_6270704 := by exact prefixLift 6270704
  have htrace : WordTrace (prefixWord ++ tailWord_6270704) baseStart_6270704 baseEnd_6270704 := by
    simpa [prefixWord, tailWord_6270704, baseEnd_6270704] using wordTrace_append hprefix tailTrace_6270704
  have hstable : (prefixWord ++ tailWord_6270704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270704).length < 2 ^ (prefixWord ++ tailWord_6270704).sum := by decide
  have hdescent : baseEnd_6270704 < baseStart_6270704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270708 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6270708 : Nat := 118140960795 + 6270708 * 2 ^ 59
def prefixEnd_6270708 : Nat := 4983230072969 + 3 ^ 40 * 6270708 * 2
def baseEnd_6270708 : Nat := 3219887247993957059811545

theorem tailTrace_6270708 : CollatzResearch.WordTrace tailWord_6270708 prefixEnd_6270708 3219887247993957059811545 := by
  unfold tailWord_6270708
  simp only [CollatzResearch.WordTrace]
  refine ⟨114355755083151671254346389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152474340110868895005795185 114355755083151671254346389)
  ·
    refine ⟨5360426019522734590047487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114355755083151671254346389 5360426019522734590047487)
    ·
      refine ⟨8040639029284101885071231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360426019522734590047487 8040639029284101885071231)
      ·
        refine ⟨12060958543926152827606847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040639029284101885071231 12060958543926152827606847)
        ·
          refine ⟨18091437815889229241410271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12060958543926152827606847 18091437815889229241410271)
          ·
            refine ⟨27137156723833843862115407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18091437815889229241410271 27137156723833843862115407)
            ·
              refine ⟨40705735085750765793173111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27137156723833843862115407 40705735085750765793173111)
              ·
                refine ⟨61058602628626148689759667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40705735085750765793173111 61058602628626148689759667)
                ·
                  refine ⟨91587903942939223034639501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61058602628626148689759667 91587903942939223034639501)
                  ·
                    refine ⟨34345463978602208637989813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91587903942939223034639501 34345463978602208637989813)
                    ·
                      refine ⟨3219887247993957059811545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34345463978602208637989813 3219887247993957059811545)
                      ·
                        rfl

theorem cell23_6270708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6270708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270708 prefixEnd_6270708 := by exact prefixLift 6270708
  have htrace : WordTrace (prefixWord ++ tailWord_6270708) baseStart_6270708 baseEnd_6270708 := by
    simpa [prefixWord, tailWord_6270708, baseEnd_6270708] using wordTrace_append hprefix tailTrace_6270708
  have hstable : (prefixWord ++ tailWord_6270708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270708).length < 2 ^ (prefixWord ++ tailWord_6270708).sum := by decide
  have hdescent : baseEnd_6270708 < baseStart_6270708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270711 : List Nat := [1, 1, 3, 1, 1, 1, 7, 3, 5]
def baseStart_6270711 : Nat := 118140960795 + 6270711 * 2 ^ 59
def prefixEnd_6270711 : Nat := 4983230072969 + 3 ^ 40 * 6270711 * 2
def baseEnd_6270711 : Nat := 357765420937324505341559

theorem tailTrace_6270711 : CollatzResearch.WordTrace tailWord_6270711 prefixEnd_6270711 357765420937324505341559 := by
  unfold tailWord_6270711
  simp only [CollatzResearch.WordTrace]
  refine ⟨228711619585292474021051987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152474413056861649347367991 228711619585292474021051987)
  ·
    refine ⟨343067429377938711031577981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228711619585292474021051987 343067429377938711031577981)
    ·
      refine ⟨128650286016727016636841743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343067429377938711031577981 128650286016727016636841743)
      ·
        refine ⟨192975429025090524955262615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128650286016727016636841743 192975429025090524955262615)
        ·
          refine ⟨289463143537635787432893923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192975429025090524955262615 289463143537635787432893923)
          ·
            refine ⟨434194715306453681149340885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289463143537635787432893923 434194715306453681149340885)
            ·
              refine ⟨10176438639995008151937677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 434194715306453681149340885 10176438639995008151937677)
              ·
                refine ⟨3816164489998128056976629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10176438639995008151937677 3816164489998128056976629)
                ·
                  refine ⟨357765420937324505341559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3816164489998128056976629 357765420937324505341559)
                  ·
                    rfl

theorem cell23_6270711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 3, 5].length) (baseStart_6270711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270711 prefixEnd_6270711 := by exact prefixLift 6270711
  have htrace : WordTrace (prefixWord ++ tailWord_6270711) baseStart_6270711 baseEnd_6270711 := by
    simpa [prefixWord, tailWord_6270711, baseEnd_6270711] using wordTrace_append hprefix tailTrace_6270711
  have hstable : (prefixWord ++ tailWord_6270711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270711).length < 2 ^ (prefixWord ++ tailWord_6270711).sum := by decide
  have hdescent : baseEnd_6270711 < baseStart_6270711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270728 : List Nat := [2, 1, 3, 2, 2, 1, 5, 2, 5]
def baseStart_6270728 : Nat := 118140960795 + 6270728 * 2 ^ 59
def prefixEnd_6270728 : Nat := 4983230072969 + 3 ^ 40 * 6270728 * 2
def baseEnd_6270728 : Nat := 357766390845227442395717

theorem tailTrace_6270728 : CollatzResearch.WordTrace tailWord_6270728 prefixEnd_6270728 357766390845227442395717 := by
  unfold tailWord_6270728
  simp only [CollatzResearch.WordTrace]
  refine ⟨114356119813115442962210419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152474826417487257282947225 114356119813115442962210419)
  ·
    refine ⟨171534179719673164443315629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114356119813115442962210419 171534179719673164443315629)
    ·
      refine ⟨64325317394877436666243361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171534179719673164443315629 64325317394877436666243361)
      ·
        refine ⟨48243988046158077499682521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64325317394877436666243361 48243988046158077499682521)
        ·
          refine ⟨36182991034618558124761891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48243988046158077499682521 36182991034618558124761891)
          ·
            refine ⟨54274486551927837187142837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36182991034618558124761891 54274486551927837187142837)
            ·
              refine ⟨5088233114243234736294641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54274486551927837187142837 5088233114243234736294641)
              ·
                refine ⟨3816174835682426052220981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088233114243234736294641 3816174835682426052220981)
                ·
                  refine ⟨357766390845227442395717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3816174835682426052220981 357766390845227442395717)
                  ·
                    rfl

theorem cell23_6270728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 2, 5].length) (baseStart_6270728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270728 prefixEnd_6270728 := by exact prefixLift 6270728
  have htrace : WordTrace (prefixWord ++ tailWord_6270728) baseStart_6270728 baseEnd_6270728 := by
    simpa [prefixWord, tailWord_6270728, baseEnd_6270728] using wordTrace_append hprefix tailTrace_6270728
  have hstable : (prefixWord ++ tailWord_6270728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270728).length < 2 ^ (prefixWord ++ tailWord_6270728).sum := by decide
  have hdescent : baseEnd_6270728 < baseStart_6270728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270733 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_6270733 : Nat := 118140960795 + 6270733 * 2 ^ 59
def prefixEnd_6270733 : Nat := 4983230072969 + 3 ^ 40 * 6270733 * 2
def baseEnd_6270733 : Nat := 3219900085010319461998931

theorem tailTrace_6270733 : CollatzResearch.WordTrace tailWord_6270733 prefixEnd_6270733 3219900085010319461998931 := by
  unfold tailWord_6270733
  simp only [CollatzResearch.WordTrace]
  refine ⟨228712421991212771778352853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152474947994141847852235235 228712421991212771778352853)
  ·
    refine ⟨5360447390419049338555145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 228712421991212771778352853 5360447390419049338555145)
    ·
      refine ⟨4020335542814287003916359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5360447390419049338555145 4020335542814287003916359)
      ·
        refine ⟨6030503314221430505874539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4020335542814287003916359 6030503314221430505874539)
        ·
          refine ⟨9045754971332145758811809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6030503314221430505874539 9045754971332145758811809)
          ·
            refine ⟨6784316228499109319108857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9045754971332145758811809 6784316228499109319108857)
            ·
              refine ⟨5088237171374331989331643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6784316228499109319108857 5088237171374331989331643)
              ·
                refine ⟨7632355757061497983997465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088237171374331989331643 7632355757061497983997465)
                ·
                  refine ⟨5724266817796123487998099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7632355757061497983997465 5724266817796123487998099)
                  ·
                    refine ⟨8586400226694185231997149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724266817796123487998099 8586400226694185231997149)
                    ·
                      refine ⟨3219900085010319461998931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8586400226694185231997149 3219900085010319461998931)
                      ·
                        rfl

theorem cell23_6270733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_6270733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270733 prefixEnd_6270733 := by exact prefixLift 6270733
  have htrace : WordTrace (prefixWord ++ tailWord_6270733) baseStart_6270733 baseEnd_6270733 := by
    simpa [prefixWord, tailWord_6270733, baseEnd_6270733] using wordTrace_append hprefix tailTrace_6270733
  have hstable : (prefixWord ++ tailWord_6270733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270733).length < 2 ^ (prefixWord ++ tailWord_6270733).sum := by decide
  have hdescent : baseEnd_6270733 < baseStart_6270733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270734 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6270734 : Nat := 118140960795 + 6270734 * 2 ^ 59
def prefixEnd_6270734 : Nat := 4983230072969 + 3 ^ 40 * 6270734 * 2
def baseEnd_6270734 : Nat := 3219900598490973958086425

theorem tailTrace_6270734 : CollatzResearch.WordTrace tailWord_6270734 prefixEnd_6270734 3219900598490973958086425 := by
  unfold tailWord_6270734
  simp only [CollatzResearch.WordTrace]
  refine ⟨28589057308026143618642407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152474972309472765966092837 28589057308026143618642407)
  ·
    refine ⟨42883585962039215427963611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28589057308026143618642407 42883585962039215427963611)
    ·
      refine ⟨64325378943058823141945417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42883585962039215427963611 64325378943058823141945417)
      ·
        refine ⟨48244034207294117356459063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64325378943058823141945417 48244034207294117356459063)
        ·
          refine ⟨72366051310941176034688595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48244034207294117356459063 72366051310941176034688595)
          ·
            refine ⟨108549076966411764052032893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72366051310941176034688595 108549076966411764052032893)
            ·
              refine ⟨40705903862404411519512335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108549076966411764052032893 40705903862404411519512335)
              ·
                refine ⟨61058855793606617279268503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40705903862404411519512335 61058855793606617279268503)
                ·
                  refine ⟨91588283690409925918902755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61058855793606617279268503 91588283690409925918902755)
                  ·
                    refine ⟨137382425535614888878354133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91588283690409925918902755 137382425535614888878354133)
                    ·
                      refine ⟨3219900598490973958086425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 137382425535614888878354133 3219900598490973958086425)
                      ·
                        rfl

theorem cell23_6270734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6270734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270734 prefixEnd_6270734 := by exact prefixLift 6270734
  have htrace : WordTrace (prefixWord ++ tailWord_6270734) baseStart_6270734 baseEnd_6270734 := by
    simpa [prefixWord, tailWord_6270734, baseEnd_6270734] using wordTrace_append hprefix tailTrace_6270734
  have hstable : (prefixWord ++ tailWord_6270734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270734).length < 2 ^ (prefixWord ++ tailWord_6270734).sum := by decide
  have hdescent : baseEnd_6270734 < baseStart_6270734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270744 : List Nat := [2, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6270744 : Nat := 118140960795 + 6270744 * 2 ^ 59
def prefixEnd_6270744 : Nat := 4983230072969 + 3 ^ 40 * 6270744 * 2
def baseEnd_6270744 : Nat := 3219905733297518918961379

theorem tailTrace_6270744 : CollatzResearch.WordTrace tailWord_6270744 prefixEnd_6270744 3219905733297518918961379 := by
  unfold tailWord_6270744
  simp only [CollatzResearch.WordTrace]
  refine ⟨114356411597086460328501643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152475215462781947104668857 114356411597086460328501643)
  ·
    refine ⟨171534617395629690492752465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114356411597086460328501643 171534617395629690492752465)
    ·
      refine ⟨128650963046722267869564349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171534617395629690492752465 128650963046722267869564349)
      ·
        refine ⟨48244111142520850451086631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128650963046722267869564349 48244111142520850451086631)
        ·
          refine ⟨72366166713781275676629947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48244111142520850451086631 72366166713781275676629947)
          ·
            refine ⟨108549250070671913514944921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72366166713781275676629947 108549250070671913514944921)
            ·
              refine ⟨81411937553003935136208691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108549250070671913514944921 81411937553003935136208691)
              ·
                refine ⟨122117906329505902704313037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81411937553003935136208691 122117906329505902704313037)
                ·
                  refine ⟨45794214873564713514117389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122117906329505902704313037 45794214873564713514117389)
                  ·
                    refine ⟨17172830577586767567794021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45794214873564713514117389 17172830577586767567794021)
                    ·
                      refine ⟨3219905733297518918961379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17172830577586767567794021 3219905733297518918961379)
                      ·
                        rfl

theorem cell23_6270744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6270744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270744 prefixEnd_6270744 := by exact prefixLift 6270744
  have htrace : WordTrace (prefixWord ++ tailWord_6270744) baseStart_6270744 baseEnd_6270744 := by
    simpa [prefixWord, tailWord_6270744, baseEnd_6270744] using wordTrace_append hprefix tailTrace_6270744
  have hstable : (prefixWord ++ tailWord_6270744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270744).length < 2 ^ (prefixWord ++ tailWord_6270744).sum := by decide
  have hdescent : baseEnd_6270744 < baseStart_6270744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270801 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 6]
def baseStart_6270801 : Nat := 118140960795 + 6270801 * 2 ^ 59
def prefixEnd_6270801 : Nat := 4983230072969 + 3 ^ 40 * 6270801 * 2
def baseEnd_6270801 : Nat := 357770555743869466216513

theorem tailTrace_6270801 : CollatzResearch.WordTrace tailWord_6270801 prefixEnd_6270801 357770555743869466216513 := by
  unfold tailWord_6270801
  simp only [CollatzResearch.WordTrace]
  refine ⟨228714902154966419391828257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152476601436644279594552171 228714902154966419391828257)
  ·
    refine ⟨171536176616224814543871193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228714902154966419391828257 171536176616224814543871193)
    ·
      refine ⟨128652132462168610907903395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171536176616224814543871193 128652132462168610907903395)
      ·
        refine ⟨192978198693252916361855093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128652132462168610907903395 192978198693252916361855093)
        ·
          refine ⟨18091706127492460908923915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 192978198693252916361855093 18091706127492460908923915)
          ·
            refine ⟨27137559191238691363385873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18091706127492460908923915 27137559191238691363385873)
            ·
              refine ⟨20353169393429018522539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27137559191238691363385873 20353169393429018522539405)
              ·
                refine ⟨7632438522535881945952277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20353169393429018522539405 7632438522535881945952277)
                ·
                  refine ⟨357770555743869466216513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7632438522535881945952277 357770555743869466216513)
                  ·
                    rfl

theorem cell23_6270801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_6270801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270801 prefixEnd_6270801 := by exact prefixLift 6270801
  have htrace : WordTrace (prefixWord ++ tailWord_6270801) baseStart_6270801 baseEnd_6270801 := by
    simpa [prefixWord, tailWord_6270801, baseEnd_6270801] using wordTrace_append hprefix tailTrace_6270801
  have hstable : (prefixWord ++ tailWord_6270801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270801).length < 2 ^ (prefixWord ++ tailWord_6270801).sum := by decide
  have hdescent : baseEnd_6270801 < baseStart_6270801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270812 : List Nat := [2, 2, 4, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6270812 : Nat := 118140960795 + 6270812 * 2 ^ 59
def prefixEnd_6270812 : Nat := 4983230072969 + 3 ^ 40 * 6270812 * 2
def baseEnd_6270812 : Nat := 3219940649982024652911067

theorem tailTrace_6270812 : CollatzResearch.WordTrace tailWord_6270812 prefixEnd_6270812 3219940649982024652911067 := by
  unfold tailWord_6270812
  simp only [CollatzResearch.WordTrace]
  refine ⟨114357651678963284135239345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152476868905284378846985793 114357651678963284135239345)
  ·
    refine ⟨85768238759222463101429509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114357651678963284135239345 85768238759222463101429509)
    ·
      refine ⟨16081544767354211831518033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85768238759222463101429509 16081544767354211831518033)
      ·
        refine ⟨12061158575515658873638525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16081544767354211831518033 12061158575515658873638525)
        ·
          refine ⟨4522934465818372077614447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12061158575515658873638525 4522934465818372077614447)
          ·
            refine ⟨6784401698727558116421671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4522934465818372077614447 6784401698727558116421671)
            ·
              refine ⟨10176602548091337174632507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784401698727558116421671 10176602548091337174632507)
              ·
                refine ⟨15264903822137005761948761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10176602548091337174632507 15264903822137005761948761)
                ·
                  refine ⟨11448677866602754321461571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15264903822137005761948761 11448677866602754321461571)
                  ·
                    refine ⟨17173016799904131482192357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11448677866602754321461571 17173016799904131482192357)
                    ·
                      refine ⟨3219940649982024652911067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17173016799904131482192357 3219940649982024652911067)
                      ·
                        rfl

theorem cell23_6270812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6270812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270812 prefixEnd_6270812 := by exact prefixLift 6270812
  have htrace : WordTrace (prefixWord ++ tailWord_6270812) baseStart_6270812 baseEnd_6270812 := by
    simpa [prefixWord, tailWord_6270812, baseEnd_6270812] using wordTrace_append hprefix tailTrace_6270812
  have hstable : (prefixWord ++ tailWord_6270812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270812).length < 2 ^ (prefixWord ++ tailWord_6270812).sum := by decide
  have hdescent : baseEnd_6270812 < baseStart_6270812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270844 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_6270844 : Nat := 118140960795 + 6270844 * 2 ^ 59
def prefixEnd_6270844 : Nat := 4983230072969 + 3 ^ 40 * 6270844 * 2
def baseEnd_6270844 : Nat := 1073319027120989509236973

theorem tailTrace_6270844 : CollatzResearch.WordTrace tailWord_6270844 prefixEnd_6270844 1073319027120989509236973 := by
  unfold tailWord_6270844
  simp only [CollatzResearch.WordTrace]
  refine ⟨114358235246905318867821793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152477646995873758490429057 114358235246905318867821793)
  ·
    refine ⟨85768676435178989150866345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114358235246905318867821793 85768676435178989150866345)
    ·
      refine ⟨64326507326384241863149759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85768676435178989150866345 64326507326384241863149759)
      ·
        refine ⟨96489760989576362794724639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64326507326384241863149759 96489760989576362794724639)
        ·
          refine ⟨144734641484364544192086959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96489760989576362794724639 144734641484364544192086959)
          ·
            refine ⟨217101962226546816288130439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144734641484364544192086959 217101962226546816288130439)
            ·
              refine ⟨325652943339820224432195659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217101962226546816288130439 325652943339820224432195659)
              ·
                refine ⟨488479415009730336648293489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325652943339820224432195659 488479415009730336648293489)
                ·
                  refine ⟨366359561257297752486220117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 488479415009730336648293489 366359561257297752486220117)
                  ·
                    refine ⟨1073319027120989509236973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 366359561257297752486220117 1073319027120989509236973)
                    ·
                      rfl

theorem cell23_6270844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_6270844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270844 prefixEnd_6270844 := by exact prefixLift 6270844
  have htrace : WordTrace (prefixWord ++ tailWord_6270844) baseStart_6270844 baseEnd_6270844 := by
    simpa [prefixWord, tailWord_6270844, baseEnd_6270844] using wordTrace_append hprefix tailTrace_6270844
  have hstable : (prefixWord ++ tailWord_6270844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270844).length < 2 ^ (prefixWord ++ tailWord_6270844).sum := by decide
  have hdescent : baseEnd_6270844 < baseStart_6270844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270879 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6270879 : Nat := 118140960795 + 6270879 * 2 ^ 59
def prefixEnd_6270879 : Nat := 4983230072969 + 3 ^ 40 * 6270879 * 2
def baseEnd_6270879 : Nat := 3219975053185875890773259

theorem tailTrace_6270879 : CollatzResearch.WordTrace tailWord_6270879 prefixEnd_6270879 3219975053185875890773259 := by
  unfold tailWord_6270879
  simp only [CollatzResearch.WordTrace]
  refine ⟨228717747048683838713167691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152478498032455892475445127 228717747048683838713167691)
  ·
    refine ⟨343076620573025758069751537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228717747048683838713167691 343076620573025758069751537)
    ·
      refine ⟨257307465429769318552313653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343076620573025758069751537 257307465429769318552313653)
      ·
        refine ⟨24122574884040873614279405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257307465429769318552313653 24122574884040873614279405)
        ·
          refine ⟨9045965581515327605354777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24122574884040873614279405 9045965581515327605354777)
          ·
            refine ⟨6784474186136495704016083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9045965581515327605354777 6784474186136495704016083)
            ·
              refine ⟨10176711279204743556024125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784474186136495704016083 10176711279204743556024125)
              ·
                refine ⟨3816266729701778833509047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10176711279204743556024125 3816266729701778833509047)
                ·
                  refine ⟨5724400094552668250263571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816266729701778833509047 5724400094552668250263571)
                  ·
                    refine ⟨8586600141829002375395357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724400094552668250263571 8586600141829002375395357)
                    ·
                      refine ⟨3219975053185875890773259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8586600141829002375395357 3219975053185875890773259)
                      ·
                        rfl

theorem cell23_6270879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6270879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270879 prefixEnd_6270879 := by exact prefixLift 6270879
  have htrace : WordTrace (prefixWord ++ tailWord_6270879) baseStart_6270879 baseEnd_6270879 := by
    simpa [prefixWord, tailWord_6270879, baseEnd_6270879] using wordTrace_append hprefix tailTrace_6270879
  have hstable : (prefixWord ++ tailWord_6270879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270879).length < 2 ^ (prefixWord ++ tailWord_6270879).sum := by decide
  have hdescent : baseEnd_6270879 < baseStart_6270879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270945 : List Nat := [1, 2, 3, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_6270945 : Nat := 118140960795 + 6270945 * 2 ^ 59
def prefixEnd_6270945 : Nat := 4983230072969 + 3 ^ 40 * 6270945 * 2
def baseEnd_6270945 : Nat := 3220008942909072632547955

theorem tailTrace_6270945 : CollatzResearch.WordTrace tailWord_6270945 prefixEnd_6270945 3220008942909072632547955 := by
  unfold tailWord_6270945
  simp only [CollatzResearch.WordTrace]
  refine ⟨228720154266444731985070289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152480102844296487990046859 228720154266444731985070289)
  ·
    refine ⟨171540115699833548988802717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228720154266444731985070289 171540115699833548988802717)
    ·
      refine ⟨64327543387437580870801019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171540115699833548988802717 64327543387437580870801019)
      ·
        refine ⟨96491315081156371306201529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64327543387437580870801019 96491315081156371306201529)
        ·
          refine ⟨72368486310867278479651147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96491315081156371306201529 72368486310867278479651147)
          ·
            refine ⟨108552729466300917719476721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72368486310867278479651147 108552729466300917719476721)
            ·
              refine ⟨81414547099725688289607541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108552729466300917719476721 81414547099725688289607541)
              ·
                refine ⟨7632613790599283277150707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81414547099725688289607541 7632613790599283277150707)
                ·
                  refine ⟨11448920685898924915726061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632613790599283277150707 11448920685898924915726061)
                  ·
                    refine ⟨4293345257212096843397273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11448920685898924915726061 4293345257212096843397273)
                    ·
                      refine ⟨3220008942909072632547955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293345257212096843397273 3220008942909072632547955)
                      ·
                        rfl

theorem cell23_6270945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_6270945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270945 prefixEnd_6270945 := by exact prefixLift 6270945
  have htrace : WordTrace (prefixWord ++ tailWord_6270945) baseStart_6270945 baseEnd_6270945 := by
    simpa [prefixWord, tailWord_6270945, baseEnd_6270945] using wordTrace_append hprefix tailTrace_6270945
  have hstable : (prefixWord ++ tailWord_6270945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270945).length < 2 ^ (prefixWord ++ tailWord_6270945).sum := by decide
  have hdescent : baseEnd_6270945 < baseStart_6270945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270958 : List Nat := [4, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4]
def baseStart_6270958 : Nat := 118140960795 + 6270958 * 2 ^ 59
def prefixEnd_6270958 : Nat := 4983230072969 + 3 ^ 40 * 6270958 * 2
def baseEnd_6270958 : Nat := 3220015618157581081685395

theorem tailTrace_6270958 : CollatzResearch.WordTrace tailWord_6270958 prefixEnd_6270958 3220015618157581081685395 := by
  unfold tailWord_6270958
  simp only [CollatzResearch.WordTrace]
  refine ⟨28590078551924704400661691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152480418943598423470195685 28590078551924704400661691)
  ·
    refine ⟨42885117827887056600992537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28590078551924704400661691 42885117827887056600992537)
    ·
      refine ⟨32163838370915292450744403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42885117827887056600992537 32163838370915292450744403)
      ·
        refine ⟨48245757556372938676116605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32163838370915292450744403 48245757556372938676116605)
        ·
          refine ⟨18092159083639852003543727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48245757556372938676116605 18092159083639852003543727)
          ·
            refine ⟨27138238625459778005315591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092159083639852003543727 27138238625459778005315591)
            ·
              refine ⟨40707357938189667007973387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138238625459778005315591 40707357938189667007973387)
              ·
                refine ⟨61061036907284500511960081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40707357938189667007973387 61061036907284500511960081)
                ·
                  refine ⟨45795777680463375383970061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61061036907284500511960081 45795777680463375383970061)
                  ·
                    refine ⟨17173416630173765768988773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45795777680463375383970061 17173416630173765768988773)
                    ·
                      refine ⟨3220015618157581081685395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17173416630173765768988773 3220015618157581081685395)
                      ·
                        rfl

theorem cell23_6270958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_6270958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270958 prefixEnd_6270958 := by exact prefixLift 6270958
  have htrace : WordTrace (prefixWord ++ tailWord_6270958) baseStart_6270958 baseEnd_6270958 := by
    simpa [prefixWord, tailWord_6270958, baseEnd_6270958] using wordTrace_append hprefix tailTrace_6270958
  have hstable : (prefixWord ++ tailWord_6270958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270958).length < 2 ^ (prefixWord ++ tailWord_6270958).sum := by decide
  have hdescent : baseEnd_6270958 < baseStart_6270958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270971 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4]
def baseStart_6270971 : Nat := 118140960795 + 6270971 * 2 ^ 59
def prefixEnd_6270971 : Nat := 4983230072969 + 3 ^ 40 * 6270971 * 2
def baseEnd_6270971 : Nat := 3220022293406089530822835

theorem tailTrace_6270971 : CollatzResearch.WordTrace tailWord_6270971 prefixEnd_6270971 3220022293406089530822835 := by
  unfold tailWord_6270971
  simp only [CollatzResearch.WordTrace]
  refine ⟨228721102564350538425516767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152480735042900358950344511 228721102564350538425516767)
  ·
    refine ⟨343081653846525807638275151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228721102564350538425516767 343081653846525807638275151)
    ·
      refine ⟨514622480769788711457412727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343081653846525807638275151 514622480769788711457412727)
      ·
        refine ⟨771933721154683067186119091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514622480769788711457412727 771933721154683067186119091)
        ·
          refine ⟨1157900581732024600779178637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771933721154683067186119091 1157900581732024600779178637)
          ·
            refine ⟨434212718149509225292191989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1157900581732024600779178637 434212718149509225292191989)
            ·
              refine ⟨40707442326516489871142999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 434212718149509225292191989 40707442326516489871142999)
              ·
                refine ⟨61061163489774734806714499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40707442326516489871142999 61061163489774734806714499)
                ·
                  refine ⟨91591745234662102210071749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61061163489774734806714499 91591745234662102210071749)
                  ·
                    refine ⟨17173452231499144164388453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91591745234662102210071749 17173452231499144164388453)
                    ·
                      refine ⟨3220022293406089530822835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17173452231499144164388453 3220022293406089530822835)
                      ·
                        rfl

theorem cell23_6270971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 4, 4].length) (baseStart_6270971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270971 prefixEnd_6270971 := by exact prefixLift 6270971
  have htrace : WordTrace (prefixWord ++ tailWord_6270971) baseStart_6270971 baseEnd_6270971 := by
    simpa [prefixWord, tailWord_6270971, baseEnd_6270971] using wordTrace_append hprefix tailTrace_6270971
  have hstable : (prefixWord ++ tailWord_6270971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270971).length < 2 ^ (prefixWord ++ tailWord_6270971).sum := by decide
  have hdescent : baseEnd_6270971 < baseStart_6270971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270981 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 9]
def baseStart_6270981 : Nat := 118140960795 + 6270981 * 2 ^ 59
def prefixEnd_6270981 : Nat := 4983230072969 + 3 ^ 40 * 6270981 * 2
def baseEnd_6270981 : Nat := 357780825356959387966421

theorem tailTrace_6270981 : CollatzResearch.WordTrace tailWord_6270981 prefixEnd_6270981 357780825356959387966421 := by
  unfold tailWord_6270981
  simp only [CollatzResearch.WordTrace]
  refine ⟨228721467294314310133380797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152480978196209540088920531 228721467294314310133380797)
  ·
    refine ⟨85770550235367866300017799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228721467294314310133380797 85770550235367866300017799)
    ·
      refine ⟨128655825353051799450026699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85770550235367866300017799 128655825353051799450026699)
      ·
        refine ⟨192983738029577699175040049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128655825353051799450026699 192983738029577699175040049)
        ·
          refine ⟨144737803522183274381280037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 192983738029577699175040049 144737803522183274381280037)
          ·
            refine ⟨27138338160409363946490007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144737803522183274381280037 27138338160409363946490007)
            ·
              refine ⟨40707507240614045919735011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138338160409363946490007 40707507240614045919735011)
              ·
                refine ⟨61061260860921068879602517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40707507240614045919735011 61061260860921068879602517)
                ·
                  refine ⟨357780825356959387966421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61061260860921068879602517 357780825356959387966421)
                  ·
                    rfl

theorem cell23_6270981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_6270981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270981 prefixEnd_6270981 := by exact prefixLift 6270981
  have htrace : WordTrace (prefixWord ++ tailWord_6270981) baseStart_6270981 baseEnd_6270981 := by
    simpa [prefixWord, tailWord_6270981, baseEnd_6270981] using wordTrace_append hprefix tailTrace_6270981
  have hstable : (prefixWord ++ tailWord_6270981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270981).length < 2 ^ (prefixWord ++ tailWord_6270981).sum := by decide
  have hdescent : baseEnd_6270981 < baseStart_6270981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6270996 : List Nat := [2, 4, 3, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_6270996 : Nat := 118140960795 + 6270996 * 2 ^ 59
def prefixEnd_6270996 : Nat := 4983230072969 + 3 ^ 40 * 6270996 * 2
def baseEnd_6270996 : Nat := 3220035130422451933010221

theorem tailTrace_6270996 : CollatzResearch.WordTrace tailWord_6270996 prefixEnd_6270996 3220035130422451933010221 := by
  unfold tailWord_6270996
  simp only [CollatzResearch.WordTrace]
  refine ⟨114361007194629983847588421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152481342926173311796784561 114361007194629983847588421)
  ·
    refine ⟨21442688848993121971422829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114361007194629983847588421 21442688848993121971422829)
    ·
      refine ⟨8041008318372420739283561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21442688848993121971422829 8041008318372420739283561)
      ·
        refine ⟨6030756238779315554462671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041008318372420739283561 6030756238779315554462671)
        ·
          refine ⟨9046134358168973331694007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6030756238779315554462671 9046134358168973331694007)
          ·
            refine ⟨13569201537253459997541011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046134358168973331694007 13569201537253459997541011)
            ·
              refine ⟨20353802305880189996311517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13569201537253459997541011 20353802305880189996311517)
              ·
                refine ⟨7632675864705071248616819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20353802305880189996311517 7632675864705071248616819)
                ·
                  refine ⟨11449013797057606872925229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632675864705071248616819 11449013797057606872925229)
                  ·
                    refine ⟨4293380173896602577346961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11449013797057606872925229 4293380173896602577346961)
                    ·
                      refine ⟨3220035130422451933010221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293380173896602577346961 3220035130422451933010221)
                      ·
                        rfl

theorem cell23_6270996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_6270996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6270996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6270996 prefixEnd_6270996 := by exact prefixLift 6270996
  have htrace : WordTrace (prefixWord ++ tailWord_6270996) baseStart_6270996 baseEnd_6270996 := by
    simpa [prefixWord, tailWord_6270996, baseEnd_6270996] using wordTrace_append hprefix tailTrace_6270996
  have hstable : (prefixWord ++ tailWord_6270996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6270996).length < 2 ^ (prefixWord ++ tailWord_6270996).sum := by decide
  have hdescent : baseEnd_6270996 < baseStart_6270996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6270996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271062 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_6271062 : Nat := 118140960795 + 6271062 * 2 ^ 59
def prefixEnd_6271062 : Nat := 4983230072969 + 3 ^ 40 * 6271062 * 2
def baseEnd_6271062 : Nat := 1073356340048549558261639

theorem tailTrace_6271062 : CollatzResearch.WordTrace tailWord_6271062 prefixEnd_6271062 1073356340048549558261639 := by
  unfold tailWord_6271062
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295276350438803810442465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152482947738013907311386293 14295276350438803810442465)
  ·
    refine ⟨10721457262829102857831849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14295276350438803810442465 10721457262829102857831849)
    ·
      refine ⟨8041092947121827143373887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10721457262829102857831849 8041092947121827143373887)
      ·
        refine ⟨12061639420682740715060831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8041092947121827143373887 12061639420682740715060831)
        ·
          refine ⟨18092459131024111072591247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061639420682740715060831 18092459131024111072591247)
          ·
            refine ⟨27138688696536166608886871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092459131024111072591247 27138688696536166608886871)
            ·
              refine ⟨40708033044804249913330307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27138688696536166608886871 40708033044804249913330307)
              ·
                refine ⟨61062049567206374869995461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40708033044804249913330307 61062049567206374869995461)
                ·
                  refine ⟨11449134293851195288124149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61062049567206374869995461 11449134293851195288124149)
                  ·
                    refine ⟨1073356340048549558261639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11449134293851195288124149 1073356340048549558261639)
                    ·
                      rfl

theorem cell23_6271062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_6271062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271062 prefixEnd_6271062 := by exact prefixLift 6271062
  have htrace : WordTrace (prefixWord ++ tailWord_6271062) baseStart_6271062 baseEnd_6271062 := by
    simpa [prefixWord, tailWord_6271062, baseEnd_6271062] using wordTrace_append hprefix tailTrace_6271062
  have hstable : (prefixWord ++ tailWord_6271062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271062).length < 2 ^ (prefixWord ++ tailWord_6271062).sum := by decide
  have hdescent : baseEnd_6271062 < baseStart_6271062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271075 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 3, 4]
def baseStart_6271075 : Nat := 118140960795 + 6271075 * 2 ^ 59
def prefixEnd_6271075 : Nat := 4983230072969 + 3 ^ 40 * 6271075 * 2
def baseEnd_6271075 : Nat := 1073358565131385707974119

theorem tailTrace_6271075 : CollatzResearch.WordTrace tailWord_6271075 prefixEnd_6271075 1073358565131385707974119 := by
  unfold tailWord_6271075
  simp only [CollatzResearch.WordTrace]
  refine ⟨228724895755973764187302679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152483263837315842791535119 228724895755973764187302679)
  ·
    refine ⟨343087343633960646280954019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228724895755973764187302679 343087343633960646280954019)
    ·
      refine ⟨514631015450940969421431029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343087343633960646280954019 514631015450940969421431029)
      ·
        refine ⟨48246657698525715883259159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 514631015450940969421431029 48246657698525715883259159)
        ·
          refine ⟨72369986547788573824888739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48246657698525715883259159 72369986547788573824888739)
          ·
            refine ⟨108554979821682860737333109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72369986547788573824888739 108554979821682860737333109)
            ·
              refine ⟨10177029358282768194124979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108554979821682860737333109 10177029358282768194124979)
              ·
                refine ⟨15265544037424152291187469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10177029358282768194124979 15265544037424152291187469)
                ·
                  refine ⟨5724579014034057109195301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15265544037424152291187469 5724579014034057109195301)
                  ·
                    refine ⟨1073358565131385707974119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724579014034057109195301 1073358565131385707974119)
                    ·
                      rfl

theorem cell23_6271075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 4].length) (baseStart_6271075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271075 prefixEnd_6271075 := by exact prefixLift 6271075
  have htrace : WordTrace (prefixWord ++ tailWord_6271075) baseStart_6271075 baseEnd_6271075 := by
    simpa [prefixWord, tailWord_6271075, baseEnd_6271075] using wordTrace_append hprefix tailTrace_6271075
  have hstable : (prefixWord ++ tailWord_6271075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271075).length < 2 ^ (prefixWord ++ tailWord_6271075).sum := by decide
  have hdescent : baseEnd_6271075 < baseStart_6271075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271085 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6271085 : Nat := 118140960795 + 6271085 * 2 ^ 59
def prefixEnd_6271085 : Nat := 4983230072969 + 3 ^ 40 * 6271085 * 2
def baseEnd_6271085 : Nat := 3220080830200702084797311

theorem tailTrace_6271085 : CollatzResearch.WordTrace tailWord_6271085 prefixEnd_6271085 3220080830200702084797311 := by
  unfold tailWord_6271085
  simp only [CollatzResearch.WordTrace]
  refine ⟨228725260485937535895166709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152483506990625023930111139 228725260485937535895166709)
  ·
    refine ⟨21442993170556643990171879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228725260485937535895166709 21442993170556643990171879)
    ·
      refine ⟨32164489755834965985257819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21442993170556643990171879 32164489755834965985257819)
      ·
        refine ⟨48246734633752448977886729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32164489755834965985257819 48246734633752448977886729)
        ·
          refine ⟨36185050975314336733415047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48246734633752448977886729 36185050975314336733415047)
          ·
            refine ⟨54277576462971505100122571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36185050975314336733415047 54277576462971505100122571)
            ·
              refine ⟨81416364694457257650183857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54277576462971505100122571 81416364694457257650183857)
              ·
                refine ⟨61062273520842943237637893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81416364694457257650183857 61062273520842943237637893)
                ·
                  refine ⟨11449176285158051857057105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61062273520842943237637893 11449176285158051857057105)
                  ·
                    refine ⟨8586882213868538892792829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11449176285158051857057105 8586882213868538892792829)
                    ·
                      refine ⟨3220080830200702084797311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8586882213868538892792829 3220080830200702084797311)
                      ·
                        rfl

theorem cell23_6271085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6271085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271085 prefixEnd_6271085 := by exact prefixLift 6271085
  have htrace : WordTrace (prefixWord ++ tailWord_6271085) baseStart_6271085 baseEnd_6271085 := by
    simpa [prefixWord, tailWord_6271085, baseEnd_6271085] using wordTrace_append hprefix tailTrace_6271085
  have hstable : (prefixWord ++ tailWord_6271085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271085).length < 2 ^ (prefixWord ++ tailWord_6271085).sum := by decide
  have hdescent : baseEnd_6271085 < baseStart_6271085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271132 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6271132 : Nat := 118140960795 + 6271132 * 2 ^ 59
def prefixEnd_6271132 : Nat := 4983230072969 + 3 ^ 40 * 6271132 * 2
def baseEnd_6271132 : Nat := 3220104963791463400909595

theorem tailTrace_6271132 : CollatzResearch.WordTrace tailWord_6271132 prefixEnd_6271132 3220104963791463400909595 := by
  unfold tailWord_6271132
  simp only [CollatzResearch.WordTrace]
  refine ⟨114363487358383631461063825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152484649811178175281418433 114363487358383631461063825)
  ·
    refine ⟨85772615518787723595797869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114363487358383631461063825 85772615518787723595797869)
    ·
      refine ⟨32164730819545396348424201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85772615518787723595797869 32164730819545396348424201)
      ·
        refine ⟨24123548114659047261318151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32164730819545396348424201 24123548114659047261318151)
        ·
          refine ⟨36185322171988570891977227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24123548114659047261318151 36185322171988570891977227)
          ·
            refine ⟨54277983257982856337965841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36185322171988570891977227 54277983257982856337965841)
            ·
              refine ⟨40708487443487142253474381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54277983257982856337965841 40708487443487142253474381)
              ·
                refine ⟨15265682791307678345052893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40708487443487142253474381 15265682791307678345052893)
                ·
                  refine ⟨5724631046740379379394835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15265682791307678345052893 5724631046740379379394835)
                  ·
                    refine ⟨8586946570110569069092253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724631046740379379394835 8586946570110569069092253)
                    ·
                      refine ⟨3220104963791463400909595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8586946570110569069092253 3220104963791463400909595)
                      ·
                        rfl

theorem cell23_6271132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6271132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271132 prefixEnd_6271132 := by exact prefixLift 6271132
  have htrace : WordTrace (prefixWord ++ tailWord_6271132) baseStart_6271132 baseEnd_6271132 := by
    simpa [prefixWord, tailWord_6271132, baseEnd_6271132] using wordTrace_append hprefix tailTrace_6271132
  have hstable : (prefixWord ++ tailWord_6271132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271132).length < 2 ^ (prefixWord ++ tailWord_6271132).sum := by decide
  have hdescent : baseEnd_6271132 < baseStart_6271132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271135 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 3, 5]
def baseStart_6271135 : Nat := 118140960795 + 6271135 * 2 ^ 59
def prefixEnd_6271135 : Nat := 4983230072969 + 3 ^ 40 * 6271135 * 2
def baseEnd_6271135 : Nat := 1073368834744475629724027

theorem tailTrace_6271135 : CollatzResearch.WordTrace tailWord_6271135 prefixEnd_6271135 1073368834744475629724027 := by
  unfold tailWord_6271135
  simp only [CollatzResearch.WordTrace]
  refine ⟨228727084135756394434486859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152484722757170929622991239 228727084135756394434486859)
  ·
    refine ⟨343090626203634591651730289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228727084135756394434486859 343090626203634591651730289)
    ·
      refine ⟨257317969652725943738797717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343090626203634591651730289 257317969652725943738797717)
      ·
        refine ⟨12061779827471528612756143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257317969652725943738797717 12061779827471528612756143)
        ·
          refine ⟨18092669741207292919134215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061779827471528612756143 18092669741207292919134215)
          ·
            refine ⟨27139004611810939378701323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18092669741207292919134215 27139004611810939378701323)
            ·
              refine ⟨40708506917716409068051985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27139004611810939378701323 40708506917716409068051985)
              ·
                refine ⟨30531380188287306801038989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40708506917716409068051985 30531380188287306801038989)
                ·
                  refine ⟨11449267570607740050389621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30531380188287306801038989 11449267570607740050389621)
                  ·
                    refine ⟨1073368834744475629724027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11449267570607740050389621 1073368834744475629724027)
                    ·
                      rfl

theorem cell23_6271135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 5].length) (baseStart_6271135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271135 prefixEnd_6271135 := by exact prefixLift 6271135
  have htrace : WordTrace (prefixWord ++ tailWord_6271135) baseStart_6271135 baseEnd_6271135 := by
    simpa [prefixWord, tailWord_6271135, baseEnd_6271135] using wordTrace_append hprefix tailTrace_6271135
  have hstable : (prefixWord ++ tailWord_6271135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271135).length < 2 ^ (prefixWord ++ tailWord_6271135).sum := by decide
  have hdescent : baseEnd_6271135 < baseStart_6271135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271149 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_6271149 : Nat := 118140960795 + 6271149 * 2 ^ 59
def prefixEnd_6271149 : Nat := 4983230072969 + 3 ^ 40 * 6271149 * 2
def baseEnd_6271149 : Nat := 3220113692962589834397017

theorem tailTrace_6271149 : CollatzResearch.WordTrace tailWord_6271149 prefixEnd_6271149 3220113692962589834397017 := by
  unfold tailWord_6271149
  simp only [CollatzResearch.WordTrace]
  refine ⟨228727594757705674825496501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152485063171803783216997667 228727594757705674825496501)
  ·
    refine ⟨21443212008534907014890297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228727594757705674825496501 21443212008534907014890297)
    ·
      refine ⟨16082409006401180261167723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21443212008534907014890297 16082409006401180261167723)
      ·
        refine ⟨24123613509601770391751585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16082409006401180261167723 24123613509601770391751585)
        ·
          refine ⟨18092710132201327793813689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24123613509601770391751585 18092710132201327793813689)
          ·
            refine ⟨13569532599150995845360267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18092710132201327793813689 13569532599150995845360267)
            ·
              refine ⟨20354298898726493768040401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13569532599150995845360267 20354298898726493768040401)
              ·
                refine ⟨15265724174044870326030301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20354298898726493768040401 15265724174044870326030301)
                ·
                  refine ⟨5724646565266826372261363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15265724174044870326030301 5724646565266826372261363)
                  ·
                    refine ⟨8586969847900239558392045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724646565266826372261363 8586969847900239558392045)
                    ·
                      refine ⟨3220113692962589834397017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8586969847900239558392045 3220113692962589834397017)
                      ·
                        rfl

theorem cell23_6271149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_6271149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271149 prefixEnd_6271149 := by exact prefixLift 6271149
  have htrace : WordTrace (prefixWord ++ tailWord_6271149) baseStart_6271149 baseEnd_6271149 := by
    simpa [prefixWord, tailWord_6271149, baseEnd_6271149] using wordTrace_append hprefix tailTrace_6271149
  have hstable : (prefixWord ++ tailWord_6271149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271149).length < 2 ^ (prefixWord ++ tailWord_6271149).sum := by decide
  have hdescent : baseEnd_6271149 < baseStart_6271149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271155 : List Nat := [1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 4]
def baseStart_6271155 : Nat := 118140960795 + 6271155 * 2 ^ 59
def prefixEnd_6271155 : Nat := 4983230072969 + 3 ^ 40 * 6271155 * 2
def baseEnd_6271155 : Nat := 3220116773846516810921989

theorem tailTrace_6271155 : CollatzResearch.WordTrace tailWord_6271155 prefixEnd_6271155 3220116773846516810921989 := by
  unfold tailWord_6271155
  simp only [CollatzResearch.WordTrace]
  refine ⟨228727813595683937850214919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152485209063789291900143279 228727813595683937850214919)
  ·
    refine ⟨343091720393525906775322379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228727813595683937850214919 343091720393525906775322379)
    ·
      refine ⟨514637580590288860162983569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343091720393525906775322379 514637580590288860162983569)
      ·
        refine ⟨385978185442716645122237677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514637580590288860162983569 385978185442716645122237677)
        ·
          refine ⟨144741819541018741920839129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385978185442716645122237677 144741819541018741920839129)
          ·
            refine ⟨108556364655764056440629347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144741819541018741920839129 108556364655764056440629347)
            ·
              refine ⟨162834546983646084660944021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108556364655764056440629347 162834546983646084660944021)
              ·
                refine ⟨7632869389858410218481751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162834546983646084660944021 7632869389858410218481751)
                ·
                  refine ⟨11449304084787615327722627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632869389858410218481751 11449304084787615327722627)
                  ·
                    refine ⟨17173956127181422991583941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11449304084787615327722627 17173956127181422991583941)
                    ·
                      refine ⟨3220116773846516810921989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17173956127181422991583941 3220116773846516810921989)
                      ·
                        rfl

theorem cell23_6271155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 1, 4].length) (baseStart_6271155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271155 prefixEnd_6271155 := by exact prefixLift 6271155
  have htrace : WordTrace (prefixWord ++ tailWord_6271155) baseStart_6271155 baseEnd_6271155 := by
    simpa [prefixWord, tailWord_6271155, baseEnd_6271155] using wordTrace_append hprefix tailTrace_6271155
  have hstable : (prefixWord ++ tailWord_6271155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271155).length < 2 ^ (prefixWord ++ tailWord_6271155).sum := by decide
  have hdescent : baseEnd_6271155 < baseStart_6271155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271159 : List Nat := [1, 1, 3, 1, 4, 4, 1, 1, 2, 3, 2]
def baseStart_6271159 : Nat := 118140960795 + 6271159 * 2 ^ 59
def prefixEnd_6271159 : Nat := 4983230072969 + 3 ^ 40 * 6271159 * 2
def baseEnd_6271159 : Nat := 3220118827769134795271971

theorem tailTrace_6271159 : CollatzResearch.WordTrace tailWord_6271159 prefixEnd_6271159 3220118827769134795271971 := by
  unfold tailWord_6271159
  simp only [CollatzResearch.WordTrace]
  refine ⟨228727959487669446533360531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152485306325112964355573687 228727959487669446533360531)
  ·
    refine ⟨343091939231504169800040797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228727959487669446533360531 343091939231504169800040797)
    ·
      refine ⟨128659477211814063675015299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343091939231504169800040797 128659477211814063675015299)
      ·
        refine ⟨192989215817721095512522949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128659477211814063675015299 192989215817721095512522949)
        ·
          refine ⟨36185477965822705408598053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 192989215817721095512522949 36185477965822705408598053)
          ·
            refine ⟨6784777118591757264112135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36185477965822705408598053 6784777118591757264112135)
            ·
              refine ⟨10177165677887635896168203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6784777118591757264112135 10177165677887635896168203)
              ·
                refine ⟨15265748516831453844252305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10177165677887635896168203 15265748516831453844252305)
                ·
                  refine ⟨11449311387623590383189229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15265748516831453844252305 11449311387623590383189229)
                  ·
                    refine ⟨4293491770358846393695961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11449311387623590383189229 4293491770358846393695961)
                    ·
                      refine ⟨3220118827769134795271971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293491770358846393695961 3220118827769134795271971)
                      ·
                        rfl

theorem cell23_6271159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_6271159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271159 prefixEnd_6271159 := by exact prefixLift 6271159
  have htrace : WordTrace (prefixWord ++ tailWord_6271159) baseStart_6271159 baseEnd_6271159 := by
    simpa [prefixWord, tailWord_6271159, baseEnd_6271159] using wordTrace_append hprefix tailTrace_6271159
  have hstable : (prefixWord ++ tailWord_6271159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271159).length < 2 ^ (prefixWord ++ tailWord_6271159).sum := by decide
  have hdescent : baseEnd_6271159 < baseStart_6271159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271165 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_6271165 : Nat := 118140960795 + 6271165 * 2 ^ 59
def prefixEnd_6271165 : Nat := 4983230072969 + 3 ^ 40 * 6271165 * 2
def baseEnd_6271165 : Nat := 1073373969551020590598981

theorem tailTrace_6271165 : CollatzResearch.WordTrace tailWord_6271165 prefixEnd_6271165 1073373969551020590598981 := by
  unfold tailWord_6271165
  simp only [CollatzResearch.WordTrace]
  refine ⟨228728178325647709558078949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152485452217098473038719299 228728178325647709558078949)
  ·
    refine ⟨42886533436058945542139803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228728178325647709558078949 42886533436058945542139803)
    ·
      refine ⟨64329800154088418313209705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42886533436058945542139803 64329800154088418313209705)
      ·
        refine ⟨48247350115566313734907279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64329800154088418313209705 48247350115566313734907279)
        ·
          refine ⟨72371025173349470602360919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48247350115566313734907279 72371025173349470602360919)
          ·
            refine ⟨108556537760024205903541379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72371025173349470602360919 108556537760024205903541379)
            ·
              refine ⟨162834806640036308855312069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108556537760024205903541379 162834806640036308855312069)
              ·
                refine ⟨30531526245006807910371013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162834806640036308855312069 30531526245006807910371013)
                ·
                  refine ⟨5724661170938776483194565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30531526245006807910371013 5724661170938776483194565)
                  ·
                    refine ⟨1073373969551020590598981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724661170938776483194565 1073373969551020590598981)
                    ·
                      rfl

theorem cell23_6271165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_6271165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271165 prefixEnd_6271165 := by exact prefixLift 6271165
  have htrace : WordTrace (prefixWord ++ tailWord_6271165) baseStart_6271165 baseEnd_6271165 := by
    simpa [prefixWord, tailWord_6271165, baseEnd_6271165] using wordTrace_append hprefix tailTrace_6271165
  have hstable : (prefixWord ++ tailWord_6271165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271165).length < 2 ^ (prefixWord ++ tailWord_6271165).sum := by decide
  have hdescent : baseEnd_6271165 < baseStart_6271165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271169 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6271169 : Nat := 118140960795 + 6271169 * 2 ^ 59
def prefixEnd_6271169 : Nat := 4983230072969 + 3 ^ 40 * 6271169 * 2
def baseEnd_6271169 : Nat := 1073374654191893252048975

theorem tailTrace_6271169 : CollatzResearch.WordTrace tailWord_6271169 prefixEnd_6271169 1073374654191893252048975 := by
  unfold tailWord_6271169
  simp only [CollatzResearch.WordTrace]
  refine ⟨228728324217633218241224561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152485549478422145494149707 228728324217633218241224561)
  ·
    refine ⟨171546243163224913680918421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228728324217633218241224561 171546243163224913680918421)
    ·
      refine ⟨8041230148276167828793051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 171546243163224913680918421 8041230148276167828793051)
      ·
        refine ⟨12061845222414251743189577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8041230148276167828793051 12061845222414251743189577)
        ·
          refine ⟨9046383916810688807392183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12061845222414251743189577 9046383916810688807392183)
          ·
            refine ⟨13569575875216033211088275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046383916810688807392183 13569575875216033211088275)
            ·
              refine ⟨20354363812824049816632413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13569575875216033211088275 20354363812824049816632413)
              ·
                refine ⟨7632886429809018681237155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20354363812824049816632413 7632886429809018681237155)
                ·
                  refine ⟨11449329644713528021855733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7632886429809018681237155 11449329644713528021855733)
                  ·
                    refine ⟨1073374654191893252048975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11449329644713528021855733 1073374654191893252048975)
                    ·
                      rfl

theorem cell23_6271169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6271169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271169 prefixEnd_6271169 := by exact prefixLift 6271169
  have htrace : WordTrace (prefixWord ++ tailWord_6271169) baseStart_6271169 baseEnd_6271169 := by
    simpa [prefixWord, tailWord_6271169, baseEnd_6271169] using wordTrace_append hprefix tailTrace_6271169
  have hstable : (prefixWord ++ tailWord_6271169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271169).length < 2 ^ (prefixWord ++ tailWord_6271169).sum := by decide
  have hdescent : baseEnd_6271169 < baseStart_6271169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271178 : List Nat := [3, 1, 2, 1, 3, 1, 12]
def baseStart_6271178 : Nat := 118140960795 + 6271178 * 2 ^ 59
def prefixEnd_6271178 : Nat := 4983230072969 + 3 ^ 40 * 6271178 * 2
def baseEnd_6271178 : Nat := 39754673875328027418943

theorem tailTrace_6271178 : CollatzResearch.WordTrace tailWord_6271178 prefixEnd_6271178 39754673875328027418943 := by
  unfold tailWord_6271178
  simp only [CollatzResearch.WordTrace]
  refine ⟨57182163118650153194575547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152485768316400408518868125 57182163118650153194575547)
  ·
    refine ⟨85773244677975229791863321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57182163118650153194575547 85773244677975229791863321)
    ·
      refine ⟨64329933508481422343897491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85773244677975229791863321 64329933508481422343897491)
      ·
        refine ⟨96494900262722133515846237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64329933508481422343897491 96494900262722133515846237)
        ·
          refine ⟨36185587598520800068442339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96494900262722133515846237 36185587598520800068442339)
          ·
            refine ⟨54278381397781200102663509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36185587598520800068442339 54278381397781200102663509)
            ·
              refine ⟨39754673875328027418943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54278381397781200102663509 39754673875328027418943)
              ·
                rfl

theorem cell23_6271178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 12].length) (baseStart_6271178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271178 prefixEnd_6271178 := by exact prefixLift 6271178
  have htrace : WordTrace (prefixWord ++ tailWord_6271178) baseStart_6271178 baseEnd_6271178 := by
    simpa [prefixWord, tailWord_6271178, baseEnd_6271178] using wordTrace_append hprefix tailTrace_6271178
  have hstable : (prefixWord ++ tailWord_6271178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271178).length < 2 ^ (prefixWord ++ tailWord_6271178).sum := by decide
  have hdescent : baseEnd_6271178 < baseStart_6271178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271182 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_6271182 : Nat := 118140960795 + 6271182 * 2 ^ 59
def prefixEnd_6271182 : Nat := 4983230072969 + 3 ^ 40 * 6271182 * 2
def baseEnd_6271182 : Nat := 1073376879274729401761455

theorem tailTrace_6271182 : CollatzResearch.WordTrace tailWord_6271182 prefixEnd_6271182 1073376879274729401761455 := by
  unfold tailWord_6271182
  simp only [CollatzResearch.WordTrace]
  refine ⟨28591099795823265182680975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152485865577724080974298533 28591099795823265182680975)
  ·
    refine ⟨42886649693734897774021463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28591099795823265182680975 42886649693734897774021463)
    ·
      refine ⟨64329974540602346661032195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42886649693734897774021463 64329974540602346661032195)
      ·
        refine ⟨96494961810903519991548293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64329974540602346661032195 96494961810903519991548293)
        ·
          refine ⟨18092805339544409998415305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96494961810903519991548293 18092805339544409998415305)
          ·
            refine ⟨13569604004658307498811479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18092805339544409998415305 13569604004658307498811479)
            ·
              refine ⟨20354406006987461248217219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13569604004658307498811479 20354406006987461248217219)
              ·
                refine ⟨30531609010481191872325829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20354406006987461248217219 30531609010481191872325829)
                ·
                  refine ⟨5724676689465223476061093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30531609010481191872325829 5724676689465223476061093)
                  ·
                    refine ⟨1073376879274729401761455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724676689465223476061093 1073376879274729401761455)
                    ·
                      rfl

theorem cell23_6271182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_6271182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271182 prefixEnd_6271182 := by exact prefixLift 6271182
  have htrace : WordTrace (prefixWord ++ tailWord_6271182) baseStart_6271182 baseEnd_6271182 := by
    simpa [prefixWord, tailWord_6271182, baseEnd_6271182] using wordTrace_append hprefix tailTrace_6271182
  have hstable : (prefixWord ++ tailWord_6271182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271182).length < 2 ^ (prefixWord ++ tailWord_6271182).sum := by decide
  have hdescent : baseEnd_6271182 < baseStart_6271182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271222 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6271222 : Nat := 118140960795 + 6271222 * 2 ^ 59
def prefixEnd_6271222 : Nat := 4983230072969 + 3 ^ 40 * 6271222 * 2
def baseEnd_6271222 : Nat := 3220151177050368048784181

theorem tailTrace_6271222 : CollatzResearch.WordTrace tailWord_6271222 prefixEnd_6271222 3220151177050368048784181 := by
  unfold tailWord_6271222
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295641080402575518306495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152486838190960805528602613 14295641080402575518306495)
  ·
    refine ⟨21443461620603863277459743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14295641080402575518306495 21443461620603863277459743)
    ·
      refine ⟨32165192430905794916189615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21443461620603863277459743 32165192430905794916189615)
      ·
        refine ⟨48247788646358692374284423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32165192430905794916189615 48247788646358692374284423)
        ·
          refine ⟨72371682969538038561426635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48247788646358692374284423 72371682969538038561426635)
          ·
            refine ⟨108557524454307057842139953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72371682969538038561426635 108557524454307057842139953)
            ·
              refine ⟨81418143340730293381604965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108557524454307057842139953 81418143340730293381604965)
              ·
                refine ⟨15265901876386930009050931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81418143340730293381604965 15265901876386930009050931)
                ·
                  refine ⟨22898852814580395013576397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15265901876386930009050931 22898852814580395013576397)
                  ·
                    refine ⟨8587069805467648130091149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22898852814580395013576397 8587069805467648130091149)
                    ·
                      refine ⟨3220151177050368048784181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587069805467648130091149 3220151177050368048784181)
                      ·
                        rfl

theorem cell23_6271222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6271222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271222 prefixEnd_6271222 := by exact prefixLift 6271222
  have htrace : WordTrace (prefixWord ++ tailWord_6271222) baseStart_6271222 baseEnd_6271222 := by
    simpa [prefixWord, tailWord_6271222, baseEnd_6271222] using wordTrace_append hprefix tailTrace_6271222
  have hstable : (prefixWord ++ tailWord_6271222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271222).length < 2 ^ (prefixWord ++ tailWord_6271222).sum := by decide
  have hdescent : baseEnd_6271222 < baseStart_6271222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271265 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_6271265 : Nat := 118140960795 + 6271265 * 2 ^ 59
def prefixEnd_6271265 : Nat := 4983230072969 + 3 ^ 40 * 6271265 * 2
def baseEnd_6271265 : Nat := 3220173256718511380546483

theorem tailTrace_6271265 : CollatzResearch.WordTrace tailWord_6271265 prefixEnd_6271265 3220173256718511380546483 := by
  unfold tailWord_6271265
  simp only [CollatzResearch.WordTrace]
  refine ⟨228731825625285426636719249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152487883750190284424479499 228731825625285426636719249)
  ·
    refine ⟨171548869218964069977539437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228731825625285426636719249 171548869218964069977539437)
    ·
      refine ⟨64330825957111526241577289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171548869218964069977539437 64330825957111526241577289)
      ·
        refine ⟨48248119467833644681182967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64330825957111526241577289 48248119467833644681182967)
        ·
          refine ⟨72372179201750467021774451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48248119467833644681182967 72372179201750467021774451)
          ·
            refine ⟨108558268802625700532661677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72372179201750467021774451 108558268802625700532661677)
            ·
              refine ⟨40709350800984637699748129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108558268802625700532661677 40709350800984637699748129)
              ·
                refine ⟨30532013100738478274811097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40709350800984637699748129 30532013100738478274811097)
                ·
                  refine ⟨22899009825553858706108323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30532013100738478274811097 22899009825553858706108323)
                  ·
                    refine ⟨34348514738330788059162485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22899009825553858706108323 34348514738330788059162485)
                    ·
                      refine ⟨3220173256718511380546483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34348514738330788059162485 3220173256718511380546483)
                      ·
                        rfl

theorem cell23_6271265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_6271265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271265 prefixEnd_6271265 := by exact prefixLift 6271265
  have htrace : WordTrace (prefixWord ++ tailWord_6271265) baseStart_6271265 baseEnd_6271265 := by
    simpa [prefixWord, tailWord_6271265, baseEnd_6271265] using wordTrace_append hprefix tailTrace_6271265
  have hstable : (prefixWord ++ tailWord_6271265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271265).length < 2 ^ (prefixWord ++ tailWord_6271265).sum := by decide
  have hdescent : baseEnd_6271265 < baseStart_6271265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271266 : List Nat := [3, 3, 1, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_6271266 : Nat := 118140960795 + 6271266 * 2 ^ 59
def prefixEnd_6271266 : Nat := 4983230072969 + 3 ^ 40 * 6271266 * 2
def baseEnd_6271266 : Nat := 3220173770199165876633979

theorem tailTrace_6271266 : CollatzResearch.WordTrace tailWord_6271266 prefixEnd_6271266 3220173770199165876633979 := by
  unfold tailWord_6271266
  simp only [CollatzResearch.WordTrace]
  refine ⟨57182965524570450951876413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152487908065521202538337101 57182965524570450951876413)
  ·
    refine ⟨21443612071713919106953655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57182965524570450951876413 21443612071713919106953655)
    ·
      refine ⟨32165418107570878660430483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21443612071713919106953655 32165418107570878660430483)
      ·
        refine ⟨48248127161356317990645725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32165418107570878660430483 48248127161356317990645725)
        ·
          refine ⟨18093047685508619246492147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48248127161356317990645725 18093047685508619246492147)
          ·
            refine ⟨27139571528262928869738221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18093047685508619246492147 27139571528262928869738221)
            ·
              refine ⟨10177339323098598326151833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27139571528262928869738221 10177339323098598326151833)
              ·
                refine ⟨7633004492323948744613875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10177339323098598326151833 7633004492323948744613875)
                ·
                  refine ⟨11449506738485923116920813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633004492323948744613875 11449506738485923116920813)
                  ·
                    refine ⟨4293565026932221168845305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11449506738485923116920813 4293565026932221168845305)
                    ·
                      refine ⟨3220173770199165876633979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293565026932221168845305 3220173770199165876633979)
                      ·
                        rfl

theorem cell23_6271266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_6271266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271266 prefixEnd_6271266 := by exact prefixLift 6271266
  have htrace : WordTrace (prefixWord ++ tailWord_6271266) baseStart_6271266 baseEnd_6271266 := by
    simpa [prefixWord, tailWord_6271266, baseEnd_6271266] using wordTrace_append hprefix tailTrace_6271266
  have hstable : (prefixWord ++ tailWord_6271266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271266).length < 2 ^ (prefixWord ++ tailWord_6271266).sum := by decide
  have hdescent : baseEnd_6271266 < baseStart_6271266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271312 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_6271312 : Nat := 118140960795 + 6271312 * 2 ^ 59
def prefixEnd_6271312 : Nat := 4983230072969 + 3 ^ 40 * 6271312 * 2
def baseEnd_6271312 : Nat := 3220197390309272696658767

theorem tailTrace_6271312 : CollatzResearch.WordTrace tailWord_6271312 prefixEnd_6271312 3220197390309272696658767 := by
  unfold tailWord_6271312
  simp only [CollatzResearch.WordTrace]
  refine ⟨114366769928057576831840095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152489026570743435775786793 114366769928057576831840095)
  ·
    refine ⟨171550154892086365247760143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114366769928057576831840095 171550154892086365247760143)
    ·
      refine ⟨257325232338129547871640215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171550154892086365247760143 257325232338129547871640215)
      ·
        refine ⟨385987848507194321807460323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257325232338129547871640215 385987848507194321807460323)
        ·
          refine ⟨578981772760791482711190485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385987848507194321807460323 578981772760791482711190485)
          ·
            refine ⟨13569885299081050376043527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 578981772760791482711190485 13569885299081050376043527)
            ·
              refine ⟨20354827948621575564065291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13569885299081050376043527 20354827948621575564065291)
              ·
                refine ⟨30532241922932363346097937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20354827948621575564065291 30532241922932363346097937)
                ·
                  refine ⟨22899181442199272509573453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30532241922932363346097937 22899181442199272509573453)
                  ·
                    refine ⟨8587193040824727191090045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22899181442199272509573453 8587193040824727191090045)
                    ·
                      refine ⟨3220197390309272696658767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587193040824727191090045 3220197390309272696658767)
                      ·
                        rfl

theorem cell23_6271312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_6271312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271312 prefixEnd_6271312 := by exact prefixLift 6271312
  have htrace : WordTrace (prefixWord ++ tailWord_6271312) baseStart_6271312 baseEnd_6271312 := by
    simpa [prefixWord, tailWord_6271312, baseEnd_6271312] using wordTrace_append hprefix tailTrace_6271312
  have hstable : (prefixWord ++ tailWord_6271312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271312).length < 2 ^ (prefixWord ++ tailWord_6271312).sum := by decide
  have hdescent : baseEnd_6271312 < baseStart_6271312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271322 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_6271322 : Nat := 118140960795 + 6271322 * 2 ^ 59
def prefixEnd_6271322 : Nat := 4983230072969 + 3 ^ 40 * 6271322 * 2
def baseEnd_6271322 : Nat := 3220202525115817657533721

theorem tailTrace_6271322 : CollatzResearch.WordTrace tailWord_6271322 prefixEnd_6271322 3220202525115817657533721 := by
  unfold tailWord_6271322
  simp only [CollatzResearch.WordTrace]
  refine ⟨57183476146519731342886055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152489269724052616914362813 57183476146519731342886055)
  ·
    refine ⟨85775214219779597014329083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57183476146519731342886055 85775214219779597014329083)
    ·
      refine ⟨128662821329669395521493625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85775214219779597014329083 128662821329669395521493625)
      ·
        refine ⟨96497115997252046641120219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128662821329669395521493625 96497115997252046641120219)
        ·
          refine ⟨144745673995878069961680329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96497115997252046641120219 144745673995878069961680329)
          ·
            refine ⟨108559255496908552471260247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144745673995878069961680329 108559255496908552471260247)
            ·
              refine ⟨162838883245362828706890371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108559255496908552471260247 162838883245362828706890371)
              ·
                refine ⟨244258324868044243060335557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162838883245362828706890371 244258324868044243060335557)
                ·
                  refine ⟨45798435912758295573812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244258324868044243060335557 45798435912758295573812917)
                  ·
                    refine ⟨4293603366821090210044961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45798435912758295573812917 4293603366821090210044961)
                    ·
                      refine ⟨3220202525115817657533721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293603366821090210044961 3220202525115817657533721)
                      ·
                        rfl

theorem cell23_6271322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_6271322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271322 prefixEnd_6271322 := by exact prefixLift 6271322
  have htrace : WordTrace (prefixWord ++ tailWord_6271322) baseStart_6271322 baseEnd_6271322 := by
    simpa [prefixWord, tailWord_6271322, baseEnd_6271322] using wordTrace_append hprefix tailTrace_6271322
  have hstable : (prefixWord ++ tailWord_6271322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271322).length < 2 ^ (prefixWord ++ tailWord_6271322).sum := by decide
  have hdescent : baseEnd_6271322 < baseStart_6271322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271365 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_6271365 : Nat := 118140960795 + 6271365 * 2 ^ 59
def prefixEnd_6271365 : Nat := 4983230072969 + 3 ^ 40 * 6271365 * 2
def baseEnd_6271365 : Nat := 3220224604783960989296023

theorem tailTrace_6271365 : CollatzResearch.WordTrace tailWord_6271365 prefixEnd_6271365 3220224604783960989296023 := by
  unfold tailWord_6271365
  simp only [CollatzResearch.WordTrace]
  refine ⟨228735472924923143715359549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152490315283282095810239699 228735472924923143715359549)
  ·
    refine ⟨85775802346846178893259831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228735472924923143715359549 85775802346846178893259831)
    ·
      refine ⟨128663703520269268339889747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85775802346846178893259831 128663703520269268339889747)
      ·
        refine ⟨192995555280403902509834621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128663703520269268339889747 192995555280403902509834621)
        ·
          refine ⟨72373333230151463441187983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192995555280403902509834621 72373333230151463441187983)
          ·
            refine ⟨108559999845227195161781975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72373333230151463441187983 108559999845227195161781975)
            ·
              refine ⟨162839999767840792742672963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108559999845227195161781975 162839999767840792742672963)
              ·
                refine ⟨244259999651761189114009445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162839999767840792742672963 244259999651761189114009445)
                ·
                  refine ⟨45798749934705222958876771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 244259999651761189114009445 45798749934705222958876771)
                  ·
                    refine ⟨68698124902057834438315157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45798749934705222958876771 68698124902057834438315157)
                    ·
                      refine ⟨3220224604783960989296023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68698124902057834438315157 3220224604783960989296023)
                      ·
                        rfl

theorem cell23_6271365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_6271365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271365 prefixEnd_6271365 := by exact prefixLift 6271365
  have htrace : WordTrace (prefixWord ++ tailWord_6271365) baseStart_6271365 baseEnd_6271365 := by
    simpa [prefixWord, tailWord_6271365, baseEnd_6271365] using wordTrace_append hprefix tailTrace_6271365
  have hstable : (prefixWord ++ tailWord_6271365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271365).length < 2 ^ (prefixWord ++ tailWord_6271365).sum := by decide
  have hdescent : baseEnd_6271365 < baseStart_6271365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271369 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 2, 4, 2]
def baseStart_6271369 : Nat := 118140960795 + 6271369 * 2 ^ 59
def prefixEnd_6271369 : Nat := 4983230072969 + 3 ^ 40 * 6271369 * 2
def baseEnd_6271369 : Nat := 3220226658706578973646005

theorem tailTrace_6271369 : CollatzResearch.WordTrace tailWord_6271369 prefixEnd_6271369 3220226658706578973646005 := by
  unfold tailWord_6271369
  simp only [CollatzResearch.WordTrace]
  refine ⟨228735618816908652398505161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152490412544605768265670107 228735618816908652398505161)
  ·
    refine ⟨171551714112681489298878871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228735618816908652398505161 171551714112681489298878871)
    ·
      refine ⟨257327571169022233948318307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171551714112681489298878871 257327571169022233948318307)
      ·
        refine ⟨385991356753533350922477461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257327571169022233948318307 385991356753533350922477461)
        ·
          refine ⟨18093344847821875824491131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 385991356753533350922477461 18093344847821875824491131)
          ·
            refine ⟨27140017271732813736736697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18093344847821875824491131 27140017271732813736736697)
            ·
              refine ⟨20355012953799610302552523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27140017271732813736736697 20355012953799610302552523)
              ·
                refine ⟨30532519430699415453828785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20355012953799610302552523 30532519430699415453828785)
                ·
                  refine ⟨22899389573024561590371589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30532519430699415453828785 22899389573024561590371589)
                  ·
                    refine ⟨4293635544942105298194673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22899389573024561590371589 4293635544942105298194673)
                    ·
                      refine ⟨3220226658706578973646005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293635544942105298194673 3220226658706578973646005)
                      ·
                        rfl

theorem cell23_6271369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 4, 2].length) (baseStart_6271369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271369 prefixEnd_6271369 := by exact prefixLift 6271369
  have htrace : WordTrace (prefixWord ++ tailWord_6271369) baseStart_6271369 baseEnd_6271369 := by
    simpa [prefixWord, tailWord_6271369, baseEnd_6271369] using wordTrace_append hprefix tailTrace_6271369
  have hstable : (prefixWord ++ tailWord_6271369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271369).length < 2 ^ (prefixWord ++ tailWord_6271369).sum := by decide
  have hdescent : baseEnd_6271369 < baseStart_6271369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271372 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_6271372 : Nat := 118140960795 + 6271372 * 2 ^ 59
def prefixEnd_6271372 : Nat := 4983230072969 + 3 ^ 40 * 6271372 * 2
def baseEnd_6271372 : Nat := 3220228199148542461908491

theorem tailTrace_6271372 : CollatzResearch.WordTrace tailWord_6271372 prefixEnd_6271372 3220228199148542461908491 := by
  unfold tailWord_6271372
  simp only [CollatzResearch.WordTrace]
  refine ⟨114367864117948891955432185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152490485490598522607242913 114367864117948891955432185)
  ·
    refine ⟨85775898088461668966574139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114367864117948891955432185 85775898088461668966574139)
    ·
      refine ⟨128663847132692503449861209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85775898088461668966574139 128663847132692503449861209)
      ·
        refine ⟨96497885349519377587395907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128663847132692503449861209 96497885349519377587395907)
        ·
          refine ⟨144746828024279066381093861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96497885349519377587395907 144746828024279066381093861)
          ·
            refine ⟨27140030254552324946455099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144746828024279066381093861 27140030254552324946455099)
            ·
              refine ⟨40710045381828487419682649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27140030254552324946455099 40710045381828487419682649)
              ·
                refine ⟨30532534036371365564761987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40710045381828487419682649 30532534036371365564761987)
                ·
                  refine ⟨45798801054557048347142981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30532534036371365564761987 45798801054557048347142981)
                  ·
                    refine ⟨8587275197729446565089309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45798801054557048347142981 8587275197729446565089309)
                    ·
                      refine ⟨3220228199148542461908491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587275197729446565089309 3220228199148542461908491)
                      ·
                        rfl

theorem cell23_6271372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_6271372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271372 prefixEnd_6271372 := by exact prefixLift 6271372
  have htrace : WordTrace (prefixWord ++ tailWord_6271372) baseStart_6271372 baseEnd_6271372 := by
    simpa [prefixWord, tailWord_6271372, baseEnd_6271372] using wordTrace_append hprefix tailTrace_6271372
  have hstable : (prefixWord ++ tailWord_6271372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271372).length < 2 ^ (prefixWord ++ tailWord_6271372).sum := by decide
  have hdescent : baseEnd_6271372 < baseStart_6271372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271396 : List Nat := [2, 3, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_6271396 : Nat := 118140960795 + 6271396 * 2 ^ 59
def prefixEnd_6271396 : Nat := 4983230072969 + 3 ^ 40 * 6271396 * 2
def baseEnd_6271396 : Nat := 1073413507561416789336127

theorem tailTrace_6271396 : CollatzResearch.WordTrace tailWord_6271396 prefixEnd_6271396 1073413507561416789336127 := by
  unfold tailWord_6271396
  simp only [CollatzResearch.WordTrace]
  refine ⟨114368301793905418004869021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152491069058540557339825361 114368301793905418004869021)
  ·
    refine ⟨42888113172714531751825883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114368301793905418004869021 42888113172714531751825883)
    ·
      refine ⟨64332169759071797627738825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42888113172714531751825883 64332169759071797627738825)
      ·
        refine ⟨48249127319303848220804119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64332169759071797627738825 48249127319303848220804119)
        ·
          refine ⟨72373690978955772331206179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48249127319303848220804119 72373690978955772331206179)
          ·
            refine ⟨108560536468433658496809269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72373690978955772331206179 108560536468433658496809269)
            ·
              refine ⟨10177550293915655484075869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108560536468433658496809269 10177550293915655484075869)
              ·
                refine ⟨3816581360218370806528451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10177550293915655484075869 3816581360218370806528451)
                ·
                  refine ⟨5724872040327556209792677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816581360218370806528451 5724872040327556209792677)
                  ·
                    refine ⟨1073413507561416789336127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724872040327556209792677 1073413507561416789336127)
                    ·
                      rfl

theorem cell23_6271396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_6271396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271396 prefixEnd_6271396 := by exact prefixLift 6271396
  have htrace : WordTrace (prefixWord ++ tailWord_6271396) baseStart_6271396 baseEnd_6271396 := by
    simpa [prefixWord, tailWord_6271396, baseEnd_6271396] using wordTrace_append hprefix tailTrace_6271396
  have hstable : (prefixWord ++ tailWord_6271396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271396).length < 2 ^ (prefixWord ++ tailWord_6271396).sum := by decide
  have hdescent : baseEnd_6271396 < baseStart_6271396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271413 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 3, 4]
def baseStart_6271413 : Nat := 118140960795 + 6271413 * 2 ^ 59
def prefixEnd_6271413 : Nat := 4983230072969 + 3 ^ 40 * 6271413 * 2
def baseEnd_6271413 : Nat := 1073416417285125600498601

theorem tailTrace_6271413 : CollatzResearch.WordTrace tailWord_6271413 prefixEnd_6271413 1073416417285125600498601 := by
  unfold tailWord_6271413
  simp only [CollatzResearch.WordTrace]
  refine ⟨228737223628749247913106893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152491482419166165275404595 228737223628749247913106893)
  ·
    refine ⟨85776458860780967967415085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228737223628749247913106893 85776458860780967967415085)
    ·
      refine ⟨32166172072792862987780657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85776458860780967967415085 32166172072792862987780657)
      ·
        refine ⟨24124629054594647240835493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32166172072792862987780657 24124629054594647240835493)
        ·
          refine ⟨4523367947736496357656655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24124629054594647240835493 4523367947736496357656655)
          ·
            refine ⟨6785051921604744536484983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523367947736496357656655 6785051921604744536484983)
            ·
              refine ⟨10177577882407116804727475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785051921604744536484983 10177577882407116804727475)
              ·
                refine ⟨15266366823610675207091213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10177577882407116804727475 15266366823610675207091213)
                ·
                  refine ⟨5724887558854003202659205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15266366823610675207091213 5724887558854003202659205)
                  ·
                    refine ⟨1073416417285125600498601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724887558854003202659205 1073416417285125600498601)
                    ·
                      rfl

theorem cell23_6271413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_6271413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271413 prefixEnd_6271413 := by exact prefixLift 6271413
  have htrace : WordTrace (prefixWord ++ tailWord_6271413) baseStart_6271413 baseEnd_6271413 := by
    simpa [prefixWord, tailWord_6271413, baseEnd_6271413] using wordTrace_append hprefix tailTrace_6271413
  have hstable : (prefixWord ++ tailWord_6271413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271413).length < 2 ^ (prefixWord ++ tailWord_6271413).sum := by decide
  have hdescent : baseEnd_6271413 < baseStart_6271413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271453 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_6271453 : Nat := 118140960795 + 6271453 * 2 ^ 59
def prefixEnd_6271453 : Nat := 4983230072969 + 3 ^ 40 * 6271453 * 2
def baseEnd_6271453 : Nat := 3220269791081556644995619

theorem tailTrace_6271453 : CollatzResearch.WordTrace tailWord_6271453 prefixEnd_6271453 3220269791081556644995619 := by
  unfold tailWord_6271453
  simp only [CollatzResearch.WordTrace]
  refine ⟨228738682548604334744563013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152492455032402889829708675 228738682548604334744563013)
  ·
    refine ⟨42888502977863312764605565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228738682548604334744563013 42888502977863312764605565)
    ·
      refine ⟨16083188616698742286727087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42888502977863312764605565 16083188616698742286727087)
      ·
        refine ⟨24124782925048113430090631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083188616698742286727087 24124782925048113430090631)
        ·
          refine ⟨36187174387572170145135947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24124782925048113430090631 36187174387572170145135947)
          ·
            refine ⟨54280761581358255217703921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36187174387572170145135947 54280761581358255217703921)
            ·
              refine ⟨40710571186018691413277941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54280761581358255217703921 40710571186018691413277941)
              ·
                refine ⟨3816616048689252319994807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40710571186018691413277941 3816616048689252319994807)
                ·
                  refine ⟨5724924073033878479992211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816616048689252319994807 5724924073033878479992211)
                  ·
                    refine ⟨8587386109550817719988317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724924073033878479992211 8587386109550817719988317)
                    ·
                      refine ⟨3220269791081556644995619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587386109550817719988317 3220269791081556644995619)
                      ·
                        rfl

theorem cell23_6271453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_6271453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271453 prefixEnd_6271453 := by exact prefixLift 6271453
  have htrace : WordTrace (prefixWord ++ tailWord_6271453) baseStart_6271453 baseEnd_6271453 := by
    simpa [prefixWord, tailWord_6271453, baseEnd_6271453] using wordTrace_append hprefix tailTrace_6271453
  have hstable : (prefixWord ++ tailWord_6271453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271453).length < 2 ^ (prefixWord ++ tailWord_6271453).sum := by decide
  have hdescent : baseEnd_6271453 < baseStart_6271453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271470 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3]
def baseStart_6271470 : Nat := 118140960795 + 6271470 * 2 ^ 59
def prefixEnd_6271470 : Nat := 4983230072969 + 3 ^ 40 * 6271470 * 2
def baseEnd_6271470 : Nat := 3220278520252683078483041

theorem tailTrace_6271470 : CollatzResearch.WordTrace tailWord_6271470 prefixEnd_6271470 3220278520252683078483041 := by
  unfold tailWord_6271470
  simp only [CollatzResearch.WordTrace]
  refine ⟨28592412823692843330991483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152492868393028497765287909 28592412823692843330991483)
  ·
    refine ⟨42888619235539264996487225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28592412823692843330991483 42888619235539264996487225)
    ·
      refine ⟨32166464426654448747365419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42888619235539264996487225 32166464426654448747365419)
      ·
        refine ⟨48249696639981673121048129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32166464426654448747365419 48249696639981673121048129)
        ·
          refine ⟨36187272479986254840786097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48249696639981673121048129 36187272479986254840786097)
          ·
            refine ⟨27140454359989691130589573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36187272479986254840786097 27140454359989691130589573)
            ·
              refine ⟨5088835192498067086985545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27140454359989691130589573 5088835192498067086985545)
              ·
                refine ⟨3816626394373550315239159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5088835192498067086985545 3816626394373550315239159)
                ·
                  refine ⟨5724939591560325472858739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3816626394373550315239159 5724939591560325472858739)
                  ·
                    refine ⟨8587409387340488209288109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5724939591560325472858739 8587409387340488209288109)
                    ·
                      refine ⟨3220278520252683078483041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587409387340488209288109 3220278520252683078483041)
                      ·
                        rfl

theorem cell23_6271470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_6271470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271470 prefixEnd_6271470 := by exact prefixLift 6271470
  have htrace : WordTrace (prefixWord ++ tailWord_6271470) baseStart_6271470 baseEnd_6271470 := by
    simpa [prefixWord, tailWord_6271470, baseEnd_6271470] using wordTrace_append hprefix tailTrace_6271470
  have hstable : (prefixWord ++ tailWord_6271470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271470).length < 2 ^ (prefixWord ++ tailWord_6271470).sum := by decide
  have hdescent : baseEnd_6271470 < baseStart_6271470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271472 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_6271472 : Nat := 118140960795 + 6271472 * 2 ^ 59
def prefixEnd_6271472 : Nat := 4983230072969 + 3 ^ 40 * 6271472 * 2
def baseEnd_6271472 : Nat := 3220279547213992070658031

theorem tailTrace_6271472 : CollatzResearch.WordTrace tailWord_6271472 prefixEnd_6271472 3220279547213992070658031 := by
  unfold tailWord_6271472
  simp only [CollatzResearch.WordTrace]
  refine ⟨114369687767767750494752335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152492917023690333993003113 114369687767767750494752335)
  ·
    refine ⟨171554531651651625742128503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114369687767767750494752335 171554531651651625742128503)
    ·
      refine ⟨257331797477477438613192755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171554531651651625742128503 257331797477477438613192755)
      ·
        refine ⟨385997696216216157919789133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257331797477477438613192755 385997696216216157919789133)
        ·
          refine ⟨144749136081081059219920925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 385997696216216157919789133 144749136081081059219920925)
          ·
            refine ⟨54280926030405397207470347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144749136081081059219920925 54280926030405397207470347)
            ·
              refine ⟨81421389045608095811205521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54280926030405397207470347 81421389045608095811205521)
              ·
                refine ⟨61066041784206071858404141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81421389045608095811205521 61066041784206071858404141)
                ·
                  refine ⟨22899765669077276946901553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61066041784206071858404141 22899765669077276946901553)
                  ·
                    refine ⟨17174824251807957710176165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22899765669077276946901553 17174824251807957710176165)
                    ·
                      refine ⟨3220279547213992070658031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17174824251807957710176165 3220279547213992070658031)
                      ·
                        rfl

theorem cell23_6271472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_6271472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271472 prefixEnd_6271472 := by exact prefixLift 6271472
  have htrace : WordTrace (prefixWord ++ tailWord_6271472) baseStart_6271472 baseEnd_6271472 := by
    simpa [prefixWord, tailWord_6271472, baseEnd_6271472] using wordTrace_append hprefix tailTrace_6271472
  have hstable : (prefixWord ++ tailWord_6271472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271472).length < 2 ^ (prefixWord ++ tailWord_6271472).sum := by decide
  have hdescent : baseEnd_6271472 < baseStart_6271472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271489 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_6271489 : Nat := 118140960795 + 6271489 * 2 ^ 59
def prefixEnd_6271489 : Nat := 4983230072969 + 3 ^ 40 * 6271489 * 2
def baseEnd_6271489 : Nat := 3220288276385118504145453

theorem tailTrace_6271489 : CollatzResearch.WordTrace tailWord_6271489 prefixEnd_6271489 3220288276385118504145453 := by
  unfold tailWord_6271489
  simp only [CollatzResearch.WordTrace]
  refine ⟨228739995576473912892873521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152493330384315941928582347 228739995576473912892873521)
  ·
    refine ⟨171554996682355434669655141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228739995576473912892873521 171554996682355434669655141)
    ·
      refine ⟨32166561877941644000560339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 171554996682355434669655141 32166561877941644000560339)
      ·
        refine ⟨48249842816912466000840509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32166561877941644000560339 48249842816912466000840509)
        ·
          refine ⟨18093691056342174750315191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48249842816912466000840509 18093691056342174750315191)
          ·
            refine ⟨27140536584513262125472787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18093691056342174750315191 27140536584513262125472787)
            ·
              refine ⟨40710804876769893188209181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27140536584513262125472787 40710804876769893188209181)
              ·
                refine ⟨15266551828788709945578443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40710804876769893188209181 15266551828788709945578443)
                ·
                  refine ⟨22899827743183064918367665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15266551828788709945578443 22899827743183064918367665)
                  ·
                    refine ⟨17174870807387298688775749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22899827743183064918367665 17174870807387298688775749)
                    ·
                      refine ⟨3220288276385118504145453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17174870807387298688775749 3220288276385118504145453)
                      ·
                        rfl

theorem cell23_6271489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_6271489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271489 prefixEnd_6271489 := by exact prefixLift 6271489
  have htrace : WordTrace (prefixWord ++ tailWord_6271489) baseStart_6271489 baseEnd_6271489 := by
    simpa [prefixWord, tailWord_6271489, baseEnd_6271489] using wordTrace_append hprefix tailTrace_6271489
  have hstable : (prefixWord ++ tailWord_6271489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271489).length < 2 ^ (prefixWord ++ tailWord_6271489).sum := by decide
  have hdescent : baseEnd_6271489 < baseStart_6271489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271499 : List Nat := [1, 1, 1, 1, 7, 2, 3, 7]
def baseStart_6271499 : Nat := 118140960795 + 6271499 * 2 ^ 59
def prefixEnd_6271499 : Nat := 4983230072969 + 3 ^ 40 * 6271499 * 2
def baseEnd_6271499 : Nat := 119270126340431980185941

theorem tailTrace_6271499 : CollatzResearch.WordTrace tailWord_6271499 prefixEnd_6271499 119270126340431980185941 := by
  unfold tailWord_6271499
  simp only [CollatzResearch.WordTrace]
  refine ⟨228740360306437684600737551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152493573537625123067158367 228740360306437684600737551)
  ·
    refine ⟨343110540459656526901106327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228740360306437684600737551 343110540459656526901106327)
    ·
      refine ⟨514665810689484790351659491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343110540459656526901106327 514665810689484790351659491)
      ·
        refine ⟨771998716034227185527489237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514665810689484790351659491 771998716034227185527489237)
        ·
          refine ⟨18093719907052199660800529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 771998716034227185527489237 18093719907052199660800529)
          ·
            refine ⟨13570289930289149745600397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18093719907052199660800529 13570289930289149745600397)
            ·
              refine ⟨5088858723858431154600149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13570289930289149745600397 5088858723858431154600149)
              ·
                refine ⟨119270126340431980185941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5088858723858431154600149 119270126340431980185941)
                ·
                  rfl

theorem cell23_6271499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 7].length) (baseStart_6271499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271499 prefixEnd_6271499 := by exact prefixLift 6271499
  have htrace : WordTrace (prefixWord ++ tailWord_6271499) baseStart_6271499 baseEnd_6271499 := by
    simpa [prefixWord, tailWord_6271499, baseEnd_6271499] using wordTrace_append hprefix tailTrace_6271499
  have hstable : (prefixWord ++ tailWord_6271499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271499).length < 2 ^ (prefixWord ++ tailWord_6271499).sum := by decide
  have hdescent : baseEnd_6271499 < baseStart_6271499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271509 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_6271509 : Nat := 118140960795 + 6271509 * 2 ^ 59
def prefixEnd_6271509 : Nat := 4983230072969 + 3 ^ 40 * 6271509 * 2
def baseEnd_6271509 : Nat := 3220298545998208425895361

theorem tailTrace_6271509 : CollatzResearch.WordTrace tailWord_6271509 prefixEnd_6271509 3220298545998208425895361 := by
  unfold tailWord_6271509
  simp only [CollatzResearch.WordTrace]
  refine ⟨228740725036401456308601581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152493816690934304205734387 228740725036401456308601581)
  ·
    refine ⟨85777771888650546115725593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228740725036401456308601581 85777771888650546115725593)
    ·
      refine ⟨64333328916487909586794195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85777771888650546115725593 64333328916487909586794195)
      ·
        refine ⟨96499993374731864380191293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64333328916487909586794195 96499993374731864380191293)
        ·
          refine ⟨36187497515524449142571735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96499993374731864380191293 36187497515524449142571735)
          ·
            refine ⟨54281246273286673713857603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36187497515524449142571735 54281246273286673713857603)
            ·
              refine ⟨81421869409930010570786405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54281246273286673713857603 81421869409930010570786405)
              ·
                refine ⟨15266600514361876982022451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81421869409930010570786405 15266600514361876982022451)
                ·
                  refine ⟨22899900771542815473033677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15266600514361876982022451 22899900771542815473033677)
                  ·
                    refine ⟨8587462789328555802387629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22899900771542815473033677 8587462789328555802387629)
                    ·
                      refine ⟨3220298545998208425895361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587462789328555802387629 3220298545998208425895361)
                      ·
                        rfl

theorem cell23_6271509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_6271509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271509 prefixEnd_6271509 := by exact prefixLift 6271509
  have htrace : WordTrace (prefixWord ++ tailWord_6271509) baseStart_6271509 baseEnd_6271509 := by
    simpa [prefixWord, tailWord_6271509, baseEnd_6271509] using wordTrace_append hprefix tailTrace_6271509
  have hstable : (prefixWord ++ tailWord_6271509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271509).length < 2 ^ (prefixWord ++ tailWord_6271509).sum := by decide
  have hdescent : baseEnd_6271509 < baseStart_6271509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271520 : List Nat := [2, 1, 1, 6, 3, 1, 1, 2, 2, 4]
def baseStart_6271520 : Nat := 118140960795 + 6271520 * 2 ^ 59
def prefixEnd_6271520 : Nat := 4983230072969 + 3 ^ 40 * 6271520 * 2
def baseEnd_6271520 : Nat := 1073434731428469294285937

theorem tailTrace_6271520 : CollatzResearch.WordTrace tailWord_6271520 prefixEnd_6271520 1073434731428469294285937 := by
  unfold tailWord_6271520
  simp only [CollatzResearch.WordTrace]
  refine ⟨114370563119680802593626007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152494084159574403458168009 114370563119680802593626007)
  ·
    refine ⟨171555844679521203890439011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114370563119680802593626007 171555844679521203890439011)
    ·
      refine ⟨257333767019281805835658517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171555844679521203890439011 257333767019281805835658517)
      ·
        refine ⟨12062520329028834648546493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 257333767019281805835658517 12062520329028834648546493)
        ·
          refine ⟨4523445123385812993204935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12062520329028834648546493 4523445123385812993204935)
          ·
            refine ⟨6785167685078719489807403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523445123385812993204935 6785167685078719489807403)
            ·
              refine ⟨10177751527618079234711105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785167685078719489807403 10177751527618079234711105)
              ·
                refine ⟨7633313645713559426033329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10177751527618079234711105 7633313645713559426033329)
                ·
                  refine ⟨5724985234285169569524997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7633313645713559426033329 5724985234285169569524997)
                  ·
                    refine ⟨1073434731428469294285937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5724985234285169569524997 1073434731428469294285937)
                    ·
                      rfl

theorem cell23_6271520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 1, 2, 2, 4].length) (baseStart_6271520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271520 prefixEnd_6271520 := by exact prefixLift 6271520
  have htrace : WordTrace (prefixWord ++ tailWord_6271520) baseStart_6271520 baseEnd_6271520 := by
    simpa [prefixWord, tailWord_6271520, baseEnd_6271520] using wordTrace_append hprefix tailTrace_6271520
  have hstable : (prefixWord ++ tailWord_6271520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271520).length < 2 ^ (prefixWord ++ tailWord_6271520).sum := by decide
  have hdescent : baseEnd_6271520 < baseStart_6271520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271527 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6271527 : Nat := 118140960795 + 6271527 * 2 ^ 59
def prefixEnd_6271527 : Nat := 4983230072969 + 3 ^ 40 * 6271527 * 2
def baseEnd_6271527 : Nat := 3220307788649989355470279

theorem tailTrace_6271527 : CollatzResearch.WordTrace tailWord_6271527 prefixEnd_6271527 3220307788649989355470279 := by
  unfold tailWord_6271527
  simp only [CollatzResearch.WordTrace]
  refine ⟨228741381550336245382756835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152494254366890830255171223 228741381550336245382756835)
  ·
    refine ⟨343112072325504368074135253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228741381550336245382756835 343112072325504368074135253)
    ·
      refine ⟨8041689195129008626737545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 343112072325504368074135253 8041689195129008626737545)
      ·
        refine ⟨6031266896346756470053159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8041689195129008626737545 6031266896346756470053159)
        ·
          refine ⟨9046900344520134705079739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031266896346756470053159 9046900344520134705079739)
          ·
            refine ⟨13570350516780202057619609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9046900344520134705079739 13570350516780202057619609)
            ·
              refine ⟨10177762887585151543214707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13570350516780202057619609 10177762887585151543214707)
              ·
                refine ⟨15266644331377727314822061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10177762887585151543214707 15266644331377727314822061)
                ·
                  refine ⟨5724991624266647743058273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15266644331377727314822061 5724991624266647743058273)
                  ·
                    refine ⟨4293743718199985807293705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5724991624266647743058273 4293743718199985807293705)
                    ·
                      refine ⟨3220307788649989355470279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293743718199985807293705 3220307788649989355470279)
                      ·
                        rfl

theorem cell23_6271527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6271527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271527 prefixEnd_6271527 := by exact prefixLift 6271527
  have htrace : WordTrace (prefixWord ++ tailWord_6271527) baseStart_6271527 baseEnd_6271527 := by
    simpa [prefixWord, tailWord_6271527, baseEnd_6271527] using wordTrace_append hprefix tailTrace_6271527
  have hstable : (prefixWord ++ tailWord_6271527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271527).length < 2 ^ (prefixWord ++ tailWord_6271527).sum := by decide
  have hdescent : baseEnd_6271527 < baseStart_6271527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271532 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_6271532 : Nat := 118140960795 + 6271532 * 2 ^ 59
def prefixEnd_6271532 : Nat := 4983230072969 + 3 ^ 40 * 6271532 * 2
def baseEnd_6271532 : Nat := 3220310356053261835907755

theorem tailTrace_6271532 : CollatzResearch.WordTrace tailWord_6271532 prefixEnd_6271532 3220310356053261835907755 := by
  unfold tailWord_6271532
  simp only [CollatzResearch.WordTrace]
  refine ⟨114370781957659065618344425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152494375943545420824459233 114370781957659065618344425)
  ·
    refine ⟨85778086468244299213758319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114370781957659065618344425 85778086468244299213758319)
    ·
      refine ⟨128667129702366448820637479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85778086468244299213758319 128667129702366448820637479)
      ·
        refine ⟨193000694553549673230956219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128667129702366448820637479 193000694553549673230956219)
        ·
          refine ⟨289501041830324509846434329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193000694553549673230956219 289501041830324509846434329)
          ·
            refine ⟨217125781372743382384825747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289501041830324509846434329 217125781372743382384825747)
            ·
              refine ⟨325688672059115073577238621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217125781372743382384825747 325688672059115073577238621)
              ·
                refine ⟨122133252022168152591464483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325688672059115073577238621 122133252022168152591464483)
                ·
                  refine ⟨183199878033252228887196725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122133252022168152591464483 183199878033252228887196725)
                  ·
                    refine ⟨17174988565617396458174693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 183199878033252228887196725 17174988565617396458174693)
                    ·
                      refine ⟨3220310356053261835907755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17174988565617396458174693 3220310356053261835907755)
                      ·
                        rfl

theorem cell23_6271532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_6271532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271532 prefixEnd_6271532 := by exact prefixLift 6271532
  have htrace : WordTrace (prefixWord ++ tailWord_6271532) baseStart_6271532 baseEnd_6271532 := by
    simpa [prefixWord, tailWord_6271532, baseEnd_6271532] using wordTrace_append hprefix tailTrace_6271532
  have hstable : (prefixWord ++ tailWord_6271532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271532).length < 2 ^ (prefixWord ++ tailWord_6271532).sum := by decide
  have hdescent : baseEnd_6271532 < baseStart_6271532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271540 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6271540 : Nat := 118140960795 + 6271540 * 2 ^ 59
def prefixEnd_6271540 : Nat := 4983230072969 + 3 ^ 40 * 6271540 * 2
def baseEnd_6271540 : Nat := 3220314463898497804607719

theorem tailTrace_6271540 : CollatzResearch.WordTrace tailWord_6271540 prefixEnd_6271540 3220314463898497804607719 := by
  unfold tailWord_6271540
  simp only [CollatzResearch.WordTrace]
  refine ⟨114370927849644574301490037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152494570466192765735320049 114370927849644574301490037)
  ·
    refine ⟨10722274485904178840764691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114370927849644574301490037 10722274485904178840764691)
    ·
      refine ⟨16083411728856268261147037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10722274485904178840764691 16083411728856268261147037)
      ·
        refine ⟨6031279398321100597930139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16083411728856268261147037 6031279398321100597930139)
        ·
          refine ⟨9046919097481650896895209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6031279398321100597930139 9046919097481650896895209)
          ·
            refine ⟨6785189323111238172671407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9046919097481650896895209 6785189323111238172671407)
            ·
              refine ⟨10177783984666857259007111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785189323111238172671407 10177783984666857259007111)
              ·
                refine ⟨15266675977000285888510667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10177783984666857259007111 15266675977000285888510667)
                ·
                  refine ⟨22900013965500428832766001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15266675977000285888510667 22900013965500428832766001)
                  ·
                    refine ⟨17175010474125321624574501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22900013965500428832766001 17175010474125321624574501)
                    ·
                      refine ⟨3220314463898497804607719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17175010474125321624574501 3220314463898497804607719)
                      ·
                        rfl

theorem cell23_6271540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6271540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271540 prefixEnd_6271540 := by exact prefixLift 6271540
  have htrace : WordTrace (prefixWord ++ tailWord_6271540) baseStart_6271540 baseEnd_6271540 := by
    simpa [prefixWord, tailWord_6271540, baseEnd_6271540] using wordTrace_append hprefix tailTrace_6271540
  have hstable : (prefixWord ++ tailWord_6271540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271540).length < 2 ^ (prefixWord ++ tailWord_6271540).sum := by decide
  have hdescent : baseEnd_6271540 < baseStart_6271540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271543 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 2, 1, 3]
def baseStart_6271543 : Nat := 118140960795 + 6271543 * 2 ^ 59
def prefixEnd_6271543 : Nat := 4983230072969 + 3 ^ 40 * 6271543 * 2
def baseEnd_6271543 : Nat := 3220316004340461292870205

theorem tailTrace_6271543 : CollatzResearch.WordTrace tailWord_6271543 prefixEnd_6271543 3220316004340461292870205 := by
  unfold tailWord_6271543
  simp only [CollatzResearch.WordTrace]
  refine ⟨228741965118278280115339283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152494643412185520076892855 228741965118278280115339283)
  ·
    refine ⟨343112947677417420173008925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228741965118278280115339283 343112947677417420173008925)
    ·
      refine ⟨128667355379031532564878347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343112947677417420173008925 128667355379031532564878347)
      ·
        refine ⟨193001033068547298847317521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128667355379031532564878347 193001033068547298847317521)
        ·
          refine ⟨144750774801410474135488141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193001033068547298847317521 144750774801410474135488141)
          ·
            refine ⟨54281540550528927800808053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144750774801410474135488141 54281540550528927800808053)
            ·
              refine ⟨5088894426612086981325755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54281540550528927800808053 5088894426612086981325755)
              ·
                refine ⟨7633341639918130471988633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5088894426612086981325755 7633341639918130471988633)
                ·
                  refine ⟨5725006229938597853991475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7633341639918130471988633 5725006229938597853991475)
                  ·
                    refine ⟨8587509344907896780987213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5725006229938597853991475 8587509344907896780987213)
                    ·
                      refine ⟨3220316004340461292870205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587509344907896780987213 3220316004340461292870205)
                      ·
                        rfl

theorem cell23_6271543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_6271543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271543 prefixEnd_6271543 := by exact prefixLift 6271543
  have htrace : WordTrace (prefixWord ++ tailWord_6271543) baseStart_6271543 baseEnd_6271543 := by
    simpa [prefixWord, tailWord_6271543, baseEnd_6271543] using wordTrace_append hprefix tailTrace_6271543
  have hstable : (prefixWord ++ tailWord_6271543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271543).length < 2 ^ (prefixWord ++ tailWord_6271543).sum := by decide
  have hdescent : baseEnd_6271543 < baseStart_6271543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271550 : List Nat := [4, 2, 1, 4, 2, 1, 2, 7]
def baseStart_6271550 : Nat := 118140960795 + 6271550 * 2 ^ 59
def prefixEnd_6271550 : Nat := 4983230072969 + 3 ^ 40 * 6271550 * 2
def baseEnd_6271550 : Nat := 119271096248334917240099

theorem tailTrace_6271550 : CollatzResearch.WordTrace tailWord_6271550 prefixEnd_6271550 119271096248334917240099 := by
  unfold tailWord_6271550
  simp only [CollatzResearch.WordTrace]
  refine ⟨28592777553656615038855513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152494813619501946873896069 28592777553656615038855513)
  ·
    refine ⟨21444583165242461279141635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28592777553656615038855513 21444583165242461279141635)
    ·
      refine ⟨32166874747863691918712453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21444583165242461279141635 32166874747863691918712453)
      ·
        refine ⟨6031289015224442234758585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32166874747863691918712453 6031289015224442234758585)
        ·
          refine ⟨4523466761418331676068939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6031289015224442234758585 4523466761418331676068939)
          ·
            refine ⟨6785200142127497514103409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523466761418331676068939 6785200142127497514103409)
            ·
              refine ⟨5088900106595623135577557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6785200142127497514103409 5088900106595623135577557)
              ·
                refine ⟨119271096248334917240099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5088900106595623135577557 119271096248334917240099)
                ·
                  rfl

theorem cell23_6271550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_6271550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271550 prefixEnd_6271550 := by exact prefixLift 6271550
  have htrace : WordTrace (prefixWord ++ tailWord_6271550) baseStart_6271550 baseEnd_6271550 := by
    simpa [prefixWord, tailWord_6271550, baseEnd_6271550] using wordTrace_append hprefix tailTrace_6271550
  have hstable : (prefixWord ++ tailWord_6271550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271550).length < 2 ^ (prefixWord ++ tailWord_6271550).sum := by decide
  have hdescent : baseEnd_6271550 < baseStart_6271550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271553 : List Nat := [1, 2, 5, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6271553 : Nat := 118140960795 + 6271553 * 2 ^ 59
def prefixEnd_6271553 : Nat := 4983230072969 + 3 ^ 40 * 6271553 * 2
def baseEnd_6271553 : Nat := 3220321139147006253745159

theorem tailTrace_6271553 : CollatzResearch.WordTrace tailWord_6271553 prefixEnd_6271553 3220321139147006253745159 := by
  unfold tailWord_6271553
  simp only [CollatzResearch.WordTrace]
  refine ⟨228742329848242051823203313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152494886565494701215468875 228742329848242051823203313)
  ·
    refine ⟨171556747386181538867402485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228742329848242051823203313 171556747386181538867402485)
    ·
      refine ⟨16083445067454519268818983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171556747386181538867402485 16083445067454519268818983)
      ·
        refine ⟨24125167601181778903228475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083445067454519268818983 24125167601181778903228475)
        ·
          refine ⟨36187751401772668354842713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24125167601181778903228475 36187751401772668354842713)
          ·
            refine ⟨27140813551329501266132035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36187751401772668354842713 27140813551329501266132035)
            ·
              refine ⟨40711220326994251899198053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27140813551329501266132035 40711220326994251899198053)
              ·
                refine ⟨7633353811311422231099635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40711220326994251899198053 7633353811311422231099635)
                ·
                  refine ⟨11450030716967133346649453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633353811311422231099635 11450030716967133346649453)
                  ·
                    refine ⟨4293761518862675004993545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11450030716967133346649453 4293761518862675004993545)
                    ·
                      refine ⟨3220321139147006253745159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293761518862675004993545 3220321139147006253745159)
                      ·
                        rfl

theorem cell23_6271553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6271553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271553 prefixEnd_6271553 := by exact prefixLift 6271553
  have htrace : WordTrace (prefixWord ++ tailWord_6271553) baseStart_6271553 baseEnd_6271553 := by
    simpa [prefixWord, tailWord_6271553, baseEnd_6271553] using wordTrace_append hprefix tailTrace_6271553
  have hstable : (prefixWord ++ tailWord_6271553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271553).length < 2 ^ (prefixWord ++ tailWord_6271553).sum := by decide
  have hdescent : baseEnd_6271553 < baseStart_6271553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271566 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2]
def baseStart_6271566 : Nat := 118140960795 + 6271566 * 2 ^ 59
def prefixEnd_6271566 : Nat := 4983230072969 + 3 ^ 40 * 6271566 * 2
def baseEnd_6271566 : Nat := 3220327814395514702882599

theorem tailTrace_6271566 : CollatzResearch.WordTrace tailWord_6271566 prefixEnd_6271566 3220327814395514702882599 := by
  unfold tailWord_6271566
  simp only [CollatzResearch.WordTrace]
  refine ⟨28592850499649369380428319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152495202664796636695617701 28592850499649369380428319)
  ·
    refine ⟨42889275749474054070642479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28592850499649369380428319 42889275749474054070642479)
    ·
      refine ⟨64333913624211081105963719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42889275749474054070642479 64333913624211081105963719)
      ·
        refine ⟨96500870436316621658945579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64333913624211081105963719 96500870436316621658945579)
        ·
          refine ⟨144751305654474932488418369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96500870436316621658945579 144751305654474932488418369)
          ·
            refine ⟨108563479240856199366313777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144751305654474932488418369 108563479240856199366313777)
            ·
              refine ⟨81422609430642149524735333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108563479240856199366313777 81422609430642149524735333)
              ·
                refine ⟨15266739268245403035887875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81422609430642149524735333 15266739268245403035887875)
                ·
                  refine ⟨22900108902368104553831813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15266739268245403035887875 22900108902368104553831813)
                  ·
                    refine ⟨4293770419194019603843465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22900108902368104553831813 4293770419194019603843465)
                    ·
                      refine ⟨3220327814395514702882599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293770419194019603843465 3220327814395514702882599)
                      ·
                        rfl

theorem cell23_6271566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_6271566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271566 prefixEnd_6271566 := by exact prefixLift 6271566
  have htrace : WordTrace (prefixWord ++ tailWord_6271566) baseStart_6271566 baseEnd_6271566 := by
    simpa [prefixWord, tailWord_6271566, baseEnd_6271566] using wordTrace_append hprefix tailTrace_6271566
  have hstable : (prefixWord ++ tailWord_6271566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271566).length < 2 ^ (prefixWord ++ tailWord_6271566).sum := by decide
  have hdescent : baseEnd_6271566 < baseStart_6271566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271569 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_6271569 : Nat := 118140960795 + 6271569 * 2 ^ 59
def prefixEnd_6271569 : Nat := 4983230072969 + 3 ^ 40 * 6271569 * 2
def baseEnd_6271569 : Nat := 3220329354837478191145085

theorem tailTrace_6271569 : CollatzResearch.WordTrace tailWord_6271569 prefixEnd_6271569 3220329354837478191145085 := by
  unfold tailWord_6271569
  simp only [CollatzResearch.WordTrace]
  refine ⟨228742913416184086555785761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152495275610789391037190507 228742913416184086555785761)
  ·
    refine ⟨171557185062138064916839321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228742913416184086555785761 171557185062138064916839321)
    ·
      refine ⟨128667888796603548687629491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171557185062138064916839321 128667888796603548687629491)
      ·
        refine ⟨193001833194905323031444237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128667888796603548687629491 193001833194905323031444237)
        ·
          refine ⟨72375687448089496136791589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193001833194905323031444237 72375687448089496136791589)
          ·
            refine ⟨13570441396516780525648423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72375687448089496136791589 13570441396516780525648423)
            ·
              refine ⟨20355662094775170788472635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13570441396516780525648423 20355662094775170788472635)
              ·
                refine ⟨30533493142162756182708953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20355662094775170788472635 30533493142162756182708953)
                ·
                  refine ⟨22900119856622067137031715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30533493142162756182708953 22900119856622067137031715)
                  ·
                    refine ⟨34350179784933100705547573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22900119856622067137031715 34350179784933100705547573)
                    ·
                      refine ⟨3220329354837478191145085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34350179784933100705547573 3220329354837478191145085)
                      ·
                        rfl

theorem cell23_6271569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_6271569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271569 prefixEnd_6271569 := by exact prefixLift 6271569
  have htrace : WordTrace (prefixWord ++ tailWord_6271569) baseStart_6271569 baseEnd_6271569 := by
    simpa [prefixWord, tailWord_6271569, baseEnd_6271569] using wordTrace_append hprefix tailTrace_6271569
  have hstable : (prefixWord ++ tailWord_6271569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271569).length < 2 ^ (prefixWord ++ tailWord_6271569).sum := by decide
  have hdescent : baseEnd_6271569 < baseStart_6271569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271599 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3]
def baseStart_6271599 : Nat := 118140960795 + 6271599 * 2 ^ 59
def prefixEnd_6271599 : Nat := 4983230072969 + 3 ^ 40 * 6271599 * 2
def baseEnd_6271599 : Nat := 3220344759257113073769947

theorem tailTrace_6271599 : CollatzResearch.WordTrace tailWord_6271599 prefixEnd_6271599 3220344759257113073769947 := by
  unfold tailWord_6271599
  simp only [CollatzResearch.WordTrace]
  refine ⟨228744007606075401679377851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152496005070716934452918567 228744007606075401679377851)
  ·
    refine ⟨343116011409113102519066777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228744007606075401679377851 343116011409113102519066777)
    ·
      refine ⟨257337008556834826889300083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343116011409113102519066777 257337008556834826889300083)
      ·
        refine ⟨386005512835252240333950125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257337008556834826889300083 386005512835252240333950125)
        ·
          refine ⟨144752067313219590125231297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386005512835252240333950125 144752067313219590125231297)
          ·
            refine ⟨108564050484914692593923473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144752067313219590125231297 108564050484914692593923473)
            ·
              refine ⟨81423037863686019445442605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108564050484914692593923473 81423037863686019445442605)
              ·
                refine ⟨30533639198882257292040977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81423037863686019445442605 30533639198882257292040977)
                ·
                  refine ⟨22900229399161692969030733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30533639198882257292040977 22900229399161692969030733)
                  ·
                    refine ⟨8587586024685634863386525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22900229399161692969030733 8587586024685634863386525)
                    ·
                      refine ⟨3220344759257113073769947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587586024685634863386525 3220344759257113073769947)
                      ·
                        rfl

theorem cell23_6271599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_6271599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271599 prefixEnd_6271599 := by exact prefixLift 6271599
  have htrace : WordTrace (prefixWord ++ tailWord_6271599) baseStart_6271599 baseEnd_6271599 := by
    simpa [prefixWord, tailWord_6271599, baseEnd_6271599] using wordTrace_append hprefix tailTrace_6271599
  have hstable : (prefixWord ++ tailWord_6271599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271599).length < 2 ^ (prefixWord ++ tailWord_6271599).sum := by decide
  have hdescent : baseEnd_6271599 < baseStart_6271599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271600 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2]
def baseStart_6271600 : Nat := 118140960795 + 6271600 * 2 ^ 59
def prefixEnd_6271600 : Nat := 4983230072969 + 3 ^ 40 * 6271600 * 2
def baseEnd_6271600 : Nat := 3220345272737767569857443

theorem tailTrace_6271600 : CollatzResearch.WordTrace tailWord_6271600 prefixEnd_6271600 3220345272737767569857443 := by
  unfold tailWord_6271600
  simp only [CollatzResearch.WordTrace]
  refine ⟨114372022039535889425082127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152496029386047852566776169 114372022039535889425082127)
  ·
    refine ⟨171558033059303834137623191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114372022039535889425082127 171558033059303834137623191)
    ·
      refine ⟨257337049588955751206434787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171558033059303834137623191 257337049588955751206434787)
      ·
        refine ⟨386005574383433626809652181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257337049588955751206434787 386005574383433626809652181)
        ·
          refine ⟨9047005649611725628351223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 386005574383433626809652181 9047005649611725628351223)
          ·
            refine ⟨13570508474417588442526835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9047005649611725628351223 13570508474417588442526835)
            ·
              refine ⟨20355762711626382663790253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13570508474417588442526835 20355762711626382663790253)
              ·
                refine ⟨7633411016859893498921345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20355762711626382663790253 7633411016859893498921345)
                ·
                  refine ⟨5725058262644920124191009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7633411016859893498921345 5725058262644920124191009)
                  ·
                    refine ⟨4293793696983690093143257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5725058262644920124191009 4293793696983690093143257)
                    ·
                      refine ⟨3220345272737767569857443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293793696983690093143257 3220345272737767569857443)
                      ·
                        rfl

theorem cell23_6271600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 2, 2, 2].length) (baseStart_6271600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271600 prefixEnd_6271600 := by exact prefixLift 6271600
  have htrace : WordTrace (prefixWord ++ tailWord_6271600) baseStart_6271600 baseEnd_6271600 := by
    simpa [prefixWord, tailWord_6271600, baseEnd_6271600] using wordTrace_append hprefix tailTrace_6271600
  have hstable : (prefixWord ++ tailWord_6271600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271600).length < 2 ^ (prefixWord ++ tailWord_6271600).sum := by decide
  have hdescent : baseEnd_6271600 < baseStart_6271600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271619 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 2, 5]
def baseStart_6271619 : Nat := 118140960795 + 6271619 * 2 ^ 59
def prefixEnd_6271619 : Nat := 4983230072969 + 3 ^ 40 * 6271619 * 2
def baseEnd_6271619 : Nat := 1073451676290067665173285

theorem tailTrace_6271619 : CollatzResearch.WordTrace tailWord_6271619 prefixEnd_6271619 1073451676290067665173285 := by
  unfold tailWord_6271619
  simp only [CollatzResearch.WordTrace]
  refine ⟨228744737066002945095105911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152496491377335296730070607 228744737066002945095105911)
  ·
    refine ⟨343117105599004417642658867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228744737066002945095105911 343117105599004417642658867)
    ·
      refine ⟨514675658398506626463988301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343117105599004417642658867 514675658398506626463988301)
      ·
        refine ⟨193003371899439984923995613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514675658398506626463988301 193003371899439984923995613)
        ·
          refine ⟨72376264462289994346498355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193003371899439984923995613 72376264462289994346498355)
          ·
            refine ⟨108564396693434991519747533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72376264462289994346498355 108564396693434991519747533)
            ·
              refine ⟨40711648760038121819905325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108564396693434991519747533 40711648760038121819905325)
              ·
                refine ⟨15266868285014295682464497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40711648760038121819905325 15266868285014295682464497)
                ·
                  refine ⟨11450151213760721761848373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15266868285014295682464497 11450151213760721761848373)
                  ·
                    refine ⟨1073451676290067665173285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11450151213760721761848373 1073451676290067665173285)
                    ·
                      rfl

theorem cell23_6271619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 5].length) (baseStart_6271619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271619 prefixEnd_6271619 := by exact prefixLift 6271619
  have htrace : WordTrace (prefixWord ++ tailWord_6271619) baseStart_6271619 baseEnd_6271619 := by
    simpa [prefixWord, tailWord_6271619, baseEnd_6271619] using wordTrace_append hprefix tailTrace_6271619
  have hstable : (prefixWord ++ tailWord_6271619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271619).length < 2 ^ (prefixWord ++ tailWord_6271619).sum := by decide
  have hdescent : baseEnd_6271619 < baseStart_6271619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271646 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6271646 : Nat := 118140960795 + 6271646 * 2 ^ 59
def prefixEnd_6271646 : Nat := 4983230072969 + 3 ^ 40 * 6271646 * 2
def baseEnd_6271646 : Nat := 3220368892847874389882231

theorem tailTrace_6271646 : CollatzResearch.WordTrace tailWord_6271646 prefixEnd_6271646 3220368892847874389882231 := by
  unfold tailWord_6271646
  simp only [CollatzResearch.WordTrace]
  refine ⟨28593215229613141088292349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152497147891270085804225861 28593215229613141088292349)
  ·
    refine ⟨10722455711104927908109631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28593215229613141088292349 10722455711104927908109631)
    ·
      refine ⟨16083683566657391862164447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10722455711104927908109631 16083683566657391862164447)
      ·
        refine ⟨24125525349986087793246671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16083683566657391862164447 24125525349986087793246671)
        ·
          refine ⟨36188288024979131689870007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24125525349986087793246671 36188288024979131689870007)
          ·
            refine ⟨54282432037468697534805011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36188288024979131689870007 54282432037468697534805011)
            ·
              refine ⟨81423648056203046302207517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54282432037468697534805011 81423648056203046302207517)
              ·
                refine ⟨30533868021076142363327819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81423648056203046302207517 30533868021076142363327819)
                ·
                  refine ⟨45800802031614213544991729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30533868021076142363327819 45800802031614213544991729)
                  ·
                    refine ⟨34350601523710660158743797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45800802031614213544991729 34350601523710660158743797)
                    ·
                      refine ⟨3220368892847874389882231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34350601523710660158743797 3220368892847874389882231)
                      ·
                        rfl

theorem cell23_6271646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6271646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271646 prefixEnd_6271646 := by exact prefixLift 6271646
  have htrace : WordTrace (prefixWord ++ tailWord_6271646) baseStart_6271646 baseEnd_6271646 := by
    simpa [prefixWord, tailWord_6271646, baseEnd_6271646] using wordTrace_append hprefix tailTrace_6271646
  have hstable : (prefixWord ++ tailWord_6271646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271646).length < 2 ^ (prefixWord ++ tailWord_6271646).sum := by decide
  have hdescent : baseEnd_6271646 < baseStart_6271646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271676 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_6271676 : Nat := 118140960795 + 6271676 * 2 ^ 59
def prefixEnd_6271676 : Nat := 4983230072969 + 3 ^ 40 * 6271676 * 2
def baseEnd_6271676 : Nat := 3220384297267509272507093

theorem tailTrace_6271676 : CollatzResearch.WordTrace tailWord_6271676 prefixEnd_6271676 3220384297267509272507093 := by
  unfold tailWord_6271676
  simp only [CollatzResearch.WordTrace]
  refine ⟨114373408013398221914965441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152497877351197629219953921 114373408013398221914965441)
  ·
    refine ⟨85780056010048666436224081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114373408013398221914965441 85780056010048666436224081)
    ·
      refine ⟨64335042007536499827168061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85780056010048666436224081 64335042007536499827168061)
      ·
        refine ⟨24125640752826187435188023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64335042007536499827168061 24125640752826187435188023)
        ·
          refine ⟨36188461129239281152782035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24125640752826187435188023 36188461129239281152782035)
          ·
            refine ⟨54282691693858921729173053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36188461129239281152782035 54282691693858921729173053)
            ·
              refine ⟨20356009385197095648439895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54282691693858921729173053 20356009385197095648439895)
              ·
                refine ⟨30534014077795643472659843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20356009385197095648439895 30534014077795643472659843)
                ·
                  refine ⟨45801021116693465208989765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30534014077795643472659843 45801021116693465208989765)
                  ·
                    refine ⟨8587691459380024726685581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45801021116693465208989765 8587691459380024726685581)
                    ·
                      refine ⟨3220384297267509272507093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587691459380024726685581 3220384297267509272507093)
                      ·
                        rfl

theorem cell23_6271676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_6271676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271676 prefixEnd_6271676 := by exact prefixLift 6271676
  have htrace : WordTrace (prefixWord ++ tailWord_6271676) baseStart_6271676 baseEnd_6271676 := by
    simpa [prefixWord, tailWord_6271676, baseEnd_6271676] using wordTrace_append hprefix tailTrace_6271676
  have hstable : (prefixWord ++ tailWord_6271676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271676).length < 2 ^ (prefixWord ++ tailWord_6271676).sum := by decide
  have hdescent : baseEnd_6271676 < baseStart_6271676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271689 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 3]
def baseStart_6271689 : Nat := 118140960795 + 6271689 * 2 ^ 59
def prefixEnd_6271689 : Nat := 4983230072969 + 3 ^ 40 * 6271689 * 2
def baseEnd_6271689 : Nat := 3220390972516017721644533

theorem tailTrace_6271689 : CollatzResearch.WordTrace tailWord_6271689 prefixEnd_6271689 3220390972516017721644533 := by
  unfold tailWord_6271689
  simp only [CollatzResearch.WordTrace]
  refine ⟨228747290175749347050154121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152498193450499564700102747 228747290175749347050154121)
  ·
    refine ⟨171560467631812010287615591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228747290175749347050154121 171560467631812010287615591)
    ·
      refine ⟨257340701447718015431423387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171560467631812010287615591 257340701447718015431423387)
      ·
        refine ⟨386011052171577023147135081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257340701447718015431423387 386011052171577023147135081)
        ·
          refine ⟨289508289128682767360351311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386011052171577023147135081 289508289128682767360351311)
          ·
            refine ⟨434262433693024151040526967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289508289128682767360351311 434262433693024151040526967)
            ·
              refine ⟨651393650539536226560790451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434262433693024151040526967 651393650539536226560790451)
              ·
                refine ⟨977090475809304339841185677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651393650539536226560790451 977090475809304339841185677)
                ·
                  refine ⟨366408928428489127440444629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977090475809304339841185677 366408928428489127440444629)
                  ·
                    refine ⟨8587709260042713924385421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 366408928428489127440444629 8587709260042713924385421)
                    ·
                      refine ⟨3220390972516017721644533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587709260042713924385421 3220390972516017721644533)
                      ·
                        rfl

theorem cell23_6271689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 3].length) (baseStart_6271689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271689 prefixEnd_6271689 := by exact prefixLift 6271689
  have htrace : WordTrace (prefixWord ++ tailWord_6271689) baseStart_6271689 baseEnd_6271689 := by
    simpa [prefixWord, tailWord_6271689, baseEnd_6271689] using wordTrace_append hprefix tailTrace_6271689
  have hstable : (prefixWord ++ tailWord_6271689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271689).length < 2 ^ (prefixWord ++ tailWord_6271689).sum := by decide
  have hdescent : baseEnd_6271689 < baseStart_6271689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271700 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_6271700 : Nat := 118140960795 + 6271700 * 2 ^ 59
def prefixEnd_6271700 : Nat := 4983230072969 + 3 ^ 40 * 6271700 * 2
def baseEnd_6271700 : Nat := 1073465540267739059535661

theorem tailTrace_6271700 : CollatzResearch.WordTrace tailWord_6271700 prefixEnd_6271700 1073465540267739059535661 := by
  unfold tailWord_6271700
  simp only [CollatzResearch.WordTrace]
  refine ⟨114373845689354747964402277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152498460919139663952536369 114373845689354747964402277)
  ·
    refine ⟨21445096066754015243325427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114373845689354747964402277 21445096066754015243325427)
    ·
      refine ⟨32167644100131022864988141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21445096066754015243325427 32167644100131022864988141)
      ·
        refine ⟨12062866537549133574370553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32167644100131022864988141 12062866537549133574370553)
        ·
          refine ⟨9047149903161850180777915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12062866537549133574370553 9047149903161850180777915)
          ·
            refine ⟨13570724854742775271166873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9047149903161850180777915 13570724854742775271166873)
            ·
              refine ⟨10178043641057081453375155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13570724854742775271166873 10178043641057081453375155)
              ·
                refine ⟨15267065461585622180062733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10178043641057081453375155 15267065461585622180062733)
                ·
                  refine ⟨5725149548094608317523525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15267065461585622180062733 5725149548094608317523525)
                  ·
                    refine ⟨1073465540267739059535661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725149548094608317523525 1073465540267739059535661)
                    ·
                      rfl

theorem cell23_6271700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_6271700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271700 prefixEnd_6271700 := by exact prefixLift 6271700
  have htrace : WordTrace (prefixWord ++ tailWord_6271700) baseStart_6271700 baseEnd_6271700 := by
    simpa [prefixWord, tailWord_6271700, baseEnd_6271700] using wordTrace_append hprefix tailTrace_6271700
  have hstable : (prefixWord ++ tailWord_6271700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271700).length < 2 ^ (prefixWord ++ tailWord_6271700).sum := by decide
  have hdescent : baseEnd_6271700 < baseStart_6271700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271713 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 6]
def baseStart_6271713 : Nat := 118140960795 + 6271713 * 2 ^ 59
def prefixEnd_6271713 : Nat := 4983230072969 + 3 ^ 40 * 6271713 * 2
def baseEnd_6271713 : Nat := 357822588450191736416047

theorem tailTrace_6271713 : CollatzResearch.WordTrace tailWord_6271713 prefixEnd_6271713 357822588450191736416047 := by
  unfold tailWord_6271713
  simp only [CollatzResearch.WordTrace]
  refine ⟨228748165527662399149027793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152498777018441599432685195 228748165527662399149027793)
  ·
    refine ⟨171561124145746799361770845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228748165527662399149027793 171561124145746799361770845)
    ·
      refine ⟨64335421554655049760664067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171561124145746799361770845 64335421554655049760664067)
      ·
        refine ⟨96503132331982574640996101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64335421554655049760664067 96503132331982574640996101)
        ·
          refine ⟨18094337312246732745186769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96503132331982574640996101 18094337312246732745186769)
          ·
            refine ⟨13570752984185049558890077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18094337312246732745186769 13570752984185049558890077)
            ·
              refine ⟨5089032369069393584583779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13570752984185049558890077 5089032369069393584583779)
              ·
                refine ⟨7633548553604090376875669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089032369069393584583779 7633548553604090376875669)
                ·
                  refine ⟨357822588450191736416047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7633548553604090376875669 357822588450191736416047)
                  ·
                    rfl

theorem cell23_6271713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 6].length) (baseStart_6271713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271713 prefixEnd_6271713 := by exact prefixLift 6271713
  have htrace : WordTrace (prefixWord ++ tailWord_6271713) baseStart_6271713 baseEnd_6271713 := by
    simpa [prefixWord, tailWord_6271713, baseEnd_6271713] using wordTrace_append hprefix tailTrace_6271713
  have hstable : (prefixWord ++ tailWord_6271713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271713).length < 2 ^ (prefixWord ++ tailWord_6271713).sum := by decide
  have hdescent : baseEnd_6271713 < baseStart_6271713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271759 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6]
def baseStart_6271759 : Nat := 118140960795 + 6271759 * 2 ^ 59
def prefixEnd_6271759 : Nat := 4983230072969 + 3 ^ 40 * 6271759 * 2
def baseEnd_6271759 : Nat := 3220426916161832447769211

theorem tailTrace_6271759 : CollatzResearch.WordTrace tailWord_6271759 prefixEnd_6271759 3220426916161832447769211 := by
  unfold tailWord_6271759
  simp only [CollatzResearch.WordTrace]
  refine ⟨228749843285495749005202331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152499895523663832670134887 228749843285495749005202331)
  ·
    refine ⟨343124764928243623507803497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228749843285495749005202331 343124764928243623507803497)
    ·
      refine ⟨257343573696182717630852623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343124764928243623507803497 257343573696182717630852623)
      ·
        refine ⟨386015360544274076446278935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257343573696182717630852623 386015360544274076446278935)
        ·
          refine ⟨579023040816411114669418403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386015360544274076446278935 579023040816411114669418403)
          ·
            refine ⟨868534561224616672004127605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579023040816411114669418403 868534561224616672004127605)
            ·
              refine ⟨81425115114807813000386963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 868534561224616672004127605 81425115114807813000386963)
              ·
                refine ⟨122137672672211719500580445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81425115114807813000386963 122137672672211719500580445)
                ·
                  refine ⟨45801627252079394812717667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122137672672211719500580445 45801627252079394812717667)
                  ·
                    refine ⟨68702440878119092219076501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45801627252079394812717667 68702440878119092219076501)
                    ·
                      refine ⟨3220426916161832447769211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68702440878119092219076501 3220426916161832447769211)
                      ·
                        rfl

theorem cell23_6271759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_6271759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271759 prefixEnd_6271759 := by exact prefixLift 6271759
  have htrace : WordTrace (prefixWord ++ tailWord_6271759) baseStart_6271759 baseEnd_6271759 := by
    simpa [prefixWord, tailWord_6271759, baseEnd_6271759] using wordTrace_append hprefix tailTrace_6271759
  have hstable : (prefixWord ++ tailWord_6271759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271759).length < 2 ^ (prefixWord ++ tailWord_6271759).sum := by decide
  have hdescent : baseEnd_6271759 < baseStart_6271759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271776 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6271776 : Nat := 118140960795 + 6271776 * 2 ^ 59
def prefixEnd_6271776 : Nat := 4983230072969 + 3 ^ 40 * 6271776 * 2
def baseEnd_6271776 : Nat := 3220435645332958881256633

theorem tailTrace_6271776 : CollatzResearch.WordTrace tailWord_6271776 prefixEnd_6271776 3220435645332958881256633 := by
  unfold tailWord_6271776
  simp only [CollatzResearch.WordTrace]
  refine ⟨114375231663217080454285591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152500308884289440605714121 114375231663217080454285591)
  ·
    refine ⟨171562847494825620681428387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114375231663217080454285591 171562847494825620681428387)
    ·
      refine ⟨257344271242238431022142581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171562847494825620681428387 257344271242238431022142581)
      ·
        refine ⟨24126025428959852908325867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 257344271242238431022142581 24126025428959852908325867)
        ·
          refine ⟨36189038143439779362488801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24126025428959852908325867 36189038143439779362488801)
          ·
            refine ⟨27141778607579834521866601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36189038143439779362488801 27141778607579834521866601)
            ·
              refine ⟨20356333955684875891399951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27141778607579834521866601 20356333955684875891399951)
              ·
                refine ⟨30534500933527313837099927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20356333955684875891399951 30534500933527313837099927)
                ·
                  refine ⟨45801751400290970755649891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30534500933527313837099927 45801751400290970755649891)
                  ·
                    refine ⟨68702627100436456133474837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45801751400290970755649891 68702627100436456133474837)
                    ·
                      refine ⟨3220435645332958881256633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68702627100436456133474837 3220435645332958881256633)
                      ·
                        rfl

theorem cell23_6271776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6271776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271776 prefixEnd_6271776 := by exact prefixLift 6271776
  have htrace : WordTrace (prefixWord ++ tailWord_6271776) baseStart_6271776 baseEnd_6271776 := by
    simpa [prefixWord, tailWord_6271776, baseEnd_6271776] using wordTrace_append hprefix tailTrace_6271776
  have hstable : (prefixWord ++ tailWord_6271776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271776).length < 2 ^ (prefixWord ++ tailWord_6271776).sum := by decide
  have hdescent : baseEnd_6271776 < baseStart_6271776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271800 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_6271800 : Nat := 118140960795 + 6271800 * 2 ^ 59
def prefixEnd_6271800 : Nat := 4983230072969 + 3 ^ 40 * 6271800 * 2
def baseEnd_6271800 : Nat := 3220447968868666787356523

theorem tailTrace_6271800 : CollatzResearch.WordTrace tailWord_6271800 prefixEnd_6271800 3220447968868666787356523 := by
  unfold tailWord_6271800
  simp only [CollatzResearch.WordTrace]
  refine ⟨114375669339173606503722427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152500892452231475338296569 114375669339173606503722427)
  ·
    refine ⟨171563504008760409755583641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114375669339173606503722427 171563504008760409755583641)
    ·
      refine ⟨128672628006570307316687731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171563504008760409755583641 128672628006570307316687731)
      ·
        refine ⟨193008942009855460975031597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128672628006570307316687731 193008942009855460975031597)
        ·
          refine ⟨72378353253695797865636849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193008942009855460975031597 72378353253695797865636849)
          ·
            refine ⟨54283764940271848399227637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72378353253695797865636849 54283764940271848399227637)
            ·
              refine ⟨5089102963150485787427591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54283764940271848399227637 5089102963150485787427591)
              ·
                refine ⟨7633654444725728681141387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089102963150485787427591 7633654444725728681141387)
                ·
                  refine ⟨11450481667088593021712081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633654444725728681141387 11450481667088593021712081)
                  ·
                    refine ⟨8587861250316444766284061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11450481667088593021712081 8587861250316444766284061)
                    ·
                      refine ⟨3220447968868666787356523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8587861250316444766284061 3220447968868666787356523)
                      ·
                        rfl

theorem cell23_6271800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_6271800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271800 prefixEnd_6271800 := by exact prefixLift 6271800
  have htrace : WordTrace (prefixWord ++ tailWord_6271800) baseStart_6271800 baseEnd_6271800 := by
    simpa [prefixWord, tailWord_6271800, baseEnd_6271800] using wordTrace_append hprefix tailTrace_6271800
  have hstable : (prefixWord ++ tailWord_6271800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271800).length < 2 ^ (prefixWord ++ tailWord_6271800).sum := by decide
  have hdescent : baseEnd_6271800 < baseStart_6271800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271840 : List Nat := [2, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2]
def baseStart_6271840 : Nat := 118140960795 + 6271840 * 2 ^ 59
def prefixEnd_6271840 : Nat := 4983230072969 + 3 ^ 40 * 6271840 * 2
def baseEnd_6271840 : Nat := 3220468508094846630856339

theorem tailTrace_6271840 : CollatzResearch.WordTrace tailWord_6271840 prefixEnd_6271840 3220468508094846630856339 := by
  unfold tailWord_6271840
  simp only [CollatzResearch.WordTrace]
  refine ⟨114376398799101149919450487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152501865065468199892600649 114376398799101149919450487)
  ·
    refine ⟨171564598198651724879175731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114376398799101149919450487 171564598198651724879175731)
    ·
      refine ⟨257346897297977587318763597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171564598198651724879175731 257346897297977587318763597)
      ·
        refine ⟨96505086486741595244536349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257346897297977587318763597 96505086486741595244536349)
        ·
          refine ⟨36189407432528098216701131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96505086486741595244536349 36189407432528098216701131)
          ·
            refine ⟨54284111148792147325051697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36189407432528098216701131 54284111148792147325051697)
            ·
              refine ⟨40713083361594110493788773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54284111148792147325051697 40713083361594110493788773)
              ·
                refine ⟨7633703130298895717585395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40713083361594110493788773 7633703130298895717585395)
                ·
                  refine ⟨11450554695448343576378093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633703130298895717585395 11450554695448343576378093)
                  ·
                    refine ⟨4293958010793128841141785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11450554695448343576378093 4293958010793128841141785)
                    ·
                      refine ⟨3220468508094846630856339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293958010793128841141785 3220468508094846630856339)
                      ·
                        rfl

theorem cell23_6271840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_6271840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271840 prefixEnd_6271840 := by exact prefixLift 6271840
  have htrace : WordTrace (prefixWord ++ tailWord_6271840) baseStart_6271840 baseEnd_6271840 := by
    simpa [prefixWord, tailWord_6271840, baseEnd_6271840] using wordTrace_append hprefix tailTrace_6271840
  have hstable : (prefixWord ++ tailWord_6271840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271840).length < 2 ^ (prefixWord ++ tailWord_6271840).sum := by decide
  have hdescent : baseEnd_6271840 < baseStart_6271840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271856 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_6271856 : Nat := 118140960795 + 6271856 * 2 ^ 59
def prefixEnd_6271856 : Nat := 4983230072969 + 3 ^ 40 * 6271856 * 2
def baseEnd_6271856 : Nat := 3220476723785318568256265

theorem tailTrace_6271856 : CollatzResearch.WordTrace tailWord_6271856 prefixEnd_6271856 3220476723785318568256265 := by
  unfold tailWord_6271856
  simp only [CollatzResearch.WordTrace]
  refine ⟨114376690583072167285741711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152502254110762889714322281 114376690583072167285741711)
  ·
    refine ⟨171565035874608250928612567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114376690583072167285741711 171565035874608250928612567)
    ·
      refine ⟨257347553811912376392918851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171565035874608250928612567 257347553811912376392918851)
      ·
        refine ⟨386021330717868564589378277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257347553811912376392918851 386021330717868564589378277)
        ·
          refine ⟨72378999509600355860508427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386021330717868564589378277 72378999509600355860508427)
          ·
            refine ⟨108568499264400533790762641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72378999509600355860508427 108568499264400533790762641)
            ·
              refine ⟨81426374448300400343071981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108568499264400533790762641 81426374448300400343071981)
              ·
                refine ⟨30534890418112650128651993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81426374448300400343071981 30534890418112650128651993)
                ·
                  refine ⟨22901167813584487596488995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30534890418112650128651993 22901167813584487596488995)
                  ·
                    refine ⟨34351751720376731394733493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22901167813584487596488995 34351751720376731394733493)
                    ·
                      refine ⟨3220476723785318568256265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34351751720376731394733493 3220476723785318568256265)
                      ·
                        rfl

theorem cell23_6271856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_6271856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271856 prefixEnd_6271856 := by exact prefixLift 6271856
  have htrace : WordTrace (prefixWord ++ tailWord_6271856) baseStart_6271856 baseEnd_6271856 := by
    simpa [prefixWord, tailWord_6271856, baseEnd_6271856] using wordTrace_append hprefix tailTrace_6271856
  have hstable : (prefixWord ++ tailWord_6271856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271856).length < 2 ^ (prefixWord ++ tailWord_6271856).sum := by decide
  have hdescent : baseEnd_6271856 < baseStart_6271856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271857 : List Nat := [1, 2, 2, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_6271857 : Nat := 118140960795 + 6271857 * 2 ^ 59
def prefixEnd_6271857 : Nat := 4983230072969 + 3 ^ 40 * 6271857 * 2
def baseEnd_6271857 : Nat := 3220477237265973064343761

theorem tailTrace_6271857 : CollatzResearch.WordTrace tailWord_6271857 prefixEnd_6271857 3220477237265973064343761 := by
  unfold tailWord_6271857
  simp only [CollatzResearch.WordTrace]
  refine ⟨228753417639140711742269825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152502278426093807828179883 228753417639140711742269825)
  ·
    refine ⟨171565063229355533806702369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228753417639140711742269825 171565063229355533806702369)
    ·
      refine ⟨128673797422016650355026777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171565063229355533806702369 128673797422016650355026777)
      ·
        refine ⟨96505348066512487766270083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128673797422016650355026777 96505348066512487766270083)
        ·
          refine ⟨144758022099768731649405125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96505348066512487766270083 144758022099768731649405125)
          ·
            refine ⟨27142129143706637184263461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144758022099768731649405125 27142129143706637184263461)
            ·
              refine ⟨5089149214444994472049399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27142129143706637184263461 5089149214444994472049399)
              ·
                refine ⟨7633723821667491708074099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089149214444994472049399 7633723821667491708074099)
                ·
                  refine ⟨11450585732501237562111149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633723821667491708074099 11450585732501237562111149)
                  ·
                    refine ⟨4293969649687964085791681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11450585732501237562111149 4293969649687964085791681)
                    ·
                      refine ⟨3220477237265973064343761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4293969649687964085791681 3220477237265973064343761)
                      ·
                        rfl

theorem cell23_6271857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_6271857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271857 prefixEnd_6271857 := by exact prefixLift 6271857
  have htrace : WordTrace (prefixWord ++ tailWord_6271857) baseStart_6271857 baseEnd_6271857 := by
    simpa [prefixWord, tailWord_6271857, baseEnd_6271857] using wordTrace_append hprefix tailTrace_6271857
  have hstable : (prefixWord ++ tailWord_6271857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271857).length < 2 ^ (prefixWord ++ tailWord_6271857).sum := by decide
  have hdescent : baseEnd_6271857 < baseStart_6271857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271916 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_6271916 : Nat := 118140960795 + 6271916 * 2 ^ 59
def prefixEnd_6271916 : Nat := 4983230072969 + 3 ^ 40 * 6271916 * 2
def baseEnd_6271916 : Nat := 3220507532624588333505989

theorem tailTrace_6271916 : CollatzResearch.WordTrace tailWord_6271916 prefixEnd_6271916 3220507532624588333505989 := by
  unfold tailWord_6271916
  simp only [CollatzResearch.WordTrace]
  refine ⟨114377784772963482409333801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152503713030617976545778401 114377784772963482409333801)
  ·
    refine ⟨85783338579722611807000351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114377784772963482409333801 85783338579722611807000351)
    ·
      refine ⟨128675007869583917710500527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85783338579722611807000351 128675007869583917710500527)
      ·
        refine ⟨193012511804375876565750791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128675007869583917710500527 193012511804375876565750791)
        ·
          refine ⟨289518767706563814848626187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193012511804375876565750791 289518767706563814848626187)
          ·
            refine ⟨434278151559845722272939281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289518767706563814848626187 434278151559845722272939281)
            ·
              refine ⟨325708613669884291704704461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434278151559845722272939281 325708613669884291704704461)
              ·
                refine ⟨122140730126206609389264173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 325708613669884291704704461 122140730126206609389264173)
                ·
                  refine ⟨45802773797327478520974065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122140730126206609389264173 45802773797327478520974065)
                  ·
                    refine ⟨34352080347995608890730549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45802773797327478520974065 34352080347995608890730549)
                    ·
                      refine ⟨3220507532624588333505989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34352080347995608890730549 3220507532624588333505989)
                      ·
                        rfl

theorem cell23_6271916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_6271916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271916 prefixEnd_6271916 := by exact prefixLift 6271916
  have htrace : WordTrace (prefixWord ++ tailWord_6271916) baseStart_6271916 baseEnd_6271916 := by
    simpa [prefixWord, tailWord_6271916, baseEnd_6271916] using wordTrace_append hprefix tailTrace_6271916
  have hstable : (prefixWord ++ tailWord_6271916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271916).length < 2 ^ (prefixWord ++ tailWord_6271916).sum := by decide
  have hdescent : baseEnd_6271916 < baseStart_6271916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271942 : List Nat := [6, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_6271942 : Nat := 118140960795 + 6271942 * 2 ^ 59
def prefixEnd_6271942 : Nat := 4983230072969 + 3 ^ 40 * 6271942 * 2
def baseEnd_6271942 : Nat := 3220520883121605231780871

theorem tailTrace_6271942 : CollatzResearch.WordTrace tailWord_6271942 prefixEnd_6271942 3220520883121605231780871 := by
  unfold tailWord_6271942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7148641182619774101847315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152504345229221847506076053 7148641182619774101847315)
  ·
    refine ⟨10722961773929661152770973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7148641182619774101847315 10722961773929661152770973)
    ·
      refine ⟨4021110665223622932289115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10722961773929661152770973 4021110665223622932289115)
      ·
        refine ⟨6031665997835434398433673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021110665223622932289115 6031665997835434398433673)
        ·
          refine ⟨4523749498376575798825255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6031665997835434398433673 4523749498376575798825255)
          ·
            refine ⟨6785624247564863698237883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523749498376575798825255 6785624247564863698237883)
            ·
              refine ⟨10178436371347295547356825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785624247564863698237883 10178436371347295547356825)
              ·
                refine ⟨7633827278510471660517619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10178436371347295547356825 7633827278510471660517619)
                ·
                  refine ⟨11450740917765707490776429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7633827278510471660517619 11450740917765707490776429)
                  ·
                    refine ⟨4294027844162140309041161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11450740917765707490776429 4294027844162140309041161)
                    ·
                      refine ⟨3220520883121605231780871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294027844162140309041161 3220520883121605231780871)
                      ·
                        rfl

theorem cell23_6271942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_6271942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271942 prefixEnd_6271942 := by exact prefixLift 6271942
  have htrace : WordTrace (prefixWord ++ tailWord_6271942) baseStart_6271942 baseEnd_6271942 := by
    simpa [prefixWord, tailWord_6271942, baseEnd_6271942] using wordTrace_append hprefix tailTrace_6271942
  have hstable : (prefixWord ++ tailWord_6271942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271942).length < 2 ^ (prefixWord ++ tailWord_6271942).sum := by decide
  have hdescent : baseEnd_6271942 < baseStart_6271942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271953 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 5, 4]
def baseStart_6271953 : Nat := 118140960795 + 6271953 * 2 ^ 59
def prefixEnd_6271953 : Nat := 4983230072969 + 3 ^ 40 * 6271953 * 2
def baseEnd_6271953 : Nat := 1073508843802934896247773

theorem tailTrace_6271953 : CollatzResearch.WordTrace tailWord_6271953 prefixEnd_6271953 1073508843802934896247773 := by
  unfold tailWord_6271953
  simp only [CollatzResearch.WordTrace]
  refine ⟨228756919046792920137764513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152504612697861946758509675 228756919046792920137764513)
  ·
    refine ⟨171567689285094690103323385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228756919046792920137764513 171567689285094690103323385)
    ·
      refine ⟨128675766963821017577492539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171567689285094690103323385 128675766963821017577492539)
      ·
        refine ⟨193013650445731526366238809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128675766963821017577492539 193013650445731526366238809)
        ·
          refine ⟨144760237834298644774679107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193013650445731526366238809 144760237834298644774679107)
          ·
            refine ⟨217140356751447967162018661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144760237834298644774679107 217140356751447967162018661)
            ·
              refine ⟨40713816890896493842878499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217140356751447967162018661 40713816890896493842878499)
              ·
                refine ⟨61070725336344740764317749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40713816890896493842878499 61070725336344740764317749)
                ·
                  refine ⟨5725380500282319446654789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61070725336344740764317749 5725380500282319446654789)
                  ·
                    refine ⟨1073508843802934896247773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725380500282319446654789 1073508843802934896247773)
                    ·
                      rfl

theorem cell23_6271953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_6271953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271953 prefixEnd_6271953 := by exact prefixLift 6271953
  have htrace : WordTrace (prefixWord ++ tailWord_6271953) baseStart_6271953 baseEnd_6271953 := by
    simpa [prefixWord, tailWord_6271953, baseEnd_6271953] using wordTrace_append hprefix tailTrace_6271953
  have hstable : (prefixWord ++ tailWord_6271953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271953).length < 2 ^ (prefixWord ++ tailWord_6271953).sum := by decide
  have hdescent : baseEnd_6271953 < baseStart_6271953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271960 : List Nat := [2, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_6271960 : Nat := 118140960795 + 6271960 * 2 ^ 59
def prefixEnd_6271960 : Nat := 4983230072969 + 3 ^ 40 * 6271960 * 2
def baseEnd_6271960 : Nat := 3220530125773386161355787

theorem tailTrace_6271960 : CollatzResearch.WordTrace tailWord_6271960 prefixEnd_6271960 3220530125773386161355787 := by
  unfold tailWord_6271960
  simp only [CollatzResearch.WordTrace]
  refine ⟨114378587178883780166634667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152504782905178373555512889 114378587178883780166634667)
  ·
    refine ⟨171567880768325670249952001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114378587178883780166634667 171567880768325670249952001)
    ·
      refine ⟨128675910576244252687464001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171567880768325670249952001 128675910576244252687464001)
      ·
        refine ⟨96506932932183189515598001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128675910576244252687464001 96506932932183189515598001)
        ·
          refine ⟨72380199699137392136698501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96506932932183189515598001 72380199699137392136698501)
          ·
            refine ⟨13571287443588261025630969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72380199699137392136698501 13571287443588261025630969)
            ·
              refine ⟨10178465582691195769223227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13571287443588261025630969 10178465582691195769223227)
              ·
                refine ⟨15267698374036793653834841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10178465582691195769223227 15267698374036793653834841)
                ·
                  refine ⟨11450773780527595240376131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15267698374036793653834841 11450773780527595240376131)
                  ·
                    refine ⟨17176160670791392860564197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11450773780527595240376131 17176160670791392860564197)
                    ·
                      refine ⟨3220530125773386161355787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17176160670791392860564197 3220530125773386161355787)
                      ·
                        rfl

theorem cell23_6271960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_6271960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271960 prefixEnd_6271960 := by exact prefixLift 6271960
  have htrace : WordTrace (prefixWord ++ tailWord_6271960) baseStart_6271960 baseEnd_6271960 := by
    simpa [prefixWord, tailWord_6271960, baseEnd_6271960] using wordTrace_append hprefix tailTrace_6271960
  have hstable : (prefixWord ++ tailWord_6271960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271960).length < 2 ^ (prefixWord ++ tailWord_6271960).sum := by decide
  have hdescent : baseEnd_6271960 < baseStart_6271960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6271983 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 6]
def baseStart_6271983 : Nat := 118140960795 + 6271983 * 2 ^ 59
def prefixEnd_6271983 : Nat := 4983230072969 + 3 ^ 40 * 6271983 * 2
def baseEnd_6271983 : Nat := 357837992869826619040909

theorem tailTrace_6271983 : CollatzResearch.WordTrace tailWord_6271983 prefixEnd_6271983 357837992869826619040909 := by
  unfold tailWord_6271983
  simp only [CollatzResearch.WordTrace]
  refine ⟨228758013236684235261356603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152505342157789490174237735 228758013236684235261356603)
  ·
    refine ⟨343137019855026352892034905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228758013236684235261356603 343137019855026352892034905)
    ·
      refine ⟨257352764891269764669026179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343137019855026352892034905 257352764891269764669026179)
      ·
        refine ⟨386029147336904647003539269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257352764891269764669026179 386029147336904647003539269)
        ·
          refine ⟨72380465125669621313163613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 386029147336904647003539269 72380465125669621313163613)
          ·
            refine ⟨27142674422126107992436355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72380465125669621313163613 27142674422126107992436355)
            ·
              refine ⟨40714011633189161988654533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27142674422126107992436355 40714011633189161988654533)
              ·
                refine ⟨7633877181222967872872725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40714011633189161988654533 7633877181222967872872725)
                ·
                  refine ⟨357837992869826619040909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7633877181222967872872725 357837992869826619040909)
                  ·
                    rfl

theorem cell23_6271983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 6].length) (baseStart_6271983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6271983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6271983 prefixEnd_6271983 := by exact prefixLift 6271983
  have htrace : WordTrace (prefixWord ++ tailWord_6271983) baseStart_6271983 baseEnd_6271983 := by
    simpa [prefixWord, tailWord_6271983, baseEnd_6271983] using wordTrace_append hprefix tailTrace_6271983
  have hstable : (prefixWord ++ tailWord_6271983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6271983).length < 2 ^ (prefixWord ++ tailWord_6271983).sum := by decide
  have hdescent : baseEnd_6271983 < baseStart_6271983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6271983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272060 : List Nat := [2, 2, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_6272060 : Nat := 118140960795 + 6272060 * 2 ^ 59
def prefixEnd_6272060 : Nat := 4983230072969 + 3 ^ 40 * 6272060 * 2
def baseEnd_6272060 : Nat := 1073527157946278590035109

theorem tailTrace_6272060 : CollatzResearch.WordTrace tailWord_6272060 prefixEnd_6272060 1073527157946278590035109 := by
  unfold tailWord_6272060
  simp only [CollatzResearch.WordTrace]
  refine ⟨114380410828702638705954817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152507214438270184941273089 114380410828702638705954817)
  ·
    refine ⟨85785308121526979029466113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114380410828702638705954817 85785308121526979029466113)
    ·
      refine ⟨64338981091145234272099585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85785308121526979029466113 64338981091145234272099585)
      ·
        refine ⟨48254235818358925704074689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64338981091145234272099585 48254235818358925704074689)
        ·
          refine ⟨36190676863769194278056017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48254235818358925704074689 36190676863769194278056017)
          ·
            refine ⟨27143007647826895708542013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36190676863769194278056017 27143007647826895708542013)
            ·
              refine ⟨10178627867935085890703255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27143007647826895708542013 10178627867935085890703255)
              ·
                refine ⟨15267941801902628836054883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10178627867935085890703255 15267941801902628836054883)
                ·
                  refine ⟨22901912702853943254082325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15267941801902628836054883 22901912702853943254082325)
                  ·
                    refine ⟨1073527157946278590035109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22901912702853943254082325 1073527157946278590035109)
                    ·
                      rfl

theorem cell23_6272060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_6272060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272060 prefixEnd_6272060 := by exact prefixLift 6272060
  have htrace : WordTrace (prefixWord ++ tailWord_6272060) baseStart_6272060 baseEnd_6272060 := by
    simpa [prefixWord, tailWord_6272060, baseEnd_6272060] using wordTrace_append hprefix tailTrace_6272060
  have hstable : (prefixWord ++ tailWord_6272060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272060).length < 2 ^ (prefixWord ++ tailWord_6272060).sum := by decide
  have hdescent : baseEnd_6272060 < baseStart_6272060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272067 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 3, 2, 2]
def baseStart_6272067 : Nat := 118140960795 + 6272067 * 2 ^ 59
def prefixEnd_6272067 : Nat := 4983230072969 + 3 ^ 40 * 6272067 * 2
def baseEnd_6272067 : Nat := 3220585068203417242717795

theorem tailTrace_6272067 : CollatzResearch.WordTrace tailWord_6272067 prefixEnd_6272067 3220585068203417242717795 := by
  unfold tailWord_6272067
  simp only [CollatzResearch.WordTrace]
  refine ⟨228761076968379917607414455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152507384645586611738276303 228761076968379917607414455)
  ·
    refine ⟨343141615452569876411121683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228761076968379917607414455 343141615452569876411121683)
    ·
      refine ⟨514712423178854814616682525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343141615452569876411121683 514712423178854814616682525)
      ·
        refine ⟨193017158692070555481255947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514712423178854814616682525 193017158692070555481255947)
        ·
          refine ⟨289525738038105833221883921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193017158692070555481255947 289525738038105833221883921)
          ·
            refine ⟨217144303528579374916412941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289525738038105833221883921 217144303528579374916412941)
            ·
              refine ⟨81429113823217265593654853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217144303528579374916412941 81429113823217265593654853)
              ·
                refine ⟨15267958841853237298810285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81429113823217265593654853 15267958841853237298810285)
                ·
                  refine ⟨5725484565694963987053857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15267958841853237298810285 5725484565694963987053857)
                  ·
                    refine ⟨4294113424271222990290393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5725484565694963987053857 4294113424271222990290393)
                    ·
                      refine ⟨3220585068203417242717795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294113424271222990290393 3220585068203417242717795)
                      ·
                        rfl

theorem cell23_6272067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_6272067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272067 prefixEnd_6272067 := by exact prefixLift 6272067
  have htrace : WordTrace (prefixWord ++ tailWord_6272067) baseStart_6272067 baseEnd_6272067 := by
    simpa [prefixWord, tailWord_6272067, baseEnd_6272067] using wordTrace_append hprefix tailTrace_6272067
  have hstable : (prefixWord ++ tailWord_6272067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272067).length < 2 ^ (prefixWord ++ tailWord_6272067).sum := by decide
  have hdescent : baseEnd_6272067 < baseStart_6272067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272077 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6272077 : Nat := 118140960795 + 6272077 * 2 ^ 59
def prefixEnd_6272077 : Nat := 4983230072969 + 3 ^ 40 * 6272077 * 2
def baseEnd_6272077 : Nat := 1073530067669987401197583

theorem tailTrace_6272077 : CollatzResearch.WordTrace tailWord_6272077 prefixEnd_6272077 1073530067669987401197583 := by
  unfold tailWord_6272077
  simp only [CollatzResearch.WordTrace]
  refine ⟨228761441698343689315278485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152507627798895792876852323 228761441698343689315278485)
  ·
    refine ⟨10723192579609860436653679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228761441698343689315278485 10723192579609860436653679)
    ·
      refine ⟨16084788869414790654980519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10723192579609860436653679 16084788869414790654980519)
      ·
        refine ⟨24127183304122185982470779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16084788869414790654980519 24127183304122185982470779)
        ·
          refine ⟨36190774956183278973706169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24127183304122185982470779 36190774956183278973706169)
          ·
            refine ⟨27143081217137459230279627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36190774956183278973706169 27143081217137459230279627)
            ·
              refine ⟨40714621825706188845419441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27143081217137459230279627 40714621825706188845419441)
              ·
                refine ⟨30535966369279641634064581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40714621825706188845419441 30535966369279641634064581)
                ·
                  refine ⟨5725493694239932806387109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30535966369279641634064581 5725493694239932806387109)
                  ·
                    refine ⟨1073530067669987401197583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5725493694239932806387109 1073530067669987401197583)
                    ·
                      rfl

theorem cell23_6272077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6272077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272077 prefixEnd_6272077 := by exact prefixLift 6272077
  have htrace : WordTrace (prefixWord ++ tailWord_6272077) baseStart_6272077 baseEnd_6272077 := by
    simpa [prefixWord, tailWord_6272077, baseEnd_6272077] using wordTrace_append hprefix tailTrace_6272077
  have hstable : (prefixWord ++ tailWord_6272077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272077).length < 2 ^ (prefixWord ++ tailWord_6272077).sum := by decide
  have hdescent : baseEnd_6272077 < baseStart_6272077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272113 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_6272113 : Nat := 118140960795 + 6272113 * 2 ^ 59
def prefixEnd_6272113 : Nat := 4983230072969 + 3 ^ 40 * 6272113 * 2
def baseEnd_6272113 : Nat := 3220608688313524062742583

theorem tailTrace_6272113 : CollatzResearch.WordTrace tailWord_6272113 prefixEnd_6272113 3220608688313524062742583 := by
  unfold tailWord_6272113
  simp only [CollatzResearch.WordTrace]
  refine ⟨228762754726213267463588993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152508503150808844975725995 228762754726213267463588993)
  ·
    refine ⟨171572066044659950597691745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228762754726213267463588993 171572066044659950597691745)
    ·
      refine ⟨128679049533494962948268809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171572066044659950597691745 128679049533494962948268809)
      ·
        refine ⟨96509287150121222211201607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128679049533494962948268809 96509287150121222211201607)
        ·
          refine ⟨144763930725181833316802411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96509287150121222211201607 144763930725181833316802411)
          ·
            refine ⟨217145896087772749975203617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144763930725181833316802411 217145896087772749975203617)
            ·
              refine ⟨162859422065829562481402713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217145896087772749975203617 162859422065829562481402713)
              ·
                refine ⟨122144566549372171861052035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162859422065829562481402713 122144566549372171861052035)
                ·
                  refine ⟨183216849824058257791578053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122144566549372171861052035 183216849824058257791578053)
                  ·
                    refine ⟨34353159342010923335920885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 183216849824058257791578053 34353159342010923335920885)
                    ·
                      refine ⟨3220608688313524062742583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34353159342010923335920885 3220608688313524062742583)
                      ·
                        rfl

theorem cell23_6272113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_6272113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272113 prefixEnd_6272113 := by exact prefixLift 6272113
  have htrace : WordTrace (prefixWord ++ tailWord_6272113) baseStart_6272113 baseEnd_6272113 := by
    simpa [prefixWord, tailWord_6272113, baseEnd_6272113] using wordTrace_append hprefix tailTrace_6272113
  have hstable : (prefixWord ++ tailWord_6272113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272113).length < 2 ^ (prefixWord ++ tailWord_6272113).sum := by decide
  have hdescent : baseEnd_6272113 < baseStart_6272113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272121 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 1, 2, 3]
def baseStart_6272121 : Nat := 118140960795 + 6272121 * 2 ^ 59
def prefixEnd_6272121 : Nat := 4983230072969 + 3 ^ 40 * 6272121 * 2
def baseEnd_6272121 : Nat := 3220612796158760031442547

theorem tailTrace_6272121 : CollatzResearch.WordTrace tailWord_6272121 prefixEnd_6272121 3220612796158760031442547 := by
  unfold tailWord_6272121
  simp only [CollatzResearch.WordTrace]
  refine ⟨228763046510184284829880217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152508697673456189886586811 228763046510184284829880217)
  ·
    refine ⟨171572284882638213622410163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228763046510184284829880217 171572284882638213622410163)
    ·
      refine ⟨257358427323957320433615245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171572284882638213622410163 257358427323957320433615245)
      ·
        refine ⟨96509410246483995162605717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 257358427323957320433615245 96509410246483995162605717)
        ·
          refine ⟨4523878605303937273247143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 96509410246483995162605717 4523878605303937273247143)
          ·
            refine ⟨6785817907955905909870715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4523878605303937273247143 6785817907955905909870715)
            ·
              refine ⟨10178726861933858864806073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6785817907955905909870715 10178726861933858864806073)
              ·
                refine ⟨7634045146450394148604555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10178726861933858864806073 7634045146450394148604555)
                ·
                  refine ⟨11451067719675591222906833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634045146450394148604555 11451067719675591222906833)
                  ·
                    refine ⟨8588300789756693417180125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11451067719675591222906833 8588300789756693417180125)
                    ·
                      refine ⟨3220612796158760031442547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8588300789756693417180125 3220612796158760031442547)
                      ·
                        rfl

theorem cell23_6272121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 2, 3].length) (baseStart_6272121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272121 prefixEnd_6272121 := by exact prefixLift 6272121
  have htrace : WordTrace (prefixWord ++ tailWord_6272121) baseStart_6272121 baseEnd_6272121 := by
    simpa [prefixWord, tailWord_6272121, baseEnd_6272121] using wordTrace_append hprefix tailTrace_6272121
  have hstable : (prefixWord ++ tailWord_6272121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272121).length < 2 ^ (prefixWord ++ tailWord_6272121).sum := by decide
  have hdescent : baseEnd_6272121 < baseStart_6272121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272143 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5]
def baseStart_6272143 : Nat := 118140960795 + 6272143 * 2 ^ 59
def prefixEnd_6272143 : Nat := 4983230072969 + 3 ^ 40 * 6272143 * 2
def baseEnd_6272143 : Nat := 3220624092733158945367445

theorem tailTrace_6272143 : CollatzResearch.WordTrace tailWord_6272143 prefixEnd_6272143 3220624092733158945367445 := by
  unfold tailWord_6272143
  simp only [CollatzResearch.WordTrace]
  refine ⟨228763848916104582587181083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152509232610736388391454055 228763848916104582587181083)
  ·
    refine ⟨343145773374156873880771625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228763848916104582587181083 343145773374156873880771625)
    ·
      refine ⟨257359330030617655410578719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343145773374156873880771625 257359330030617655410578719)
      ·
        refine ⟨386038995045926483115868079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257359330030617655410578719 386038995045926483115868079)
        ·
          refine ⟨579058492568889724673802119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386038995045926483115868079 579058492568889724673802119)
          ·
            refine ⟨868587738853334587010703179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579058492568889724673802119 868587738853334587010703179)
            ·
              refine ⟨1302881608280001880516054769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868587738853334587010703179 1302881608280001880516054769)
              ·
                refine ⟨977161206210001410387041077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302881608280001880516054769 977161206210001410387041077)
                ·
                  refine ⟨91608863082187632223785101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 977161206210001410387041077 91608863082187632223785101)
                  ·
                    refine ⟨34353323655820362083919413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91608863082187632223785101 34353323655820362083919413)
                    ·
                      refine ⟨3220624092733158945367445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34353323655820362083919413 3220624092733158945367445)
                      ·
                        rfl

theorem cell23_6272143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_6272143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272143 prefixEnd_6272143 := by exact prefixLift 6272143
  have htrace : WordTrace (prefixWord ++ tailWord_6272143) baseStart_6272143 baseEnd_6272143 := by
    simpa [prefixWord, tailWord_6272143, baseEnd_6272143] using wordTrace_append hprefix tailTrace_6272143
  have hstable : (prefixWord ++ tailWord_6272143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272143).length < 2 ^ (prefixWord ++ tailWord_6272143).sum := by decide
  have hdescent : baseEnd_6272143 < baseStart_6272143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272153 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 6]
def baseStart_6272153 : Nat := 118140960795 + 6272153 * 2 ^ 59
def prefixEnd_6272153 : Nat := 4983230072969 + 3 ^ 40 * 6272153 * 2
def baseEnd_6272153 : Nat := 3220629227539703906242399

theorem tailTrace_6272153 : CollatzResearch.WordTrace tailWord_6272153 prefixEnd_6272153 3220629227539703906242399 := by
  unfold tailWord_6272153
  simp only [CollatzResearch.WordTrace]
  refine ⟨228764213646068354295045113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152509475764045569530030075 228764213646068354295045113)
  ·
    refine ⟨171573160234551265721283835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228764213646068354295045113 171573160234551265721283835)
    ·
      refine ⟨257359740351826898581925753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171573160234551265721283835 257359740351826898581925753)
      ·
        refine ⟨193019805263870173936444315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257359740351826898581925753 193019805263870173936444315)
        ·
          refine ⟨289529707895805260904666473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193019805263870173936444315 289529707895805260904666473)
          ·
            refine ⟨217147280921853945678499855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289529707895805260904666473 217147280921853945678499855)
            ·
              refine ⟨325720921382780918517749783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217147280921853945678499855 325720921382780918517749783)
              ·
                refine ⟨488581382074171377776624675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325720921382780918517749783 488581382074171377776624675)
                ·
                  refine ⟨732872073111257066664937013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488581382074171377776624675 732872073111257066664937013)
                  ·
                    refine ⟨68706756854180349999837845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 732872073111257066664937013 68706756854180349999837845)
                    ·
                      refine ⟨3220629227539703906242399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68706756854180349999837845 3220629227539703906242399)
                      ·
                        rfl

theorem cell23_6272153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_6272153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272153 prefixEnd_6272153 := by exact prefixLift 6272153
  have htrace : WordTrace (prefixWord ++ tailWord_6272153) baseStart_6272153 baseEnd_6272153 := by
    simpa [prefixWord, tailWord_6272153, baseEnd_6272153] using wordTrace_append hprefix tailTrace_6272153
  have hstable : (prefixWord ++ tailWord_6272153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272153).length < 2 ^ (prefixWord ++ tailWord_6272153).sum := by decide
  have hdescent : baseEnd_6272153 < baseStart_6272153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272157 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_6272157 : Nat := 118140960795 + 6272157 * 2 ^ 59
def prefixEnd_6272157 : Nat := 4983230072969 + 3 ^ 40 * 6272157 * 2
def baseEnd_6272157 : Nat := 3220631281462321890592381

theorem tailTrace_6272157 : CollatzResearch.WordTrace tailWord_6272157 prefixEnd_6272157 3220631281462321890592381 := by
  unfold tailWord_6272157
  simp only [CollatzResearch.WordTrace]
  refine ⟨228764359538053862978190725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152509573025369241985460483 228764359538053862978190725)
  ·
    refine ⟨42893317413385099308410761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228764359538053862978190725 42893317413385099308410761)
    ·
      refine ⟨32169988060038824481308071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42893317413385099308410761 32169988060038824481308071)
      ·
        refine ⟨48254982090058236721962107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32169988060038824481308071 48254982090058236721962107)
        ·
          refine ⟨72382473135087355082943161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48254982090058236721962107 72382473135087355082943161)
          ·
            refine ⟨54286854851315516312207371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72382473135087355082943161 54286854851315516312207371)
            ·
              refine ⟨81430282276973274468311057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54286854851315516312207371 81430282276973274468311057)
              ·
                refine ⟨61072711707729955851233293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81430282276973274468311057 61072711707729955851233293)
                ·
                  refine ⟨22902266890398733444212485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61072711707729955851233293 22902266890398733444212485)
                  ·
                    refine ⟨4294175041949762520789841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22902266890398733444212485 4294175041949762520789841)
                    ·
                      refine ⟨3220631281462321890592381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294175041949762520789841 3220631281462321890592381)
                      ·
                        rfl

theorem cell23_6272157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_6272157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272157 prefixEnd_6272157 := by exact prefixLift 6272157
  have htrace : WordTrace (prefixWord ++ tailWord_6272157) baseStart_6272157 baseEnd_6272157 := by
    simpa [prefixWord, tailWord_6272157, baseEnd_6272157] using wordTrace_append hprefix tailTrace_6272157
  have hstable : (prefixWord ++ tailWord_6272157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272157).length < 2 ^ (prefixWord ++ tailWord_6272157).sum := by decide
  have hdescent : baseEnd_6272157 < baseStart_6272157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272160 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_6272160 : Nat := 118140960795 + 6272160 * 2 ^ 59
def prefixEnd_6272160 : Nat := 4983230072969 + 3 ^ 40 * 6272160 * 2
def baseEnd_6272160 : Nat := 3220632821904285378854867

theorem tailTrace_6272160 : CollatzResearch.WordTrace tailWord_6272160 prefixEnd_6272160 3220632821904285378854867 := by
  unfold tailWord_6272160
  simp only [CollatzResearch.WordTrace]
  refine ⟨114382234478521497245274967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152509645971361996327033289 114382234478521497245274967)
  ·
    refine ⟨171573351717782245867912451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114382234478521497245274967 171573351717782245867912451)
    ·
      refine ⟨257360027576673368801868677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171573351717782245867912451 257360027576673368801868677)
      ·
        refine ⟨48255005170626256650350377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257360027576673368801868677 48255005170626256650350377)
        ·
          refine ⟨36191253877969692487762783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48255005170626256650350377 36191253877969692487762783)
          ·
            refine ⟨54286880816954538731644175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36191253877969692487762783 54286880816954538731644175)
            ·
              refine ⟨81430321225431808097466263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54286880816954538731644175 81430321225431808097466263)
              ·
                refine ⟨122145481838147712146199395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81430321225431808097466263 122145481838147712146199395)
                ·
                  refine ⟨183218222757221568219299093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122145481838147712146199395 183218222757221568219299093)
                  ·
                    refine ⟨8588354191744761010279645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 183218222757221568219299093 8588354191744761010279645)
                    ·
                      refine ⟨3220632821904285378854867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8588354191744761010279645 3220632821904285378854867)
                      ·
                        rfl

theorem cell23_6272160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_6272160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272160 prefixEnd_6272160 := by exact prefixLift 6272160
  have htrace : WordTrace (prefixWord ++ tailWord_6272160) baseStart_6272160 baseEnd_6272160 := by
    simpa [prefixWord, tailWord_6272160, baseEnd_6272160] using wordTrace_append hprefix tailTrace_6272160
  have hstable : (prefixWord ++ tailWord_6272160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272160).length < 2 ^ (prefixWord ++ tailWord_6272160).sum := by decide
  have hdescent : baseEnd_6272160 < baseStart_6272160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272163 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 11]
def baseStart_6272163 : Nat := 118140960795 + 6272163 * 2 ^ 59
def prefixEnd_6272163 : Nat := 4983230072969 + 3 ^ 40 * 6272163 * 2
def baseEnd_6272163 : Nat := 357848262482916540790817

theorem tailTrace_6272163 : CollatzResearch.WordTrace tailWord_6272163 prefixEnd_6272163 357848262482916540790817 := by
  unfold tailWord_6272163
  simp only [CollatzResearch.WordTrace]
  refine ⟨228764578376032126002909143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152509718917354750668606095 228764578376032126002909143)
  ·
    refine ⟨343146867564048189004363715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228764578376032126002909143 343146867564048189004363715)
    ·
      refine ⟨514720301346072283506545573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343146867564048189004363715 514720301346072283506545573)
      ·
        refine ⟨96510056502388553157477295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 514720301346072283506545573 96510056502388553157477295)
        ·
          refine ⟨144765084753582829736215943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96510056502388553157477295 144765084753582829736215943)
          ·
            refine ⟨217147627130374244604323915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144765084753582829736215943 217147627130374244604323915)
            ·
              refine ⟨325721440695561366906485873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217147627130374244604323915 325721440695561366906485873)
              ·
                refine ⟨244291080521671025179864405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325721440695561366906485873 244291080521671025179864405)
                ·
                  refine ⟨357848262482916540790817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 244291080521671025179864405 357848262482916540790817)
                  ·
                    rfl

theorem cell23_6272163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 11].length) (baseStart_6272163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272163 prefixEnd_6272163 := by exact prefixLift 6272163
  have htrace : WordTrace (prefixWord ++ tailWord_6272163) baseStart_6272163 baseEnd_6272163 := by
    simpa [prefixWord, tailWord_6272163, baseEnd_6272163] using wordTrace_append hprefix tailTrace_6272163
  have hstable : (prefixWord ++ tailWord_6272163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272163).length < 2 ^ (prefixWord ++ tailWord_6272163).sum := by decide
  have hdescent : baseEnd_6272163 < baseStart_6272163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272167 : List Nat := [1, 1, 6, 2, 1, 2, 1, 1, 2, 6]
def baseStart_6272167 : Nat := 118140960795 + 6272167 * 2 ^ 59
def prefixEnd_6272167 : Nat := 4983230072969 + 3 ^ 40 * 6272167 * 2
def baseEnd_6272167 : Nat := 1073545472089622283822445

theorem tailTrace_6272167 : CollatzResearch.WordTrace tailWord_6272167 prefixEnd_6272167 1073545472089622283822445 := by
  unfold tailWord_6272167
  simp only [CollatzResearch.WordTrace]
  refine ⟨228764724268017634686054755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152509816178678423124036503 228764724268017634686054755)
  ·
    refine ⟨343147086402026452029082133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228764724268017634686054755 343147086402026452029082133)
    ·
      refine ⟨16085019675094989938863225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 343147086402026452029082133 16085019675094989938863225)
      ·
        refine ⟨12063764756321242454147419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16085019675094989938863225 12063764756321242454147419)
        ·
          refine ⟨18095647134481863681221129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12063764756321242454147419 18095647134481863681221129)
          ·
            refine ⟨13571735350861397760915847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18095647134481863681221129 13571735350861397760915847)
            ·
              refine ⟨20357603026292096641373771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13571735350861397760915847 20357603026292096641373771)
              ·
                refine ⟨30536404539438144962060657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20357603026292096641373771 30536404539438144962060657)
                ·
                  refine ⟨22902303404578608721545493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30536404539438144962060657 22902303404578608721545493)
                  ·
                    refine ⟨1073545472089622283822445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22902303404578608721545493 1073545472089622283822445)
                    ·
                      rfl

theorem cell23_6272167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_6272167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272167 prefixEnd_6272167 := by exact prefixLift 6272167
  have htrace : WordTrace (prefixWord ++ tailWord_6272167) baseStart_6272167 baseEnd_6272167 := by
    simpa [prefixWord, tailWord_6272167, baseEnd_6272167] using wordTrace_append hprefix tailTrace_6272167
  have hstable : (prefixWord ++ tailWord_6272167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272167).length < 2 ^ (prefixWord ++ tailWord_6272167).sum := by decide
  have hdescent : baseEnd_6272167 < baseStart_6272167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272264 : List Nat := [2, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_6272264 : Nat := 118140960795 + 6272264 * 2 ^ 59
def prefixEnd_6272264 : Nat := 4983230072969 + 3 ^ 40 * 6272264 * 2
def baseEnd_6272264 : Nat := 3220686223892352971954389

theorem tailTrace_6272264 : CollatzResearch.WordTrace tailWord_6272264 prefixEnd_6272264 3220686223892352971954389 := by
  unfold tailWord_6272264
  simp only [CollatzResearch.WordTrace]
  refine ⟨114384131074333110126167923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152512174765777480168223897 114384131074333110126167923)
  ·
    refine ⟨171576196611499665189251885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114384131074333110126167923 171576196611499665189251885)
    ·
      refine ⟨64341073729312374445969457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171576196611499665189251885 64341073729312374445969457)
      ·
        refine ⟨48255805296984280834477093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64341073729312374445969457 48255805296984280834477093)
        ·
          refine ⟨9047963493184552656464455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48255805296984280834477093 9047963493184552656464455)
          ·
            refine ⟨13571945239776828984696683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9047963493184552656464455 13571945239776828984696683)
            ·
              refine ⟨20357917859665243477045025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13571945239776828984696683 20357917859665243477045025)
              ·
                refine ⟨15268438394748932607783769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20357917859665243477045025 15268438394748932607783769)
                ·
                  refine ⟨11451328796061699455837827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15268438394748932607783769 11451328796061699455837827)
                  ·
                    refine ⟨17176993194092549183756741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11451328796061699455837827 17176993194092549183756741)
                    ·
                      refine ⟨3220686223892352971954389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17176993194092549183756741 3220686223892352971954389)
                      ·
                        rfl

theorem cell23_6272264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_6272264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272264 prefixEnd_6272264 := by exact prefixLift 6272264
  have htrace : WordTrace (prefixWord ++ tailWord_6272264) baseStart_6272264 baseEnd_6272264 := by
    simpa [prefixWord, tailWord_6272264, baseEnd_6272264] using wordTrace_append hprefix tailTrace_6272264
  have hstable : (prefixWord ++ tailWord_6272264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272264).length < 2 ^ (prefixWord ++ tailWord_6272264).sum := by decide
  have hdescent : baseEnd_6272264 < baseStart_6272264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272267 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3]
def baseStart_6272267 : Nat := 118140960795 + 6272267 * 2 ^ 59
def prefixEnd_6272267 : Nat := 4983230072969 + 3 ^ 40 * 6272267 * 2
def baseEnd_6272267 : Nat := 3220687764334316460216875

theorem tailTrace_6272267 : CollatzResearch.WordTrace tailWord_6272267 prefixEnd_6272267 3220687764334316460216875 := by
  unfold tailWord_6272267
  simp only [CollatzResearch.WordTrace]
  refine ⟨228768371567655351764695055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152512247711770234509796703 228768371567655351764695055)
  ·
    refine ⟨343152557351483027647042583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228768371567655351764695055 343152557351483027647042583)
    ·
      refine ⟨514728836027224541470563875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343152557351483027647042583 514728836027224541470563875)
      ·
        refine ⟨772093254040836812205845813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514728836027224541470563875 772093254040836812205845813)
        ·
          refine ⟨72383742566328451144298045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 772093254040836812205845813 72383742566328451144298045)
          ·
            refine ⟨27143903462373169179111767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72383742566328451144298045 27143903462373169179111767)
            ·
              refine ⟨40715855193559753768667651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27143903462373169179111767 40715855193559753768667651)
              ·
                refine ⟨61073782790339630653001477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40715855193559753768667651 61073782790339630653001477)
                ·
                  refine ⟨11451334273188680747437777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61073782790339630653001477 11451334273188680747437777)
                  ·
                    refine ⟨8588500704891510560578333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11451334273188680747437777 8588500704891510560578333)
                    ·
                      refine ⟨3220687764334316460216875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8588500704891510560578333 3220687764334316460216875)
                      ·
                        rfl

theorem cell23_6272267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 2, 3].length) (baseStart_6272267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272267 prefixEnd_6272267 := by exact prefixLift 6272267
  have htrace : WordTrace (prefixWord ++ tailWord_6272267) baseStart_6272267 baseEnd_6272267 := by
    simpa [prefixWord, tailWord_6272267, baseEnd_6272267] using wordTrace_append hprefix tailTrace_6272267
  have hstable : (prefixWord ++ tailWord_6272267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272267).length < 2 ^ (prefixWord ++ tailWord_6272267).sum := by decide
  have hdescent : baseEnd_6272267 < baseStart_6272267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272301 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6272301 : Nat := 118140960795 + 6272301 * 2 ^ 59
def prefixEnd_6272301 : Nat := 4983230072969 + 3 ^ 40 * 6272301 * 2
def baseEnd_6272301 : Nat := 3220705222676569327191719

theorem tailTrace_6272301 : CollatzResearch.WordTrace tailWord_6272301 prefixEnd_6272301 3220705222676569327191719 := by
  unfold tailWord_6272301
  simp only [CollatzResearch.WordTrace]
  refine ⟨228769611649532175571432757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152513074433021450380955171 228769611649532175571432757)
  ·
    refine ⟨21447151092143641459821821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228769611649532175571432757 21447151092143641459821821)
    ·
      refine ⟨8042681659553865547433183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21447151092143641459821821 8042681659553865547433183)
      ·
        refine ⟨12064022489330798321149775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8042681659553865547433183 12064022489330798321149775)
        ·
          refine ⟨18096033733996197481724663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12064022489330798321149775 18096033733996197481724663)
          ·
            refine ⟨27144050600994296222586995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18096033733996197481724663 27144050600994296222586995)
            ·
              refine ⟨40716075901491444333880493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27144050600994296222586995 40716075901491444333880493)
              ·
                refine ⟨15268528463059291625205185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40716075901491444333880493 15268528463059291625205185)
                ·
                  refine ⟨11451396347294468718903889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15268528463059291625205185 11451396347294468718903889)
                  ·
                    refine ⟨8588547260470851539177917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11451396347294468718903889 8588547260470851539177917)
                    ·
                      refine ⟨3220705222676569327191719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8588547260470851539177917 3220705222676569327191719)
                      ·
                        rfl

theorem cell23_6272301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6272301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272301 prefixEnd_6272301 := by exact prefixLift 6272301
  have htrace : WordTrace (prefixWord ++ tailWord_6272301) baseStart_6272301 baseEnd_6272301 := by
    simpa [prefixWord, tailWord_6272301, baseEnd_6272301] using wordTrace_append hprefix tailTrace_6272301
  have hstable : (prefixWord ++ tailWord_6272301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272301).length < 2 ^ (prefixWord ++ tailWord_6272301).sum := by decide
  have hdescent : baseEnd_6272301 < baseStart_6272301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272337 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_6272337 : Nat := 118140960795 + 6272337 * 2 ^ 59
def prefixEnd_6272337 : Nat := 4983230072969 + 3 ^ 40 * 6272337 * 2
def baseEnd_6272337 : Nat := 3220723707980131186341553

theorem tailTrace_6272337 : CollatzResearch.WordTrace tailWord_6272337 prefixEnd_6272337 3220723707980131186341553 := by
  unfold tailWord_6272337
  simp only [CollatzResearch.WordTrace]
  refine ⟨228770924677401753719743265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152513949784934502479828843 228770924677401753719743265)
  ·
    refine ⟨171578193508051315289807449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228770924677401753719743265 171578193508051315289807449)
    ·
      refine ⟨128683645131038486467355587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171578193508051315289807449 128683645131038486467355587)
      ·
        refine ⟨193025467696557729701033381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128683645131038486467355587 193025467696557729701033381)
        ·
          refine ⟨36192275193104574318943759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193025467696557729701033381 36192275193104574318943759)
          ·
            refine ⟨54288412789656861478415639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36192275193104574318943759 54288412789656861478415639)
            ·
              refine ⟨81432619184485292217623459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54288412789656861478415639 81432619184485292217623459)
              ·
                refine ⟨122148928776727938326435189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81432619184485292217623459 122148928776727938326435189)
                ·
                  refine ⟨11451462072818244218103299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122148928776727938326435189 11451462072818244218103299)
                  ·
                    refine ⟨17177193109227366327154949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11451462072818244218103299 17177193109227366327154949)
                    ·
                      refine ⟨3220723707980131186341553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17177193109227366327154949 3220723707980131186341553)
                      ·
                        rfl

theorem cell23_6272337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_6272337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272337 prefixEnd_6272337 := by exact prefixLift 6272337
  have htrace : WordTrace (prefixWord ++ tailWord_6272337) baseStart_6272337 baseEnd_6272337 := by
    simpa [prefixWord, tailWord_6272337, baseEnd_6272337] using wordTrace_append hprefix tailTrace_6272337
  have hstable : (prefixWord ++ tailWord_6272337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272337).length < 2 ^ (prefixWord ++ tailWord_6272337).sum := by decide
  have hdescent : baseEnd_6272337 < baseStart_6272337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272354 : List Nat := [3, 3, 2, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6272354 : Nat := 118140960795 + 6272354 * 2 ^ 59
def prefixEnd_6272354 : Nat := 4983230072969 + 3 ^ 40 * 6272354 * 2
def baseEnd_6272354 : Nat := 3220732437151257619828975

theorem tailTrace_6272354 : CollatzResearch.WordTrace tailWord_6272354 prefixEnd_6272354 3220732437151257619828975 := by
  unfold tailWord_6272354
  simp only [CollatzResearch.WordTrace]
  refine ⟨57192886179585041405778029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152514363145560110415408077 57192886179585041405778029)
  ·
    refine ⟨21447332317344390527166761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57192886179585041405778029 21447332317344390527166761)
    ·
      refine ⟨16085499238008292895375071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21447332317344390527166761 16085499238008292895375071)
      ·
        refine ⟨24128248857012439343062607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16085499238008292895375071 24128248857012439343062607)
        ·
          refine ⟨36192373285518659014593911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24128248857012439343062607 36192373285518659014593911)
          ·
            refine ⟨54288559928277988521890867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36192373285518659014593911 54288559928277988521890867)
            ·
              refine ⟨81432839892416982782836301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54288559928277988521890867 81432839892416982782836301)
              ·
                refine ⟨30537314959656368543563613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81432839892416982782836301 30537314959656368543563613)
                ·
                  refine ⟨11451493109871138203836355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30537314959656368543563613 11451493109871138203836355)
                  ·
                    refine ⟨17177239664806707305754533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11451493109871138203836355 17177239664806707305754533)
                    ·
                      refine ⟨3220732437151257619828975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17177239664806707305754533 3220732437151257619828975)
                      ·
                        rfl

theorem cell23_6272354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6272354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272354 prefixEnd_6272354 := by exact prefixLift 6272354
  have htrace : WordTrace (prefixWord ++ tailWord_6272354) baseStart_6272354 baseEnd_6272354 := by
    simpa [prefixWord, tailWord_6272354, baseEnd_6272354] using wordTrace_append hprefix tailTrace_6272354
  have hstable : (prefixWord ++ tailWord_6272354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272354).length < 2 ^ (prefixWord ++ tailWord_6272354).sum := by decide
  have hdescent : baseEnd_6272354 < baseStart_6272354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272367 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4]
def baseStart_6272367 : Nat := 118140960795 + 6272367 * 2 ^ 59
def prefixEnd_6272367 : Nat := 4983230072969 + 3 ^ 40 * 6272367 * 2
def baseEnd_6272367 : Nat := 3220739112399766068966415

theorem tailTrace_6272367 : CollatzResearch.WordTrace tailWord_6272367 prefixEnd_6272367 3220739112399766068966415 := by
  unfold tailWord_6272367
  simp only [CollatzResearch.WordTrace]
  refine ⟨228772018867293068843335355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152514679244862045895556903 228772018867293068843335355)
  ·
    refine ⟨343158028300939603265003033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228772018867293068843335355 343158028300939603265003033)
    ·
      refine ⟨257368521225704702448752275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343158028300939603265003033 257368521225704702448752275)
      ·
        refine ⟨386052781838557053673128413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257368521225704702448752275 386052781838557053673128413)
        ·
          refine ⟨144769793189458895127423155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386052781838557053673128413 144769793189458895127423155)
          ·
            refine ⟨217154689784188342691134733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144769793189458895127423155 217154689784188342691134733)
            ·
              refine ⟨81433008669070628509175525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217154689784188342691134733 81433008669070628509175525)
              ·
                refine ⟨15268689125450742845470411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81433008669070628509175525 15268689125450742845470411)
                ·
                  refine ⟨22903033688176114268205617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15268689125450742845470411 22903033688176114268205617)
                  ·
                    refine ⟨17177275266132085701154213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22903033688176114268205617 17177275266132085701154213)
                    ·
                      refine ⟨3220739112399766068966415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17177275266132085701154213 3220739112399766068966415)
                      ·
                        rfl

theorem cell23_6272367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_6272367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272367 prefixEnd_6272367 := by exact prefixLift 6272367
  have htrace : WordTrace (prefixWord ++ tailWord_6272367) baseStart_6272367 baseEnd_6272367 := by
    simpa [prefixWord, tailWord_6272367, baseEnd_6272367] using wordTrace_append hprefix tailTrace_6272367
  have hstable : (prefixWord ++ tailWord_6272367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272367).length < 2 ^ (prefixWord ++ tailWord_6272367).sum := by decide
  have hdescent : baseEnd_6272367 < baseStart_6272367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272388 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_6272388 : Nat := 118140960795 + 6272388 * 2 ^ 59
def prefixEnd_6272388 : Nat := 4983230072969 + 3 ^ 40 * 6272388 * 2
def baseEnd_6272388 : Nat := 3220749895493510486803819

theorem tailTrace_6272388 : CollatzResearch.WordTrace tailWord_6272388 prefixEnd_6272388 3220749895493510486803819 := by
  unfold tailWord_6272388
  simp only [CollatzResearch.WordTrace]
  refine ⟨114386392400108494714924909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152515189866811326286566545 114386392400108494714924909)
  ·
    refine ⟨42894897150040685518096841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114386392400108494714924909 42894897150040685518096841)
    ·
      refine ⟨32171172862530514138572631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42894897150040685518096841 32171172862530514138572631)
      ·
        refine ⟨48256759293795771207858947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171172862530514138572631 48256759293795771207858947)
        ·
          refine ⟨72385138940693656811788421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48256759293795771207858947 72385138940693656811788421)
          ·
            refine ⟨13572213551380060652210329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72385138940693656811788421 13572213551380060652210329)
            ·
              refine ⟨10179160163535045489157747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572213551380060652210329 10179160163535045489157747)
              ·
                refine ⟨15268740245302568233736621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179160163535045489157747 15268740245302568233736621)
                ·
                  refine ⟨5725777591988463087651233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15268740245302568233736621 5725777591988463087651233)
                  ·
                    refine ⟨4294333193991347315738425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5725777591988463087651233 4294333193991347315738425)
                    ·
                      refine ⟨3220749895493510486803819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294333193991347315738425 3220749895493510486803819)
                      ·
                        rfl

theorem cell23_6272388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_6272388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272388 prefixEnd_6272388 := by exact prefixLift 6272388
  have htrace : WordTrace (prefixWord ++ tailWord_6272388) baseStart_6272388 baseEnd_6272388 := by
    simpa [prefixWord, tailWord_6272388, baseEnd_6272388] using wordTrace_append hprefix tailTrace_6272388
  have hstable : (prefixWord ++ tailWord_6272388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272388).length < 2 ^ (prefixWord ++ tailWord_6272388).sum := by decide
  have hdescent : baseEnd_6272388 < baseStart_6272388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272398 : List Nat := [4, 1, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_6272398 : Nat := 118140960795 + 6272398 * 2 ^ 59
def prefixEnd_6272398 : Nat := 4983230072969 + 3 ^ 40 * 6272398 * 2
def baseEnd_6272398 : Nat := 1073585010100018482559591

theorem tailTrace_6272398 : CollatzResearch.WordTrace tailWord_6272398 prefixEnd_6272398 1073585010100018482559591 := by
  unfold tailWord_6272398
  simp only [CollatzResearch.WordTrace]
  refine ⟨28596643691272595142214231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152515433020120507425142565 28596643691272595142214231)
  ·
    refine ⟨42894965536908892713321347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28596643691272595142214231 42894965536908892713321347)
    ·
      refine ⟨64342448305363339069982021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42894965536908892713321347 64342448305363339069982021)
      ·
        refine ⟨12064209057255626075621629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64342448305363339069982021 12064209057255626075621629)
        ·
          refine ⟨4524078396470859778358111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12064209057255626075621629 4524078396470859778358111)
          ·
            refine ⟨6786117594706289667537167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524078396470859778358111 6786117594706289667537167)
            ·
              refine ⟨10179176392059434501305751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786117594706289667537167 10179176392059434501305751)
              ·
                refine ⟨15268764588089151751958627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179176392059434501305751 15268764588089151751958627)
                ·
                  refine ⟨22903146882133727627937941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15268764588089151751958627 22903146882133727627937941)
                  ·
                    refine ⟨1073585010100018482559591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22903146882133727627937941 1073585010100018482559591)
                    ·
                      rfl

theorem cell23_6272398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_6272398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272398 prefixEnd_6272398 := by exact prefixLift 6272398
  have htrace : WordTrace (prefixWord ++ tailWord_6272398) baseStart_6272398 baseEnd_6272398 := by
    simpa [prefixWord, tailWord_6272398, baseEnd_6272398] using wordTrace_append hprefix tailTrace_6272398
  have hstable : (prefixWord ++ tailWord_6272398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272398).length < 2 ^ (prefixWord ++ tailWord_6272398).sum := by decide
  have hdescent : baseEnd_6272398 < baseStart_6272398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272408 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6272408 : Nat := 118140960795 + 6272408 * 2 ^ 59
def prefixEnd_6272408 : Nat := 4983230072969 + 3 ^ 40 * 6272408 * 2
def baseEnd_6272408 : Nat := 3220760165106600408553727

theorem tailTrace_6272408 : CollatzResearch.WordTrace tailWord_6272408 prefixEnd_6272408 3220760165106600408553727 := by
  unfold tailWord_6272408
  simp only [CollatzResearch.WordTrace]
  refine ⟨114386757130072266422788939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152515676173429688563718585 114386757130072266422788939)
  ·
    refine ⟨171580135695108399634183409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114386757130072266422788939 171580135695108399634183409)
    ·
      refine ⟨128685101771331299725637557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171580135695108399634183409 128685101771331299725637557)
      ·
        refine ⟨12064228291062309349278521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 128685101771331299725637557 12064228291062309349278521)
        ·
          refine ⟨9048171218296732011958891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12064228291062309349278521 9048171218296732011958891)
          ·
            refine ⟨13572256827445098017938337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048171218296732011958891 13572256827445098017938337)
            ·
              refine ⟨10179192620583823513453753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572256827445098017938337 10179192620583823513453753)
              ·
                refine ⟨7634394465437867635090315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10179192620583823513453753 7634394465437867635090315)
                ·
                  refine ⟨11451591698156801452635473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634394465437867635090315 11451591698156801452635473)
                  ·
                    refine ⟨8588693773617601089476605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11451591698156801452635473 8588693773617601089476605)
                    ·
                      refine ⟨3220760165106600408553727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8588693773617601089476605 3220760165106600408553727)
                      ·
                        rfl

theorem cell23_6272408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6272408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272408 prefixEnd_6272408 := by exact prefixLift 6272408
  have htrace : WordTrace (prefixWord ++ tailWord_6272408) baseStart_6272408 baseEnd_6272408 := by
    simpa [prefixWord, tailWord_6272408, baseEnd_6272408] using wordTrace_append hprefix tailTrace_6272408
  have hstable : (prefixWord ++ tailWord_6272408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272408).length < 2 ^ (prefixWord ++ tailWord_6272408).sum := by decide
  have hdescent : baseEnd_6272408 < baseStart_6272408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272457 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 4]
def baseStart_6272457 : Nat := 118140960795 + 6272457 * 2 ^ 59
def prefixEnd_6272457 : Nat := 4983230072969 + 3 ^ 40 * 6272457 * 2
def baseEnd_6272457 : Nat := 3220785325658670716841001

theorem tailTrace_6272457 : CollatzResearch.WordTrace tailWord_6272457 prefixEnd_6272457 3220785325658670716841001 := by
  unfold tailWord_6272457
  simp only [CollatzResearch.WordTrace]
  refine ⟨228775301436967014214111625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152516867624644676142741083 228775301436967014214111625)
  ·
    refine ⟨171581476077725260660583719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228775301436967014214111625 171581476077725260660583719)
    ·
      refine ⟨257372214116587890990875579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171581476077725260660583719 257372214116587890990875579)
      ·
        refine ⟨386058321174881836486313369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257372214116587890990875579 386058321174881836486313369)
        ·
          refine ⟨289543740881161377364735027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386058321174881836486313369 289543740881161377364735027)
          ·
            refine ⟨434315611321742066047102541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289543740881161377364735027 434315611321742066047102541)
            ·
              refine ⟨162868354245653274767663453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 434315611321742066047102541 162868354245653274767663453)
              ·
                refine ⟨61075632842119978037873795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162868354245653274767663453 61075632842119978037873795)
                ·
                  refine ⟨91613449263179967056810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61075632842119978037873795 91613449263179967056810693)
                  ·
                    refine ⟨17177521736846243823152005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91613449263179967056810693 17177521736846243823152005)
                    ·
                      refine ⟨3220785325658670716841001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17177521736846243823152005 3220785325658670716841001)
                      ·
                        rfl

theorem cell23_6272457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 4].length) (baseStart_6272457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272457 prefixEnd_6272457 := by exact prefixLift 6272457
  have htrace : WordTrace (prefixWord ++ tailWord_6272457) baseStart_6272457 baseEnd_6272457 := by
    simpa [prefixWord, tailWord_6272457, baseEnd_6272457] using wordTrace_append hprefix tailTrace_6272457
  have hstable : (prefixWord ++ tailWord_6272457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272457).length < 2 ^ (prefixWord ++ tailWord_6272457).sum := by decide
  have hdescent : baseEnd_6272457 < baseStart_6272457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272531 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 2, 5]
def baseStart_6272531 : Nat := 118140960795 + 6272531 * 2 ^ 59
def prefixEnd_6272531 : Nat := 4983230072969 + 3 ^ 40 * 6272531 * 2
def baseEnd_6272531 : Nat := 1073607774409034475771887

theorem tailTrace_6272531 : CollatzResearch.WordTrace tailWord_6272531 prefixEnd_6272531 1073607774409034475771887 := by
  unfold tailWord_6272531
  simp only [CollatzResearch.WordTrace]
  refine ⟨228778000438698924852305447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152518666959132616568203631 228778000438698924852305447)
  ·
    refine ⟨343167000658048387278458171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228778000438698924852305447 343167000658048387278458171)
    ·
      refine ⟨514750500987072580917687257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343167000658048387278458171 514750500987072580917687257)
      ·
        refine ⟨386062875740304435688265443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514750500987072580917687257 386062875740304435688265443)
        ·
          refine ⟨579094313610456653532398165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386062875740304435688265443 579094313610456653532398165)
          ·
            refine ⟨6786261487622538908582791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 579094313610456653532398165 6786261487622538908582791)
            ·
              refine ⟨10179392231433808362874187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786261487622538908582791 10179392231433808362874187)
              ·
                refine ⟨15269088347150712544311281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179392231433808362874187 15269088347150712544311281)
                ·
                  refine ⟨11451816260363034408233461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15269088347150712544311281 11451816260363034408233461)
                  ·
                    refine ⟨1073607774409034475771887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11451816260363034408233461 1073607774409034475771887)
                    ·
                      rfl

theorem cell23_6272531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 2, 5].length) (baseStart_6272531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272531 prefixEnd_6272531 := by exact prefixLift 6272531
  have htrace : WordTrace (prefixWord ++ tailWord_6272531) baseStart_6272531 baseEnd_6272531 := by
    simpa [prefixWord, tailWord_6272531, baseEnd_6272531] using wordTrace_append hprefix tailTrace_6272531
  have hstable : (prefixWord ++ tailWord_6272531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272531).length < 2 ^ (prefixWord ++ tailWord_6272531).sum := by decide
  have hdescent : baseEnd_6272531 < baseStart_6272531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272537 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 9]
def baseStart_6272537 : Nat := 118140960795 + 6272537 * 2 ^ 59
def prefixEnd_6272537 : Nat := 4983230072969 + 3 ^ 40 * 6272537 * 2
def baseEnd_6272537 : Nat := 3220826404111030403840633

theorem tailTrace_6272537 : CollatzResearch.WordTrace tailWord_6272537 prefixEnd_6272537 3220826404111030403840633 := by
  unfold tailWord_6272537
  simp only [CollatzResearch.WordTrace]
  refine ⟨228778219276677187877023865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152518812851118125251349243 228778219276677187877023865)
  ·
    refine ⟨171583664457507890907767899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228778219276677187877023865 171583664457507890907767899)
    ·
      refine ⟨257375496686261836361651849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171583664457507890907767899 257375496686261836361651849)
      ·
        refine ⟨193031622514696377271238887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257375496686261836361651849 193031622514696377271238887)
        ·
          refine ⟨289547433772044565906858331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193031622514696377271238887 289547433772044565906858331)
          ·
            refine ⟨434321150658066848860287497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289547433772044565906858331 434321150658066848860287497)
            ·
              refine ⟨325740862993550136645215623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434321150658066848860287497 325740862993550136645215623)
              ·
                refine ⟨488611294490325204967823435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325740862993550136645215623 488611294490325204967823435)
                ·
                  refine ⟨732916941735487807451735153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488611294490325204967823435 732916941735487807451735153)
                  ·
                    refine ⟨549687706301615855588801365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 732916941735487807451735153 549687706301615855588801365)
                    ·
                      refine ⟨3220826404111030403840633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 549687706301615855588801365 3220826404111030403840633)
                      ·
                        rfl

theorem cell23_6272537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_6272537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272537 prefixEnd_6272537 := by exact prefixLift 6272537
  have htrace : WordTrace (prefixWord ++ tailWord_6272537) baseStart_6272537 baseEnd_6272537 := by
    simpa [prefixWord, tailWord_6272537, baseEnd_6272537] using wordTrace_append hprefix tailTrace_6272537
  have hstable : (prefixWord ++ tailWord_6272537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272537).length < 2 ^ (prefixWord ++ tailWord_6272537).sum := by decide
  have hdescent : baseEnd_6272537 < baseStart_6272537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272601 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 3]
def baseStart_6272601 : Nat := 118140960795 + 6272601 * 2 ^ 59
def prefixEnd_6272601 : Nat := 4983230072969 + 3 ^ 40 * 6272601 * 2
def baseEnd_6272601 : Nat := 3220859266872918153440339

theorem tailTrace_6272601 : CollatzResearch.WordTrace tailWord_6272601 prefixEnd_6272601 3220859266872918153440339 := by
  unfold tailWord_6272601
  simp only [CollatzResearch.WordTrace]
  refine ⟨228780553548445326807353657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152520369032296884538235771 228780553548445326807353657)
  ·
    refine ⟨171585415161333995105515243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228780553548445326807353657 171585415161333995105515243)
    ·
      refine ⟨257378122742000992658272865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171585415161333995105515243 257378122742000992658272865)
      ·
        refine ⟨193033592056500744493704649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257378122742000992658272865 193033592056500744493704649)
        ·
          refine ⟨144775194042375558370278487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193033592056500744493704649 144775194042375558370278487)
          ·
            refine ⟨217162791063563337555417731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144775194042375558370278487 217162791063563337555417731)
            ·
              refine ⟨325744186595345006333126597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217162791063563337555417731 325744186595345006333126597)
              ·
                refine ⟨61077034986627188687461237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325744186595345006333126597 61077034986627188687461237)
                ·
                  refine ⟨5725972029996298939449491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61077034986627188687461237 5725972029996298939449491)
                  ·
                    refine ⟨8588958044994448409174237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5725972029996298939449491 8588958044994448409174237)
                    ·
                      refine ⟨3220859266872918153440339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8588958044994448409174237 3220859266872918153440339)
                      ·
                        rfl

theorem cell23_6272601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 5, 1, 3].length) (baseStart_6272601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272601 prefixEnd_6272601 := by exact prefixLift 6272601
  have htrace : WordTrace (prefixWord ++ tailWord_6272601) baseStart_6272601 baseEnd_6272601 := by
    simpa [prefixWord, tailWord_6272601, baseEnd_6272601] using wordTrace_append hprefix tailTrace_6272601
  have hstable : (prefixWord ++ tailWord_6272601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272601).length < 2 ^ (prefixWord ++ tailWord_6272601).sum := by decide
  have hdescent : baseEnd_6272601 < baseStart_6272601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272664 : List Nat := [2, 1, 2, 4, 1, 13]
def baseStart_6272664 : Nat := 118140960795 + 6272664 * 2 ^ 59
def prefixEnd_6272664 : Nat := 4983230072969 + 3 ^ 40 * 6272664 * 2
def baseEnd_6272664 : Nat := 13254698008864820604743

theorem tailTrace_6272664 : CollatzResearch.WordTrace tailWord_6272664 prefixEnd_6272664 13254698008864820604743 := by
  unfold tailWord_6272664
  simp only [CollatzResearch.WordTrace]
  refine ⟨114391425673608544283448523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152521900898144725711264697 114391425673608544283448523)
  ·
    refine ⟨171587138510412816425172785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114391425673608544283448523 171587138510412816425172785)
    ·
      refine ⟨128690353882809612318879589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171587138510412816425172785 128690353882809612318879589)
      ·
        refine ⟨24129441353026802309789923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128690353882809612318879589 24129441353026802309789923)
        ·
          refine ⟨36194162029540203464684885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24129441353026802309789923 36194162029540203464684885)
          ·
            refine ⟨13254698008864820604743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 36194162029540203464684885 13254698008864820604743)
            ·
              rfl

theorem cell23_6272664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 13].length) (baseStart_6272664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272664 prefixEnd_6272664 := by exact prefixLift 6272664
  have htrace : WordTrace (prefixWord ++ tailWord_6272664) baseStart_6272664 baseEnd_6272664 := by
    simpa [prefixWord, tailWord_6272664, baseEnd_6272664] using wordTrace_append hprefix tailTrace_6272664
  have hstable : (prefixWord ++ tailWord_6272664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272664).length < 2 ^ (prefixWord ++ tailWord_6272664).sum := by decide
  have hdescent : baseEnd_6272664 < baseStart_6272664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272706 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6272706 : Nat := 118140960795 + 6272706 * 2 ^ 59
def prefixEnd_6272706 : Nat := 4983230072969 + 3 ^ 40 * 6272706 * 2
def baseEnd_6272706 : Nat := 1073637727447213414209119

theorem tailTrace_6272706 : CollatzResearch.WordTrace tailWord_6272706 prefixEnd_6272706 1073637727447213414209119 := by
  unfold tailWord_6272706
  simp only [CollatzResearch.WordTrace]
  refine ⟨57196095803266232434981493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152522922142043286493283981 57196095803266232434981493)
  ·
    refine ⟨5362133981556209290779515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57196095803266232434981493 5362133981556209290779515)
    ·
      refine ⟨8043200972334313936169273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5362133981556209290779515 8043200972334313936169273)
      ·
        refine ⟨6032400729250735452126955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8043200972334313936169273 6032400729250735452126955)
        ·
          refine ⟨9048601093876103178190433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032400729250735452126955 9048601093876103178190433)
          ·
            refine ⟨6786450820407077383642825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9048601093876103178190433 6786450820407077383642825)
            ·
              refine ⟨5089838115305308037732119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6786450820407077383642825 5089838115305308037732119)
              ·
                refine ⟨7634757172957962056598179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089838115305308037732119 7634757172957962056598179)
                ·
                  refine ⟨11452135759436943084897269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634757172957962056598179 11452135759436943084897269)
                  ·
                    refine ⟨1073637727447213414209119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11452135759436943084897269 1073637727447213414209119)
                    ·
                      rfl

theorem cell23_6272706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6272706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272706 prefixEnd_6272706 := by exact prefixLift 6272706
  have htrace : WordTrace (prefixWord ++ tailWord_6272706) baseStart_6272706 baseEnd_6272706 := by
    simpa [prefixWord, tailWord_6272706, baseEnd_6272706] using wordTrace_append hprefix tailTrace_6272706
  have hstable : (prefixWord ++ tailWord_6272706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272706).length < 2 ^ (prefixWord ++ tailWord_6272706).sum := by decide
  have hdescent : baseEnd_6272706 < baseStart_6272706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272708 : List Nat := [2, 3, 3, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_6272708 : Nat := 118140960795 + 6272708 * 2 ^ 59
def prefixEnd_6272708 : Nat := 4983230072969 + 3 ^ 40 * 6272708 * 2
def baseEnd_6272708 : Nat := 3220914209302949234802347

theorem tailTrace_6272708 : CollatzResearch.WordTrace tailWord_6272708 prefixEnd_6272708 3220914209302949234802347 := by
  unfold tailWord_6272708
  simp only [CollatzResearch.WordTrace]
  refine ⟨114392228079528842040749389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152522970772705122720999185 114392228079528842040749389)
  ·
    refine ⟨42897085529823315765281021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114392228079528842040749389 42897085529823315765281021)
    ·
      refine ⟨16086407073683743411980383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42897085529823315765281021 16086407073683743411980383)
      ·
        refine ⟨24129610610525615117970575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16086407073683743411980383 24129610610525615117970575)
        ·
          refine ⟨36194415915788422676955863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24129610610525615117970575 36194415915788422676955863)
          ·
            refine ⟨54291623873682634015433795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36194415915788422676955863 54291623873682634015433795)
            ·
              refine ⟨81437435810523951023150693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54291623873682634015433795 81437435810523951023150693)
              ·
                refine ⟨15269519214473240816840755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81437435810523951023150693 15269519214473240816840755)
                ·
                  refine ⟨22904278821709861225261133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15269519214473240816840755 22904278821709861225261133)
                  ·
                    refine ⟨8589104558141197959472925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22904278821709861225261133 8589104558141197959472925)
                    ·
                      refine ⟨3220914209302949234802347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589104558141197959472925 3220914209302949234802347)
                      ·
                        rfl

theorem cell23_6272708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_6272708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272708 prefixEnd_6272708 := by exact prefixLift 6272708
  have htrace : WordTrace (prefixWord ++ tailWord_6272708) baseStart_6272708 baseEnd_6272708 := by
    simpa [prefixWord, tailWord_6272708, baseEnd_6272708] using wordTrace_append hprefix tailTrace_6272708
  have hstable : (prefixWord ++ tailWord_6272708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272708).length < 2 ^ (prefixWord ++ tailWord_6272708).sum := by decide
  have hdescent : baseEnd_6272708 < baseStart_6272708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272726 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6272726 : Nat := 118140960795 + 6272726 * 2 ^ 59
def prefixEnd_6272726 : Nat := 4983230072969 + 3 ^ 40 * 6272726 * 2
def baseEnd_6272726 : Nat := 3220923451954730164377265

theorem tailTrace_6272726 : CollatzResearch.WordTrace tailWord_6272726 prefixEnd_6272726 3220923451954730164377265 := by
  unfold tailWord_6272726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299069542062029572228377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152523408448661648770436021 14299069542062029572228377)
  ·
    refine ⟨10724302156546522179171283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14299069542062029572228377 10724302156546522179171283)
    ·
      refine ⟨16086453234819783268756925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724302156546522179171283 16086453234819783268756925)
      ·
        refine ⟨6032419963057418725783847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16086453234819783268756925 6032419963057418725783847)
        ·
          refine ⟨9048629944586128088675771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032419963057418725783847 9048629944586128088675771)
          ·
            refine ⟨13572944916879192133013657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9048629944586128088675771 13572944916879192133013657)
            ·
              refine ⟨10179708687659394099760243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13572944916879192133013657 10179708687659394099760243)
              ·
                refine ⟨15269563031489091149640365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10179708687659394099760243 15269563031489091149640365)
                ·
                  refine ⟨5726086136808409181115137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15269563031489091149640365 5726086136808409181115137)
                  ·
                    refine ⟨4294564602606306885836353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5726086136808409181115137 4294564602606306885836353)
                    ·
                      refine ⟨3220923451954730164377265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294564602606306885836353 3220923451954730164377265)
                      ·
                        rfl

theorem cell23_6272726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6272726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272726 prefixEnd_6272726 := by exact prefixLift 6272726
  have htrace : WordTrace (prefixWord ++ tailWord_6272726) baseStart_6272726 baseEnd_6272726 := by
    simpa [prefixWord, tailWord_6272726, baseEnd_6272726] using wordTrace_append hprefix tailTrace_6272726
  have hstable : (prefixWord ++ tailWord_6272726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272726).length < 2 ^ (prefixWord ++ tailWord_6272726).sum := by decide
  have hdescent : baseEnd_6272726 < baseStart_6272726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272741 : List Nat := [1, 3, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_6272741 : Nat := 118140960795 + 6272741 * 2 ^ 59
def prefixEnd_6272741 : Nat := 4983230072969 + 3 ^ 40 * 6272741 * 2
def baseEnd_6272741 : Nat := 1073643718054849201896565

theorem tailTrace_6272741 : CollatzResearch.WordTrace tailWord_6272741 prefixEnd_6272741 1073643718054849201896565 := by
  unfold tailWord_6272741
  simp only [CollatzResearch.WordTrace]
  refine ⟨228785659767938130717450077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152523773178625420478300051 228785659767938130717450077)
  ·
    refine ⟨85794622412976799019043779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228785659767938130717450077 85794622412976799019043779)
    ·
      refine ⟨128691933619465198528565669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85794622412976799019043779 128691933619465198528565669)
      ·
        refine ⟨24129737553649724724106063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128691933619465198528565669 24129737553649724724106063)
        ·
          refine ⟨36194606330474587086159095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24129737553649724724106063 36194606330474587086159095)
          ·
            refine ⟨54291909495711880629238643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36194606330474587086159095 54291909495711880629238643)
            ·
              refine ⟨81437864243567820943857965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54291909495711880629238643 81437864243567820943857965)
              ·
                refine ⟨30539199091337932853946737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81437864243567820943857965 30539199091337932853946737)
                ·
                  refine ⟨22904399318503449640460053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30539199091337932853946737 22904399318503449640460053)
                  ·
                    refine ⟨1073643718054849201896565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22904399318503449640460053 1073643718054849201896565)
                    ·
                      rfl

theorem cell23_6272741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_6272741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272741 prefixEnd_6272741 := by exact prefixLift 6272741
  have htrace : WordTrace (prefixWord ++ tailWord_6272741) baseStart_6272741 baseEnd_6272741 := by
    simpa [prefixWord, tailWord_6272741, baseEnd_6272741] using wordTrace_append hprefix tailTrace_6272741
  have hstable : (prefixWord ++ tailWord_6272741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272741).length < 2 ^ (prefixWord ++ tailWord_6272741).sum := by decide
  have hdescent : baseEnd_6272741 < baseStart_6272741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272751 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5]
def baseStart_6272751 : Nat := 118140960795 + 6272751 * 2 ^ 59
def prefixEnd_6272751 : Nat := 4983230072969 + 3 ^ 40 * 6272751 * 2
def baseEnd_6272751 : Nat := 3220936288971092566564649

theorem tailTrace_6272751 : CollatzResearch.WordTrace tailWord_6272751 prefixEnd_6272751 3220936288971092566564649 := by
  unfold tailWord_6272751
  simp only [CollatzResearch.WordTrace]
  refine ⟨228786024497901902425314107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152524016331934601616876071 228786024497901902425314107)
  ·
    refine ⟨343179036746852853637971161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228786024497901902425314107 343179036746852853637971161)
    ·
      refine ⟨257384277560139640228478371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343179036746852853637971161 257384277560139640228478371)
      ·
        refine ⟨386076416340209460342717557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257384277560139640228478371 386076416340209460342717557)
        ·
          refine ⟨36194664031894636907129771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 386076416340209460342717557 36194664031894636907129771)
          ·
            refine ⟨54291996047841955360694657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36194664031894636907129771 54291996047841955360694657)
            ·
              refine ⟨40718997035881466520520993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54291996047841955360694657 40718997035881466520520993)
              ·
                refine ⟨30539247776911099890390745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40718997035881466520520993 30539247776911099890390745)
                ·
                  refine ⟨22904435832683324917793059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30539247776911099890390745 22904435832683324917793059)
                  ·
                    refine ⟨34356653749024987376689589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22904435832683324917793059 34356653749024987376689589)
                    ·
                      refine ⟨3220936288971092566564649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34356653749024987376689589 3220936288971092566564649)
                      ·
                        rfl

theorem cell23_6272751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_6272751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272751 prefixEnd_6272751 := by exact prefixLift 6272751
  have htrace : WordTrace (prefixWord ++ tailWord_6272751) baseStart_6272751 baseEnd_6272751 := by
    simpa [prefixWord, tailWord_6272751, baseEnd_6272751] using wordTrace_append hprefix tailTrace_6272751
  have hstable : (prefixWord ++ tailWord_6272751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272751).length < 2 ^ (prefixWord ++ tailWord_6272751).sum := by decide
  have hdescent : baseEnd_6272751 < baseStart_6272751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272818 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_6272818 : Nat := 118140960795 + 6272818 * 2 ^ 59
def prefixEnd_6272818 : Nat := 4983230072969 + 3 ^ 40 * 6272818 * 2
def baseEnd_6272818 : Nat := 1073656897391647934808947

theorem tailTrace_6272818 : CollatzResearch.WordTrace tailWord_6272818 prefixEnd_6272818 1073656897391647934808947 := by
  unfold tailWord_6272818
  simp only [CollatzResearch.WordTrace]
  refine ⟨57197117047164793217000777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152525645459106115245335405 57197117047164793217000777)
  ·
    refine ⟨42897837785373594912750583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57197117047164793217000777 42897837785373594912750583)
    ·
      refine ⟨64346756678060392369125875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42897837785373594912750583 64346756678060392369125875)
      ·
        refine ⟨96520135017090588553688813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64346756678060392369125875 96520135017090588553688813)
        ·
          refine ⟨36195050631408970707633305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96520135017090588553688813 36195050631408970707633305)
          ·
            refine ⟨27146287973556728030724979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36195050631408970707633305 27146287973556728030724979)
            ·
              refine ⟨40719431960335092046087469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27146287973556728030724979 40719431960335092046087469)
              ·
                refine ⟨15269786985125659517282801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40719431960335092046087469 15269786985125659517282801)
                ·
                  refine ⟨11452340238844244637962101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15269786985125659517282801 11452340238844244637962101)
                  ·
                    refine ⟨1073656897391647934808947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11452340238844244637962101 1073656897391647934808947)
                    ·
                      rfl

theorem cell23_6272818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_6272818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272818 prefixEnd_6272818 := by exact prefixLift 6272818
  have htrace : WordTrace (prefixWord ++ tailWord_6272818) baseStart_6272818 baseEnd_6272818 := by
    simpa [prefixWord, tailWord_6272818, baseEnd_6272818] using wordTrace_append hprefix tailTrace_6272818
  have hstable : (prefixWord ++ tailWord_6272818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272818).length < 2 ^ (prefixWord ++ tailWord_6272818).sum := by decide
  have hdescent : baseEnd_6272818 < baseStart_6272818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272841 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 5]
def baseStart_6272841 : Nat := 118140960795 + 6272841 * 2 ^ 59
def prefixEnd_6272841 : Nat := 4983230072969 + 3 ^ 40 * 6272841 * 2
def baseEnd_6272841 : Nat := 3220982502229997214439235

theorem tailTrace_6272841 : CollatzResearch.WordTrace tailWord_6272841 prefixEnd_6272841 3220982502229997214439235 := by
  unfold tailWord_6272841
  simp only [CollatzResearch.WordTrace]
  refine ⟨228789307067575847796090377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152526204711717231864060251 228789307067575847796090377)
  ·
    refine ⟨171591980300681885847067783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228789307067575847796090377 171591980300681885847067783)
    ·
      refine ⟨257387970451022828770601675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171591980300681885847067783 257387970451022828770601675)
      ·
        refine ⟨386081955676534243155902513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257387970451022828770601675 386081955676534243155902513)
        ·
          refine ⟨289561466757400682366926885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386081955676534243155902513 289561466757400682366926885)
          ·
            refine ⟨54292775017012627943798791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 289561466757400682366926885 54292775017012627943798791)
            ·
              refine ⟨81439162525518941915698187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54292775017012627943798791 81439162525518941915698187)
              ·
                refine ⟨122158743788278412873547281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81439162525518941915698187 122158743788278412873547281)
                ·
                  refine ⟨91619057841208809655160461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122158743788278412873547281 91619057841208809655160461)
                  ·
                    refine ⟨34357146690453303620685173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91619057841208809655160461 34357146690453303620685173)
                    ·
                      refine ⟨3220982502229997214439235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34357146690453303620685173 3220982502229997214439235)
                      ·
                        rfl

theorem cell23_6272841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_6272841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272841 prefixEnd_6272841 := by exact prefixLift 6272841
  have htrace : WordTrace (prefixWord ++ tailWord_6272841) baseStart_6272841 baseEnd_6272841 := by
    simpa [prefixWord, tailWord_6272841, baseEnd_6272841] using wordTrace_append hprefix tailTrace_6272841
  have hstable : (prefixWord ++ tailWord_6272841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272841).length < 2 ^ (prefixWord ++ tailWord_6272841).sum := by decide
  have hdescent : baseEnd_6272841 < baseStart_6272841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272845 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6272845 : Nat := 118140960795 + 6272845 * 2 ^ 59
def prefixEnd_6272845 : Nat := 4983230072969 + 3 ^ 40 * 6272845 * 2
def baseEnd_6272845 : Nat := 3220984556152615198789217

theorem tailTrace_6272845 : CollatzResearch.WordTrace tailWord_6272845 prefixEnd_6272845 3220984556152615198789217 := by
  unfold tailWord_6272845
  simp only [CollatzResearch.WordTrace]
  refine ⟨228789452959561356479235989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152526301973040904319490659 228789452959561356479235989)
  ·
    refine ⟨10724505607479438584964187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 228789452959561356479235989 10724505607479438584964187)
    ·
      refine ⟨16086758411219157877446281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724505607479438584964187 16086758411219157877446281)
      ·
        refine ⟨12065068808414368408084711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16086758411219157877446281 12065068808414368408084711)
        ·
          refine ⟨18097603212621552612127067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12065068808414368408084711 18097603212621552612127067)
          ·
            refine ⟨27146404818932328918190601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18097603212621552612127067 27146404818932328918190601)
            ·
              refine ⟨20359803614199246688642951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27146404818932328918190601 20359803614199246688642951)
              ·
                refine ⟨30539705421298870032964427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20359803614199246688642951 30539705421298870032964427)
                ·
                  refine ⟨45809558131948305049446641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30539705421298870032964427 45809558131948305049446641)
                  ·
                    refine ⟨34357168598961228787084981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45809558131948305049446641 34357168598961228787084981)
                    ·
                      refine ⟨3220984556152615198789217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34357168598961228787084981 3220984556152615198789217)
                      ·
                        rfl

theorem cell23_6272845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6272845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272845 prefixEnd_6272845 := by exact prefixLift 6272845
  have htrace : WordTrace (prefixWord ++ tailWord_6272845) baseStart_6272845 baseEnd_6272845 := by
    simpa [prefixWord, tailWord_6272845, baseEnd_6272845] using wordTrace_append hprefix tailTrace_6272845
  have hstable : (prefixWord ++ tailWord_6272845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272845).length < 2 ^ (prefixWord ++ tailWord_6272845).sum := by decide
  have hdescent : baseEnd_6272845 < baseStart_6272845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272848 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_6272848 : Nat := 118140960795 + 6272848 * 2 ^ 59
def prefixEnd_6272848 : Nat := 4983230072969 + 3 ^ 40 * 6272848 * 2
def baseEnd_6272848 : Nat := 1073662032198192895683901

theorem tailTrace_6272848 : CollatzResearch.WordTrace tailWord_6272848 prefixEnd_6272848 1073662032198192895683901 := by
  unfold tailWord_6272848
  simp only [CollatzResearch.WordTrace]
  refine ⟨114394781189275243995797599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152526374919033658661063465 114394781189275243995797599)
  ·
    refine ⟨171592171783912865993696399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114394781189275243995797599 171592171783912865993696399)
    ·
      refine ⟨257388257675869298990544599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171592171783912865993696399 257388257675869298990544599)
      ·
        refine ⟨386082386513803948485816899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257388257675869298990544599 386082386513803948485816899)
        ·
          refine ⟨579123579770705922728725349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386082386513803948485816899 579123579770705922728725349)
          ·
            refine ⟨108585671207007360511636003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 579123579770705922728725349 108585671207007360511636003)
            ·
              refine ⟨162878506810511040767454005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108585671207007360511636003 162878506810511040767454005)
              ·
                refine ⟨15269860013485410071948813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162878506810511040767454005 15269860013485410071948813)
                ·
                  refine ⟨5726197505057028776980805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15269860013485410071948813 5726197505057028776980805)
                  ·
                    refine ⟨1073662032198192895683901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726197505057028776980805 1073662032198192895683901)
                    ·
                      rfl

theorem cell23_6272848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_6272848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272848 prefixEnd_6272848 := by exact prefixLift 6272848
  have htrace : WordTrace (prefixWord ++ tailWord_6272848) baseStart_6272848 baseEnd_6272848 := by
    simpa [prefixWord, tailWord_6272848, baseEnd_6272848] using wordTrace_append hprefix tailTrace_6272848
  have hstable : (prefixWord ++ tailWord_6272848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272848).length < 2 ^ (prefixWord ++ tailWord_6272848).sum := by decide
  have hdescent : baseEnd_6272848 < baseStart_6272848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272851 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4]
def baseStart_6272851 : Nat := 118140960795 + 6272851 * 2 ^ 59
def prefixEnd_6272851 : Nat := 4983230072969 + 3 ^ 40 * 6272851 * 2
def baseEnd_6272851 : Nat := 3220987637036542175314189

theorem tailTrace_6272851 : CollatzResearch.WordTrace tailWord_6272851 prefixEnd_6272851 3220987637036542175314189 := by
  unfold tailWord_6272851
  simp only [CollatzResearch.WordTrace]
  refine ⟨228789671797539619503954407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152526447865026413002636271 228789671797539619503954407)
  ·
    refine ⟨343184507696309429255931611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228789671797539619503954407 343184507696309429255931611)
    ·
      refine ⟨514776761544464143883897417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343184507696309429255931611 514776761544464143883897417)
      ·
        refine ⟨386082571158348107912923063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 514776761544464143883897417 386082571158348107912923063)
        ·
          refine ⟨579123856737522161869384595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386082571158348107912923063 579123856737522161869384595)
          ·
            refine ⟨868685785106283242804076893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579123856737522161869384595 868685785106283242804076893)
            ·
              refine ⟨325757169414856216051528835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868685785106283242804076893 325757169414856216051528835)
              ·
                refine ⟨488635754122284324077293253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325757169414856216051528835 488635754122284324077293253)
                ·
                  refine ⟨91619203897928310764492485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 488635754122284324077293253 91619203897928310764492485)
                  ·
                    refine ⟨17178600730861558268342341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91619203897928310764492485 17178600730861558268342341)
                    ·
                      refine ⟨3220987637036542175314189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17178600730861558268342341 3220987637036542175314189)
                      ·
                        rfl

theorem cell23_6272851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_6272851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272851 prefixEnd_6272851 := by exact prefixLift 6272851
  have htrace : WordTrace (prefixWord ++ tailWord_6272851) baseStart_6272851 baseEnd_6272851 := by
    simpa [prefixWord, tailWord_6272851, baseEnd_6272851] using wordTrace_append hprefix tailTrace_6272851
  have hstable : (prefixWord ++ tailWord_6272851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272851).length < 2 ^ (prefixWord ++ tailWord_6272851).sum := by decide
  have hdescent : baseEnd_6272851 < baseStart_6272851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272858 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_6272858 : Nat := 118140960795 + 6272858 * 2 ^ 59
def prefixEnd_6272858 : Nat := 4983230072969 + 3 ^ 40 * 6272858 * 2
def baseEnd_6272858 : Nat := 3220991231401123647926657

theorem tailTrace_6272858 : CollatzResearch.WordTrace tailWord_6272858 prefixEnd_6272858 3220991231401123647926657 := by
  unfold tailWord_6272858
  simp only [CollatzResearch.WordTrace]
  refine ⟨57197481777128564924864807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152526618072342839799639485 57197481777128564924864807)
  ·
    refine ⟨85796222665692847387297211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57197481777128564924864807 85796222665692847387297211)
    ·
      refine ⟨128694333998539271080945817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85796222665692847387297211 128694333998539271080945817)
      ·
        refine ⟨96520750498904453310709363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128694333998539271080945817 96520750498904453310709363)
        ·
          refine ⟨144781125748356679966064045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96520750498904453310709363 144781125748356679966064045)
          ·
            refine ⟨54292922155633754987274017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144781125748356679966064045 54292922155633754987274017)
            ·
              refine ⟨40719691616725316240455513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54292922155633754987274017 40719691616725316240455513)
              ·
                refine ⟨30539768712543987180341635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40719691616725316240455513 30539768712543987180341635)
                ·
                  refine ⟨45809653068815980770512453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30539768712543987180341635 45809653068815980770512453)
                  ·
                    refine ⟨8589309950402996394471085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45809653068815980770512453 8589309950402996394471085)
                    ·
                      refine ⟨3220991231401123647926657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589309950402996394471085 3220991231401123647926657)
                      ·
                        rfl

theorem cell23_6272858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_6272858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272858 prefixEnd_6272858 := by exact prefixLift 6272858
  have htrace : WordTrace (prefixWord ++ tailWord_6272858) baseStart_6272858 baseEnd_6272858 := by
    simpa [prefixWord, tailWord_6272858, baseEnd_6272858] using wordTrace_append hprefix tailTrace_6272858
  have hstable : (prefixWord ++ tailWord_6272858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272858).length < 2 ^ (prefixWord ++ tailWord_6272858).sum := by decide
  have hdescent : baseEnd_6272858 < baseStart_6272858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272922 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_6272922 : Nat := 118140960795 + 6272922 * 2 ^ 59
def prefixEnd_6272922 : Nat := 4983230072969 + 3 ^ 40 * 6272922 * 2
def baseEnd_6272922 : Nat := 3221024094163011397526363

theorem tailTrace_6272922 : CollatzResearch.WordTrace tailWord_6272922 prefixEnd_6272922 3221024094163011397526363 := by
  unfold tailWord_6272922
  simp only [CollatzResearch.WordTrace]
  refine ⟨57198065345070599657447255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152528174253521599086526013 57198065345070599657447255)
  ·
    refine ⟨85797098017605899486170883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57198065345070599657447255 85797098017605899486170883)
    ·
      refine ⟨128695647026408849229256325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85797098017605899486170883 128695647026408849229256325)
      ·
        refine ⟨24130433817451659230485561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128695647026408849229256325 24130433817451659230485561)
        ·
          refine ⟨18097825363088744422864171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24130433817451659230485561 18097825363088744422864171)
          ·
            refine ⟨27146738044633116634296257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18097825363088744422864171 27146738044633116634296257)
            ·
              refine ⟨20360053533474837475722193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27146738044633116634296257 20360053533474837475722193)
              ·
                refine ⟨15270040150106128106791645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20360053533474837475722193 15270040150106128106791645)
                ·
                  refine ⟨5726265056289798040046867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15270040150106128106791645 5726265056289798040046867)
                  ·
                    refine ⟨8589397584434697060070301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726265056289798040046867 8589397584434697060070301)
                    ·
                      refine ⟨3221024094163011397526363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589397584434697060070301 3221024094163011397526363)
                      ·
                        rfl

theorem cell23_6272922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_6272922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272922 prefixEnd_6272922 := by exact prefixLift 6272922
  have htrace : WordTrace (prefixWord ++ tailWord_6272922) baseStart_6272922 baseEnd_6272922 := by
    simpa [prefixWord, tailWord_6272922, baseEnd_6272922] using wordTrace_append hprefix tailTrace_6272922
  have hstable : (prefixWord ++ tailWord_6272922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272922).length < 2 ^ (prefixWord ++ tailWord_6272922).sum := by decide
  have hdescent : baseEnd_6272922 < baseStart_6272922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272925 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6272925 : Nat := 118140960795 + 6272925 * 2 ^ 59
def prefixEnd_6272925 : Nat := 4983230072969 + 3 ^ 40 * 6272925 * 2
def baseEnd_6272925 : Nat := 1073675211534991628596283

theorem tailTrace_6272925 : CollatzResearch.WordTrace tailWord_6272925 prefixEnd_6272925 1073675211534991628596283 := by
  unfold tailWord_6272925
  simp only [CollatzResearch.WordTrace]
  refine ⟨228792370799271530142148229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152528247199514353428098819 228792370799271530142148229)
  ·
    refine ⟨42898569524863411901652793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228792370799271530142148229 42898569524863411901652793)
    ·
      refine ⟨32173927143647558926239595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42898569524863411901652793 32173927143647558926239595)
      ·
        refine ⟨48260890715471338389359393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32173927143647558926239595 48260890715471338389359393)
        ·
          refine ⟨36195668036603503792019545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48260890715471338389359393 36195668036603503792019545)
          ·
            refine ⟨27146751027452627844014659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36195668036603503792019545 27146751027452627844014659)
            ·
              refine ⟨40720126541178941766021989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27146751027452627844014659 40720126541178941766021989)
              ·
                refine ⟨7635023726471051581129123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40720126541178941766021989 7635023726471051581129123)
                ·
                  refine ⟨11452535589706577371693685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635023726471051581129123 11452535589706577371693685)
                  ·
                    refine ⟨1073675211534991628596283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11452535589706577371693685 1073675211534991628596283)
                    ·
                      rfl

theorem cell23_6272925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6272925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272925 prefixEnd_6272925 := by exact prefixLift 6272925
  have htrace : WordTrace (prefixWord ++ tailWord_6272925) baseStart_6272925 baseEnd_6272925 := by
    simpa [prefixWord, tailWord_6272925, baseEnd_6272925] using wordTrace_append hprefix tailTrace_6272925
  have hstable : (prefixWord ++ tailWord_6272925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272925).length < 2 ^ (prefixWord ++ tailWord_6272925).sum := by decide
  have hdescent : baseEnd_6272925 < baseStart_6272925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272956 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6272956 : Nat := 118140960795 + 6272956 * 2 ^ 59
def prefixEnd_6272956 : Nat := 4983230072969 + 3 ^ 40 * 6272956 * 2
def baseEnd_6272956 : Nat := 3221041552505264264501207

theorem tailTrace_6272956 : CollatzResearch.WordTrace tailWord_6272956 prefixEnd_6272956 3221041552505264264501207 := by
  unfold tailWord_6272956
  simp only [CollatzResearch.WordTrace]
  refine ⟨114396750731079611218263361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152529000974772814957684481 114396750731079611218263361)
  ·
    refine ⟨85797563048309708413697521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114396750731079611218263361 85797563048309708413697521)
    ·
      refine ⟨64348172286232281310273141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85797563048309708413697521 64348172286232281310273141)
      ·
        refine ⟨6032641151834276372838107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64348172286232281310273141 6032641151834276372838107)
        ·
          refine ⟨9048961727751414559257161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032641151834276372838107 9048961727751414559257161)
          ·
            refine ⟨6786721295813560919442871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9048961727751414559257161 6786721295813560919442871)
            ·
              refine ⟨10180081943720341379164307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786721295813560919442871 10180081943720341379164307)
              ·
                refine ⟨15270122915580512068746461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10180081943720341379164307 15270122915580512068746461)
                ·
                  refine ⟨5726296093342692025779923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15270122915580512068746461 5726296093342692025779923)
                  ·
                    refine ⟨8589444140014038038669885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726296093342692025779923 8589444140014038038669885)
                    ·
                      refine ⟨3221041552505264264501207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589444140014038038669885 3221041552505264264501207)
                      ·
                        rfl

theorem cell23_6272956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6272956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272956 prefixEnd_6272956 := by exact prefixLift 6272956
  have htrace : WordTrace (prefixWord ++ tailWord_6272956) baseStart_6272956 baseEnd_6272956 := by
    simpa [prefixWord, tailWord_6272956, baseEnd_6272956] using wordTrace_append hprefix tailTrace_6272956
  have hstable : (prefixWord ++ tailWord_6272956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272956).length < 2 ^ (prefixWord ++ tailWord_6272956).sum := by decide
  have hdescent : baseEnd_6272956 < baseStart_6272956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272968 : List Nat := [2, 1, 3, 1, 4, 1, 1, 10]
def baseStart_6272968 : Nat := 118140960795 + 6272968 * 2 ^ 59
def prefixEnd_6272968 : Nat := 4983230072969 + 3 ^ 40 * 6272968 * 2
def baseEnd_6272968 : Nat := 119298063491596971020413

theorem tailTrace_6272968 : CollatzResearch.WordTrace tailWord_6272968 prefixEnd_6272968 119298063491596971020413 := by
  unfold tailWord_6272968
  simp only [CollatzResearch.WordTrace]
  refine ⟨114396969569057874242981779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152529292758743832323975705 114396969569057874242981779)
  ·
    refine ⟨171595454353586811364472669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114396969569057874242981779 171595454353586811364472669)
    ·
      refine ⟨64348295382595054261677251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171595454353586811364472669 64348295382595054261677251)
      ·
        refine ⟨96522443073892581392515877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64348295382595054261677251 96522443073892581392515877)
        ·
          refine ⟨18097958076354859011096727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96522443073892581392515877 18097958076354859011096727)
          ·
            refine ⟨27146937114532288516645091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18097958076354859011096727 27146937114532288516645091)
            ·
              refine ⟨40720405671798432774967637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27146937114532288516645091 40720405671798432774967637)
              ·
                refine ⟨119298063491596971020413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40720405671798432774967637 119298063491596971020413)
                ·
                  rfl

theorem cell23_6272968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 10].length) (baseStart_6272968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272968 prefixEnd_6272968 := by exact prefixLift 6272968
  have htrace : WordTrace (prefixWord ++ tailWord_6272968) baseStart_6272968 baseEnd_6272968 := by
    simpa [prefixWord, tailWord_6272968, baseEnd_6272968] using wordTrace_append hprefix tailTrace_6272968
  have hstable : (prefixWord ++ tailWord_6272968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272968).length < 2 ^ (prefixWord ++ tailWord_6272968).sum := by decide
  have hdescent : baseEnd_6272968 < baseStart_6272968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272972 : List Nat := [2, 2, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_6272972 : Nat := 118140960795 + 6272972 * 2 ^ 59
def prefixEnd_6272972 : Nat := 4983230072969 + 3 ^ 40 * 6272972 * 2
def baseEnd_6272972 : Nat := 1073683256065245400633711

theorem tailTrace_6272972 : CollatzResearch.WordTrace tailWord_6272972 prefixEnd_6272972 1073683256065245400633711 := by
  unfold tailWord_6272972
  simp only [CollatzResearch.WordTrace]
  refine ⟨114397042515050628584554585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152529390020067504779406113 114397042515050628584554585)
  ·
    refine ⟨85797781886287971438415939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114397042515050628584554585 85797781886287971438415939)
    ·
      refine ⟨128696672829431957157623909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85797781886287971438415939 128696672829431957157623909)
      ·
        refine ⟨24130626155518491967054483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128696672829431957157623909 24130626155518491967054483)
        ·
          refine ⟨36195939233277737950581725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24130626155518491967054483 36195939233277737950581725)
          ·
            refine ⟨13573477212479151731468147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36195939233277737950581725 13573477212479151731468147)
            ·
              refine ⟨20360215818718727597202221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13573477212479151731468147 20360215818718727597202221)
              ·
                refine ⟨7635080932019522848950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20360215818718727597202221 7635080932019522848950833)
                ·
                  refine ⟨5726310699014642136713125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635080932019522848950833 5726310699014642136713125)
                  ·
                    refine ⟨1073683256065245400633711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726310699014642136713125 1073683256065245400633711)
                    ·
                      rfl

theorem cell23_6272972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_6272972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272972 prefixEnd_6272972 := by exact prefixLift 6272972
  have htrace : WordTrace (prefixWord ++ tailWord_6272972) baseStart_6272972 baseEnd_6272972 := by
    simpa [prefixWord, tailWord_6272972, baseEnd_6272972] using wordTrace_append hprefix tailTrace_6272972
  have hstable : (prefixWord ++ tailWord_6272972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272972).length < 2 ^ (prefixWord ++ tailWord_6272972).sum := by decide
  have hdescent : baseEnd_6272972 < baseStart_6272972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272995 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3]
def baseStart_6272995 : Nat := 118140960795 + 6272995 * 2 ^ 59
def prefixEnd_6272995 : Nat := 4983230072969 + 3 ^ 40 * 6272995 * 2
def baseEnd_6272995 : Nat := 3221061578250789611913527

theorem tailTrace_6272995 : CollatzResearch.WordTrace tailWord_6272995 prefixEnd_6272995 3221061578250789611913527 := by
  unfold tailWord_6272995
  simp only [CollatzResearch.WordTrace]
  refine ⟨228794923909017932097196439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152529949272678621398130959 228794923909017932097196439)
  ·
    refine ⟨343192385863526898145794659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228794923909017932097196439 343192385863526898145794659)
    ·
      refine ⟨514788578795290347218691989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343192385863526898145794659 514788578795290347218691989)
      ·
        refine ⟨24130714631029235025876187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 514788578795290347218691989 24130714631029235025876187)
        ·
          refine ⟨36196071946543852538814281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24130714631029235025876187 36196071946543852538814281)
          ·
            refine ⟨27147053959907889404110711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36196071946543852538814281 27147053959907889404110711)
            ·
              refine ⟨40720580939861834106166067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27147053959907889404110711 40720580939861834106166067)
              ·
                refine ⟨61080871409792751159249101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40720580939861834106166067 61080871409792751159249101)
                ·
                  refine ⟨22905326778672281684718413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61080871409792751159249101 22905326778672281684718413)
                  ·
                    refine ⟨8589497542002105631769405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22905326778672281684718413 8589497542002105631769405)
                    ·
                      refine ⟨3221061578250789611913527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589497542002105631769405 3221061578250789611913527)
                      ·
                        rfl

theorem cell23_6272995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_6272995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272995 prefixEnd_6272995 := by exact prefixLift 6272995
  have htrace : WordTrace (prefixWord ++ tailWord_6272995) baseStart_6272995 baseEnd_6272995 := by
    simpa [prefixWord, tailWord_6272995, baseEnd_6272995] using wordTrace_append hprefix tailTrace_6272995
  have hstable : (prefixWord ++ tailWord_6272995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272995).length < 2 ^ (prefixWord ++ tailWord_6272995).sum := by decide
  have hdescent : baseEnd_6272995 < baseStart_6272995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6272999 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6272999 : Nat := 118140960795 + 6272999 * 2 ^ 59
def prefixEnd_6272999 : Nat := 4983230072969 + 3 ^ 40 * 6272999 * 2
def baseEnd_6272999 : Nat := 3221063632173407596263509

theorem tailTrace_6272999 : CollatzResearch.WordTrace tailWord_6272999 prefixEnd_6272999 3221063632173407596263509 := by
  unfold tailWord_6272999
  simp only [CollatzResearch.WordTrace]
  refine ⟨228795069801003440780342051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152530046534002293853561367 228795069801003440780342051)
  ·
    refine ⟨343192604701505161170513077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228795069801003440780342051 343192604701505161170513077)
    ·
      refine ⟨32174306690766108859735601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 343192604701505161170513077 32174306690766108859735601)
      ·
        refine ⟨24130730018074581644801701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32174306690766108859735601 24130730018074581644801701)
        ·
          refine ⟨4524511878388984058400319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24130730018074581644801701 4524511878388984058400319)
          ·
            refine ⟨6786767817583476087600479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524511878388984058400319 6786767817583476087600479)
            ·
              refine ⟨10180151726375214131400719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786767817583476087600479 10180151726375214131400719)
              ·
                refine ⟨15270227589562821197101079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10180151726375214131400719 15270227589562821197101079)
                ·
                  refine ⟨22905341384344231795651619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15270227589562821197101079 22905341384344231795651619)
                  ·
                    refine ⟨34358012076516347693477429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22905341384344231795651619 34358012076516347693477429)
                    ·
                      refine ⟨3221063632173407596263509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34358012076516347693477429 3221063632173407596263509)
                      ·
                        rfl

theorem cell23_6272999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6272999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6272999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6272999 prefixEnd_6272999 := by exact prefixLift 6272999
  have htrace : WordTrace (prefixWord ++ tailWord_6272999) baseStart_6272999 baseEnd_6272999 := by
    simpa [prefixWord, tailWord_6272999, baseEnd_6272999] using wordTrace_append hprefix tailTrace_6272999
  have hstable : (prefixWord ++ tailWord_6272999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6272999).length < 2 ^ (prefixWord ++ tailWord_6272999).sum := by decide
  have hdescent : baseEnd_6272999 < baseStart_6272999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6272999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273008 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_6273008 : Nat := 118140960795 + 6273008 * 2 ^ 59
def prefixEnd_6273008 : Nat := 4983230072969 + 3 ^ 40 * 6273008 * 2
def baseEnd_6273008 : Nat := 3221068253499298061050967

theorem tailTrace_6273008 : CollatzResearch.WordTrace tailWord_6273008 prefixEnd_6273008 3221068253499298061050967 := by
  unfold tailWord_6273008
  simp only [CollatzResearch.WordTrace]
  refine ⟨114397699028985417658709839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152530265371980556878279785 114397699028985417658709839)
  ·
    refine ⟨171596548543478126488064759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114397699028985417658709839 171596548543478126488064759)
    ·
      refine ⟨257394822815217189732097139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171596548543478126488064759 257394822815217189732097139)
      ·
        refine ⟨386092234222825784598145709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257394822815217189732097139 386092234222825784598145709)
        ·
          refine ⟨144784587833559669224304641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386092234222825784598145709 144784587833559669224304641)
          ·
            refine ⟨108588440875169751918228481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144784587833559669224304641 108588440875169751918228481)
            ·
              refine ⟨81441330656377313938671361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108588440875169751918228481 81441330656377313938671361)
              ·
                refine ⟨61080997992282985454003521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81441330656377313938671361 61080997992282985454003521)
                ·
                  refine ⟨45810748494212239090502641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61080997992282985454003521 45810748494212239090502641)
                  ·
                    refine ⟨34358061370659179317876981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45810748494212239090502641 34358061370659179317876981)
                    ·
                      refine ⟨3221068253499298061050967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34358061370659179317876981 3221068253499298061050967)
                      ·
                        rfl

theorem cell23_6273008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_6273008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273008 prefixEnd_6273008 := by exact prefixLift 6273008
  have htrace : WordTrace (prefixWord ++ tailWord_6273008) baseStart_6273008 baseEnd_6273008 := by
    simpa [prefixWord, tailWord_6273008, baseEnd_6273008] using wordTrace_append hprefix tailTrace_6273008
  have hstable : (prefixWord ++ tailWord_6273008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273008).length < 2 ^ (prefixWord ++ tailWord_6273008).sum := by decide
  have hdescent : baseEnd_6273008 < baseStart_6273008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273063 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6273063 : Nat := 118140960795 + 6273063 * 2 ^ 59
def prefixEnd_6273063 : Nat := 4983230072969 + 3 ^ 40 * 6273063 * 2
def baseEnd_6273063 : Nat := 3221096494935295345863215

theorem tailTrace_6273063 : CollatzResearch.WordTrace tailWord_6273063 prefixEnd_6273063 3221096494935295345863215 := by
  unfold tailWord_6273063
  simp only [CollatzResearch.WordTrace]
  refine ⟨228797404072771579710671843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152531602715181053140447895 228797404072771579710671843)
  ·
    refine ⟨343196106109157369566007765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228797404072771579710671843 343196106109157369566007765)
    ·
      refine ⟨8043658736933375849203307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 343196106109157369566007765 8043658736933375849203307)
      ·
        refine ⟨12065488105400063773804961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043658736933375849203307 12065488105400063773804961)
        ·
          refine ⟨9049116079050047830353721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12065488105400063773804961 9049116079050047830353721)
          ·
            refine ⟨6786837059287535872765291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9049116079050047830353721 6786837059287535872765291)
            ·
              refine ⟨10180255588931303809147937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786837059287535872765291 10180255588931303809147937)
              ·
                refine ⟨7635191691698477856860953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10180255588931303809147937 7635191691698477856860953)
                ·
                  refine ⟨5726393768773858392645715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635191691698477856860953 5726393768773858392645715)
                  ·
                    refine ⟨8589590653160787588968573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726393768773858392645715 8589590653160787588968573)
                    ·
                      refine ⟨3221096494935295345863215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589590653160787588968573 3221096494935295345863215)
                      ·
                        rfl

theorem cell23_6273063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6273063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273063 prefixEnd_6273063 := by exact prefixLift 6273063
  have htrace : WordTrace (prefixWord ++ tailWord_6273063) baseStart_6273063 baseEnd_6273063 := by
    simpa [prefixWord, tailWord_6273063, baseEnd_6273063] using wordTrace_append hprefix tailTrace_6273063
  have hstable : (prefixWord ++ tailWord_6273063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273063).length < 2 ^ (prefixWord ++ tailWord_6273063).sum := by decide
  have hdescent : baseEnd_6273063 < baseStart_6273063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273068 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_6273068 : Nat := 118140960795 + 6273068 * 2 ^ 59
def prefixEnd_6273068 : Nat := 4983230072969 + 3 ^ 40 * 6273068 * 2
def baseEnd_6273068 : Nat := 3221099062338567826300691

theorem tailTrace_6273068 : CollatzResearch.WordTrace tailWord_6273068 prefixEnd_6273068 3221099062338567826300691 := by
  unfold tailWord_6273068
  simp only [CollatzResearch.WordTrace]
  refine ⟨114398793218876732782301929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152531724291835643709735905 114398793218876732782301929)
  ·
    refine ⟨85799094914157549586726447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114398793218876732782301929 85799094914157549586726447)
    ·
      refine ⟨128698642371236324380089671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85799094914157549586726447 128698642371236324380089671)
      ·
        refine ⟨193047963556854486570134507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128698642371236324380089671 193047963556854486570134507)
        ·
          refine ⟨289571945335281729855201761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193047963556854486570134507 289571945335281729855201761)
          ·
            refine ⟨217178959001461297391401321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289571945335281729855201761 217178959001461297391401321)
            ·
              refine ⟨162884219251095973043550991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217178959001461297391401321 162884219251095973043550991)
              ·
                refine ⟨244326328876643959565326487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162884219251095973043550991 244326328876643959565326487)
                ·
                  refine ⟨366489493314965939347989731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244326328876643959565326487 366489493314965939347989731)
                  ·
                    refine ⟨549734239972448909021984597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 366489493314965939347989731 549734239972448909021984597)
                    ·
                      refine ⟨3221099062338567826300691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 549734239972448909021984597 3221099062338567826300691)
                      ·
                        rfl

theorem cell23_6273068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_6273068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273068 prefixEnd_6273068 := by exact prefixLift 6273068
  have htrace : WordTrace (prefixWord ++ tailWord_6273068) baseStart_6273068 baseEnd_6273068 := by
    simpa [prefixWord, tailWord_6273068, baseEnd_6273068] using wordTrace_append hprefix tailTrace_6273068
  have hstable : (prefixWord ++ tailWord_6273068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273068).length < 2 ^ (prefixWord ++ tailWord_6273068).sum := by decide
  have hdescent : baseEnd_6273068 < baseStart_6273068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273105 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 2, 5]
def baseStart_6273105 : Nat := 118140960795 + 6273105 * 2 ^ 59
def prefixEnd_6273105 : Nat := 4983230072969 + 3 ^ 40 * 6273105 * 2
def baseEnd_6273105 : Nat := 1073706020374261393846007

theorem tailTrace_6273105 : CollatzResearch.WordTrace tailWord_6273105 prefixEnd_6273105 1073706020374261393846007 := by
  unfold tailWord_6273105
  simp only [CollatzResearch.WordTrace]
  refine ⟨228798935938619420883700769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152532623959079613922467179 228798935938619420883700769)
  ·
    refine ⟨171599201953964565662775577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228798935938619420883700769 171599201953964565662775577)
    ·
      refine ⟨128699401465473424247081683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171599201953964565662775577 128699401465473424247081683)
      ·
        refine ⟨193049102198210136370622525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128699401465473424247081683 193049102198210136370622525)
        ·
          refine ⟨72393413324328801138983447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193049102198210136370622525 72393413324328801138983447)
          ·
            refine ⟨108590119986493201708475171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72393413324328801138983447 108590119986493201708475171)
            ·
              refine ⟨162885179979739802562712757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108590119986493201708475171 162885179979739802562712757)
              ·
                refine ⟨15270485623100606490254321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162885179979739802562712757 15270485623100606490254321)
                ·
                  refine ⟨11452864217325454867690741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15270485623100606490254321 11452864217325454867690741)
                  ·
                    refine ⟨1073706020374261393846007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11452864217325454867690741 1073706020374261393846007)
                    ·
                      rfl

theorem cell23_6273105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_6273105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273105 prefixEnd_6273105 := by exact prefixLift 6273105
  have htrace : WordTrace (prefixWord ++ tailWord_6273105) baseStart_6273105 baseEnd_6273105 := by
    simpa [prefixWord, tailWord_6273105, baseEnd_6273105] using wordTrace_append hprefix tailTrace_6273105
  have hstable : (prefixWord ++ tailWord_6273105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273105).length < 2 ^ (prefixWord ++ tailWord_6273105).sum := by decide
  have hdescent : baseEnd_6273105 < baseStart_6273105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273109 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 5]
def baseStart_6273109 : Nat := 118140960795 + 6273109 * 2 ^ 59
def prefixEnd_6273109 : Nat := 4983230072969 + 3 ^ 40 * 6273109 * 2
def baseEnd_6273109 : Nat := 357902235005044685098667

theorem tailTrace_6273109 : CollatzResearch.WordTrace tailWord_6273109 prefixEnd_6273109 357902235005044685098667 := by
  unfold tailWord_6273109
  simp only [CollatzResearch.WordTrace]
  refine ⟨228799081830604929566846381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152532721220403286377897587 228799081830604929566846381)
  ·
    refine ⟨85799655686476848587567393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228799081830604929566846381 85799655686476848587567393)
    ·
      refine ⟨64349741764857636440675545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85799655686476848587567393 64349741764857636440675545)
      ·
        refine ⟨48262306323643227330506659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64349741764857636440675545 48262306323643227330506659)
        ·
          refine ⟨72393459485464840995759989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48262306323643227330506659 72393459485464840995759989)
          ·
            refine ⟨6786886826762328843352499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72393459485464840995759989 6786886826762328843352499)
            ·
              refine ⟨10180330240143493265028749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786886826762328843352499 10180330240143493265028749)
              ·
                refine ⟨3817623840053809974385781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10180330240143493265028749 3817623840053809974385781)
                ·
                  refine ⟨357902235005044685098667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3817623840053809974385781 357902235005044685098667)
                  ·
                    rfl

theorem cell23_6273109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_6273109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273109 prefixEnd_6273109 := by exact prefixLift 6273109
  have htrace : WordTrace (prefixWord ++ tailWord_6273109) baseStart_6273109 baseEnd_6273109 := by
    simpa [prefixWord, tailWord_6273109, baseEnd_6273109] using wordTrace_append hprefix tailTrace_6273109
  have hstable : (prefixWord ++ tailWord_6273109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273109).length < 2 ^ (prefixWord ++ tailWord_6273109).sum := by decide
  have hdescent : baseEnd_6273109 < baseStart_6273109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273209 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 3]
def baseStart_6273209 : Nat := 118140960795 + 6273209 * 2 ^ 59
def prefixEnd_6273209 : Nat := 4983230072969 + 3 ^ 40 * 6273209 * 2
def baseEnd_6273209 : Nat := 3221171463110851774637543

theorem tailTrace_6273209 : CollatzResearch.WordTrace tailWord_6273209 prefixEnd_6273209 3221171463110851774637543 := by
  unfold tailWord_6273209
  simp only [CollatzResearch.WordTrace]
  refine ⟨228802729130242646645486681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152535152753495097763657787 228802729130242646645486681)
  ·
    refine ⟨171602046847681984984115011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228802729130242646645486681 171602046847681984984115011)
    ·
      refine ⟨257403070271522977476172517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171602046847681984984115011 257403070271522977476172517)
      ·
        refine ⟨48263075675910558276782347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 257403070271522977476172517 48263075675910558276782347)
        ·
          refine ⟨72394613513865837415173521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48263075675910558276782347 72394613513865837415173521)
          ·
            refine ⟨54295960135399378061380141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72394613513865837415173521 54295960135399378061380141)
            ·
              refine ⟨20360985050774766773017553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54295960135399378061380141 20360985050774766773017553)
              ·
                refine ⟨15270738788081075079763165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20360985050774766773017553 15270738788081075079763165)
                ·
                  refine ⟨5726527045530403154911187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15270738788081075079763165 5726527045530403154911187)
                  ·
                    refine ⟨8589790568295604732366781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726527045530403154911187 8589790568295604732366781)
                    ·
                      refine ⟨3221171463110851774637543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589790568295604732366781 3221171463110851774637543)
                      ·
                        rfl

theorem cell23_6273209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_6273209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273209 prefixEnd_6273209 := by exact prefixLift 6273209
  have htrace : WordTrace (prefixWord ++ tailWord_6273209) baseStart_6273209 baseEnd_6273209 := by
    simpa [prefixWord, tailWord_6273209, baseEnd_6273209] using wordTrace_append hprefix tailTrace_6273209
  have hstable : (prefixWord ++ tailWord_6273209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273209).length < 2 ^ (prefixWord ++ tailWord_6273209).sum := by decide
  have hdescent : baseEnd_6273209 < baseStart_6273209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273225 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 3, 6]
def baseStart_6273225 : Nat := 118140960795 + 6273225 * 2 ^ 59
def prefixEnd_6273225 : Nat := 4983230072969 + 3 ^ 40 * 6273225 * 2
def baseEnd_6273225 : Nat := 1073726559600441237345823

theorem tailTrace_6273225 : CollatzResearch.WordTrace tailWord_6273225 prefixEnd_6273225 1073726559600441237345823 := by
  unfold tailWord_6273225
  simp only [CollatzResearch.WordTrace]
  refine ⟨228803312698184681378069129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152535541798789787585379419 228803312698184681378069129)
  ·
    refine ⟨171602484523638511033551847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228803312698184681378069129 171602484523638511033551847)
    ·
      refine ⟨257403726785457766550327771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171602484523638511033551847 257403726785457766550327771)
      ·
        refine ⟨386105590178186649825491657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257403726785457766550327771 386105590178186649825491657)
        ·
          refine ⟨289579192633639987369118743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386105590178186649825491657 289579192633639987369118743)
          ·
            refine ⟨434368788950459981053678115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289579192633639987369118743 434368788950459981053678115)
            ·
              refine ⟨651553183425689971580517173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434368788950459981053678115 651553183425689971580517173)
              ·
                refine ⟨61083110946158434835673485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 651553183425689971580517173 61083110946158434835673485)
                ·
                  refine ⟨22906166604809413063377557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61083110946158434835673485 22906166604809413063377557)
                  ·
                    refine ⟨1073726559600441237345823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22906166604809413063377557 1073726559600441237345823)
                    ·
                      rfl

theorem cell23_6273225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 6].length) (baseStart_6273225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273225 prefixEnd_6273225 := by exact prefixLift 6273225
  have htrace : WordTrace (prefixWord ++ tailWord_6273225) baseStart_6273225 baseEnd_6273225 := by
    simpa [prefixWord, tailWord_6273225, baseEnd_6273225] using wordTrace_append hprefix tailTrace_6273225
  have hstable : (prefixWord ++ tailWord_6273225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273225).length < 2 ^ (prefixWord ++ tailWord_6273225).sum := by decide
  have hdescent : baseEnd_6273225 < baseStart_6273225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273232 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2]
def baseStart_6273232 : Nat := 118140960795 + 6273232 * 2 ^ 59
def prefixEnd_6273232 : Nat := 4983230072969 + 3 ^ 40 * 6273232 * 2
def baseEnd_6273232 : Nat := 3221183273165905184649937

theorem tailTrace_6273232 : CollatzResearch.WordTrace tailWord_6273232 prefixEnd_6273232 3221183273165905184649937 := by
  unfold tailWord_6273232
  simp only [CollatzResearch.WordTrace]
  refine ⟨114401784004579660786786975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152535712006106214382382633 114401784004579660786786975)
  ·
    refine ⟨171602676006869491180180463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114401784004579660786786975 171602676006869491180180463)
    ·
      refine ⟨257404014010304236770270695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171602676006869491180180463 257404014010304236770270695)
      ·
        refine ⟨386106021015456355155406043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257404014010304236770270695 386106021015456355155406043)
        ·
          refine ⟨579159031523184532733109065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386106021015456355155406043 579159031523184532733109065)
          ·
            refine ⟨434369273642388399549831799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579159031523184532733109065 434369273642388399549831799)
            ·
              refine ⟨651553910463582599324747699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434369273642388399549831799 651553910463582599324747699)
              ·
                refine ⟨977330865695373898987121549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651553910463582599324747699 977330865695373898987121549)
                ·
                  refine ⟨366499074635765212120170581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977330865695373898987121549 366499074635765212120170581)
                  ·
                    refine ⟨4294911030887873579533249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 366499074635765212120170581 4294911030887873579533249)
                    ·
                      refine ⟨3221183273165905184649937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294911030887873579533249 3221183273165905184649937)
                      ·
                        rfl

theorem cell23_6273232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 8, 2].length) (baseStart_6273232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273232 prefixEnd_6273232 := by exact prefixLift 6273232
  have htrace : WordTrace (prefixWord ++ tailWord_6273232) baseStart_6273232 baseEnd_6273232 := by
    simpa [prefixWord, tailWord_6273232, baseEnd_6273232] using wordTrace_append hprefix tailTrace_6273232
  have hstable : (prefixWord ++ tailWord_6273232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273232).length < 2 ^ (prefixWord ++ tailWord_6273232).sum := by decide
  have hdescent : baseEnd_6273232 < baseStart_6273232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273250 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_6273250 : Nat := 118140960795 + 6273250 * 2 ^ 59
def prefixEnd_6273250 : Nat := 4983230072969 + 3 ^ 40 * 6273250 * 2
def baseEnd_6273250 : Nat := 357910279535298457136095

theorem tailTrace_6273250 : CollatzResearch.WordTrace tailWord_6273250 prefixEnd_6273250 357910279535298457136095 := by
  unfold tailWord_6273250
  simp only [CollatzResearch.WordTrace]
  refine ⟨57201056130773527661932301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152536149682062740431819469 57201056130773527661932301)
  ·
    refine ⟨21450396049040072873224613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57201056130773527661932301 21450396049040072873224613)
    ·
      refine ⟨4021949259195013663729615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21450396049040072873224613 4021949259195013663729615)
      ·
        refine ⟨6032923888792520495594423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021949259195013663729615 6032923888792520495594423)
        ·
          refine ⟨9049385833188780743391635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032923888792520495594423 9049385833188780743391635)
          ·
            refine ⟨13574078749783171115087453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049385833188780743391635 13574078749783171115087453)
            ·
              refine ⟨5090279531168689168157795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13574078749783171115087453 5090279531168689168157795)
              ·
                refine ⟨7635419296753033752236693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090279531168689168157795 7635419296753033752236693)
                ·
                  refine ⟨357910279535298457136095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7635419296753033752236693 357910279535298457136095)
                  ·
                    rfl

theorem cell23_6273250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_6273250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273250 prefixEnd_6273250 := by exact prefixLift 6273250
  have htrace : WordTrace (prefixWord ++ tailWord_6273250) baseStart_6273250 baseEnd_6273250 := by
    simpa [prefixWord, tailWord_6273250, baseEnd_6273250] using wordTrace_append hprefix tailTrace_6273250
  have hstable : (prefixWord ++ tailWord_6273250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273250).length < 2 ^ (prefixWord ++ tailWord_6273250).sum := by decide
  have hdescent : baseEnd_6273250 < baseStart_6273250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273266 : List Nat := [3, 2, 1, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6273266 : Nat := 118140960795 + 6273266 * 2 ^ 59
def prefixEnd_6273266 : Nat := 4983230072969 + 3 ^ 40 * 6273266 * 2
def baseEnd_6273266 : Nat := 3221200731508158051624781

theorem tailTrace_6273266 : CollatzResearch.WordTrace tailWord_6273266 prefixEnd_6273266 3221200731508158051624781 := by
  unfold tailWord_6273266
  simp only [CollatzResearch.WordTrace]
  refine ⟨57201202022759036345077913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152536538727357430253541101 57201202022759036345077913)
  ·
    refine ⟨42900901517069277258808435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57201202022759036345077913 42900901517069277258808435)
    ·
      refine ⟨64351352275603915888212653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42900901517069277258808435 64351352275603915888212653)
      ·
        refine ⟨24131757103351468458079745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64351352275603915888212653 24131757103351468458079745)
        ·
          refine ⟨18098817827513601343559809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24131757103351468458079745 18098817827513601343559809)
          ·
            refine ⟨13574113370635201007669857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18098817827513601343559809 13574113370635201007669857)
            ·
              refine ⟨10180585027976400755752393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13574113370635201007669857 10180585027976400755752393)
              ·
                refine ⟨7635438770982300566814295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10180585027976400755752393 7635438770982300566814295)
                ·
                  refine ⟨11453158156473450850221443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635438770982300566814295 11453158156473450850221443)
                  ·
                    refine ⟨17179737234710176275332165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11453158156473450850221443 17179737234710176275332165)
                    ·
                      refine ⟨3221200731508158051624781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17179737234710176275332165 3221200731508158051624781)
                      ·
                        rfl

theorem cell23_6273266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6273266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273266 prefixEnd_6273266 := by exact prefixLift 6273266
  have htrace : WordTrace (prefixWord ++ tailWord_6273266) baseStart_6273266 baseEnd_6273266 := by
    simpa [prefixWord, tailWord_6273266, baseEnd_6273266] using wordTrace_append hprefix tailTrace_6273266
  have hstable : (prefixWord ++ tailWord_6273266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273266).length < 2 ^ (prefixWord ++ tailWord_6273266).sum := by decide
  have hdescent : baseEnd_6273266 < baseStart_6273266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273275 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6]
def baseStart_6273275 : Nat := 118140960795 + 6273275 * 2 ^ 59
def prefixEnd_6273275 : Nat := 4983230072969 + 3 ^ 40 * 6273275 * 2
def baseEnd_6273275 : Nat := 3221205352834048516412239

theorem tailTrace_6273275 : CollatzResearch.WordTrace tailWord_6273275 prefixEnd_6273275 3221205352834048516412239 := by
  unfold tailWord_6273275
  simp only [CollatzResearch.WordTrace]
  refine ⟨228805136348003539917389279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152536757565335693278259519 228805136348003539917389279)
  ·
    refine ⟨343207704522005309876083919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228805136348003539917389279 343207704522005309876083919)
    ·
      refine ⟨514811556783007964814125879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343207704522005309876083919 514811556783007964814125879)
      ·
        refine ⟨772217335174511947221188819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514811556783007964814125879 772217335174511947221188819)
        ·
          refine ⟨1158326002761767920831783229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772217335174511947221188819 1158326002761767920831783229)
          ·
            refine ⟨434372251035662970311918711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1158326002761767920831783229 434372251035662970311918711)
            ·
              refine ⟨651558376553494455467878067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434372251035662970311918711 651558376553494455467878067)
              ·
                refine ⟨977337564830241683201817101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651558376553494455467878067 977337564830241683201817101)
                ·
                  refine ⟨366501586811340631200681413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977337564830241683201817101 366501586811340631200681413)
                  ·
                    refine ⟨68719047527126368350127765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366501586811340631200681413 68719047527126368350127765)
                    ·
                      refine ⟨3221205352834048516412239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68719047527126368350127765 3221205352834048516412239)
                      ·
                        rfl

theorem cell23_6273275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_6273275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273275 prefixEnd_6273275 := by exact prefixLift 6273275
  have htrace : WordTrace (prefixWord ++ tailWord_6273275) baseStart_6273275 baseEnd_6273275 := by
    simpa [prefixWord, tailWord_6273275, baseEnd_6273275] using wordTrace_append hprefix tailTrace_6273275
  have hstable : (prefixWord ++ tailWord_6273275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273275).length < 2 ^ (prefixWord ++ tailWord_6273275).sum := by decide
  have hdescent : baseEnd_6273275 < baseStart_6273275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273310 : List Nat := [4, 3, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6273310 : Nat := 118140960795 + 6273310 * 2 ^ 59
def prefixEnd_6273310 : Nat := 4983230072969 + 3 ^ 40 * 6273310 * 2
def baseEnd_6273310 : Nat := 1073741108218985293158193

theorem tailTrace_6273310 : CollatzResearch.WordTrace tailWord_6273310 prefixEnd_6273310 1073741108218985293158193 := by
  unfold tailWord_6273310
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600801612859592611864173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152537608601917827263275589 28600801612859592611864173)
  ·
    refine ⟨10725300604822347229449065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28600801612859592611864173 10725300604822347229449065)
    ·
      refine ⟨8043975453616760422086799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10725300604822347229449065 8043975453616760422086799)
      ·
        refine ⟨12065963180425140633130199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8043975453616760422086799 12065963180425140633130199)
        ·
          refine ⟨18098944770637710949695299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12065963180425140633130199 18098944770637710949695299)
          ·
            refine ⟨27148417155956566424542949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18098944770637710949695299 27148417155956566424542949)
            ·
              refine ⟨5090328216741856204601803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27148417155956566424542949 5090328216741856204601803)
              ·
                refine ⟨7635492325112784306902705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090328216741856204601803 7635492325112784306902705)
                ·
                  refine ⟨5726619243834588230177029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635492325112784306902705 5726619243834588230177029)
                  ·
                    refine ⟨1073741108218985293158193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726619243834588230177029 1073741108218985293158193)
                    ·
                      rfl

theorem cell23_6273310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6273310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273310 prefixEnd_6273310 := by exact prefixLift 6273310
  have htrace : WordTrace (prefixWord ++ tailWord_6273310) baseStart_6273310 baseEnd_6273310 := by
    simpa [prefixWord, tailWord_6273310, baseEnd_6273310] using wordTrace_append hprefix tailTrace_6273310
  have hstable : (prefixWord ++ tailWord_6273310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273310).length < 2 ^ (prefixWord ++ tailWord_6273310).sum := by decide
  have hdescent : baseEnd_6273310 < baseStart_6273310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273320 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_6273320 : Nat := 118140960795 + 6273320 * 2 ^ 59
def prefixEnd_6273320 : Nat := 4983230072969 + 3 ^ 40 * 6273320 * 2
def baseEnd_6273320 : Nat := 3221228459463500840349533

theorem tailTrace_6273320 : CollatzResearch.WordTrace tailWord_6273320 prefixEnd_6273320 3221228459463500840349533 := by
  unfold tailWord_6273320
  simp only [CollatzResearch.WordTrace]
  refine ⟨114403388816420256301388707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152537851755227008401851609 114403388816420256301388707)
  ·
    refine ⟨171605083224630384452083061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114403388816420256301388707 171605083224630384452083061)
    ·
      refine ⟨16087976552309098542382787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171605083224630384452083061 16087976552309098542382787)
      ·
        refine ⟨24131964828463647813574181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16087976552309098542382787 24131964828463647813574181)
        ·
          refine ⟨4524743405336933965045159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24131964828463647813574181 4524743405336933965045159)
          ·
            refine ⟨6787115108005400947567739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524743405336933965045159 6787115108005400947567739)
            ·
              refine ⟨10180672662008101421351609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787115108005400947567739 10180672662008101421351609)
              ·
                refine ⟨7635504496506076066013707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10180672662008101421351609 7635504496506076066013707)
                ·
                  refine ⟨11453256744759114099020561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635504496506076066013707 11453256744759114099020561)
                  ·
                    refine ⟨8589942558569335574265421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11453256744759114099020561 8589942558569335574265421)
                    ·
                      refine ⟨3221228459463500840349533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8589942558569335574265421 3221228459463500840349533)
                      ·
                        rfl

theorem cell23_6273320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_6273320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273320 prefixEnd_6273320 := by exact prefixLift 6273320
  have htrace : WordTrace (prefixWord ++ tailWord_6273320) baseStart_6273320 baseEnd_6273320 := by
    simpa [prefixWord, tailWord_6273320, baseEnd_6273320] using wordTrace_append hprefix tailTrace_6273320
  have hstable : (prefixWord ++ tailWord_6273320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273320).length < 2 ^ (prefixWord ++ tailWord_6273320).sum := by decide
  have hdescent : baseEnd_6273320 < baseStart_6273320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273343 : List Nat := [1, 1, 2, 2, 4, 1, 5, 1, 1, 3, 2]
def baseStart_6273343 : Nat := 118140960795 + 6273343 * 2 ^ 59
def prefixEnd_6273343 : Nat := 4983230072969 + 3 ^ 40 * 6273343 * 2
def baseEnd_6273343 : Nat := 3221240269518554250361927

theorem tailTrace_6273343 : CollatzResearch.WordTrace tailWord_6273343 prefixEnd_6273343 3221240269518554250361927 := by
  unfold tailWord_6273343
  simp only [CollatzResearch.WordTrace]
  refine ⟨228807616511757187530864683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152538411007838125020576455 228807616511757187530864683)
  ·
    refine ⟨343211424767635781296297025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228807616511757187530864683 343211424767635781296297025)
    ·
      refine ⟨257408568575726835972222769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343211424767635781296297025 257408568575726835972222769)
      ·
        refine ⟨193056426431795126979167077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257408568575726835972222769 193056426431795126979167077)
        ·
          refine ⟨36198079955961586308593827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193056426431795126979167077 36198079955961586308593827)
          ·
            refine ⟨54297119933942379462890741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36198079955961586308593827 54297119933942379462890741)
            ·
              refine ⟨5090354993807098074646007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54297119933942379462890741 5090354993807098074646007)
              ·
                refine ⟨7635532490710647111969011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090354993807098074646007 7635532490710647111969011)
                ·
                  refine ⟨11453298736065970667953517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635532490710647111969011 11453298736065970667953517)
                  ·
                    refine ⟨4294987026024739000482569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11453298736065970667953517 4294987026024739000482569)
                    ·
                      refine ⟨3221240269518554250361927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4294987026024739000482569 3221240269518554250361927)
                      ·
                        rfl

theorem cell23_6273343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_6273343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273343 prefixEnd_6273343 := by exact prefixLift 6273343
  have htrace : WordTrace (prefixWord ++ tailWord_6273343) baseStart_6273343 baseEnd_6273343 := by
    simpa [prefixWord, tailWord_6273343, baseEnd_6273343] using wordTrace_append hprefix tailTrace_6273343
  have hstable : (prefixWord ++ tailWord_6273343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273343).length < 2 ^ (prefixWord ++ tailWord_6273343).sum := by decide
  have hdescent : baseEnd_6273343 < baseStart_6273343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273389 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6273389 : Nat := 118140960795 + 6273389 * 2 ^ 59
def prefixEnd_6273389 : Nat := 4983230072969 + 3 ^ 40 * 6273389 * 2
def baseEnd_6273389 : Nat := 3221263889628661070386715

theorem tailTrace_6273389 : CollatzResearch.WordTrace tailWord_6273389 prefixEnd_6273389 3221263889628661070386715 := by
  unfold tailWord_6273389
  simp only [CollatzResearch.WordTrace]
  refine ⟨228809294269590537387039221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152539529513060358258026147 228809294269590537387039221)
  ·
    refine ⟨21450871337774112880034927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228809294269590537387039221 21450871337774112880034927)
    ·
      refine ⟨32176307006661169320052391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21450871337774112880034927 32176307006661169320052391)
      ·
        refine ⟨48264460509991753980078587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32176307006661169320052391 48264460509991753980078587)
        ·
          refine ⟨72396690764987630970117881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48264460509991753980078587 72396690764987630970117881)
          ·
            refine ⟨54297518073740723227588411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72396690764987630970117881 54297518073740723227588411)
            ·
              refine ⟨81446277110611084841382617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54297518073740723227588411 81446277110611084841382617)
              ·
                refine ⟨61084707832958313631036963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81446277110611084841382617 61084707832958313631036963)
                ·
                  refine ⟨91627061749437470446555445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61084707832958313631036963 91627061749437470446555445)
                  ·
                    refine ⟨8590037039009762854364573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91627061749437470446555445 8590037039009762854364573)
                    ·
                      refine ⟨3221263889628661070386715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590037039009762854364573 3221263889628661070386715)
                      ·
                        rfl

theorem cell23_6273389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6273389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273389 prefixEnd_6273389 := by exact prefixLift 6273389
  have htrace : WordTrace (prefixWord ++ tailWord_6273389) baseStart_6273389 baseEnd_6273389 := by
    simpa [prefixWord, tailWord_6273389, baseEnd_6273389] using wordTrace_append hprefix tailTrace_6273389
  have hstable : (prefixWord ++ tailWord_6273389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273389).length < 2 ^ (prefixWord ++ tailWord_6273389).sum := by decide
  have hdescent : baseEnd_6273389 < baseStart_6273389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273399 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 7, 2]
def baseStart_6273399 : Nat := 118140960795 + 6273399 * 2 ^ 59
def prefixEnd_6273399 : Nat := 4983230072969 + 3 ^ 40 * 6273399 * 2
def baseEnd_6273399 : Nat := 3221269024435206031261669

theorem tailTrace_6273399 : CollatzResearch.WordTrace tailWord_6273399 prefixEnd_6273399 3221269024435206031261669 := by
  unfold tailWord_6273399
  simp only [CollatzResearch.WordTrace]
  refine ⟨228809658999554309094903251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152539772666369539396602167 228809658999554309094903251)
  ·
    refine ⟨343214488499331463642354877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228809658999554309094903251 343214488499331463642354877)
    ·
      refine ⟨128705433187249298865883079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 343214488499331463642354877 128705433187249298865883079)
      ·
        refine ⟨193058149780873948298824619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128705433187249298865883079 193058149780873948298824619)
        ·
          refine ⟨289587224671310922448236929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193058149780873948298824619 289587224671310922448236929)
          ·
            refine ⟨217190418503483191836177697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289587224671310922448236929 217190418503483191836177697)
            ·
              refine ⟨162892813877612393877133273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217190418503483191836177697 162892813877612393877133273)
              ·
                refine ⟨122169610408209295407849955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162892813877612393877133273 122169610408209295407849955)
                ·
                  refine ⟨183254415612313943111774933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122169610408209295407849955 183254415612313943111774933)
                  ·
                    refine ⟨4295025365913608041682225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 183254415612313943111774933 4295025365913608041682225)
                    ·
                      refine ⟨3221269024435206031261669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295025365913608041682225 3221269024435206031261669)
                      ·
                        rfl

theorem cell23_6273399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 7, 2].length) (baseStart_6273399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273399 prefixEnd_6273399 := by exact prefixLift 6273399
  have htrace : WordTrace (prefixWord ++ tailWord_6273399) baseStart_6273399 baseEnd_6273399 := by
    simpa [prefixWord, tailWord_6273399, baseEnd_6273399] using wordTrace_append hprefix tailTrace_6273399
  have hstable : (prefixWord ++ tailWord_6273399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273399).length < 2 ^ (prefixWord ++ tailWord_6273399).sum := by decide
  have hdescent : baseEnd_6273399 < baseStart_6273399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273449 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 3]
def baseStart_6273449 : Nat := 118140960795 + 6273449 * 2 ^ 59
def prefixEnd_6273449 : Nat := 4983230072969 + 3 ^ 40 * 6273449 * 2
def baseEnd_6273449 : Nat := 3221294698467930835636439

theorem tailTrace_6273449 : CollatzResearch.WordTrace tailWord_6273449 prefixEnd_6273449 3221294698467930835636439 := by
  unfold tailWord_6273449
  simp only [CollatzResearch.WordTrace]
  refine ⟨228811482649373167634223401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152540988432915445089482267 228811482649373167634223401)
  ·
    refine ⟨171608611987029875725667551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228811482649373167634223401 171608611987029875725667551)
    ·
      refine ⟨257412917980544813588501327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171608611987029875725667551 257412917980544813588501327)
      ·
        refine ⟨386119376970817220382751991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257412917980544813588501327 386119376970817220382751991)
        ·
          refine ⟨579179065456225830574127987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386119376970817220382751991 579179065456225830574127987)
          ·
            refine ⟨868768598184338745861191981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579179065456225830574127987 868768598184338745861191981)
            ·
              refine ⟨325788224319127029697946993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 868768598184338745861191981 325788224319127029697946993)
              ·
                refine ⟨244341168239345272273460245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325788224319127029697946993 244341168239345272273460245)
                ·
                  refine ⟨11453492261219309637818449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 244341168239345272273460245 11453492261219309637818449)
                  ·
                    refine ⟨8590119195914482228363837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11453492261219309637818449 8590119195914482228363837)
                    ·
                      refine ⟨3221294698467930835636439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590119195914482228363837 3221294698467930835636439)
                      ·
                        rfl

theorem cell23_6273449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 2, 3].length) (baseStart_6273449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273449 prefixEnd_6273449 := by exact prefixLift 6273449
  have htrace : WordTrace (prefixWord ++ tailWord_6273449) baseStart_6273449 baseEnd_6273449 := by
    simpa [prefixWord, tailWord_6273449, baseEnd_6273449] using wordTrace_append hprefix tailTrace_6273449
  have hstable : (prefixWord ++ tailWord_6273449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273449).length < 2 ^ (prefixWord ++ tailWord_6273449).sum := by decide
  have hdescent : baseEnd_6273449 < baseStart_6273449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273460 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_6273460 : Nat := 118140960795 + 6273460 * 2 ^ 59
def prefixEnd_6273460 : Nat := 4983230072969 + 3 ^ 40 * 6273460 * 2
def baseEnd_6273460 : Nat := 1073766782251710097532963

theorem tailTrace_6273460 : CollatzResearch.WordTrace tailWord_6273460 prefixEnd_6273460 1073766782251710097532963 := by
  unfold tailWord_6273460
  simp only [CollatzResearch.WordTrace]
  refine ⟨114405941926166658256436917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152541255901555544341915889 114405941926166658256436917)
  ·
    refine ⟨10725557055578124211540961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114405941926166658256436917 10725557055578124211540961)
    ·
      refine ⟨8044167791683593158655721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10725557055578124211540961 8044167791683593158655721)
      ·
        refine ⟨6033125843762694868991791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8044167791683593158655721 6033125843762694868991791)
        ·
          refine ⟨9049688765644042303487687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033125843762694868991791 9049688765644042303487687)
          ·
            refine ⟨13574533148466063455231531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049688765644042303487687 13574533148466063455231531)
            ·
              refine ⟨20361799722699095182847297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13574533148466063455231531 20361799722699095182847297)
              ·
                refine ⟨15271349792024321387135473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20361799722699095182847297 15271349792024321387135473)
                ·
                  refine ⟨11453512344018241040351605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15271349792024321387135473 11453512344018241040351605)
                  ·
                    refine ⟨1073766782251710097532963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11453512344018241040351605 1073766782251710097532963)
                    ·
                      rfl

theorem cell23_6273460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_6273460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273460 prefixEnd_6273460 := by exact prefixLift 6273460
  have htrace : WordTrace (prefixWord ++ tailWord_6273460) baseStart_6273460 baseEnd_6273460 := by
    simpa [prefixWord, tailWord_6273460, baseEnd_6273460] using wordTrace_append hprefix tailTrace_6273460
  have hstable : (prefixWord ++ tailWord_6273460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273460).length < 2 ^ (prefixWord ++ tailWord_6273460).sum := by decide
  have hdescent : baseEnd_6273460 < baseStart_6273460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273469 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 8]
def baseStart_6273469 : Nat := 118140960795 + 6273469 * 2 ^ 59
def prefixEnd_6273469 : Nat := 4983230072969 + 3 ^ 40 * 6273469 * 2
def baseEnd_6273469 : Nat := 357922774231224528598483

theorem tailTrace_6273469 : CollatzResearch.WordTrace tailWord_6273469 prefixEnd_6273469 357922774231224528598483 := by
  unfold tailWord_6273469
  simp only [CollatzResearch.WordTrace]
  refine ⟨228812212109300711049951461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152541474739533807366634307 228812212109300711049951461)
  ·
    refine ⟨42902289770493883321865899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228812212109300711049951461 42902289770493883321865899)
    ·
      refine ⟨64353434655740824982798849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42902289770493883321865899 64353434655740824982798849)
      ·
        refine ⟨48265075991805618737099137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64353434655740824982798849 48265075991805618737099137)
        ·
          refine ⟨36198806993854214052824353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48265075991805618737099137 36198806993854214052824353)
          ·
            refine ⟨27149105245390660539618265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36198806993854214052824353 27149105245390660539618265)
            ·
              refine ⟨20361828934042995404713699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27149105245390660539618265 20361828934042995404713699)
              ·
                refine ⟨30542743401064493107070549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20361828934042995404713699 30542743401064493107070549)
                ·
                  refine ⟨357922774231224528598483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30542743401064493107070549 357922774231224528598483)
                  ·
                    rfl

theorem cell23_6273469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_6273469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273469 prefixEnd_6273469 := by exact prefixLift 6273469
  have htrace : WordTrace (prefixWord ++ tailWord_6273469) baseStart_6273469 baseEnd_6273469 := by
    simpa [prefixWord, tailWord_6273469, baseEnd_6273469] using wordTrace_append hprefix tailTrace_6273469
  have hstable : (prefixWord ++ tailWord_6273469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273469).length < 2 ^ (prefixWord ++ tailWord_6273469).sum := by decide
  have hdescent : baseEnd_6273469 < baseStart_6273469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273496 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_6273496 : Nat := 118140960795 + 6273496 * 2 ^ 59
def prefixEnd_6273496 : Nat := 4983230072969 + 3 ^ 40 * 6273496 * 2
def baseEnd_6273496 : Nat := 3221318832058692151748723

theorem tailTrace_6273496 : CollatzResearch.WordTrace tailWord_6273496 prefixEnd_6273496 3221318832058692151748723 := by
  unfold tailWord_6273496
  simp only [CollatzResearch.WordTrace]
  refine ⟨114406598440101447330592171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152542131253468596440789561 114406598440101447330592171)
  ·
    refine ⟨171609897660152170995888257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114406598440101447330592171 171609897660152170995888257)
    ·
      refine ⟨128707423245114128246916193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171609897660152170995888257 128707423245114128246916193)
      ·
        refine ⟨96530567433835596185187145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128707423245114128246916193 96530567433835596185187145)
        ·
          refine ⟨72397925575376697138890359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96530567433835596185187145 72397925575376697138890359)
          ·
            refine ⟨108596888363065045708335539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72397925575376697138890359 108596888363065045708335539)
            ·
              refine ⟨162895332544597568562503309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108596888363065045708335539 162895332544597568562503309)
              ·
                refine ⟨61085749704224088210938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162895332544597568562503309 61085749704224088210938741)
                ·
                  refine ⟨5726789034771008269775507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61085749704224088210938741 5726789034771008269775507)
                  ·
                    refine ⟨8590183552156512404663261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726789034771008269775507 8590183552156512404663261)
                    ·
                      refine ⟨3221318832058692151748723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590183552156512404663261 3221318832058692151748723)
                      ·
                        rfl

theorem cell23_6273496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_6273496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273496 prefixEnd_6273496 := by exact prefixLift 6273496
  have htrace : WordTrace (prefixWord ++ tailWord_6273496) baseStart_6273496 baseEnd_6273496 := by
    simpa [prefixWord, tailWord_6273496, baseEnd_6273496] using wordTrace_append hprefix tailTrace_6273496
  have hstable : (prefixWord ++ tailWord_6273496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273496).length < 2 ^ (prefixWord ++ tailWord_6273496).sum := by decide
  have hdescent : baseEnd_6273496 < baseStart_6273496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273539 : List Nat := [1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5]
def baseStart_6273539 : Nat := 118140960795 + 6273539 * 2 ^ 59
def prefixEnd_6273539 : Nat := 4983230072969 + 3 ^ 40 * 6273539 * 2
def baseEnd_6273539 : Nat := 3221340911726835483511025

theorem tailTrace_6273539 : CollatzResearch.WordTrace tailWord_6273539 prefixEnd_6273539 3221340911726835483511025 := by
  unfold tailWord_6273539
  simp only [CollatzResearch.WordTrace]
  refine ⟨228814765219047113004999671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152543176812698075336666447 228814765219047113004999671)
  ·
    refine ⟨343222147828570669507499507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228814765219047113004999671 343222147828570669507499507)
    ·
      refine ⟨514833221742856004261249261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343222147828570669507499507 514833221742856004261249261)
      ·
        refine ⟨193062458153571001597968473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514833221742856004261249261 193062458153571001597968473)
        ·
          refine ⟨144796843615178251198476355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193062458153571001597968473 144796843615178251198476355)
          ·
            refine ⟨217195265422767376797714533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144796843615178251198476355 217195265422767376797714533)
            ·
              refine ⟨40724112266768883149571475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 217195265422767376797714533 40724112266768883149571475)
              ·
                refine ⟨61086168400153324724357213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40724112266768883149571475 61086168400153324724357213)
                ·
                  refine ⟨22907313150057496771633955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61086168400153324724357213 22907313150057496771633955)
                  ·
                    refine ⟨34360969725086245157450933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22907313150057496771633955 34360969725086245157450933)
                    ·
                      refine ⟨3221340911726835483511025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34360969725086245157450933 3221340911726835483511025)
                      ·
                        rfl

theorem cell23_6273539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_6273539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273539 prefixEnd_6273539 := by exact prefixLift 6273539
  have htrace : WordTrace (prefixWord ++ tailWord_6273539) baseStart_6273539 baseEnd_6273539 := by
    simpa [prefixWord, tailWord_6273539, baseEnd_6273539] using wordTrace_append hprefix tailTrace_6273539
  have hstable : (prefixWord ++ tailWord_6273539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273539).length < 2 ^ (prefixWord ++ tailWord_6273539).sum := by decide
  have hdescent : baseEnd_6273539 < baseStart_6273539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273546 : List Nat := [3, 1, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_6273546 : Nat := 118140960795 + 6273546 * 2 ^ 59
def prefixEnd_6273546 : Nat := 4983230072969 + 3 ^ 40 * 6273546 * 2
def baseEnd_6273546 : Nat := 1073781502030472318707831

theorem tailTrace_6273546 : CollatzResearch.WordTrace tailWord_6273546 prefixEnd_6273546 1073781502030472318707831 := by
  unfold tailWord_6273546
  simp only [CollatzResearch.WordTrace]
  refine ⟨57203755132505438300126123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152543347020014502133669661 57203755132505438300126123)
  ·
    refine ⟨85805632698758157450189185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57203755132505438300126123 85805632698758157450189185)
    ·
      refine ⟨64354224524068618087641889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85805632698758157450189185 64354224524068618087641889)
      ·
        refine ⟨48265668393051463565731417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64354224524068618087641889 48265668393051463565731417)
        ·
          refine ⟨36199251294788597674298563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48265668393051463565731417 36199251294788597674298563)
          ·
            refine ⟨54298876942182896511447845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36199251294788597674298563 54298876942182896511447845)
            ·
              refine ⟨10181039426659293095896471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54298876942182896511447845 10181039426659293095896471)
              ·
                refine ⟨15271559139988939643844707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10181039426659293095896471 15271559139988939643844707)
                ·
                  refine ⟨22907338709983409465767061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15271559139988939643844707 22907338709983409465767061)
                  ·
                    refine ⟨1073781502030472318707831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22907338709983409465767061 1073781502030472318707831)
                    ·
                      rfl

theorem cell23_6273546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_6273546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273546 prefixEnd_6273546 := by exact prefixLift 6273546
  have htrace : WordTrace (prefixWord ++ tailWord_6273546) baseStart_6273546 baseEnd_6273546 := by
    simpa [prefixWord, tailWord_6273546, baseEnd_6273546] using wordTrace_append hprefix tailTrace_6273546
  have hstable : (prefixWord ++ tailWord_6273546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273546).length < 2 ^ (prefixWord ++ tailWord_6273546).sum := by decide
  have hdescent : baseEnd_6273546 < baseStart_6273546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273576 : List Nat := [2, 1, 5, 2, 1, 2, 10]
def baseStart_6273576 : Nat := 118140960795 + 6273576 * 2 ^ 59
def prefixEnd_6273576 : Nat := 4983230072969 + 3 ^ 40 * 6273576 * 2
def baseEnd_6273576 : Nat := 39769875438408047391955

theorem tailTrace_6273576 : CollatzResearch.WordTrace tailWord_6273576 prefixEnd_6273576 39769875438408047391955 := by
  unfold tailWord_6273576
  simp only [CollatzResearch.WordTrace]
  refine ⟨114408057359956534162048291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152544076479942045549397721 114408057359956534162048291)
  ·
    refine ⟨171612086039934801243072437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114408057359956534162048291 171612086039934801243072437)
    ·
      refine ⟨16088633066243887616538041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 171612086039934801243072437 16088633066243887616538041)
      ·
        refine ⟨12066474799682915712403531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16088633066243887616538041 12066474799682915712403531)
        ·
          refine ⟨18099712199524373568605297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12066474799682915712403531 18099712199524373568605297)
          ·
            refine ⟨13574784149643280176453973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18099712199524373568605297 13574784149643280176453973)
            ·
              refine ⟨39769875438408047391955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13574784149643280176453973 39769875438408047391955)
              ·
                rfl

theorem cell23_6273576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 10].length) (baseStart_6273576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273576 prefixEnd_6273576 := by exact prefixLift 6273576
  have htrace : WordTrace (prefixWord ++ tailWord_6273576) baseStart_6273576 baseEnd_6273576 := by
    simpa [prefixWord, tailWord_6273576, baseEnd_6273576] using wordTrace_append hprefix tailTrace_6273576
  have hstable : (prefixWord ++ tailWord_6273576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273576).length < 2 ^ (prefixWord ++ tailWord_6273576).sum := by decide
  have hdescent : baseEnd_6273576 < baseStart_6273576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273586 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_6273586 : Nat := 118140960795 + 6273586 * 2 ^ 59
def prefixEnd_6273586 : Nat := 4983230072969 + 3 ^ 40 * 6273586 * 2
def baseEnd_6273586 : Nat := 3221365045317596799623309

theorem tailTrace_6273586 : CollatzResearch.WordTrace tailWord_6273586 prefixEnd_6273586 3221365045317596799623309 := by
  unfold tailWord_6273586
  simp only [CollatzResearch.WordTrace]
  refine ⟨57204119862469210007990153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152544319633251226687973741 57204119862469210007990153)
  ·
    refine ⟨42903089896851907505992615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57204119862469210007990153 42903089896851907505992615)
    ·
      refine ⟨64354634845277861258988923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42903089896851907505992615 64354634845277861258988923)
      ·
        refine ⟨96531952267916791888483385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64354634845277861258988923 96531952267916791888483385)
        ·
          refine ⟨72398964200937593916362539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96531952267916791888483385 72398964200937593916362539)
          ·
            refine ⟨108598446301406390874543809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72398964200937593916362539 108598446301406390874543809)
            ·
              refine ⟨81448834726054793155907857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108598446301406390874543809 81448834726054793155907857)
              ·
                refine ⟨61086626044541094866930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81448834726054793155907857 61086626044541094866930893)
                ·
                  refine ⟨22907484766702910575099085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61086626044541094866930893 22907484766702910575099085)
                  ·
                    refine ⟨8590306787513591465662157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22907484766702910575099085 8590306787513591465662157)
                    ·
                      refine ⟨3221365045317596799623309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590306787513591465662157 3221365045317596799623309)
                      ·
                        rfl

theorem cell23_6273586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_6273586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273586 prefixEnd_6273586 := by exact prefixLift 6273586
  have htrace : WordTrace (prefixWord ++ tailWord_6273586) baseStart_6273586 baseEnd_6273586 := by
    simpa [prefixWord, tailWord_6273586, baseEnd_6273586] using wordTrace_append hprefix tailTrace_6273586
  have hstable : (prefixWord ++ tailWord_6273586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273586).length < 2 ^ (prefixWord ++ tailWord_6273586).sum := by decide
  have hdescent : baseEnd_6273586 < baseStart_6273586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273603 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 3]
def baseStart_6273603 : Nat := 118140960795 + 6273603 * 2 ^ 59
def prefixEnd_6273603 : Nat := 4983230072969 + 3 ^ 40 * 6273603 * 2
def baseEnd_6273603 : Nat := 3221373774488723233110731

theorem tailTrace_6273603 : CollatzResearch.WordTrace tailWord_6273603 prefixEnd_6273603 3221373774488723233110731 := by
  unfold tailWord_6273603
  simp only [CollatzResearch.WordTrace]
  refine ⟨228817099490815251935329463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152544732993876834623552975 228817099490815251935329463)
  ·
    refine ⟨343225649236222877902994195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228817099490815251935329463 343225649236222877902994195)
    ·
      refine ⟨514838473854334316854491293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343225649236222877902994195 514838473854334316854491293)
      ·
        refine ⟨193064427695375368820434235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514838473854334316854491293 193064427695375368820434235)
        ·
          refine ⟨289596641543063053230651353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193064427695375368820434235 289596641543063053230651353)
          ·
            refine ⟨217197481157297289922988515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 289596641543063053230651353 217197481157297289922988515)
            ·
              refine ⟨325796221735945934884482773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217197481157297289922988515 325796221735945934884482773)
              ·
                refine ⟨7635848946936232848855065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 325796221735945934884482773 7635848946936232848855065)
                ·
                  refine ⟨5726886710202174636641299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635848946936232848855065 5726886710202174636641299)
                  ·
                    refine ⟨8590330065303261954961949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5726886710202174636641299 8590330065303261954961949)
                    ·
                      refine ⟨3221373774488723233110731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590330065303261954961949 3221373774488723233110731)
                      ·
                        rfl

theorem cell23_6273603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_6273603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273603 prefixEnd_6273603 := by exact prefixLift 6273603
  have htrace : WordTrace (prefixWord ++ tailWord_6273603) baseStart_6273603 baseEnd_6273603 := by
    simpa [prefixWord, tailWord_6273603, baseEnd_6273603] using wordTrace_append hprefix tailTrace_6273603
  have hstable : (prefixWord ++ tailWord_6273603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273603).length < 2 ^ (prefixWord ++ tailWord_6273603).sum := by decide
  have hdescent : baseEnd_6273603 < baseStart_6273603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273604 : List Nat := [2, 3, 5, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6273604 : Nat := 118140960795 + 6273604 * 2 ^ 59
def prefixEnd_6273604 : Nat := 4983230072969 + 3 ^ 40 * 6273604 * 2
def baseEnd_6273604 : Nat := 3221374287969377729198227

theorem tailTrace_6273604 : CollatzResearch.WordTrace tailWord_6273604 prefixEnd_6273604 3221374287969377729198227 := by
  unfold tailWord_6273604
  simp only [CollatzResearch.WordTrace]
  refine ⟨114408567981905814553057933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152544757309207752737410577 114408567981905814553057933)
  ·
    refine ⟨42903212993214680457396725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114408567981905814553057933 42903212993214680457396725)
    ·
      refine ⟨4022176218113876292880943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42903212993214680457396725 4022176218113876292880943)
      ·
        refine ⟨6033264327170814439321415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4022176218113876292880943 6033264327170814439321415)
        ·
          refine ⟨9049896490756221658982123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033264327170814439321415 9049896490756221658982123)
          ·
            refine ⟨13574844736134332488473185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049896490756221658982123 13574844736134332488473185)
            ·
              refine ⟨10181133552100749366354889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13574844736134332488473185 10181133552100749366354889)
              ·
                refine ⟨7635850164075562024766167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10181133552100749366354889 7635850164075562024766167)
                ·
                  refine ⟨11453775246113343037149251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635850164075562024766167 11453775246113343037149251)
                  ·
                    refine ⟨17180662869170014555723877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11453775246113343037149251 17180662869170014555723877)
                    ·
                      refine ⟨3221374287969377729198227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17180662869170014555723877 3221374287969377729198227)
                      ·
                        rfl

theorem cell23_6273604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6273604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273604 prefixEnd_6273604 := by exact prefixLift 6273604
  have htrace : WordTrace (prefixWord ++ tailWord_6273604) baseStart_6273604 baseEnd_6273604 := by
    simpa [prefixWord, tailWord_6273604, baseEnd_6273604] using wordTrace_append hprefix tailTrace_6273604
  have hstable : (prefixWord ++ tailWord_6273604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273604).length < 2 ^ (prefixWord ++ tailWord_6273604).sum := by decide
  have hdescent : baseEnd_6273604 < baseStart_6273604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273676 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_6273676 : Nat := 118140960795 + 6273676 * 2 ^ 59
def prefixEnd_6273676 : Nat := 4983230072969 + 3 ^ 40 * 6273676 * 2
def baseEnd_6273676 : Nat := 3221411258576501447497895

theorem tailTrace_6273676 : CollatzResearch.WordTrace tailWord_6273676 prefixEnd_6273676 3221411258576501447497895 := by
  unfold tailWord_6273676
  simp only [CollatzResearch.WordTrace]
  refine ⟨114409881009775392701368441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152546508013033856935157921 114409881009775392701368441)
  ·
    refine ⟨85807410757331544526026331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114409881009775392701368441 85807410757331544526026331)
    ·
      refine ⟨128711116135997316789039497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85807410757331544526026331 128711116135997316789039497)
      ·
        refine ⟨96533337101997987591779623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128711116135997316789039497 96533337101997987591779623)
        ·
          refine ⟨144800005652996981387669435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96533337101997987591779623 144800005652996981387669435)
          ·
            refine ⟨217200008479495472081504153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144800005652996981387669435 217200008479495472081504153)
            ·
              refine ⟨162900006359621604061128115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217200008479495472081504153 162900006359621604061128115)
              ·
                refine ⟨244350009539432406091692173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162900006359621604061128115 244350009539432406091692173)
                ·
                  refine ⟨91631253577287152284384565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244350009539432406091692173 91631253577287152284384565)
                  ·
                    refine ⟨8590430022870670526661053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91631253577287152284384565 8590430022870670526661053)
                    ·
                      refine ⟨3221411258576501447497895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590430022870670526661053 3221411258576501447497895)
                      ·
                        rfl

theorem cell23_6273676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_6273676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273676 prefixEnd_6273676 := by exact prefixLift 6273676
  have htrace : WordTrace (prefixWord ++ tailWord_6273676) baseStart_6273676 baseEnd_6273676 := by
    simpa [prefixWord, tailWord_6273676, baseEnd_6273676] using wordTrace_append hprefix tailTrace_6273676
  have hstable : (prefixWord ++ tailWord_6273676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273676).length < 2 ^ (prefixWord ++ tailWord_6273676).sum := by decide
  have hdescent : baseEnd_6273676 < baseStart_6273676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273694 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_6273694 : Nat := 118140960795 + 6273694 * 2 ^ 59
def prefixEnd_6273694 : Nat := 4983230072969 + 3 ^ 40 * 6273694 * 2
def baseEnd_6273694 : Nat := 3221420501228282377072813

theorem tailTrace_6273694 : CollatzResearch.WordTrace tailWord_6273694 prefixEnd_6273694 3221420501228282377072813 := by
  unfold tailWord_6273694
  simp only [CollatzResearch.WordTrace]
  refine ⟨28602552316685696809611517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152546945688990382984594757 28602552316685696809611517)
  ·
    refine ⟨10725957118757136303604319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28602552316685696809611517 10725957118757136303604319)
    ·
      refine ⟨16088935678135704455406479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10725957118757136303604319 16088935678135704455406479)
      ·
        refine ⟨24133403517203556683109719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16088935678135704455406479 24133403517203556683109719)
        ·
          refine ⟨36200105275805335024664579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24133403517203556683109719 36200105275805335024664579)
          ·
            refine ⟨54300157913708002536996869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36200105275805335024664579 54300157913708002536996869)
            ·
              refine ⟨10181279608820250475686913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54300157913708002536996869 10181279608820250475686913)
              ·
                refine ⟨7635959706615187856765185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10181279608820250475686913 7635959706615187856765185)
                ·
                  refine ⟨5726969779961390892573889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635959706615187856765185 5726969779961390892573889)
                  ·
                    refine ⟨4295227334971043169430417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5726969779961390892573889 4295227334971043169430417)
                    ·
                      refine ⟨3221420501228282377072813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295227334971043169430417 3221420501228282377072813)
                      ·
                        rfl

theorem cell23_6273694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_6273694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273694 prefixEnd_6273694 := by exact prefixLift 6273694
  have htrace : WordTrace (prefixWord ++ tailWord_6273694) baseStart_6273694 baseEnd_6273694 := by
    simpa [prefixWord, tailWord_6273694, baseEnd_6273694] using wordTrace_append hprefix tailTrace_6273694
  have hstable : (prefixWord ++ tailWord_6273694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273694).length < 2 ^ (prefixWord ++ tailWord_6273694).sum := by decide
  have hdescent : baseEnd_6273694 < baseStart_6273694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273710 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6273710 : Nat := 118140960795 + 6273710 * 2 ^ 59
def prefixEnd_6273710 : Nat := 4983230072969 + 3 ^ 40 * 6273710 * 2
def baseEnd_6273710 : Nat := 3221428716918754314472739

theorem tailTrace_6273710 : CollatzResearch.WordTrace tailWord_6273710 prefixEnd_6273710 3221428716918754314472739 := by
  unfold tailWord_6273710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28602625262678451151184323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152547334734285072806316389 28602625262678451151184323)
  ·
    refine ⟨42903937894017676726776485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28602625262678451151184323 42903937894017676726776485)
    ·
      refine ⟨8044488355128314386270591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42903937894017676726776485 8044488355128314386270591)
      ·
        refine ⟨12066732532692471579405887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8044488355128314386270591 12066732532692471579405887)
        ·
          refine ⟨18100098799038707369108831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12066732532692471579405887 18100098799038707369108831)
          ·
            refine ⟨27150148198558061053663247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18100098799038707369108831 27150148198558061053663247)
            ·
              refine ⟨40725222297837091580494871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27150148198558061053663247 40725222297837091580494871)
              ·
                refine ⟨61087833446755637370742307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40725222297837091580494871 61087833446755637370742307)
                ·
                  refine ⟨91631750170133456056113461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61087833446755637370742307 91631750170133456056113461)
                  ·
                    refine ⟨8590476578450011505260637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91631750170133456056113461 8590476578450011505260637)
                    ·
                      refine ⟨3221428716918754314472739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590476578450011505260637 3221428716918754314472739)
                      ·
                        rfl

theorem cell23_6273710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6273710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273710 prefixEnd_6273710 := by exact prefixLift 6273710
  have htrace : WordTrace (prefixWord ++ tailWord_6273710) baseStart_6273710 baseEnd_6273710 := by
    simpa [prefixWord, tailWord_6273710, baseEnd_6273710] using wordTrace_append hprefix tailTrace_6273710
  have hstable : (prefixWord ++ tailWord_6273710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273710).length < 2 ^ (prefixWord ++ tailWord_6273710).sum := by decide
  have hdescent : baseEnd_6273710 < baseStart_6273710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273733 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 6, 4, 2]
def baseStart_6273733 : Nat := 118140960795 + 6273733 * 2 ^ 59
def prefixEnd_6273733 : Nat := 4983230072969 + 3 ^ 40 * 6273733 * 2
def baseEnd_6273733 : Nat := 3221440526973807724485133

theorem tailTrace_6273733 : CollatzResearch.WordTrace tailWord_6273733 prefixEnd_6273733 3221440526973807724485133 := by
  unfold tailWord_6273733
  simp only [CollatzResearch.WordTrace]
  refine ⟨228821840980344284137561853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152547893986896189425041235 228821840980344284137561853)
  ·
    refine ⟨85808190367629106551585695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 228821840980344284137561853 85808190367629106551585695)
    ·
      refine ⟨128712285551443659827378543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85808190367629106551585695 128712285551443659827378543)
      ·
        refine ⟨193068428327165489741067815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128712285551443659827378543 193068428327165489741067815)
        ·
          refine ⟨289602642490748234611601723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193068428327165489741067815 289602642490748234611601723)
          ·
            refine ⟨434403963736122351917402585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289602642490748234611601723 434403963736122351917402585)
            ·
              refine ⟨325802972802091763938051939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434403963736122351917402585 325802972802091763938051939)
              ·
                refine ⟨488704459203137645907077909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 325802972802091763938051939 488704459203137645907077909)
                ·
                  refine ⟨22908021525147077151894277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 488704459203137645907077909 22908021525147077151894277)
                  ·
                    refine ⟨4295254035965076965980177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22908021525147077151894277 4295254035965076965980177)
                    ·
                      refine ⟨3221440526973807724485133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295254035965076965980177 3221440526973807724485133)
                      ·
                        rfl

theorem cell23_6273733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 4, 2].length) (baseStart_6273733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273733 prefixEnd_6273733 := by exact prefixLift 6273733
  have htrace : WordTrace (prefixWord ++ tailWord_6273733) baseStart_6273733 baseEnd_6273733 := by
    simpa [prefixWord, tailWord_6273733, baseEnd_6273733] using wordTrace_append hprefix tailTrace_6273733
  have hstable : (prefixWord ++ tailWord_6273733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273733).length < 2 ^ (prefixWord ++ tailWord_6273733).sum := by decide
  have hdescent : baseEnd_6273733 < baseStart_6273733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273753 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 3]
def baseStart_6273753 : Nat := 118140960795 + 6273753 * 2 ^ 59
def prefixEnd_6273753 : Nat := 4983230072969 + 3 ^ 40 * 6273753 * 2
def baseEnd_6273753 : Nat := 3221450796586897646235041

theorem tailTrace_6273753 : CollatzResearch.WordTrace tailWord_6273753 prefixEnd_6273753 3221450796586897646235041 := by
  unfold tailWord_6273753
  simp only [CollatzResearch.WordTrace]
  refine ⟨228822570440271827553289913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152548380293514551702193275 228822570440271827553289913)
  ·
    refine ⟨171616927830203870664967435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228822570440271827553289913 171616927830203870664967435)
    ·
      refine ⟨257425391745305805997451153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171616927830203870664967435 257425391745305805997451153)
      ·
        refine ⟨193069043808979354498088365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257425391745305805997451153 193069043808979354498088365)
        ·
          refine ⟨72400891428367257936783137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193069043808979354498088365 72400891428367257936783137)
          ·
            refine ⟨54300668571275443452587353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72400891428367257936783137 54300668571275443452587353)
            ·
              refine ⟨40725501428456582589440515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54300668571275443452587353 40725501428456582589440515)
              ·
                refine ⟨61088252142684873884160773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40725501428456582589440515 61088252142684873884160773)
                ·
                  refine ⟨11454047276753413853280145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61088252142684873884160773 11454047276753413853280145)
                  ·
                    refine ⟨8590535457565060389960109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11454047276753413853280145 8590535457565060389960109)
                    ·
                      refine ⟨3221450796586897646235041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590535457565060389960109 3221450796586897646235041)
                      ·
                        rfl

theorem cell23_6273753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 3].length) (baseStart_6273753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273753 prefixEnd_6273753 := by exact prefixLift 6273753
  have htrace : WordTrace (prefixWord ++ tailWord_6273753) baseStart_6273753 baseEnd_6273753 := by
    simpa [prefixWord, tailWord_6273753, baseEnd_6273753] using wordTrace_append hprefix tailTrace_6273753
  have hstable : (prefixWord ++ tailWord_6273753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273753).length < 2 ^ (prefixWord ++ tailWord_6273753).sum := by decide
  have hdescent : baseEnd_6273753 < baseStart_6273753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273776 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_6273776 : Nat := 118140960795 + 6273776 * 2 ^ 59
def prefixEnd_6273776 : Nat := 4983230072969 + 3 ^ 40 * 6273776 * 2
def baseEnd_6273776 : Nat := 3221462606641951056247435

theorem tailTrace_6273776 : CollatzResearch.WordTrace tailWord_6273776 prefixEnd_6273776 3221462606641951056247435 := by
  unfold tailWord_6273776
  simp only [CollatzResearch.WordTrace]
  refine ⟨114411704659594251240688591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152548939546125668320918121 114411704659594251240688591)
  ·
    refine ⟨171617556989391376861032887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114411704659594251240688591 171617556989391376861032887)
    ·
      refine ⟨257426335484087065291549331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171617556989391376861032887 257426335484087065291549331)
      ·
        refine ⟨386139503226130597937323997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 257426335484087065291549331 386139503226130597937323997)
        ·
          refine ⟨144802313709798974226496499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 386139503226130597937323997 144802313709798974226496499)
          ·
            refine ⟨217203470564698461339744749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144802313709798974226496499 217203470564698461339744749)
            ·
              refine ⟨81451301461761923002404281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 217203470564698461339744749 81451301461761923002404281)
              ·
                refine ⟨61088476096321442251803211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81451301461761923002404281 61088476096321442251803211)
                ·
                  refine ⟨91632714144482163377704817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61088476096321442251803211 91632714144482163377704817)
                  ·
                    refine ⟨68724535608361622533278613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91632714144482163377704817 68724535608361622533278613)
                    ·
                      refine ⟨3221462606641951056247435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68724535608361622533278613 3221462606641951056247435)
                      ·
                        rfl

theorem cell23_6273776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_6273776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273776 prefixEnd_6273776 := by exact prefixLift 6273776
  have htrace : WordTrace (prefixWord ++ tailWord_6273776) baseStart_6273776 baseEnd_6273776 := by
    simpa [prefixWord, tailWord_6273776, baseEnd_6273776] using wordTrace_append hprefix tailTrace_6273776
  have hstable : (prefixWord ++ tailWord_6273776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273776).length < 2 ^ (prefixWord ++ tailWord_6273776).sum := by decide
  have hdescent : baseEnd_6273776 < baseStart_6273776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273794 : List Nat := [3, 4, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6273794 : Nat := 118140960795 + 6273794 * 2 ^ 59
def prefixEnd_6273794 : Nat := 4983230072969 + 3 ^ 40 * 6273794 * 2
def baseEnd_6273794 : Nat := 1073823949764577328607451

theorem tailTrace_6273794 : CollatzResearch.WordTrace tailWord_6273794 prefixEnd_6273794 1073823949764577328607451 := by
  unfold tailWord_6273794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57206016458280822888883109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152549377222082194370354957 57206016458280822888883109)
  ·
    refine ⟨10726128085927654291665583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57206016458280822888883109 10726128085927654291665583)
    ·
      refine ⟨16089192128891481437498375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726128085927654291665583 16089192128891481437498375)
      ·
        refine ⟨24133788193337222156247563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089192128891481437498375 24133788193337222156247563)
        ·
          refine ⟨36200682290005833234371345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24133788193337222156247563 36200682290005833234371345)
          ·
            refine ⟨27150511717504374925778509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36200682290005833234371345 27150511717504374925778509)
            ·
              refine ⟨10181441894064140597166941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27150511717504374925778509 10181441894064140597166941)
              ·
                refine ⟨3818040710274052723937603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10181441894064140597166941 3818040710274052723937603)
                ·
                  refine ⟨5727061065411079085906405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818040710274052723937603 5727061065411079085906405)
                  ·
                    refine ⟨1073823949764577328607451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727061065411079085906405 1073823949764577328607451)
                    ·
                      rfl

theorem cell23_6273794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6273794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273794 prefixEnd_6273794 := by exact prefixLift 6273794
  have htrace : WordTrace (prefixWord ++ tailWord_6273794) baseStart_6273794 baseEnd_6273794 := by
    simpa [prefixWord, tailWord_6273794, baseEnd_6273794] using wordTrace_append hprefix tailTrace_6273794
  have hstable : (prefixWord ++ tailWord_6273794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273794).length < 2 ^ (prefixWord ++ tailWord_6273794).sum := by decide
  have hdescent : baseEnd_6273794 < baseStart_6273794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273850 : List Nat := [3, 1, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_6273850 : Nat := 118140960795 + 6273850 * 2 ^ 59
def prefixEnd_6273850 : Nat := 4983230072969 + 3 ^ 40 * 6273850 * 2
def baseEnd_6273850 : Nat := 1073833534736794588907365

theorem tailTrace_6273850 : CollatzResearch.WordTrace tailWord_6273850 prefixEnd_6273850 1073833534736794588907365 := by
  unfold tailWord_6273850
  simp only [CollatzResearch.WordTrace]
  refine ⟨57206527080230103279892751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152550738880613608746380669 57206527080230103279892751)
  ·
    refine ⟨85809790620345154919839127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57206527080230103279892751 85809790620345154919839127)
    ·
      refine ⟨128714685930517732379758691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85809790620345154919839127 128714685930517732379758691)
      ·
        refine ⟨193072028895776598569638037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128714685930517732379758691 193072028895776598569638037)
        ·
          refine ⟨9050251354489528057951783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193072028895776598569638037 9050251354489528057951783)
          ·
            refine ⟨13575377031734292086927675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9050251354489528057951783 13575377031734292086927675)
            ·
              refine ⟨20363065547601438130391513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13575377031734292086927675 20363065547601438130391513)
              ·
                refine ⟨15272299160701078597793635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20363065547601438130391513 15272299160701078597793635)
                ·
                  refine ⟨22908448741051617896690453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15272299160701078597793635 22908448741051617896690453)
                  ·
                    refine ⟨1073833534736794588907365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22908448741051617896690453 1073833534736794588907365)
                    ·
                      rfl

theorem cell23_6273850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_6273850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273850 prefixEnd_6273850 := by exact prefixLift 6273850
  have htrace : WordTrace (prefixWord ++ tailWord_6273850) baseStart_6273850 baseEnd_6273850 := by
    simpa [prefixWord, tailWord_6273850, baseEnd_6273850] using wordTrace_append hprefix tailTrace_6273850
  have hstable : (prefixWord ++ tailWord_6273850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273850).length < 2 ^ (prefixWord ++ tailWord_6273850).sum := by decide
  have hdescent : baseEnd_6273850 < baseStart_6273850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273854 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6273854 : Nat := 118140960795 + 6273854 * 2 ^ 59
def prefixEnd_6273854 : Nat := 4983230072969 + 3 ^ 40 * 6273854 * 2
def baseEnd_6273854 : Nat := 1073834219377667250357359

theorem tailTrace_6273854 : CollatzResearch.WordTrace tailWord_6273854 prefixEnd_6273854 1073834219377667250357359 := by
  unfold tailWord_6273854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603281776613240225339577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152550836141937281201811077 28603281776613240225339577)
  ·
    refine ⟨21452461332459930169004683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28603281776613240225339577 21452461332459930169004683)
    ·
      refine ⟨32178691998689895253507025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21452461332459930169004683 32178691998689895253507025)
      ·
        refine ⟨24134018999017421440130269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32178691998689895253507025 24134018999017421440130269)
        ·
          refine ⟨9050257124631533040048851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24134018999017421440130269 9050257124631533040048851)
          ·
            refine ⟨13575385686947299560073277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9050257124631533040048851 13575385686947299560073277)
            ·
              refine ⟨5090769632605237335027479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13575385686947299560073277 5090769632605237335027479)
              ·
                refine ⟨7636154448907856002541219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090769632605237335027479 7636154448907856002541219)
                ·
                  refine ⟨11454231673361784003811829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7636154448907856002541219 11454231673361784003811829)
                  ·
                    refine ⟨1073834219377667250357359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11454231673361784003811829 1073834219377667250357359)
                    ·
                      rfl

theorem cell23_6273854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6273854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273854 prefixEnd_6273854 := by exact prefixLift 6273854
  have htrace : WordTrace (prefixWord ++ tailWord_6273854) baseStart_6273854 baseEnd_6273854 := by
    simpa [prefixWord, tailWord_6273854, baseEnd_6273854] using wordTrace_append hprefix tailTrace_6273854
  have hstable : (prefixWord ++ tailWord_6273854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273854).length < 2 ^ (prefixWord ++ tailWord_6273854).sum := by decide
  have hdescent : baseEnd_6273854 < baseStart_6273854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273918 : List Nat := [4, 2, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_6273918 : Nat := 118140960795 + 6273918 * 2 ^ 59
def prefixEnd_6273918 : Nat := 4983230072969 + 3 ^ 40 * 6273918 * 2
def baseEnd_6273918 : Nat := 1073845173631629833557261

theorem tailTrace_6273918 : CollatzResearch.WordTrace tailWord_6273918 prefixEnd_6273918 1073845173631629833557261 := by
  unfold tailWord_6273918
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603573560584257591630801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152552392323116040488697605 28603573560584257591630801)
  ·
    refine ⟨21452680170438193193723101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28603573560584257591630801 21452680170438193193723101)
    ·
      refine ⟨8044755063914322447646163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21452680170438193193723101 8044755063914322447646163)
      ·
        refine ⟨12067132595871483671469245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8044755063914322447646163 12067132595871483671469245)
        ·
          refine ⟨4525174723451806376800967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12067132595871483671469245 4525174723451806376800967)
          ·
            refine ⟨6787762085177709565201451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4525174723451806376800967 6787762085177709565201451)
            ·
              refine ⟨10181643127766564347802177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787762085177709565201451 10181643127766564347802177)
              ·
                refine ⟨7636232345824923260851633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10181643127766564347802177 7636232345824923260851633)
                ·
                  refine ⟨5727174259368692445638725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7636232345824923260851633 5727174259368692445638725)
                  ·
                    refine ⟨1073845173631629833557261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727174259368692445638725 1073845173631629833557261)
                    ·
                      rfl

theorem cell23_6273918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_6273918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273918 prefixEnd_6273918 := by exact prefixLift 6273918
  have htrace : WordTrace (prefixWord ++ tailWord_6273918) baseStart_6273918 baseEnd_6273918 := by
    simpa [prefixWord, tailWord_6273918, baseEnd_6273918] using wordTrace_append hprefix tailTrace_6273918
  have hstable : (prefixWord ++ tailWord_6273918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273918).length < 2 ^ (prefixWord ++ tailWord_6273918).sum := by decide
  have hdescent : baseEnd_6273918 < baseStart_6273918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273923 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 4, 6]
def baseStart_6273923 : Nat := 118140960795 + 6273923 * 2 ^ 59
def prefixEnd_6273923 : Nat := 4983230072969 + 3 ^ 40 * 6273923 * 2
def baseEnd_6273923 : Nat := 1073846029432720660369753

theorem tailTrace_6273923 : CollatzResearch.WordTrace tailWord_6273923 prefixEnd_6273923 1073846029432720660369753 := by
  unfold tailWord_6273923
  simp only [CollatzResearch.WordTrace]
  refine ⟨228828770849655946586978423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152552513899770631057985615 228828770849655946586978423)
  ·
    refine ⟨343243156274483919880467635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228828770849655946586978423 343243156274483919880467635)
    ·
      refine ⟨514864734411725879820701453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343243156274483919880467635 514864734411725879820701453)
      ·
        refine ⟨193074275404397204932763045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 514864734411725879820701453 193074275404397204932763045)
        ·
          refine ⟨36201426638324475924893071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193074275404397204932763045 36201426638324475924893071)
          ·
            refine ⟨54302139957486713887339607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36201426638324475924893071 54302139957486713887339607)
            ·
              refine ⟨81453209936230070831009411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54302139957486713887339607 81453209936230070831009411)
              ·
                refine ⟨122179814904345106246514117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81453209936230070831009411 122179814904345106246514117)
                ·
                  refine ⟨22908715294564707421221397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122179814904345106246514117 22908715294564707421221397)
                  ·
                    refine ⟨1073846029432720660369753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22908715294564707421221397 1073846029432720660369753)
                    ·
                      rfl

theorem cell23_6273923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 6].length) (baseStart_6273923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273923 prefixEnd_6273923 := by exact prefixLift 6273923
  have htrace : WordTrace (prefixWord ++ tailWord_6273923) baseStart_6273923 baseEnd_6273923 := by
    simpa [prefixWord, tailWord_6273923, baseEnd_6273923] using wordTrace_append hprefix tailTrace_6273923
  have hstable : (prefixWord ++ tailWord_6273923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273923).length < 2 ^ (prefixWord ++ tailWord_6273923).sum := by decide
  have hdescent : baseEnd_6273923 < baseStart_6273923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273940 : List Nat := [2, 4, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_6273940 : Nat := 118140960795 + 6273940 * 2 ^ 59
def prefixEnd_6273940 : Nat := 4983230072969 + 3 ^ 40 * 6273940 * 2
def baseEnd_6273940 : Nat := 1073848939156429471532227

theorem tailTrace_6273940 : CollatzResearch.WordTrace tailWord_6273940 prefixEnd_6273940 1073848939156429471532227 := by
  unfold tailWord_6273940
  simp only [CollatzResearch.WordTrace]
  refine ⟨114414695445297179245173637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152552927260396238993564849 114414695445297179245173637)
  ·
    refine ⟨21452755395993221108470057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114414695445297179245173637 21452755395993221108470057)
    ·
      refine ⟨16089566546994915831352543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21452755395993221108470057 16089566546994915831352543)
      ·
        refine ⟨24134349820492373747028815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16089566546994915831352543 24134349820492373747028815)
        ·
          refine ⟨36201524730738560620543223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24134349820492373747028815 36201524730738560620543223)
          ·
            refine ⟨54302287096107840930814835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36201524730738560620543223 54302287096107840930814835)
            ·
              refine ⟨81453430644161761396222253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54302287096107840930814835 81453430644161761396222253)
              ·
                refine ⟨30545036491560660523583345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81453430644161761396222253 30545036491560660523583345)
                ·
                  refine ⟨22908777368670495392687509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30545036491560660523583345 22908777368670495392687509)
                  ·
                    refine ⟨1073848939156429471532227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22908777368670495392687509 1073848939156429471532227)
                    ·
                      rfl

theorem cell23_6273940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_6273940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273940 prefixEnd_6273940 := by exact prefixLift 6273940
  have htrace : WordTrace (prefixWord ++ tailWord_6273940) baseStart_6273940 baseEnd_6273940 := by
    simpa [prefixWord, tailWord_6273940, baseEnd_6273940] using wordTrace_append hprefix tailTrace_6273940
  have hstable : (prefixWord ++ tailWord_6273940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273940).length < 2 ^ (prefixWord ++ tailWord_6273940).sum := by decide
  have hdescent : baseEnd_6273940 < baseStart_6273940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273983 : List Nat := [1, 1, 2, 2, 2, 1, 2, 2, 3, 7]
def baseStart_6273983 : Nat := 118140960795 + 6273983 * 2 ^ 59
def prefixEnd_6273983 : Nat := 4983230072969 + 3 ^ 40 * 6273983 * 2
def baseEnd_6273983 : Nat := 1073856299045810582119661

theorem tailTrace_6273983 : CollatzResearch.WordTrace tailWord_6273983 prefixEnd_6273983 1073856299045810582119661 := by
  unfold tailWord_6273983
  simp only [CollatzResearch.WordTrace]
  refine ⟨228830959229438576834162603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152553972819625717889441735 228830959229438576834162603)
  ·
    refine ⟨343246438844157865251243905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228830959229438576834162603 343246438844157865251243905)
    ·
      refine ⟨257434829133118398938432929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343246438844157865251243905 257434829133118398938432929)
      ·
        refine ⟨193076121849838799203824697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257434829133118398938432929 193076121849838799203824697)
        ·
          refine ⟨144807091387379099402868523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193076121849838799203824697 144807091387379099402868523)
          ·
            refine ⟨217210637081068649104302785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144807091387379099402868523 217210637081068649104302785)
            ·
              refine ⟨162907977810801486828227089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217210637081068649104302785 162907977810801486828227089)
              ·
                refine ⟨122180983358101115121170317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162907977810801486828227089 122180983358101115121170317)
                ·
                  refine ⟨45817868759287918170438869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122180983358101115121170317 45817868759287918170438869)
                  ·
                    refine ⟨1073856299045810582119661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45817868759287918170438869 1073856299045810582119661)
                    ·
                      rfl

theorem cell23_6273983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 7].length) (baseStart_6273983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273983 prefixEnd_6273983 := by exact prefixLift 6273983
  have htrace : WordTrace (prefixWord ++ tailWord_6273983) baseStart_6273983 baseEnd_6273983 := by
    simpa [prefixWord, tailWord_6273983, baseEnd_6273983] using wordTrace_append hprefix tailTrace_6273983
  have hstable : (prefixWord ++ tailWord_6273983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273983).length < 2 ^ (prefixWord ++ tailWord_6273983).sum := by decide
  have hdescent : baseEnd_6273983 < baseStart_6273983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6273998 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_6273998 : Nat := 118140960795 + 6273998 * 2 ^ 59
def prefixEnd_6273998 : Nat := 4983230072969 + 3 ^ 40 * 6273998 * 2
def baseEnd_6273998 : Nat := 3221576599347249187671415

theorem tailTrace_6273998 : CollatzResearch.WordTrace tailWord_6273998 prefixEnd_6273998 3221576599347249187671415 := by
  unfold tailWord_6273998
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603938290548029299494831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152554337549589489597305765 28603938290548029299494831)
  ·
    refine ⟨42905907435822043949242247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28603938290548029299494831 42905907435822043949242247)
    ·
      refine ⟨64358861153733065923863371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42905907435822043949242247 64358861153733065923863371)
      ·
        refine ⟨96538291730599598885795057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64358861153733065923863371 96538291730599598885795057)
        ·
          refine ⟨72403718797949699164346293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96538291730599598885795057 72403718797949699164346293)
          ·
            refine ⟨6787848637307784296657465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72403718797949699164346293 6787848637307784296657465)
            ·
              refine ⟨5090886477980838222493099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6787848637307784296657465 5090886477980838222493099)
              ·
                refine ⟨7636329716971257333739649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090886477980838222493099 7636329716971257333739649)
                ·
                  refine ⟨5727247287728443000304737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7636329716971257333739649 5727247287728443000304737)
                  ·
                    refine ⟨4295435465796332250228553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5727247287728443000304737 4295435465796332250228553)
                    ·
                      refine ⟨3221576599347249187671415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295435465796332250228553 3221576599347249187671415)
                      ·
                        rfl

theorem cell23_6273998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_6273998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6273998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6273998 prefixEnd_6273998 := by exact prefixLift 6273998
  have htrace : WordTrace (prefixWord ++ tailWord_6273998) baseStart_6273998 baseEnd_6273998 := by
    simpa [prefixWord, tailWord_6273998, baseEnd_6273998] using wordTrace_append hprefix tailTrace_6273998
  have hstable : (prefixWord ++ tailWord_6273998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6273998).length < 2 ^ (prefixWord ++ tailWord_6273998).sum := by decide
  have hdescent : baseEnd_6273998 < baseStart_6273998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6273998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274040 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_6274040 : Nat := 118140960795 + 6274040 * 2 ^ 59
def prefixEnd_6274040 : Nat := 4983230072969 + 3 ^ 40 * 6274040 * 2
def baseEnd_6274040 : Nat := 3221598165534738023346221

theorem tailTrace_6274040 : CollatzResearch.WordTrace tailWord_6274040 prefixEnd_6274040 3221598165534738023346221 := by
  unfold tailWord_6274040
  simp only [CollatzResearch.WordTrace]
  refine ⟨114416519095116037784493787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152555358793488050379325049 114416519095116037784493787)
  ·
    refine ⟨171624778642674056676740681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114416519095116037784493787 171624778642674056676740681)
    ·
      refine ⟨128718583982005542507555511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171624778642674056676740681 128718583982005542507555511)
      ·
        refine ⟨193077875973008313761333267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128718583982005542507555511 193077875973008313761333267)
        ·
          refine ⟨289616813959512470641999901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193077875973008313761333267 289616813959512470641999901)
          ·
            refine ⟨108606305234817176490749963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289616813959512470641999901 108606305234817176490749963)
            ·
              refine ⟨162909457852225764736124945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108606305234817176490749963 162909457852225764736124945)
              ·
                refine ⟨122182093389169323552093709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162909457852225764736124945 122182093389169323552093709)
                ·
                  refine ⟨45818285020938496332035141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122182093389169323552093709 45818285020938496332035141)
                  ·
                    refine ⟨8590928441425968062256589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45818285020938496332035141 8590928441425968062256589)
                    ·
                      refine ⟨3221598165534738023346221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8590928441425968062256589 3221598165534738023346221)
                      ·
                        rfl

theorem cell23_6274040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_6274040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274040 prefixEnd_6274040 := by exact prefixLift 6274040
  have htrace : WordTrace (prefixWord ++ tailWord_6274040) baseStart_6274040 baseEnd_6274040 := by
    simpa [prefixWord, tailWord_6274040, baseEnd_6274040] using wordTrace_append hprefix tailTrace_6274040
  have hstable : (prefixWord ++ tailWord_6274040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274040).length < 2 ^ (prefixWord ++ tailWord_6274040).sum := by decide
  have hdescent : baseEnd_6274040 < baseStart_6274040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274081 : List Nat := [1, 2, 3, 2, 3, 2, 2, 3, 1, 4]
def baseStart_6274081 : Nat := 118140960795 + 6274081 * 2 ^ 59
def prefixEnd_6274081 : Nat := 4983230072969 + 3 ^ 40 * 6274081 * 2
def baseEnd_6274081 : Nat := 1073873072747190787644511

theorem tailTrace_6274081 : CollatzResearch.WordTrace tailWord_6274081 prefixEnd_6274081 1073873072747190787644511 := by
  unfold tailWord_6274081
  simp only [CollatzResearch.WordTrace]
  refine ⟨228834533583083539571230097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152556355722055693047486731 228834533583083539571230097)
  ·
    refine ⟨171625900187312654678422573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228834533583083539571230097 171625900187312654678422573)
    ·
      refine ⟨64359712570242245504408465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171625900187312654678422573 64359712570242245504408465)
      ·
        refine ⟨48269784427681684128306349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64359712570242245504408465 48269784427681684128306349)
        ·
          refine ⟨18101169160380631548114881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48269784427681684128306349 18101169160380631548114881)
          ·
            refine ⟨13575876870285473661086161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18101169160380631548114881 13575876870285473661086161)
            ·
              refine ⟨10181907652714105245814621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13575876870285473661086161 10181907652714105245814621)
              ·
                refine ⟨3818215369767789467180483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10181907652714105245814621 3818215369767789467180483)
                ·
                  refine ⟨5727323054651684200770725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818215369767789467180483 5727323054651684200770725)
                  ·
                    refine ⟨1073873072747190787644511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727323054651684200770725 1073873072747190787644511)
                    ·
                      rfl

theorem cell23_6274081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_6274081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274081 prefixEnd_6274081 := by exact prefixLift 6274081
  have htrace : WordTrace (prefixWord ++ tailWord_6274081) baseStart_6274081 baseEnd_6274081 := by
    simpa [prefixWord, tailWord_6274081, baseEnd_6274081] using wordTrace_append hprefix tailTrace_6274081
  have hstable : (prefixWord ++ tailWord_6274081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274081).length < 2 ^ (prefixWord ++ tailWord_6274081).sum := by decide
  have hdescent : baseEnd_6274081 < baseStart_6274081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274104 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_6274104 : Nat := 118140960795 + 6274104 * 2 ^ 59
def prefixEnd_6274104 : Nat := 4983230072969 + 3 ^ 40 * 6274104 * 2
def baseEnd_6274104 : Nat := 3221631028296625772945927

theorem tailTrace_6274104 : CollatzResearch.WordTrace tailWord_6274104 prefixEnd_6274104 3221631028296625772945927 := by
  unfold tailWord_6274104
  simp only [CollatzResearch.WordTrace]
  refine ⟨114417686231000107249658683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152556914974666809666211577 114417686231000107249658683)
  ·
    refine ⟨171626529346500160874488025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114417686231000107249658683 171626529346500160874488025)
    ·
      refine ⟨128719897009875120655866019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171626529346500160874488025 128719897009875120655866019)
      ·
        refine ⟨193079845514812680983799029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128719897009875120655866019 193079845514812680983799029)
        ·
          refine ⟨18101235517013688842231159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193079845514812680983799029 18101235517013688842231159)
          ·
            refine ⟨27151853275520533263346739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18101235517013688842231159 27151853275520533263346739)
            ·
              refine ⟨40727779913280799895020109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27151853275520533263346739 40727779913280799895020109)
              ·
                refine ⟨15272917467480299960632541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40727779913280799895020109 15272917467480299960632541)
                ·
                  refine ⟨5727344050305112485237203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15272917467480299960632541 5727344050305112485237203)
                  ·
                    refine ⟨8591016075457668727855805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5727344050305112485237203 8591016075457668727855805)
                    ·
                      refine ⟨3221631028296625772945927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591016075457668727855805 3221631028296625772945927)
                      ·
                        rfl

theorem cell23_6274104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_6274104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274104 prefixEnd_6274104 := by exact prefixLift 6274104
  have htrace : WordTrace (prefixWord ++ tailWord_6274104) baseStart_6274104 baseEnd_6274104 := by
    simpa [prefixWord, tailWord_6274104, baseEnd_6274104] using wordTrace_append hprefix tailTrace_6274104
  have hstable : (prefixWord ++ tailWord_6274104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274104).length < 2 ^ (prefixWord ++ tailWord_6274104).sum := by decide
  have hdescent : baseEnd_6274104 < baseStart_6274104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274147 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3]
def baseStart_6274147 : Nat := 118140960795 + 6274147 * 2 ^ 59
def prefixEnd_6274147 : Nat := 4983230072969 + 3 ^ 40 * 6274147 * 2
def baseEnd_6274147 : Nat := 3221653107964769104708229

theorem tailTrace_6274147 : CollatzResearch.WordTrace tailWord_6274147 prefixEnd_6274147 3221653107964769104708229 := by
  unfold tailWord_6274147
  simp only [CollatzResearch.WordTrace]
  refine ⟨228836940800844432843132695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152557960533896288562088463 228836940800844432843132695)
  ·
    refine ⟨343255411201266649264699043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228836940800844432843132695 343255411201266649264699043)
    ·
      refine ⟨514883116801899973897048565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343255411201266649264699043 514883116801899973897048565)
      ·
        refine ⟨48270292200178122552848303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 514883116801899973897048565 48270292200178122552848303)
        ·
          refine ⟨72405438300267183829272455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48270292200178122552848303 72405438300267183829272455)
          ·
            refine ⟨108608157450400775743908683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72405438300267183829272455 108608157450400775743908683)
            ·
              refine ⟨162912236175601163615863025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108608157450400775743908683 162912236175601163615863025)
              ·
                refine ⟨122184177131700872711897269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162912236175601163615863025 122184177131700872711897269)
                ·
                  refine ⟨11454766606096956816740369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122184177131700872711897269 11454766606096956816740369)
                  ·
                    refine ⟨8591074954572717612555277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11454766606096956816740369 8591074954572717612555277)
                    ·
                      refine ⟨3221653107964769104708229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591074954572717612555277 3221653107964769104708229)
                      ·
                        rfl

theorem cell23_6274147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_6274147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274147 prefixEnd_6274147 := by exact prefixLift 6274147
  have htrace : WordTrace (prefixWord ++ tailWord_6274147) baseStart_6274147 baseEnd_6274147 := by
    simpa [prefixWord, tailWord_6274147, baseEnd_6274147] using wordTrace_append hprefix tailTrace_6274147
  have hstable : (prefixWord ++ tailWord_6274147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274147).length < 2 ^ (prefixWord ++ tailWord_6274147).sum := by decide
  have hdescent : baseEnd_6274147 < baseStart_6274147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274154 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_6274154 : Nat := 118140960795 + 6274154 * 2 ^ 59
def prefixEnd_6274154 : Nat := 4983230072969 + 3 ^ 40 * 6274154 * 2
def baseEnd_6274154 : Nat := 1073885567443116859106899

theorem tailTrace_6274154 : CollatzResearch.WordTrace tailWord_6274154 prefixEnd_6274154 1073885567443116859106899 := by
  unfold tailWord_6274154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57209299027954768259659379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152558130741212715359091677 57209299027954768259659379)
  ·
    refine ⟨85813948541932152389489069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57209299027954768259659379 85813948541932152389489069)
    ·
      refine ⟨32180230703224557146058401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85813948541932152389489069 32180230703224557146058401)
      ·
        refine ⟨24135173027418417859543801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32180230703224557146058401 24135173027418417859543801)
        ·
          refine ⟨18101379770563813394657851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24135173027418417859543801 18101379770563813394657851)
          ·
            refine ⟨27152069655845720091986777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18101379770563813394657851 27152069655845720091986777)
            ·
              refine ⟨20364052241884290068990083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27152069655845720091986777 20364052241884290068990083)
              ·
                refine ⟨30546078362826435103485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20364052241884290068990083 30546078362826435103485125)
                ·
                  refine ⟨5727389693029956581903461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30546078362826435103485125 5727389693029956581903461)
                  ·
                    refine ⟨1073885567443116859106899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5727389693029956581903461 1073885567443116859106899)
                    ·
                      rfl

theorem cell23_6274154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_6274154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274154 prefixEnd_6274154 := by exact prefixLift 6274154
  have htrace : WordTrace (prefixWord ++ tailWord_6274154) baseStart_6274154 baseEnd_6274154 := by
    simpa [prefixWord, tailWord_6274154, baseEnd_6274154] using wordTrace_append hprefix tailTrace_6274154
  have hstable : (prefixWord ++ tailWord_6274154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274154).length < 2 ^ (prefixWord ++ tailWord_6274154).sum := by decide
  have hdescent : baseEnd_6274154 < baseStart_6274154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274157 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6274157 : Nat := 118140960795 + 6274157 * 2 ^ 59
def prefixEnd_6274157 : Nat := 4983230072969 + 3 ^ 40 * 6274157 * 2
def baseEnd_6274157 : Nat := 3221658242771314065583183

theorem tailTrace_6274157 : CollatzResearch.WordTrace tailWord_6274157 prefixEnd_6274157 3221658242771314065583183 := by
  unfold tailWord_6274157
  simp only [CollatzResearch.WordTrace]
  refine ⟨228837305530808204550996725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152558203687205469700664483 228837305530808204550996725)
  ·
    refine ⟨21453497393513269176655943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 228837305530808204550996725 21453497393513269176655943)
    ·
      refine ⟨32180246090269903764983915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21453497393513269176655943 32180246090269903764983915)
      ·
        refine ⟨48270369135404855647475873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32180246090269903764983915 48270369135404855647475873)
        ·
          refine ⟨36202776851553641735606905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48270369135404855647475873 36202776851553641735606905)
          ·
            refine ⟨27152082638665231301705179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36202776851553641735606905 27152082638665231301705179)
            ·
              refine ⟨40728123957997846952557769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27152082638665231301705179 40728123957997846952557769)
              ·
                refine ⟨30546092968498385214418327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40728123957997846952557769 30546092968498385214418327)
                ·
                  refine ⟨45819139452747577821627491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30546092968498385214418327 45819139452747577821627491)
                  ·
                    refine ⟨68728709179121366732441237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45819139452747577821627491 68728709179121366732441237)
                    ·
                      refine ⟨3221658242771314065583183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68728709179121366732441237 3221658242771314065583183)
                      ·
                        rfl

theorem cell23_6274157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6274157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274157 prefixEnd_6274157 := by exact prefixLift 6274157
  have htrace : WordTrace (prefixWord ++ tailWord_6274157) baseStart_6274157 baseEnd_6274157 := by
    simpa [prefixWord, tailWord_6274157, baseEnd_6274157] using wordTrace_append hprefix tailTrace_6274157
  have hstable : (prefixWord ++ tailWord_6274157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274157).length < 2 ^ (prefixWord ++ tailWord_6274157).sum := by decide
  have hdescent : baseEnd_6274157 < baseStart_6274157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274194 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_6274194 : Nat := 118140960795 + 6274194 * 2 ^ 59
def prefixEnd_6274194 : Nat := 4983230072969 + 3 ^ 40 * 6274194 * 2
def baseEnd_6274194 : Nat := 3221677241555530420820513

theorem tailTrace_6274194 : CollatzResearch.WordTrace tailWord_6274194 prefixEnd_6274194 3221677241555530420820513 := by
  unfold tailWord_6274194
  simp only [CollatzResearch.WordTrace]
  refine ⟨57209663757918539967523409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152559103354449439913395757 57209663757918539967523409)
  ·
    refine ⟨42907247818438904975642557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57209663757918539967523409 42907247818438904975642557)
    ·
      refine ⟨16090217931914589365865959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42907247818438904975642557 16090217931914589365865959)
      ·
        refine ⟨24135326897871884048798939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16090217931914589365865959 24135326897871884048798939)
        ·
          refine ⟨36202990346807826073198409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24135326897871884048798939 36202990346807826073198409)
          ·
            refine ⟨27152242760105869554898807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36202990346807826073198409 27152242760105869554898807)
            ·
              refine ⟨40728364140158804332348211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27152242760105869554898807 40728364140158804332348211)
              ·
                refine ⟨61092546210238206498522317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40728364140158804332348211 61092546210238206498522317)
                ·
                  refine ⟨22909704828839327436945869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61092546210238206498522317 22909704828839327436945869)
                  ·
                    refine ⟨8591139310814747788854701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22909704828839327436945869 8591139310814747788854701)
                    ·
                      refine ⟨3221677241555530420820513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591139310814747788854701 3221677241555530420820513)
                      ·
                        rfl

theorem cell23_6274194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_6274194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274194 prefixEnd_6274194 := by exact prefixLift 6274194
  have htrace : WordTrace (prefixWord ++ tailWord_6274194) baseStart_6274194 baseEnd_6274194 := by
    simpa [prefixWord, tailWord_6274194, baseEnd_6274194] using wordTrace_append hprefix tailTrace_6274194
  have hstable : (prefixWord ++ tailWord_6274194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274194).length < 2 ^ (prefixWord ++ tailWord_6274194).sum := by decide
  have hdescent : baseEnd_6274194 < baseStart_6274194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274212 : List Nat := [2, 3, 1, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_6274212 : Nat := 118140960795 + 6274212 * 2 ^ 59
def prefixEnd_6274212 : Nat := 4983230072969 + 3 ^ 40 * 6274212 * 2
def baseEnd_6274212 : Nat := 3221686484207311350395431

theorem tailTrace_6274212 : CollatzResearch.WordTrace tailWord_6274212 prefixEnd_6274212 3221686484207311350395431 := by
  unfold tailWord_6274212
  simp only [CollatzResearch.WordTrace]
  refine ⟨114419655772804474472124445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152559541030405965962832593 114419655772804474472124445)
  ·
    refine ⟨42907370914801677927046667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114419655772804474472124445 42907370914801677927046667)
    ·
      refine ⟨64361056372202516890570001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42907370914801677927046667 64361056372202516890570001)
      ·
        refine ⟨48270792279151887667927501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64361056372202516890570001 48270792279151887667927501)
        ·
          refine ⟨18101547104681957875472813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48270792279151887667927501 18101547104681957875472813)
          ·
            refine ⟨6788080164255734203302305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18101547104681957875472813 6788080164255734203302305)
            ·
              refine ⟨5091060123191800652476729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6788080164255734203302305 5091060123191800652476729)
              ·
                refine ⟨3818295092393850489357547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091060123191800652476729 3818295092393850489357547)
                ·
                  refine ⟨5727442638590775734036321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818295092393850489357547 5727442638590775734036321)
                  ·
                    refine ⟨4295581978943081800527241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5727442638590775734036321 4295581978943081800527241)
                    ·
                      refine ⟨3221686484207311350395431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295581978943081800527241 3221686484207311350395431)
                      ·
                        rfl

theorem cell23_6274212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_6274212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274212 prefixEnd_6274212 := by exact prefixLift 6274212
  have htrace : WordTrace (prefixWord ++ tailWord_6274212) baseStart_6274212 baseEnd_6274212 := by
    simpa [prefixWord, tailWord_6274212, baseEnd_6274212] using wordTrace_append hprefix tailTrace_6274212
  have hstable : (prefixWord ++ tailWord_6274212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274212).length < 2 ^ (prefixWord ++ tailWord_6274212).sum := by decide
  have hdescent : baseEnd_6274212 < baseStart_6274212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274237 : List Nat := [1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 5]
def baseStart_6274237 : Nat := 118140960795 + 6274237 * 2 ^ 59
def prefixEnd_6274237 : Nat := 4983230072969 + 3 ^ 40 * 6274237 * 2
def baseEnd_6274237 : Nat := 3221699321223673752582815

theorem tailTrace_6274237 : CollatzResearch.WordTrace tailWord_6274237 prefixEnd_6274237 3221699321223673752582815 := by
  unfold tailWord_6274237
  simp only [CollatzResearch.WordTrace]
  refine ⟨228840223370518378213908965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152560148913678918809272643 228840223370518378213908965)
  ·
    refine ⟨42907541881972195915107931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228840223370518378213908965 42907541881972195915107931)
    ·
      refine ⟨64361312822958293872661897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42907541881972195915107931 64361312822958293872661897)
      ·
        refine ⟨48270984617218720404496423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64361312822958293872661897 48270984617218720404496423)
        ·
          refine ⟨72406476925828080606744635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48270984617218720404496423 72406476925828080606744635)
          ·
            refine ⟨108609715388742120910116953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72406476925828080606744635 108609715388742120910116953)
            ·
              refine ⟨81457286541556590682587715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108609715388742120910116953 81457286541556590682587715)
              ·
                refine ⟨122185929812334886023881573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81457286541556590682587715 122185929812334886023881573)
                ·
                  refine ⟨22909861839812791129477795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122185929812334886023881573 22909861839812791129477795)
                  ·
                    refine ⟨34364792759719186694216693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22909861839812791129477795 34364792759719186694216693)
                    ·
                      refine ⟨3221699321223673752582815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34364792759719186694216693 3221699321223673752582815)
                      ·
                        rfl

theorem cell23_6274237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_6274237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274237 prefixEnd_6274237 := by exact prefixLift 6274237
  have htrace : WordTrace (prefixWord ++ tailWord_6274237) baseStart_6274237 baseEnd_6274237 := by
    simpa [prefixWord, tailWord_6274237, baseEnd_6274237] using wordTrace_append hprefix tailTrace_6274237
  have hstable : (prefixWord ++ tailWord_6274237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274237).length < 2 ^ (prefixWord ++ tailWord_6274237).sum := by decide
  have hdescent : baseEnd_6274237 < baseStart_6274237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274246 : List Nat := [6, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6274246 : Nat := 118140960795 + 6274246 * 2 ^ 59
def prefixEnd_6274246 : Nat := 4983230072969 + 3 ^ 40 * 6274246 * 2
def baseEnd_6274246 : Nat := 3221703942549564217370275

theorem tailTrace_6274246 : CollatzResearch.WordTrace tailWord_6274246 prefixEnd_6274246 3221703942549564217370275 := by
  unfold tailWord_6274246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7151267238358930398468331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 152560367751657181833991061 7151267238358930398468331)
  ·
    refine ⟨10726900857538395597702497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7151267238358930398468331 10726900857538395597702497)
    ·
      refine ⟨8045175643153796698276873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10726900857538395597702497 8045175643153796698276873)
      ·
        refine ⟨6033881732365347523707655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045175643153796698276873 6033881732365347523707655)
        ·
          refine ⟨9050822598548021285561483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033881732365347523707655 9050822598548021285561483)
          ·
            refine ⟨13576233897822031928342225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9050822598548021285561483 13576233897822031928342225)
            ·
              refine ⟨10182175423366523946256669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13576233897822031928342225 10182175423366523946256669)
              ·
                refine ⟨3818315783762446479846251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10182175423366523946256669 3818315783762446479846251)
                ·
                  refine ⟨5727473675643669719769377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818315783762446479846251 5727473675643669719769377)
                  ·
                    refine ⟨4295605256732752289827033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5727473675643669719769377 4295605256732752289827033)
                    ·
                      refine ⟨3221703942549564217370275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295605256732752289827033 3221703942549564217370275)
                      ·
                        rfl

theorem cell23_6274246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6274246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274246 prefixEnd_6274246 := by exact prefixLift 6274246
  have htrace : WordTrace (prefixWord ++ tailWord_6274246) baseStart_6274246 baseEnd_6274246 := by
    simpa [prefixWord, tailWord_6274246, baseEnd_6274246] using wordTrace_append hprefix tailTrace_6274246
  have hstable : (prefixWord ++ tailWord_6274246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274246).length < 2 ^ (prefixWord ++ tailWord_6274246).sum := by decide
  have hdescent : baseEnd_6274246 < baseStart_6274246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274262 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6274262 : Nat := 118140960795 + 6274262 * 2 ^ 59
def prefixEnd_6274262 : Nat := 4983230072969 + 3 ^ 40 * 6274262 * 2
def baseEnd_6274262 : Nat := 3221712158240036154770201

theorem tailTrace_6274262 : CollatzResearch.WordTrace tailWord_6274262 prefixEnd_6274262 3221712158240036154770201 := by
  unfold tailWord_6274262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302570949714237967723065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152560756796951871655712693 14302570949714237967723065)
  ·
    refine ⟨10726928212285678475792299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14302570949714237967723065 10726928212285678475792299)
    ·
      refine ⟨16090392318428517713688449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726928212285678475792299 16090392318428517713688449)
      ·
        refine ⟨12067794238821388285266337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16090392318428517713688449 12067794238821388285266337)
        ·
          refine ⟨9050845679116041213949753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12067794238821388285266337 9050845679116041213949753)
          ·
            refine ⟨6788134259337030910462315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9050845679116041213949753 6788134259337030910462315)
            ·
              refine ⟨10182201389005546365693473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788134259337030910462315 10182201389005546365693473)
              ·
                refine ⟨7636651041754159774270105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10182201389005546365693473 7636651041754159774270105)
                ·
                  refine ⟨5727488281315619830702579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7636651041754159774270105 5727488281315619830702579)
                  ·
                    refine ⟨8591232421973429746053869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5727488281315619830702579 8591232421973429746053869)
                    ·
                      refine ⟨3221712158240036154770201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591232421973429746053869 3221712158240036154770201)
                      ·
                        rfl

theorem cell23_6274262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6274262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274262 prefixEnd_6274262 := by exact prefixLift 6274262
  have htrace : WordTrace (prefixWord ++ tailWord_6274262) baseStart_6274262 baseEnd_6274262 := by
    simpa [prefixWord, tailWord_6274262, baseEnd_6274262] using wordTrace_append hprefix tailTrace_6274262
  have hstable : (prefixWord ++ tailWord_6274262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274262).length < 2 ^ (prefixWord ++ tailWord_6274262).sum := by decide
  have hdescent : baseEnd_6274262 < baseStart_6274262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274284 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_6274284 : Nat := 118140960795 + 6274284 * 2 ^ 59
def prefixEnd_6274284 : Nat := 4983230072969 + 3 ^ 40 * 6274284 * 2
def baseEnd_6274284 : Nat := 3221723454814435068695099

theorem tailTrace_6274284 : CollatzResearch.WordTrace tailWord_6274284 prefixEnd_6274284 3221723454814435068695099 := by
  unfold tailWord_6274284
  simp only [CollatzResearch.WordTrace]
  refine ⟨114420968800674052620434953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152561291734232070160579937 114420968800674052620434953)
  ·
    refine ⟨85815726600505539465326215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114420968800674052620434953 85815726600505539465326215)
    ·
      refine ⟨128723589900758309197989323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85815726600505539465326215 128723589900758309197989323)
      ·
        refine ⟨193085384851137463796983985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128723589900758309197989323 193085384851137463796983985)
        ·
          refine ⟨144814038638353097847737989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193085384851137463796983985 144814038638353097847737989)
          ·
            refine ⟨27152632244691205846450873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144814038638353097847737989 27152632244691205846450873)
            ·
              refine ⟨20364474183518404384838155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27152632244691205846450873 20364474183518404384838155)
              ·
                refine ⟨30546711275277606577257233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20364474183518404384838155 30546711275277606577257233)
                ·
                  refine ⟨22910033456458204932942925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30546711275277606577257233 22910033456458204932942925)
                  ·
                    refine ⟨8591262546171826849853597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22910033456458204932942925 8591262546171826849853597)
                    ·
                      refine ⟨3221723454814435068695099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591262546171826849853597 3221723454814435068695099)
                      ·
                        rfl

theorem cell23_6274284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_6274284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274284 prefixEnd_6274284 := by exact prefixLift 6274284
  have htrace : WordTrace (prefixWord ++ tailWord_6274284) baseStart_6274284 baseEnd_6274284 := by
    simpa [prefixWord, tailWord_6274284, baseEnd_6274284] using wordTrace_append hprefix tailTrace_6274284
  have hstable : (prefixWord ++ tailWord_6274284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274284).length < 2 ^ (prefixWord ++ tailWord_6274284).sum := by decide
  have hdescent : baseEnd_6274284 < baseStart_6274284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274308 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 5]
def baseStart_6274308 : Nat := 118140960795 + 6274308 * 2 ^ 59
def prefixEnd_6274308 : Nat := 4983230072969 + 3 ^ 40 * 6274308 * 2
def baseEnd_6274308 : Nat := 357970642038904774977221

theorem tailTrace_6274308 : CollatzResearch.WordTrace tailWord_6274308 prefixEnd_6274308 357970642038904774977221 := by
  unfold tailWord_6274308
  simp only [CollatzResearch.WordTrace]
  refine ⟨114421406476630578669871789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152561875302174104893162385 114421406476630578669871789)
  ·
    refine ⟨42908027428736467001201921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114421406476630578669871789 42908027428736467001201921)
    ·
      refine ⟨32181020571552350250901441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42908027428736467001201921 32181020571552350250901441)
      ·
        refine ⟨24135765428664262688176081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32181020571552350250901441 24135765428664262688176081)
        ·
          refine ⟨18101824071498197016132061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24135765428664262688176081 18101824071498197016132061)
          ·
            refine ⟨6788184026811823881049523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18101824071498197016132061 6788184026811823881049523)
            ·
              refine ⟨10182276040217735821574285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788184026811823881049523 10182276040217735821574285)
              ·
                refine ⟨3818353515081650933090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10182276040217735821574285 3818353515081650933090357)
                ·
                  refine ⟨357970642038904774977221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818353515081650933090357 357970642038904774977221)
                  ·
                    rfl

theorem cell23_6274308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_6274308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274308 prefixEnd_6274308 := by exact prefixLift 6274308
  have htrace : WordTrace (prefixWord ++ tailWord_6274308) baseStart_6274308 baseEnd_6274308 := by
    simpa [prefixWord, tailWord_6274308, baseEnd_6274308] using wordTrace_append hprefix tailTrace_6274308
  have hstable : (prefixWord ++ tailWord_6274308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274308).length < 2 ^ (prefixWord ++ tailWord_6274308).sum := by decide
  have hdescent : baseEnd_6274308 < baseStart_6274308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274394 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_6274394 : Nat := 118140960795 + 6274394 * 2 ^ 59
def prefixEnd_6274394 : Nat := 4983230072969 + 3 ^ 40 * 6274394 * 2
def baseEnd_6274394 : Nat := 1073926645895476546106531

theorem tailTrace_6274394 : CollatzResearch.WordTrace tailWord_6274394 prefixEnd_6274394 1073926645895476546106531 := by
  unfold tailWord_6274394
  simp only [CollatzResearch.WordTrace]
  refine ⟨57211487407737398506843559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 152563966420633062684916157 57211487407737398506843559)
  ·
    refine ⟨85817231111606097760265339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57211487407737398506843559 85817231111606097760265339)
    ·
      refine ⟨128725846667409146640398009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85817231111606097760265339 128725846667409146640398009)
      ·
        refine ⟨96544385000556859980298507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128725846667409146640398009 96544385000556859980298507)
        ·
          refine ⟨144816577500835289970447761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96544385000556859980298507 144816577500835289970447761)
          ·
            refine ⟨108612433125626467477835821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144816577500835289970447761 108612433125626467477835821)
            ·
              refine ⟨40729662422109925304188433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108612433125626467477835821 40729662422109925304188433)
              ·
                refine ⟨30547246816582443978141325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40729662422109925304188433 30547246816582443978141325)
                ·
                  refine ⟨11455217556218416491802997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30547246816582443978141325 11455217556218416491802997)
                  ·
                    refine ⟨1073926645895476546106531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11455217556218416491802997 1073926645895476546106531)
                    ·
                      rfl

theorem cell23_6274394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_6274394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274394 prefixEnd_6274394 := by exact prefixLift 6274394
  have htrace : WordTrace (prefixWord ++ tailWord_6274394) baseStart_6274394 baseEnd_6274394 := by
    simpa [prefixWord, tailWord_6274394, baseEnd_6274394] using wordTrace_append hprefix tailTrace_6274394
  have hstable : (prefixWord ++ tailWord_6274394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274394).length < 2 ^ (prefixWord ++ tailWord_6274394).sum := by decide
  have hdescent : baseEnd_6274394 < baseStart_6274394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274401 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_6274401 : Nat := 118140960795 + 6274401 * 2 ^ 59
def prefixEnd_6274401 : Nat := 4983230072969 + 3 ^ 40 * 6274401 * 2
def baseEnd_6274401 : Nat := 3221783532051011110932061

theorem tailTrace_6274401 : CollatzResearch.WordTrace tailWord_6274401 prefixEnd_6274401 3221783532051011110932061 := by
  unfold tailWord_6274401
  simp only [CollatzResearch.WordTrace]
  refine ⟨228846204941924234222879057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152564136627949489481919371 228846204941924234222879057)
  ·
    refine ⟨171634653706443175667159293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228846204941924234222879057 171634653706443175667159293)
    ·
      refine ⟨64362995139916190875184735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 171634653706443175667159293 64362995139916190875184735)
      ·
        refine ⟨96544492709874286312777103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64362995139916190875184735 96544492709874286312777103)
        ·
          refine ⟨144816739064811429469165655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96544492709874286312777103 144816739064811429469165655)
          ·
            refine ⟨217225108597217144203748483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 144816739064811429469165655 217225108597217144203748483)
            ·
              refine ⟨325837662895825716305622725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217225108597217144203748483 325837662895825716305622725)
              ·
                refine ⟨61094561792967321807304261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 325837662895825716305622725 61094561792967321807304261)
                ·
                  refine ⟨11455230336181372838869549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61094561792967321807304261 11455230336181372838869549)
                  ·
                    refine ⟨4295711376068014814576081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11455230336181372838869549 4295711376068014814576081)
                    ·
                      refine ⟨3221783532051011110932061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295711376068014814576081 3221783532051011110932061)
                      ·
                        rfl

theorem cell23_6274401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_6274401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274401 prefixEnd_6274401 := by exact prefixLift 6274401
  have htrace : WordTrace (prefixWord ++ tailWord_6274401) baseStart_6274401 baseEnd_6274401 := by
    simpa [prefixWord, tailWord_6274401, baseEnd_6274401] using wordTrace_append hprefix tailTrace_6274401
  have hstable : (prefixWord ++ tailWord_6274401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274401).length < 2 ^ (prefixWord ++ tailWord_6274401).sum := by decide
  have hdescent : baseEnd_6274401 < baseStart_6274401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274444 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6274444 : Nat := 118140960795 + 6274444 * 2 ^ 59
def prefixEnd_6274444 : Nat := 4983230072969 + 3 ^ 40 * 6274444 * 2
def baseEnd_6274444 : Nat := 3221805611719154442694363

theorem tailTrace_6274444 : CollatzResearch.WordTrace tailWord_6274444 prefixEnd_6274444 3221805611719154442694363 := by
  unfold tailWord_6274444
  simp only [CollatzResearch.WordTrace]
  refine ⟨114423886640384226283347193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152565182187178968377796257 114423886640384226283347193)
  ·
    refine ⟨85817914980288169712510395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114423886640384226283347193 85817914980288169712510395)
    ·
      refine ⟨128726872470432254568765593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85817914980288169712510395 128726872470432254568765593)
      ·
        refine ⟨96545154352824190926574195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128726872470432254568765593 96545154352824190926574195)
        ·
          refine ⟨144817731529236286389861293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96545154352824190926574195 144817731529236286389861293)
          ·
            refine ⟨54306649323463607396197985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144817731529236286389861293 54306649323463607396197985)
            ·
              refine ⟨40729986992597705547148489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54306649323463607396197985 40729986992597705547148489)
              ·
                refine ⟨30547490244448279160361367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40729986992597705547148489 30547490244448279160361367)
                ·
                  refine ⟨45821235366672418740542051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30547490244448279160361367 45821235366672418740542051)
                  ·
                    refine ⟨68731853050008628110813077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45821235366672418740542051 68731853050008628110813077)
                    ·
                      refine ⟨3221805611719154442694363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68731853050008628110813077 3221805611719154442694363)
                      ·
                        rfl

theorem cell23_6274444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6274444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274444 prefixEnd_6274444 := by exact prefixLift 6274444
  have htrace : WordTrace (prefixWord ++ tailWord_6274444) baseStart_6274444 baseEnd_6274444 := by
    simpa [prefixWord, tailWord_6274444, baseEnd_6274444] using wordTrace_append hprefix tailTrace_6274444
  have hstable : (prefixWord ++ tailWord_6274444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274444).length < 2 ^ (prefixWord ++ tailWord_6274444).sum := by decide
  have hdescent : baseEnd_6274444 < baseStart_6274444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274461 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 6]
def baseStart_6274461 : Nat := 118140960795 + 6274461 * 2 ^ 59
def prefixEnd_6274461 : Nat := 4983230072969 + 3 ^ 40 * 6274461 * 2
def baseEnd_6274461 : Nat := 3221814340890280876181785

theorem tailTrace_6274461 : CollatzResearch.WordTrace tailWord_6274461 prefixEnd_6274461 3221814340890280876181785 := by
  unfold tailWord_6274461
  simp only [CollatzResearch.WordTrace]
  refine ⟨228848393321706864470063237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152565595547804576313375491 228848393321706864470063237)
  ·
    refine ⟨42909073747820037088136857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228848393321706864470063237 42909073747820037088136857)
    ·
      refine ⟨32181805310865027816102643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42909073747820037088136857 32181805310865027816102643)
      ·
        refine ⟨48272707966297541724153965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32181805310865027816102643 48272707966297541724153965)
        ·
          refine ⟨18102265487361578146557737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48272707966297541724153965 18102265487361578146557737)
          ·
            refine ⟨13576699115521183609918303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18102265487361578146557737 13576699115521183609918303)
            ·
              refine ⟨20365048673281775414877455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13576699115521183609918303 20365048673281775414877455)
              ·
                refine ⟨30547573009922663122316183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20365048673281775414877455 30547573009922663122316183)
                ·
                  refine ⟨45821359514883994683474275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30547573009922663122316183 45821359514883994683474275)
                  ·
                    refine ⟨68732039272325992025211413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45821359514883994683474275 68732039272325992025211413)
                    ·
                      refine ⟨3221814340890280876181785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68732039272325992025211413 3221814340890280876181785)
                      ·
                        rfl

theorem cell23_6274461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_6274461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274461 prefixEnd_6274461 := by exact prefixLift 6274461
  have htrace : WordTrace (prefixWord ++ tailWord_6274461) baseStart_6274461 baseEnd_6274461 := by
    simpa [prefixWord, tailWord_6274461, baseEnd_6274461] using wordTrace_append hprefix tailTrace_6274461
  have hstable : (prefixWord ++ tailWord_6274461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274461).length < 2 ^ (prefixWord ++ tailWord_6274461).sum := by decide
  have hdescent : baseEnd_6274461 < baseStart_6274461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274481 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6274481 : Nat := 118140960795 + 6274481 * 2 ^ 59
def prefixEnd_6274481 : Nat := 4983230072969 + 3 ^ 40 * 6274481 * 2
def baseEnd_6274481 : Nat := 3221824610503370797931693

theorem tailTrace_6274481 : CollatzResearch.WordTrace tailWord_6274481 prefixEnd_6274481 3221824610503370797931693 := by
  unfold tailWord_6274481
  simp only [CollatzResearch.WordTrace]
  refine ⟨228849122781634407885791297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152566081854422938590527531 228849122781634407885791297)
  ·
    refine ⟨171636842086225805914343473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228849122781634407885791297 171636842086225805914343473)
    ·
      refine ⟨128727631564669354435757605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171636842086225805914343473 128727631564669354435757605)
      ·
        refine ⟨24136430918375503956704551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128727631564669354435757605 24136430918375503956704551)
        ·
          refine ⟨36204646377563255935056827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24136430918375503956704551 36204646377563255935056827)
          ·
            refine ⟨54306969566344883902585241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36204646377563255935056827 54306969566344883902585241)
            ·
              refine ⟨40730227174758662926938931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54306969566344883902585241 40730227174758662926938931)
              ·
                refine ⟨61095340762137994390408397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40730227174758662926938931 61095340762137994390408397)
                ·
                  refine ⟨22910752785801747896403149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61095340762137994390408397 22910752785801747896403149)
                  ·
                    refine ⟨8591532294675655461151181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22910752785801747896403149 8591532294675655461151181)
                    ·
                      refine ⟨3221824610503370797931693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591532294675655461151181 3221824610503370797931693)
                      ·
                        rfl

theorem cell23_6274481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6274481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274481 prefixEnd_6274481 := by exact prefixLift 6274481
  have htrace : WordTrace (prefixWord ++ tailWord_6274481) baseStart_6274481 baseEnd_6274481 := by
    simpa [prefixWord, tailWord_6274481, baseEnd_6274481] using wordTrace_append hprefix tailTrace_6274481
  have hstable : (prefixWord ++ tailWord_6274481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274481).length < 2 ^ (prefixWord ++ tailWord_6274481).sum := by decide
  have hdescent : baseEnd_6274481 < baseStart_6274481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274525 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 3, 3, 2]
def baseStart_6274525 : Nat := 118140960795 + 6274525 * 2 ^ 59
def prefixEnd_6274525 : Nat := 4983230072969 + 3 ^ 40 * 6274525 * 2
def baseEnd_6274525 : Nat := 3221847203652168625781491

theorem tailTrace_6274525 : CollatzResearch.WordTrace tailWord_6274525 prefixEnd_6274525 3221847203652168625781491 := by
  unfold tailWord_6274525
  simp only [CollatzResearch.WordTrace]
  refine ⟨228850727593475003400393029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152567151728983335600262019 228850727593475003400393029)
  ·
    refine ⟨42909511423776563137573693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 228850727593475003400393029 42909511423776563137573693)
    ·
      refine ⟨16091066783916211176590135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42909511423776563137573693 16091066783916211176590135)
      ·
        refine ⟨24136600175874316764885203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16091066783916211176590135 24136600175874316764885203)
        ·
          refine ⟨36204900263811475147327805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24136600175874316764885203 36204900263811475147327805)
          ·
            refine ⟨13576837598929303180247927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36204900263811475147327805 13576837598929303180247927)
            ·
              refine ⟨20365256398393954770371891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13576837598929303180247927 20365256398393954770371891)
              ·
                refine ⟨30547884597590932155557837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20365256398393954770371891 30547884597590932155557837)
                ·
                  refine ⟨11455456724096599558334189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30547884597590932155557837 11455456724096599558334189)
                  ·
                    refine ⟨4295796271536224834375321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11455456724096599558334189 4295796271536224834375321)
                    ·
                      refine ⟨3221847203652168625781491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295796271536224834375321 3221847203652168625781491)
                      ·
                        rfl

theorem cell23_6274525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_6274525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274525 prefixEnd_6274525 := by exact prefixLift 6274525
  have htrace : WordTrace (prefixWord ++ tailWord_6274525) baseStart_6274525 baseEnd_6274525 := by
    simpa [prefixWord, tailWord_6274525, baseEnd_6274525] using wordTrace_append hprefix tailTrace_6274525
  have hstable : (prefixWord ++ tailWord_6274525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274525).length < 2 ^ (prefixWord ++ tailWord_6274525).sum := by decide
  have hdescent : baseEnd_6274525 < baseStart_6274525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274542 : List Nat := [4, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_6274542 : Nat := 118140960795 + 6274542 * 2 ^ 59
def prefixEnd_6274542 : Nat := 4983230072969 + 3 ^ 40 * 6274542 * 2
def baseEnd_6274542 : Nat := 3221855932823295059268913

theorem tailTrace_6274542 : CollatzResearch.WordTrace tailWord_6274542 prefixEnd_6274542 3221855932823295059268913 := by
  unfold tailWord_6274542
  simp only [CollatzResearch.WordTrace]
  refine ⟨28606418454301676912970235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 152567565089608943535841253 28606418454301676912970235)
  ·
    refine ⟨42909627681452515369455353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28606418454301676912970235 42909627681452515369455353)
    ·
      refine ⟨32182220761089386527091515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42909627681452515369455353 32182220761089386527091515)
      ·
        refine ⟨48273331141634079790637273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32182220761089386527091515 48273331141634079790637273)
        ·
          refine ⟨36204998356225559842977955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48273331141634079790637273 36204998356225559842977955)
          ·
            refine ⟨54307497534338339764466933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36204998356225559842977955 54307497534338339764466933)
            ·
              refine ⟨5091327893844219352918775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54307497534338339764466933 5091327893844219352918775)
              ·
                refine ⟨7636991840766329029378163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091327893844219352918775 7636991840766329029378163)
                ·
                  refine ⟨11455487761149493544067245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7636991840766329029378163 11455487761149493544067245)
                  ·
                    refine ⟨4295807910431060079025217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11455487761149493544067245 4295807910431060079025217)
                    ·
                      refine ⟨3221855932823295059268913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4295807910431060079025217 3221855932823295059268913)
                      ·
                        rfl

theorem cell23_6274542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_6274542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274542 prefixEnd_6274542 := by exact prefixLift 6274542
  have htrace : WordTrace (prefixWord ++ tailWord_6274542) baseStart_6274542 baseEnd_6274542 := by
    simpa [prefixWord, tailWord_6274542, baseEnd_6274542] using wordTrace_append hprefix tailTrace_6274542
  have hstable : (prefixWord ++ tailWord_6274542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274542).length < 2 ^ (prefixWord ++ tailWord_6274542).sum := by decide
  have hdescent : baseEnd_6274542 < baseStart_6274542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274595 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 5]
def baseStart_6274595 : Nat := 118140960795 + 6274595 * 2 ^ 59
def prefixEnd_6274595 : Nat := 4983230072969 + 3 ^ 40 * 6274595 * 2
def baseEnd_6274595 : Nat := 357987016366442594656241

theorem tailTrace_6274595 : CollatzResearch.WordTrace tailWord_6274595 prefixEnd_6274595 357987016366442594656241 := by
  unfold tailWord_6274595
  simp only [CollatzResearch.WordTrace]
  refine ⟨228853280703221405355441239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152568853802147603570294159 228853280703221405355441239)
  ·
    refine ⟨343279921054832108033161859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228853280703221405355441239 343279921054832108033161859)
    ·
      refine ⟨514919881582248162049742789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343279921054832108033161859 514919881582248162049742789)
      ·
        refine ⟨96547477796671530384326773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 514919881582248162049742789 96547477796671530384326773)
        ·
          refine ⟨9051326043437955973530635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96547477796671530384326773 9051326043437955973530635)
          ·
            refine ⟨13576989065156933960295953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9051326043437955973530635 13576989065156933960295953)
            ·
              refine ⟨10182741798867700470221965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13576989065156933960295953 10182741798867700470221965)
              ·
                refine ⟨3818528174575387676333237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10182741798867700470221965 3818528174575387676333237)
                ·
                  refine ⟨357987016366442594656241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818528174575387676333237 357987016366442594656241)
                  ·
                    rfl

theorem cell23_6274595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 5].length) (baseStart_6274595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274595 prefixEnd_6274595 := by exact prefixLift 6274595
  have htrace : WordTrace (prefixWord ++ tailWord_6274595) baseStart_6274595 baseEnd_6274595 := by
    simpa [prefixWord, tailWord_6274595, baseEnd_6274595] using wordTrace_append hprefix tailTrace_6274595
  have hstable : (prefixWord ++ tailWord_6274595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274595).length < 2 ^ (prefixWord ++ tailWord_6274595).sum := by decide
  have hdescent : baseEnd_6274595 < baseStart_6274595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274641 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_6274641 : Nat := 118140960795 + 6274641 * 2 ^ 59
def prefixEnd_6274641 : Nat := 4983230072969 + 3 ^ 40 * 6274641 * 2
def baseEnd_6274641 : Nat := 3221906767408090171930957

theorem tailTrace_6274641 : CollatzResearch.WordTrace tailWord_6274641 prefixEnd_6274641 3221906767408090171930957 := by
  unfold tailWord_6274641
  simp only [CollatzResearch.WordTrace]
  refine ⟨228854958461054755211615777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 152569972307369836807743851 228854958461054755211615777)
  ·
    refine ⟨171641218845791066408711833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 228854958461054755211615777 171641218845791066408711833)
    ·
      refine ⟨128730914134343299806533875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171641218845791066408711833 128730914134343299806533875)
      ·
        refine ⟨193096371201514949709800813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128730914134343299806533875 193096371201514949709800813)
        ·
          refine ⟨72411139200568106141175305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193096371201514949709800813 72411139200568106141175305)
          ·
            refine ⟨54308354400426079605881479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72411139200568106141175305 54308354400426079605881479)
            ·
              refine ⟨81462531600639119408822219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54308354400426079605881479 81462531600639119408822219)
              ·
                refine ⟨122193797400958679113233329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81462531600639119408822219 122193797400958679113233329)
                ·
                  refine ⟨91645348050719009334924997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122193797400958679113233329 91645348050719009334924997)
                  ·
                    refine ⟨17183502759509814250298437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91645348050719009334924997 17183502759509814250298437)
                    ·
                      refine ⟨3221906767408090171930957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17183502759509814250298437 3221906767408090171930957)
                      ·
                        rfl

theorem cell23_6274641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_6274641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274641 prefixEnd_6274641 := by exact prefixLift 6274641
  have htrace : WordTrace (prefixWord ++ tailWord_6274641) baseStart_6274641 baseEnd_6274641 := by
    simpa [prefixWord, tailWord_6274641, baseEnd_6274641] using wordTrace_append hprefix tailTrace_6274641
  have hstable : (prefixWord ++ tailWord_6274641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274641).length < 2 ^ (prefixWord ++ tailWord_6274641).sum := by decide
  have hdescent : baseEnd_6274641 < baseStart_6274641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274646 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_6274646 : Nat := 118140960795 + 6274646 * 2 ^ 59
def prefixEnd_6274646 : Nat := 4983230072969 + 3 ^ 40 * 6274646 * 2
def baseEnd_6274646 : Nat := 357989926090151405818715

theorem tailTrace_6274646 : CollatzResearch.WordTrace tailWord_6274646 prefixEnd_6274646 357989926090151405818715 := by
  unfold tailWord_6274646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303446301627290066596737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 152570093884024427377031861 14303446301627290066596737)
  ·
    refine ⟨10727584726220467549947553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14303446301627290066596737 10727584726220467549947553)
    ·
      refine ⟨8045688544665350662460665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727584726220467549947553 8045688544665350662460665)
      ·
        refine ⟨6034266408499012996845499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045688544665350662460665 6034266408499012996845499)
        ·
          refine ⟨9051399612748519495268249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034266408499012996845499 9051399612748519495268249)
          ·
            refine ⟨6788549709561389621451187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9051399612748519495268249 6788549709561389621451187)
            ·
              refine ⟨10182824564342084432176781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788549709561389621451187 10182824564342084432176781)
              ·
                refine ⟨3818559211628281662066293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10182824564342084432176781 3818559211628281662066293)
                ·
                  refine ⟨357989926090151405818715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3818559211628281662066293 357989926090151405818715)
                  ·
                    rfl

theorem cell23_6274646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_6274646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274646 prefixEnd_6274646 := by exact prefixLift 6274646
  have htrace : WordTrace (prefixWord ++ tailWord_6274646) baseStart_6274646 baseEnd_6274646 := by
    simpa [prefixWord, tailWord_6274646, baseEnd_6274646] using wordTrace_append hprefix tailTrace_6274646
  have hstable : (prefixWord ++ tailWord_6274646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274646).length < 2 ^ (prefixWord ++ tailWord_6274646).sum := by decide
  have hdescent : baseEnd_6274646 < baseStart_6274646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6274648 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_6274648 : Nat := 118140960795 + 6274648 * 2 ^ 59
def prefixEnd_6274648 : Nat := 4983230072969 + 3 ^ 40 * 6274648 * 2
def baseEnd_6274648 : Nat := 3221910361772671644543425

theorem tailTrace_6274648 : CollatzResearch.WordTrace tailWord_6274648 prefixEnd_6274648 3221910361772671644543425 := by
  unfold tailWord_6274648
  simp only [CollatzResearch.WordTrace]
  refine ⟨114427606886014697703560299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 152570142514686263604747065 114427606886014697703560299)
  ·
    refine ⟨171641410329022046555340449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114427606886014697703560299 171641410329022046555340449)
    ·
      refine ⟨128731057746766534916505337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 171641410329022046555340449 128731057746766534916505337)
      ·
        refine ⟨96548293310074901187379003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128731057746766534916505337 96548293310074901187379003)
        ·
          refine ⟨144822439965112351781068505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96548293310074901187379003 144822439965112351781068505)
          ·
            refine ⟨108616829973834263835801379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144822439965112351781068505 108616829973834263835801379)
            ·
              refine ⟨162925244960751395753702069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108616829973834263835801379 162925244960751395753702069)
              ·
                refine ⟨15274241715070443351909569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 162925244960751395753702069 15274241715070443351909569)
                ·
                  refine ⟨11455681286302832513932177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15274241715070443351909569 11455681286302832513932177)
                  ·
                    refine ⟨8591760964727124385449133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11455681286302832513932177 8591760964727124385449133)
                    ·
                      refine ⟨3221910361772671644543425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8591760964727124385449133 3221910361772671644543425)
                      ·
                        rfl

theorem cell23_6274648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_6274648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6274648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6274648 prefixEnd_6274648 := by exact prefixLift 6274648
  have htrace : WordTrace (prefixWord ++ tailWord_6274648) baseStart_6274648 baseEnd_6274648 := by
    simpa [prefixWord, tailWord_6274648, baseEnd_6274648] using wordTrace_append hprefix tailTrace_6274648
  have hstable : (prefixWord ++ tailWord_6274648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6274648).length < 2 ^ (prefixWord ++ tailWord_6274648).sum := by decide
  have hdescent : baseEnd_6274648 < baseStart_6274648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6274648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
