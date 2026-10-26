import V185TrunkScan22Chunk104

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_943054 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_943054 : Nat := 118140960795 + 943054 * 2 ^ 59
def prefixEnd_943054 : Nat := 4983230072969 + 3 ^ 40 * 943054 * 2
def baseEnd_943054 : Nat := 107608885587835229019551

theorem tailTrace_943054 : CollatzResearch.WordTrace tailWord_943054 prefixEnd_943054 107608885587835229019551 := by
  unfold tailWord_943054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299500640685486705700527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22930670083655929097069477 4299500640685486705700527)
  ·
    refine ⟨6449250961028230058550791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299500640685486705700527 6449250961028230058550791)
    ·
      refine ⟨9673876441542345087826187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6449250961028230058550791 9673876441542345087826187)
      ·
        refine ⟨14510814662313517631739281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9673876441542345087826187 14510814662313517631739281)
        ·
          refine ⟨10883110996735138223804461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14510814662313517631739281 10883110996735138223804461)
          ·
            refine ⟨4081166623775676833926673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10883110996735138223804461 4081166623775676833926673)
            ·
              refine ⟨3060874967831757625445005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081166623775676833926673 3060874967831757625445005)
              ·
                refine ⟨1147828112936909109541877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060874967831757625445005 1147828112936909109541877)
                ·
                  refine ⟨107608885587835229019551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1147828112936909109541877 107608885587835229019551)
                  ·
                    rfl

theorem cell22_943054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_943054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943054 prefixEnd_943054 := by exact prefixLift 943054
  have htrace : WordTrace (prefixWord ++ tailWord_943054) baseStart_943054 baseEnd_943054 := by
    simpa [prefixWord, tailWord_943054, baseEnd_943054] using wordTrace_append hprefix tailTrace_943054
  have hstable : (prefixWord ++ tailWord_943054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943054).length < 2 ^ (prefixWord ++ tailWord_943054).sum := by decide
  have hdescent : baseEnd_943054 < baseStart_943054 := by decide
  rcases family_descends (prefixWord ++ tailWord_943054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943165 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 2, 3]
def baseStart_943165 : Nat := 118140960795 + 943165 * 2 ^ 59
def prefixEnd_943165 : Nat := 4983230072969 + 3 ^ 40 * 943165 * 2
def baseEnd_943165 : Nat := 322864654331938397533313

theorem tailTrace_943165 : CollatzResearch.WordTrace tailWord_943165 prefixEnd_943165 322864654331938397533313 := by
  unfold tailWord_943165
  simp only [CollatzResearch.WordTrace]
  refine ⟨34400053628081759602894949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22933369085387839735263299 34400053628081759602894949)
  ·
    refine ⟨6450010055265329925542803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34400053628081759602894949 6450010055265329925542803)
    ·
      refine ⟨9675015082897994888314205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450010055265329925542803 9675015082897994888314205)
      ·
        refine ⟨3628130656086748083117827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9675015082897994888314205 3628130656086748083117827)
        ·
          refine ⟨5442195984130122124676741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3628130656086748083117827 5442195984130122124676741)
          ·
            refine ⟨1020411747024397898376889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5442195984130122124676741 1020411747024397898376889)
            ·
              refine ⟨765308810268298423782667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020411747024397898376889 765308810268298423782667)
              ·
                refine ⟨1147963215402447635674001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765308810268298423782667 1147963215402447635674001)
                ·
                  refine ⟨860972411551835726755501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1147963215402447635674001 860972411551835726755501)
                  ·
                    refine ⟨322864654331938397533313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 860972411551835726755501 322864654331938397533313)
                    ·
                      rfl

theorem cell22_943165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_943165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943165 prefixEnd_943165 := by exact prefixLift 943165
  have htrace : WordTrace (prefixWord ++ tailWord_943165) baseStart_943165 baseEnd_943165 := by
    simpa [prefixWord, tailWord_943165, baseEnd_943165] using wordTrace_append hprefix tailTrace_943165
  have hstable : (prefixWord ++ tailWord_943165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943165).length < 2 ^ (prefixWord ++ tailWord_943165).sum := by decide
  have hdescent : baseEnd_943165 < baseStart_943165 := by decide
  rcases family_descends (prefixWord ++ tailWord_943165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943204 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 2, 5]
def baseStart_943204 : Nat := 118140960795 + 943204 * 2 ^ 59
def prefixEnd_943204 : Nat := 4983230072969 + 3 ^ 40 * 943204 * 2
def baseEnd_943204 : Nat := 322878004828955295808193

theorem tailTrace_943204 : CollatzResearch.WordTrace tailWord_943204 prefixEnd_943204 322878004828955295808193 := by
  unfold tailWord_943204
  simp only [CollatzResearch.WordTrace]
  refine ⟨17200738037470234631782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22934317383293646175709777 17200738037470234631782333)
  ·
    refine ⟨6450276764051337986918375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17200738037470234631782333 6450276764051337986918375)
    ·
      refine ⟨9675415146077006980377563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450276764051337986918375 9675415146077006980377563)
      ·
        refine ⟨14513122719115510470566345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9675415146077006980377563 14513122719115510470566345)
        ·
          refine ⟨10884842039336632852924759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14513122719115510470566345 10884842039336632852924759)
          ·
            refine ⟨16327263059004949279387139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10884842039336632852924759 16327263059004949279387139)
            ·
              refine ⟨24490894588507423919080709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16327263059004949279387139 24490894588507423919080709)
              ·
                refine ⟨4592042735345141984827633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24490894588507423919080709 4592042735345141984827633)
                ·
                  refine ⟨3444032051508856488620725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4592042735345141984827633 3444032051508856488620725)
                  ·
                    refine ⟨322878004828955295808193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3444032051508856488620725 322878004828955295808193)
                    ·
                      rfl

theorem cell22_943204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_943204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943204 prefixEnd_943204 := by exact prefixLift 943204
  have htrace : WordTrace (prefixWord ++ tailWord_943204) baseStart_943204 baseEnd_943204 := by
    simpa [prefixWord, tailWord_943204, baseEnd_943204] using wordTrace_append hprefix tailTrace_943204
  have hstable : (prefixWord ++ tailWord_943204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943204).length < 2 ^ (prefixWord ++ tailWord_943204).sum := by decide
  have hdescent : baseEnd_943204 < baseStart_943204 := by decide
  rcases family_descends (prefixWord ++ tailWord_943204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943210 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_943210 : Nat := 118140960795 + 943210 * 2 ^ 59
def prefixEnd_943210 : Nat := 4983230072969 + 3 ^ 40 * 943210 * 2
def baseEnd_943210 : Nat := 322880058751573280158175

theorem tailTrace_943210 : CollatzResearch.WordTrace tailWord_943210 prefixEnd_943210 322880058751573280158175 := by
  unfold tailWord_943210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600423728229683072070771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22934463275279154858855389 8600423728229683072070771)
  ·
    refine ⟨12900635592344524608106157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8600423728229683072070771 12900635592344524608106157)
    ·
      refine ⟨4837738347129196728039809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12900635592344524608106157 4837738347129196728039809)
      ·
        refine ⟨3628303760346897546029857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4837738347129196728039809 3628303760346897546029857)
        ·
          refine ⟨2721227820260173159522393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3628303760346897546029857 2721227820260173159522393)
          ·
            refine ⟨2040920865195129869641795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721227820260173159522393 2040920865195129869641795)
            ·
              refine ⟨3061381297792694804462693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040920865195129869641795 3061381297792694804462693)
              ·
                refine ⟨574008993336130275836755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061381297792694804462693 574008993336130275836755)
                ·
                  refine ⟨861013490004195413755133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574008993336130275836755 861013490004195413755133)
                  ·
                    refine ⟨322880058751573280158175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861013490004195413755133 322880058751573280158175)
                    ·
                      rfl

theorem cell22_943210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_943210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943210 prefixEnd_943210 := by exact prefixLift 943210
  have htrace : WordTrace (prefixWord ++ tailWord_943210) baseStart_943210 baseEnd_943210 := by
    simpa [prefixWord, tailWord_943210, baseEnd_943210] using wordTrace_append hprefix tailTrace_943210
  have hstable : (prefixWord ++ tailWord_943210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943210).length < 2 ^ (prefixWord ++ tailWord_943210).sum := by decide
  have hdescent : baseEnd_943210 < baseStart_943210 := by decide
  rcases family_descends (prefixWord ++ tailWord_943210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943236 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_943236 : Nat := 118140960795 + 943236 * 2 ^ 59
def prefixEnd_943236 : Nat := 4983230072969 + 3 ^ 40 * 943236 * 2
def baseEnd_943236 : Nat := 322888959082917879008095

theorem tailTrace_943236 : CollatzResearch.WordTrace tailWord_943236 prefixEnd_943236 322888959082917879008095 := by
  unfold tailWord_943236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201321605412269364364781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22935095473883025819153041 17201321605412269364364781)
  ·
    refine ⟨6450495602029601011636793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17201321605412269364364781 6450495602029601011636793)
    ·
      refine ⟨4837871701522200758727595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6450495602029601011636793 4837871701522200758727595)
      ·
        refine ⟨7256807552283301138091393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4837871701522200758727595 7256807552283301138091393)
        ·
          refine ⟨5442605664212475853568545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7256807552283301138091393 5442605664212475853568545)
          ·
            refine ⟨4081954248159356890176409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5442605664212475853568545 4081954248159356890176409)
            ·
              refine ⟨3061465686119517667632307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081954248159356890176409 3061465686119517667632307)
              ·
                refine ⟨4592198529179276501448461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061465686119517667632307 4592198529179276501448461)
                ·
                  refine ⟨1722074448442228688043173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4592198529179276501448461 1722074448442228688043173)
                  ·
                    refine ⟨322888959082917879008095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722074448442228688043173 322888959082917879008095)
                    ·
                      rfl

theorem cell22_943236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_943236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943236 prefixEnd_943236 := by exact prefixLift 943236
  have htrace : WordTrace (prefixWord ++ tailWord_943236) baseStart_943236 baseEnd_943236 := by
    simpa [prefixWord, tailWord_943236, baseEnd_943236] using wordTrace_append hprefix tailTrace_943236
  have hstable : (prefixWord ++ tailWord_943236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943236).length < 2 ^ (prefixWord ++ tailWord_943236).sum := by decide
  have hdescent : baseEnd_943236 < baseStart_943236 := by decide
  rcases family_descends (prefixWord ++ tailWord_943236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943251 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 4]
def baseStart_943251 : Nat := 118140960795 + 943251 * 2 ^ 59
def prefixEnd_943251 : Nat := 4983230072969 + 3 ^ 40 * 943251 * 2
def baseEnd_943251 : Nat := 107631364629820946627683

theorem tailTrace_943251 : CollatzResearch.WordTrace tailWord_943251 prefixEnd_943251 107631364629820946627683 := by
  unfold tailWord_943251
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403190305770196290525607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22935460203846797527017071 34403190305770196290525607)
  ·
    refine ⟨51604785458655294435788411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34403190305770196290525607 51604785458655294435788411)
    ·
      refine ⟨77407178187982941653682617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51604785458655294435788411 77407178187982941653682617)
      ·
        refine ⟨58055383640987206240261963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77407178187982941653682617 58055383640987206240261963)
        ·
          refine ⟨87083075461480809360392945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58055383640987206240261963 87083075461480809360392945)
          ·
            refine ⟨65312306596110607020294709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87083075461480809360392945 65312306596110607020294709)
            ·
              refine ⟨6123028743385369408152629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65312306596110607020294709 6123028743385369408152629)
              ·
                refine ⟨574033944692378382014309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6123028743385369408152629 574033944692378382014309)
                ·
                  refine ⟨107631364629820946627683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574033944692378382014309 107631364629820946627683)
                  ·
                    rfl

theorem cell22_943251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 4].length) (baseStart_943251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943251 prefixEnd_943251 := by exact prefixLift 943251
  have htrace : WordTrace (prefixWord ++ tailWord_943251) baseStart_943251 baseEnd_943251 := by
    simpa [prefixWord, tailWord_943251, baseEnd_943251] using wordTrace_append hprefix tailTrace_943251
  have hstable : (prefixWord ++ tailWord_943251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943251).length < 2 ^ (prefixWord ++ tailWord_943251).sum := by decide
  have hdescent : baseEnd_943251 < baseStart_943251 := by decide
  rcases family_descends (prefixWord ++ tailWord_943251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943268 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 4]
def baseStart_943268 : Nat := 118140960795 + 943268 * 2 ^ 59
def prefixEnd_943268 : Nat := 4983230072969 + 3 ^ 40 * 943268 * 2
def baseEnd_943268 : Nat := 107633304445626820735999

theorem tailTrace_943268 : CollatzResearch.WordTrace tailWord_943268 prefixEnd_943268 107633304445626820735999 := by
  unfold tailWord_943268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17201905173354304096947229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22935873564472405462596305 17201905173354304096947229)
  ·
    refine ⟨6450714440007864036355211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17201905173354304096947229 6450714440007864036355211)
    ·
      refine ⟨9676071660011796054532817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6450714440007864036355211 9676071660011796054532817)
      ·
        refine ⟨7257053745008847040899613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9676071660011796054532817 7257053745008847040899613)
        ·
          refine ⟨2721395154378317640337355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7257053745008847040899613 2721395154378317640337355)
          ·
            refine ⟨4082092731567476460506033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721395154378317640337355 4082092731567476460506033)
            ·
              refine ⟨3061569548675607345379525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082092731567476460506033 3061569548675607345379525)
              ·
                refine ⟨574044290376676377258661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3061569548675607345379525 574044290376676377258661)
                ·
                  refine ⟨107633304445626820735999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574044290376676377258661 107633304445626820735999)
                  ·
                    rfl

theorem cell22_943268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_943268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943268 prefixEnd_943268 := by exact prefixLift 943268
  have htrace : WordTrace (prefixWord ++ tailWord_943268) baseStart_943268 baseEnd_943268 := by
    simpa [prefixWord, tailWord_943268, baseEnd_943268] using wordTrace_append hprefix tailTrace_943268
  have hstable : (prefixWord ++ tailWord_943268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943268).length < 2 ^ (prefixWord ++ tailWord_943268).sum := by decide
  have hdescent : baseEnd_943268 < baseStart_943268 := by decide
  rcases family_descends (prefixWord ++ tailWord_943268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943281 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_943281 : Nat := 118140960795 + 943281 * 2 ^ 59
def prefixEnd_943281 : Nat := 4983230072969 + 3 ^ 40 * 943281 * 2
def baseEnd_943281 : Nat := 322904363502552761632957

theorem tailTrace_943281 : CollatzResearch.WordTrace tailWord_943281 prefixEnd_943281 322904363502552761632957 := by
  unfold tailWord_943281
  simp only [CollatzResearch.WordTrace]
  refine ⟨34404284495661511414117697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22936189663774340942745131 34404284495661511414117697)
  ·
    refine ⟨25803213371746133560588273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34404284495661511414117697 25803213371746133560588273)
    ·
      refine ⟨19352410028809600170441205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25803213371746133560588273 19352410028809600170441205)
      ·
        refine ⟨1814288440200900015978863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19352410028809600170441205 1814288440200900015978863)
        ·
          refine ⟨2721432660301350023968295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814288440200900015978863 2721432660301350023968295)
          ·
            refine ⟨4082148990452025035952443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721432660301350023968295 4082148990452025035952443)
            ·
              refine ⟨6123223485678037553928665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4082148990452025035952443 6123223485678037553928665)
              ·
                refine ⟨4592417614258528165446499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6123223485678037553928665 4592417614258528165446499)
                ·
                  refine ⟨6888626421387792248169749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4592417614258528165446499 6888626421387792248169749)
                  ·
                    refine ⟨322904363502552761632957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6888626421387792248169749 322904363502552761632957)
                    ·
                      rfl

theorem cell22_943281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_943281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943281 prefixEnd_943281 := by exact prefixLift 943281
  have htrace : WordTrace (prefixWord ++ tailWord_943281) baseStart_943281 baseEnd_943281 := by
    simpa [prefixWord, tailWord_943281, baseEnd_943281] using wordTrace_append hprefix tailTrace_943281
  have hstable : (prefixWord ++ tailWord_943281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943281).length < 2 ^ (prefixWord ++ tailWord_943281).sum := by decide
  have hdescent : baseEnd_943281 < baseStart_943281 := by decide
  rcases family_descends (prefixWord ++ tailWord_943281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943296 : List Nat := [2, 1, 1, 2, 6, 1, 1, 8]
def baseStart_943296 : Nat := 118140960795 + 943296 * 2 ^ 59
def prefixEnd_943296 : Nat := 4983230072969 + 3 ^ 40 * 943296 * 2
def baseEnd_943296 : Nat := 35878833145455302500879

theorem tailTrace_943296 : CollatzResearch.WordTrace tailWord_943296 prefixEnd_943296 35878833145455302500879 := by
  unfold tailWord_943296
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202415795303584487956871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22936554393738112650609161 17202415795303584487956871)
  ·
    refine ⟨25803623692955376731935307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17202415795303584487956871 25803623692955376731935307)
    ·
      refine ⟨38705435539433065097902961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25803623692955376731935307 38705435539433065097902961)
      ·
        refine ⟨29029076654574798823427221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38705435539433065097902961 29029076654574798823427221)
        ·
          refine ⟨1360737968183193694848151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29029076654574798823427221 1360737968183193694848151)
          ·
            refine ⟨2041106952274790542272227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360737968183193694848151 2041106952274790542272227)
            ·
              refine ⟨3061660428412185813408341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041106952274790542272227 3061660428412185813408341)
              ·
                refine ⟨35878833145455302500879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3061660428412185813408341 35878833145455302500879)
                ·
                  rfl

theorem cell22_943296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_943296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943296 prefixEnd_943296 := by exact prefixLift 943296
  have htrace : WordTrace (prefixWord ++ tailWord_943296) baseStart_943296 baseEnd_943296 := by
    simpa [prefixWord, tailWord_943296, baseEnd_943296] using wordTrace_append hprefix tailTrace_943296
  have hstable : (prefixWord ++ tailWord_943296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943296).length < 2 ^ (prefixWord ++ tailWord_943296).sum := by decide
  have hdescent : baseEnd_943296 < baseStart_943296 := by decide
  rcases family_descends (prefixWord ++ tailWord_943296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943328 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_943328 : Nat := 118140960795 + 943328 * 2 ^ 59
def prefixEnd_943328 : Nat := 4983230072969 + 3 ^ 40 * 943328 * 2
def baseEnd_943328 : Nat := 322920452563060305707813

theorem tailTrace_943328 : CollatzResearch.WordTrace tailWord_943328 prefixEnd_943328 322920452563060305707813 := by
  unfold tailWord_943328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17202999363245619220539319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22937332484327492294052425 17202999363245619220539319)
  ·
    refine ⟨25804499044868428830808979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17202999363245619220539319 25804499044868428830808979)
    ·
      refine ⟨38706748567302643246213469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25804499044868428830808979 38706748567302643246213469)
      ·
        refine ⟨14515030712738491217330051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38706748567302643246213469 14515030712738491217330051)
        ·
          refine ⟨21772546069107736825995077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14515030712738491217330051 21772546069107736825995077)
          ·
            refine ⟨4082352387957700654874077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21772546069107736825995077 4082352387957700654874077)
            ·
              refine ⟨1530882145484137745577779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4082352387957700654874077 1530882145484137745577779)
              ·
                refine ⟨2296323218226206618366669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530882145484137745577779 2296323218226206618366669)
                ·
                  refine ⟨861121206834827481887501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2296323218226206618366669 861121206834827481887501)
                  ·
                    refine ⟨322920452563060305707813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861121206834827481887501 322920452563060305707813)
                    ·
                      rfl

theorem cell22_943328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_943328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943328 prefixEnd_943328 := by exact prefixLift 943328
  have htrace : WordTrace (prefixWord ++ tailWord_943328) baseStart_943328 baseEnd_943328 := by
    simpa [prefixWord, tailWord_943328, baseEnd_943328] using wordTrace_append hprefix tailTrace_943328
  have hstable : (prefixWord ++ tailWord_943328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943328).length < 2 ^ (prefixWord ++ tailWord_943328).sum := by decide
  have hdescent : baseEnd_943328 < baseStart_943328 := by decide
  rcases family_descends (prefixWord ++ tailWord_943328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943405 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_943405 : Nat := 118140960795 + 943405 * 2 ^ 59
def prefixEnd_943405 : Nat := 4983230072969 + 3 ^ 40 * 943405 * 2
def baseEnd_943405 : Nat := 322946811236657771532577

theorem tailTrace_943405 : CollatzResearch.WordTrace tailWord_943405 prefixEnd_943405 322946811236657771532577 := by
  unfold tailWord_943405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34408807147212280591631669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22939204764808187061087779 34408807147212280591631669)
  ·
    refine ⟨3225825670051151305465469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34408807147212280591631669 3225825670051151305465469)
    ·
      refine ⟨1209684626269181739549551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3225825670051151305465469 1209684626269181739549551)
      ·
        refine ⟨1814526939403772609324327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209684626269181739549551 1814526939403772609324327)
        ·
          refine ⟨2721790409105658913986491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814526939403772609324327 2721790409105658913986491)
          ·
            refine ⟨4082685613658488370979737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721790409105658913986491 4082685613658488370979737)
            ·
              refine ⟨3062014210243866278234803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4082685613658488370979737 3062014210243866278234803)
              ·
                refine ⟨4593021315365799417352205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062014210243866278234803 4593021315365799417352205)
                ·
                  refine ⟨1722382993262174781507077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4593021315365799417352205 1722382993262174781507077)
                  ·
                    refine ⟨322946811236657771532577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722382993262174781507077 322946811236657771532577)
                    ·
                      rfl

theorem cell22_943405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_943405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943405 prefixEnd_943405 := by exact prefixLift 943405
  have htrace : WordTrace (prefixWord ++ tailWord_943405) baseStart_943405 baseEnd_943405 := by
    simpa [prefixWord, tailWord_943405, baseEnd_943405] using wordTrace_append hprefix tailTrace_943405
  have hstable : (prefixWord ++ tailWord_943405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943405).length < 2 ^ (prefixWord ++ tailWord_943405).sum := by decide
  have hdescent : baseEnd_943405 < baseStart_943405 := by decide
  rcases family_descends (prefixWord ++ tailWord_943405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943418 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 4, 3]
def baseStart_943418 : Nat := 118140960795 + 943418 * 2 ^ 59
def prefixEnd_943418 : Nat := 4983230072969 + 3 ^ 40 * 943418 * 2
def baseEnd_943418 : Nat := 322951261402330070957537

theorem tailTrace_943418 : CollatzResearch.WordTrace tailWord_943418 prefixEnd_943418 322951261402330070957537 := by
  unfold tailWord_943418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8602320324041295952963727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22939520864110122541236605 8602320324041295952963727)
  ·
    refine ⟨12903480486061943929445591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8602320324041295952963727 12903480486061943929445591)
    ·
      refine ⟨19355220729092915894168387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12903480486061943929445591 19355220729092915894168387)
      ·
        refine ⟨29032831093639373841252581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19355220729092915894168387 29032831093639373841252581)
        ·
          refine ⟨5443655830057382595234859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29032831093639373841252581 5443655830057382595234859)
          ·
            refine ⟨8165483745086073892852289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5443655830057382595234859 8165483745086073892852289)
            ·
              refine ⟨6124112808814555419639217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8165483745086073892852289 6124112808814555419639217)
              ·
                refine ⟨4593084606610916564729413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6124112808814555419639217 4593084606610916564729413)
                ·
                  refine ⟨861203363739546855886765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4593084606610916564729413 861203363739546855886765)
                  ·
                    refine ⟨322951261402330070957537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861203363739546855886765 322951261402330070957537)
                    ·
                      rfl

theorem cell22_943418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_943418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943418 prefixEnd_943418 := by exact prefixLift 943418
  have htrace : WordTrace (prefixWord ++ tailWord_943418) baseStart_943418 baseEnd_943418 := by
    simpa [prefixWord, tailWord_943418, baseEnd_943418] using wordTrace_append hprefix tailTrace_943418
  have hstable : (prefixWord ++ tailWord_943418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943418).length < 2 ^ (prefixWord ++ tailWord_943418).sum := by decide
  have hdescent : baseEnd_943418 < baseStart_943418 := by decide
  rcases family_descends (prefixWord ++ tailWord_943418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943420 : List Nat := [2, 2, 2, 2, 1, 4, 2, 3, 4]
def baseStart_943420 : Nat := 118140960795 + 943420 * 2 ^ 59
def prefixEnd_943420 : Nat := 4983230072969 + 3 ^ 40 * 943420 * 2
def baseEnd_943420 : Nat := 107650648681067577469177

theorem tailTrace_943420 : CollatzResearch.WordTrace tailWord_943420 prefixEnd_943420 107650648681067577469177 := by
  unfold tailWord_943420
  simp only [CollatzResearch.WordTrace]
  refine ⟨17204677121078969076713857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22939569494771958768951809 17204677121078969076713857)
  ·
    refine ⟨12903507840809226807535393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17204677121078969076713857 12903507840809226807535393)
    ·
      refine ⟨9677630880606920105651545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12903507840809226807535393 9677630880606920105651545)
      ·
        refine ⟨7258223160455190079238659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9677630880606920105651545 7258223160455190079238659)
        ·
          refine ⟨10887334740682785118857989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7258223160455190079238659 10887334740682785118857989)
          ·
            refine ⟨2041375263878022209785873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10887334740682785118857989 2041375263878022209785873)
            ·
              refine ⟨1531031447908516657339405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041375263878022209785873 1531031447908516657339405)
              ·
                refine ⟨574136792965693746502277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531031447908516657339405 574136792965693746502277)
                ·
                  refine ⟨107650648681067577469177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574136792965693746502277 107650648681067577469177)
                  ·
                    rfl

theorem cell22_943420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_943420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943420 prefixEnd_943420 := by exact prefixLift 943420
  have htrace : WordTrace (prefixWord ++ tailWord_943420) baseStart_943420 baseEnd_943420 := by
    simpa [prefixWord, tailWord_943420, baseEnd_943420] using wordTrace_append hprefix tailTrace_943420
  have hstable : (prefixWord ++ tailWord_943420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943420).length < 2 ^ (prefixWord ++ tailWord_943420).sum := by decide
  have hdescent : baseEnd_943420 < baseStart_943420 := by decide
  rcases family_descends (prefixWord ++ tailWord_943420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943431 : List Nat := [1, 1, 4, 1, 2, 4, 9]
def baseStart_943431 : Nat := 118140960795 + 943431 * 2 ^ 59
def prefixEnd_943431 : Nat := 4983230072969 + 3 ^ 40 * 943431 * 2
def baseEnd_943431 : Nat := 11961322650666754458611

theorem tailTrace_943431 : CollatzResearch.WordTrace tailWord_943431 prefixEnd_943431 11961322650666754458611 := by
  unfold tailWord_943431
  simp only [CollatzResearch.WordTrace]
  refine ⟨34409755445118087032078147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22939836963412058021385431 34409755445118087032078147)
  ·
    refine ⟨51614633167677130548117221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34409755445118087032078147 51614633167677130548117221)
    ·
      refine ⟨9677743718939461977771979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51614633167677130548117221 9677743718939461977771979)
      ·
        refine ⟨14516615578409192966657969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9677743718939461977771979 14516615578409192966657969)
        ·
          refine ⟨10887461683806894724993477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14516615578409192966657969 10887461683806894724993477)
          ·
            refine ⟨2041399065713792760936277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10887461683806894724993477 2041399065713792760936277)
            ·
              refine ⟨11961322650666754458611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2041399065713792760936277 11961322650666754458611)
              ·
                rfl

theorem cell22_943431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 9].length) (baseStart_943431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943431 prefixEnd_943431 := by exact prefixLift 943431
  have htrace : WordTrace (prefixWord ++ tailWord_943431) baseStart_943431 baseEnd_943431 := by
    simpa [prefixWord, tailWord_943431, baseEnd_943431] using wordTrace_append hprefix tailTrace_943431
  have hstable : (prefixWord ++ tailWord_943431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943431).length < 2 ^ (prefixWord ++ tailWord_943431).sum := by decide
  have hdescent : baseEnd_943431 < baseStart_943431 := by decide
  rcases family_descends (prefixWord ++ tailWord_943431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943437 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 6]
def baseStart_943437 : Nat := 118140960795 + 943437 * 2 ^ 59
def prefixEnd_943437 : Nat := 4983230072969 + 3 ^ 40 * 943437 * 2
def baseEnd_943437 : Nat := 107652588496873451577493

theorem tailTrace_943437 : CollatzResearch.WordTrace tailWord_943437 prefixEnd_943437 107652588496873451577493 := by
  unfold tailWord_943437
  simp only [CollatzResearch.WordTrace]
  refine ⟨34409974283096350056796565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22939982855397566704531043 34409974283096350056796565)
  ·
    refine ⟨1612967544520141408912339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34409974283096350056796565 1612967544520141408912339)
    ·
      refine ⟨2419451316780212113368509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612967544520141408912339 2419451316780212113368509)
      ·
        refine ⟨907294243792579542513191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2419451316780212113368509 907294243792579542513191)
        ·
          refine ⟨1360941365688869313769787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907294243792579542513191 1360941365688869313769787)
          ·
            refine ⟨2041412048533303970654681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360941365688869313769787 2041412048533303970654681)
            ·
              refine ⟨1531059036399977977991011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041412048533303970654681 1531059036399977977991011)
              ·
                refine ⟨2296588554599966966986517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531059036399977977991011 2296588554599966966986517)
                ·
                  refine ⟨107652588496873451577493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2296588554599966966986517 107652588496873451577493)
                  ·
                    rfl

theorem cell22_943437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_943437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943437 prefixEnd_943437 := by exact prefixLift 943437
  have htrace : WordTrace (prefixWord ++ tailWord_943437) baseStart_943437 baseEnd_943437 := by
    simpa [prefixWord, tailWord_943437, baseEnd_943437] using wordTrace_append hprefix tailTrace_943437
  have hstable : (prefixWord ++ tailWord_943437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943437).length < 2 ^ (prefixWord ++ tailWord_943437).sum := by decide
  have hdescent : baseEnd_943437 < baseStart_943437 := by decide
  rcases family_descends (prefixWord ++ tailWord_943437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943497 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 3, 3]
def baseStart_943497 : Nat := 118140960795 + 943497 * 2 ^ 59
def prefixEnd_943497 : Nat := 4983230072969 + 3 ^ 40 * 943497 * 2
def baseEnd_943497 : Nat := 322978304716800198232295

theorem tailTrace_943497 : CollatzResearch.WordTrace tailWord_943497 prefixEnd_943497 322978304716800198232295 := by
  unfold tailWord_943497
  simp only [CollatzResearch.WordTrace]
  refine ⟨34412162662878980303980745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22941441775252653535987163 34412162662878980303980745)
  ·
    refine ⟨25809121997159235227985559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34412162662878980303980745 25809121997159235227985559)
    ·
      refine ⟨38713682995738852841978339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25809121997159235227985559 38713682995738852841978339)
      ·
        refine ⟨58070524493608279262967509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38713682995738852841978339 58070524493608279262967509)
        ·
          refine ⟨1361027917818944045225801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 58070524493608279262967509 1361027917818944045225801)
          ·
            refine ⟨1020770938364208033919351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361027917818944045225801 1020770938364208033919351)
            ·
              refine ⟨1531156407546312050879027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020770938364208033919351 1531156407546312050879027)
              ·
                refine ⟨2296734611319468076318541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531156407546312050879027 2296734611319468076318541)
                ·
                  refine ⟨861275479244800528619453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2296734611319468076318541 861275479244800528619453)
                  ·
                    refine ⟨322978304716800198232295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861275479244800528619453 322978304716800198232295)
                    ·
                      rfl

theorem cell22_943497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_943497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943497 prefixEnd_943497 := by exact prefixLift 943497
  have htrace : WordTrace (prefixWord ++ tailWord_943497) baseStart_943497 baseEnd_943497 := by
    simpa [prefixWord, tailWord_943497, baseEnd_943497] using wordTrace_append hprefix tailTrace_943497
  have hstable : (prefixWord ++ tailWord_943497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943497).length < 2 ^ (prefixWord ++ tailWord_943497).sum := by decide
  have hdescent : baseEnd_943497 < baseStart_943497 := by decide
  rcases family_descends (prefixWord ++ tailWord_943497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943523 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_943523 : Nat := 118140960795 + 943523 * 2 ^ 59
def prefixEnd_943523 : Nat := 4983230072969 + 3 ^ 40 * 943523 * 2
def baseEnd_943523 : Nat := 322987205048144797082215

theorem tailTrace_943523 : CollatzResearch.WordTrace tailWord_943523 prefixEnd_943523 322987205048144797082215 := by
  unfold tailWord_943523
  simp only [CollatzResearch.WordTrace]
  refine ⟨34413110960784786744427223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22942073973856524496284815 34413110960784786744427223)
  ·
    refine ⟨51619666441177180116640835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34413110960784786744427223 51619666441177180116640835)
    ·
      refine ⟨77429499661765770174961253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51619666441177180116640835 77429499661765770174961253)
      ·
        refine ⟨14518031186581081907805235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77429499661765770174961253 14518031186581081907805235)
        ·
          refine ⟨21777046779871622861707853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14518031186581081907805235 21777046779871622861707853)
          ·
            refine ⟨8166392542451858573140445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21777046779871622861707853 8166392542451858573140445)
            ·
              refine ⟨3062397203419446964927667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8166392542451858573140445 3062397203419446964927667)
              ·
                refine ⟨4593595805129170447391501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062397203419446964927667 4593595805129170447391501)
                ·
                  refine ⟨1722598426923438917771813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4593595805129170447391501 1722598426923438917771813)
                  ·
                    refine ⟨322987205048144797082215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722598426923438917771813 322987205048144797082215)
                    ·
                      rfl

theorem cell22_943523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_943523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943523 prefixEnd_943523 := by exact prefixLift 943523
  have htrace : WordTrace (prefixWord ++ tailWord_943523) baseStart_943523 baseEnd_943523 := by
    simpa [prefixWord, tailWord_943523, baseEnd_943523] using wordTrace_append hprefix tailTrace_943523
  have hstable : (prefixWord ++ tailWord_943523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943523).length < 2 ^ (prefixWord ++ tailWord_943523).sum := by decide
  have hdescent : baseEnd_943523 < baseStart_943523 := by decide
  rcases family_descends (prefixWord ++ tailWord_943523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943548 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_943548 : Nat := 118140960795 + 943548 * 2 ^ 59
def prefixEnd_943548 : Nat := 4983230072969 + 3 ^ 40 * 943548 * 2
def baseEnd_943548 : Nat := 322995763059053065207139

theorem tailTrace_943548 : CollatzResearch.WordTrace tailWord_943548 prefixEnd_943548 322995763059053065207139 := by
  unfold tailWord_943548
  simp only [CollatzResearch.WordTrace]
  refine ⟨17207011392847108007043649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22942681857129477342724865 17207011392847108007043649)
  ·
    refine ⟨12905258544635331005282737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17207011392847108007043649 12905258544635331005282737)
    ·
      refine ⟨9678943908476498253962053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12905258544635331005282737 9678943908476498253962053)
      ·
        refine ⟨1814801982839343422617885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9678943908476498253962053 1814801982839343422617885)
        ·
          refine ⟨680550743564753783481707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1814801982839343422617885 680550743564753783481707)
          ·
            refine ⟨1020826115347130675222561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680550743564753783481707 1020826115347130675222561)
            ·
              refine ⟨765619586510348006416921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020826115347130675222561 765619586510348006416921)
              ·
                refine ⟨574214689882761004812691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765619586510348006416921 574214689882761004812691)
                ·
                  refine ⟨861322034824141507219037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574214689882761004812691 861322034824141507219037)
                  ·
                    refine ⟨322995763059053065207139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861322034824141507219037 322995763059053065207139)
                    ·
                      rfl

theorem cell22_943548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_943548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943548 prefixEnd_943548 := by exact prefixLift 943548
  have htrace : WordTrace (prefixWord ++ tailWord_943548) baseStart_943548 baseEnd_943548 := by
    simpa [prefixWord, tailWord_943548, baseEnd_943548] using wordTrace_append hprefix tailTrace_943548
  have hstable : (prefixWord ++ tailWord_943548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943548).length < 2 ^ (prefixWord ++ tailWord_943548).sum := by decide
  have hdescent : baseEnd_943548 < baseStart_943548 := by decide
  rcases family_descends (prefixWord ++ tailWord_943548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943585 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 2, 4]
def baseStart_943585 : Nat := 118140960795 + 943585 * 2 ^ 59
def prefixEnd_943585 : Nat := 4983230072969 + 3 ^ 40 * 943585 * 2
def baseEnd_943585 : Nat := 323008428915197302032025

theorem tailTrace_943585 : CollatzResearch.WordTrace tailWord_943585 prefixEnd_943585 323008428915197302032025 := by
  unfold tailWord_943585
  simp only [CollatzResearch.WordTrace]
  refine ⟨34415372286560171333184209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22943581524373447555456139 34415372286560171333184209)
  ·
    refine ⟨25811529214920128499888157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34415372286560171333184209 25811529214920128499888157)
    ·
      refine ⟨9679323455595048187458059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25811529214920128499888157 9679323455595048187458059)
      ·
        refine ⟨14518985183392572281187089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679323455595048187458059 14518985183392572281187089)
        ·
          refine ⟨10889238887544429210890317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14518985183392572281187089 10889238887544429210890317)
          ·
            refine ⟨4083464582829160954083869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10889238887544429210890317 4083464582829160954083869)
            ·
              refine ⟨1531299218560935357781451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4083464582829160954083869 1531299218560935357781451)
              ·
                refine ⟨2296948827841403036672177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531299218560935357781451 2296948827841403036672177)
                ·
                  refine ⟨1722711620881052277504133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2296948827841403036672177 1722711620881052277504133)
                  ·
                    refine ⟨323008428915197302032025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722711620881052277504133 323008428915197302032025)
                    ·
                      rfl

theorem cell22_943585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_943585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943585 prefixEnd_943585 := by exact prefixLift 943585
  have htrace : WordTrace (prefixWord ++ tailWord_943585) baseStart_943585 baseEnd_943585 := by
    simpa [prefixWord, tailWord_943585, baseEnd_943585] using wordTrace_append hprefix tailTrace_943585
  have hstable : (prefixWord ++ tailWord_943585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943585).length < 2 ^ (prefixWord ++ tailWord_943585).sum := by decide
  have hdescent : baseEnd_943585 < baseStart_943585 := by decide
  rcases family_descends (prefixWord ++ tailWord_943585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943649 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 1, 3]
def baseStart_943649 : Nat := 118140960795 + 943649 * 2 ^ 59
def prefixEnd_943649 : Nat := 4983230072969 + 3 ^ 40 * 943649 * 2
def baseEnd_943649 : Nat := 323030337423122468431829

theorem tailTrace_943649 : CollatzResearch.WordTrace tailWord_943649 prefixEnd_943649 323030337423122468431829 := by
  unfold tailWord_943649
  simp only [CollatzResearch.WordTrace]
  refine ⟨34417706558328310263514001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22945137705552206842342667 34417706558328310263514001)
  ·
    refine ⟨25813279918746232697635501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34417706558328310263514001 25813279918746232697635501)
    ·
      refine ⟨9679979969529837261613313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25813279918746232697635501 9679979969529837261613313)
      ·
        refine ⟨7259984977147377946209985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9679979969529837261613313 7259984977147377946209985)
        ·
          refine ⟨5444988732860533459657489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7259984977147377946209985 5444988732860533459657489)
          ·
            refine ⟨4083741549645400094743117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444988732860533459657489 4083741549645400094743117)
            ·
              refine ⟨1531403081117025035528669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4083741549645400094743117 1531403081117025035528669)
              ·
                refine ⟨574276155418884388323251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531403081117025035528669 574276155418884388323251)
                ·
                  refine ⟨861414233128326582484877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574276155418884388323251 861414233128326582484877)
                  ·
                    refine ⟨323030337423122468431829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861414233128326582484877 323030337423122468431829)
                    ·
                      rfl

theorem cell22_943649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 3].length) (baseStart_943649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943649 prefixEnd_943649 := by exact prefixLift 943649
  have htrace : WordTrace (prefixWord ++ tailWord_943649) baseStart_943649 baseEnd_943649 := by
    simpa [prefixWord, tailWord_943649, baseEnd_943649] using wordTrace_append hprefix tailTrace_943649
  have hstable : (prefixWord ++ tailWord_943649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943649).length < 2 ^ (prefixWord ++ tailWord_943649).sum := by decide
  have hdescent : baseEnd_943649 < baseStart_943649 := by decide
  rcases family_descends (prefixWord ++ tailWord_943649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943692 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_943692 : Nat := 118140960795 + 943692 * 2 ^ 59
def prefixEnd_943692 : Nat := 4983230072969 + 3 ^ 40 * 943692 * 2
def baseEnd_943692 : Nat := 323045057201884689606697

theorem tailTrace_943692 : CollatzResearch.WordTrace tailWord_943692 prefixEnd_943692 323045057201884689606697 := by
  unfold tailWord_943692
  simp only [CollatzResearch.WordTrace]
  refine ⟨17209637448586264303664665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22946183264781685738219553 17209637448586264303664665)
  ·
    refine ⟨12907228086439698227748499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17209637448586264303664665 12907228086439698227748499)
    ·
      refine ⟨19360842129659547341622749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12907228086439698227748499 19360842129659547341622749)
      ·
        refine ⟨7260315798622330253108531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19360842129659547341622749 7260315798622330253108531)
        ·
          refine ⟨10890473697933495379662797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7260315798622330253108531 10890473697933495379662797)
          ·
            refine ⟨4083927636725060767373549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10890473697933495379662797 4083927636725060767373549)
            ·
              refine ⟨1531472863771897787765081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4083927636725060767373549 1531472863771897787765081)
              ·
                refine ⟨1148604647828923340823811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1531472863771897787765081 1148604647828923340823811)
                ·
                  refine ⟨1722906971743385011235717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1148604647828923340823811 1722906971743385011235717)
                  ·
                    refine ⟨323045057201884689606697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1722906971743385011235717 323045057201884689606697)
                    ·
                      rfl

theorem cell22_943692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_943692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943692 prefixEnd_943692 := by exact prefixLift 943692
  have htrace : WordTrace (prefixWord ++ tailWord_943692) baseStart_943692 baseEnd_943692 := by
    simpa [prefixWord, tailWord_943692, baseEnd_943692] using wordTrace_append hprefix tailTrace_943692
  have hstable : (prefixWord ++ tailWord_943692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943692).length < 2 ^ (prefixWord ++ tailWord_943692).sum := by decide
  have hdescent : baseEnd_943692 < baseStart_943692 := by decide
  rcases family_descends (prefixWord ++ tailWord_943692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943705 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 6, 3]
def baseStart_943705 : Nat := 118140960795 + 943705 * 2 ^ 59
def prefixEnd_943705 : Nat := 4983230072969 + 3 ^ 40 * 943705 * 2
def baseEnd_943705 : Nat := 323049507367556989031657

theorem tailTrace_943705 : CollatzResearch.WordTrace tailWord_943705 prefixEnd_943705 323049507367556989031657 := by
  unfold tailWord_943705
  simp only [CollatzResearch.WordTrace]
  refine ⟨34419749046125431827552569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22946499364083621218368379 34419749046125431827552569)
  ·
    refine ⟨25814811784594073870664427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34419749046125431827552569 25814811784594073870664427)
    ·
      refine ⟨38722217676891110805996641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25814811784594073870664427 38722217676891110805996641)
      ·
        refine ⟨29041663257668333104497481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38722217676891110805996641 29041663257668333104497481)
        ·
          refine ⟨21781247443251249828373111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29041663257668333104497481 21781247443251249828373111)
          ·
            refine ⟨32671871164876874742559667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21781247443251249828373111 32671871164876874742559667)
            ·
              refine ⟨49007806747315312113839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32671871164876874742559667 49007806747315312113839501)
              ·
                refine ⟨18377927530243242042689813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49007806747315312113839501 18377927530243242042689813)
                ·
                  refine ⟨861465352980151970751085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18377927530243242042689813 861465352980151970751085)
                  ·
                    refine ⟨323049507367556989031657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861465352980151970751085 323049507367556989031657)
                    ·
                      rfl

theorem cell22_943705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_943705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943705 prefixEnd_943705 := by exact prefixLift 943705
  have htrace : WordTrace (prefixWord ++ tailWord_943705) baseStart_943705 baseEnd_943705 := by
    simpa [prefixWord, tailWord_943705, baseEnd_943705] using wordTrace_append hprefix tailTrace_943705
  have hstable : (prefixWord ++ tailWord_943705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943705).length < 2 ^ (prefixWord ++ tailWord_943705).sum := by decide
  have hdescent : baseEnd_943705 < baseStart_943705 := by decide
  rcases family_descends (prefixWord ++ tailWord_943705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943754 : List Nat := [3, 1, 2, 3, 2, 3, 1, 1, 2, 4]
def baseStart_943754 : Nat := 118140960795 + 943754 * 2 ^ 59
def prefixEnd_943754 : Nat := 4983230072969 + 3 ^ 40 * 943754 * 2
def baseEnd_943754 : Nat := 323066281068937194556507

theorem tailTrace_943754 : CollatzResearch.WordTrace tailWord_943754 prefixEnd_943754 323066281068937194556507 := by
  unfold tailWord_943754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605384055736978299021579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22947690815298608797390877 8605384055736978299021579)
  ·
    refine ⟨12908076083605467448532369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8605384055736978299021579 12908076083605467448532369)
    ·
      refine ⟨9681057062704100586399277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12908076083605467448532369 9681057062704100586399277)
      ·
        refine ⟨3630396398514037719899729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9681057062704100586399277 3630396398514037719899729)
        ·
          refine ⟨2722797298885528289924797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3630396398514037719899729 2722797298885528289924797)
          ·
            refine ⟨1021048987082073108721799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2722797298885528289924797 1021048987082073108721799)
            ·
              refine ⟨1531573480623109663082699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021048987082073108721799 1531573480623109663082699)
              ·
                refine ⟨2297360220934664494624049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531573480623109663082699 2297360220934664494624049)
                ·
                  refine ⟨1723020165700998370968037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2297360220934664494624049 1723020165700998370968037)
                  ·
                    refine ⟨323066281068937194556507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723020165700998370968037 323066281068937194556507)
                    ·
                      rfl

theorem cell22_943754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_943754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943754 prefixEnd_943754 := by exact prefixLift 943754
  have htrace : WordTrace (prefixWord ++ tailWord_943754) baseStart_943754 baseEnd_943754 := by
    simpa [prefixWord, tailWord_943754, baseEnd_943754] using wordTrace_append hprefix tailTrace_943754
  have hstable : (prefixWord ++ tailWord_943754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943754).length < 2 ^ (prefixWord ++ tailWord_943754).sum := by decide
  have hdescent : baseEnd_943754 < baseStart_943754 := by decide
  rcases family_descends (prefixWord ++ tailWord_943754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943795 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_943795 : Nat := 118140960795 + 943795 * 2 ^ 59
def prefixEnd_943795 : Nat := 4983230072969 + 3 ^ 40 * 943795 * 2
def baseEnd_943795 : Nat := 323080316206826754281381

theorem tailTrace_943795 : CollatzResearch.WordTrace tailWord_943795 prefixEnd_943795 323080316206826754281381 := by
  unfold tailWord_943795
  simp only [CollatzResearch.WordTrace]
  refine ⟨34423031615799377198328839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22948687743866251465552559 34423031615799377198328839)
  ·
    refine ⟨51634547423699065797493259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34423031615799377198328839 51634547423699065797493259)
    ·
      refine ⟨77451821135548598696239889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51634547423699065797493259 77451821135548598696239889)
      ·
        refine ⟨58088865851661449022179917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77451821135548598696239889 58088865851661449022179917)
        ·
          refine ⟨21783324694373043383317469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58088865851661449022179917 21783324694373043383317469)
          ·
            refine ⟨8168746760389891268744051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21783324694373043383317469 8168746760389891268744051)
            ·
              refine ⟨12253120140584836903116077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8168746760389891268744051 12253120140584836903116077)
              ·
                refine ⟨4594920052719313838668529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12253120140584836903116077 4594920052719313838668529)
                ·
                  refine ⟨3446190039539485379001397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4594920052719313838668529 3446190039539485379001397)
                  ·
                    refine ⟨323080316206826754281381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3446190039539485379001397 323080316206826754281381)
                    ·
                      rfl

theorem cell22_943795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_943795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943795 prefixEnd_943795 := by exact prefixLift 943795
  have htrace : WordTrace (prefixWord ++ tailWord_943795) baseStart_943795 baseEnd_943795 := by
    simpa [prefixWord, tailWord_943795, baseEnd_943795] using wordTrace_append hprefix tailTrace_943795
  have hstable : (prefixWord ++ tailWord_943795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943795).length < 2 ^ (prefixWord ++ tailWord_943795).sum := by decide
  have hdescent : baseEnd_943795 < baseStart_943795 := by decide
  rcases family_descends (prefixWord ++ tailWord_943795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943818 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 1, 3]
def baseStart_943818 : Nat := 118140960795 + 943818 * 2 ^ 59
def prefixEnd_943818 : Nat := 4983230072969 + 3 ^ 40 * 943818 * 2
def baseEnd_943818 : Nat := 323088189576862360956311

theorem tailTrace_943818 : CollatzResearch.WordTrace tailWord_943818 prefixEnd_943818 323088189576862360956311 := by
  unfold tailWord_943818
  simp only [CollatzResearch.WordTrace]
  refine ⟨8605967623679013031604027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22949246996477368084277405 8605967623679013031604027)
  ·
    refine ⟨12908951435518519547406041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8605967623679013031604027 12908951435518519547406041)
    ·
      refine ⟨9681713576638889660554531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12908951435518519547406041 9681713576638889660554531)
      ·
        refine ⟨14522570364958334490831797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9681713576638889660554531 14522570364958334490831797)
        ·
          refine ⟨1361490971714843858515481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14522570364958334490831797 1361490971714843858515481)
          ·
            refine ⟨1021118228786132893886611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361490971714843858515481 1021118228786132893886611)
            ·
              refine ⟨1531677343179199340829917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021118228786132893886611 1531677343179199340829917)
              ·
                refine ⟨574379003692199752811219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531677343179199340829917 574379003692199752811219)
                ·
                  refine ⟨861568505538299629216829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574379003692199752811219 861568505538299629216829)
                  ·
                    refine ⟨323088189576862360956311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861568505538299629216829 323088189576862360956311)
                    ·
                      rfl

theorem cell22_943818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_943818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943818 prefixEnd_943818 := by exact prefixLift 943818
  have htrace : WordTrace (prefixWord ++ tailWord_943818) baseStart_943818 baseEnd_943818 := by
    simpa [prefixWord, tailWord_943818, baseEnd_943818] using wordTrace_append hprefix tailTrace_943818
  have hstable : (prefixWord ++ tailWord_943818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943818).length < 2 ^ (prefixWord ++ tailWord_943818).sum := by decide
  have hdescent : baseEnd_943818 < baseStart_943818 := by decide
  rcases family_descends (prefixWord ++ tailWord_943818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943874 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_943874 : Nat := 118140960795 + 943874 * 2 ^ 59
def prefixEnd_943874 : Nat := 4983230072969 + 3 ^ 40 * 943874 * 2
def baseEnd_943874 : Nat := 323107359521296881556139

theorem tailTrace_943874 : CollatzResearch.WordTrace tailWord_943874 prefixEnd_943874 323107359521296881556139 := by
  unfold tailWord_943874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8606478245628293422613669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22950608655008782460303117 8606478245628293422613669)
  ·
    refine ⟨1613714671055305016740063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8606478245628293422613669 1613714671055305016740063)
    ·
      refine ⟨2420572006582957525110095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613714671055305016740063 2420572006582957525110095)
      ·
        refine ⟨3630858009874436287665143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420572006582957525110095 3630858009874436287665143)
        ·
          refine ⟨5446287014811654431497715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3630858009874436287665143 5446287014811654431497715)
          ·
            refine ⟨8169430522217481647246573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5446287014811654431497715 8169430522217481647246573)
            ·
              refine ⟨3063536445831555617717465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8169430522217481647246573 3063536445831555617717465)
              ·
                refine ⟨2297652334373666713288099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3063536445831555617717465 2297652334373666713288099)
                ·
                  refine ⟨3446478501560500069932149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2297652334373666713288099 3446478501560500069932149)
                  ·
                    refine ⟨323107359521296881556139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3446478501560500069932149 323107359521296881556139)
                    ·
                      rfl

theorem cell22_943874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_943874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_943874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_943874 prefixEnd_943874 := by exact prefixLift 943874
  have htrace : WordTrace (prefixWord ++ tailWord_943874) baseStart_943874 baseEnd_943874 := by
    simpa [prefixWord, tailWord_943874, baseEnd_943874] using wordTrace_append hprefix tailTrace_943874
  have hstable : (prefixWord ++ tailWord_943874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943874).length < 2 ^ (prefixWord ++ tailWord_943874).sum := by decide
  have hdescent : baseEnd_943874 < baseStart_943874 := by decide
  rcases family_descends (prefixWord ++ tailWord_943874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944009 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 4, 3]
def baseStart_944009 : Nat := 118140960795 + 944009 * 2 ^ 59
def prefixEnd_944009 : Nat := 4983230072969 + 3 ^ 40 * 944009 * 2
def baseEnd_944009 : Nat := 323153572780201529430725

theorem tailTrace_944009 : CollatzResearch.WordTrace tailWord_944009 prefixEnd_944009 323153572780201529430725 := by
  unfold tailWord_944009
  simp only [CollatzResearch.WordTrace]
  refine ⟨34430836837024091746619081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22953891224682727831079387 34430836837024091746619081)
  ·
    refine ⟨25823127627768068809964311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34430836837024091746619081 25823127627768068809964311)
    ·
      refine ⟨38734691441652103214946467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25823127627768068809964311 38734691441652103214946467)
      ·
        refine ⟨58102037162478154822419701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38734691441652103214946467 58102037162478154822419701)
        ·
          refine ⟨5447065983982327014601847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58102037162478154822419701 5447065983982327014601847)
          ·
            refine ⟨8170598975973490521902771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447065983982327014601847 8170598975973490521902771)
            ·
              refine ⟨12255898463960235782854157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8170598975973490521902771 12255898463960235782854157)
              ·
                refine ⟨4595961923985088418570309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12255898463960235782854157 4595961923985088418570309)
                ·
                  refine ⟨861742860747204078481933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4595961923985088418570309 861742860747204078481933)
                  ·
                    refine ⟨323153572780201529430725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861742860747204078481933 323153572780201529430725)
                    ·
                      rfl

theorem cell22_944009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_944009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944009 prefixEnd_944009 := by exact prefixLift 944009
  have htrace : WordTrace (prefixWord ++ tailWord_944009) baseStart_944009 baseEnd_944009 := by
    simpa [prefixWord, tailWord_944009, baseEnd_944009] using wordTrace_append hprefix tailTrace_944009
  have hstable : (prefixWord ++ tailWord_944009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944009).length < 2 ^ (prefixWord ++ tailWord_944009).sum := by decide
  have hdescent : baseEnd_944009 < baseStart_944009 := by decide
  rcases family_descends (prefixWord ++ tailWord_944009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944037 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_944037 : Nat := 118140960795 + 944037 * 2 ^ 59
def prefixEnd_944037 : Nat := 4983230072969 + 3 ^ 40 * 944037 * 2
def baseEnd_944037 : Nat := 323163157752418789730639

theorem tailTrace_944037 : CollatzResearch.WordTrace tailWord_944037 prefixEnd_944037 323163157752418789730639 := by
  unfold tailWord_944037
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431858080922652528638365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22954572053948435019092243 34431858080922652528638365)
  ·
    refine ⟨12911946780345994698239387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34431858080922652528638365 12911946780345994698239387)
    ·
      refine ⟨19367920170518992047359081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12911946780345994698239387 19367920170518992047359081)
      ·
        refine ⟨14525940127889244035519311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19367920170518992047359081 14525940127889244035519311)
        ·
          refine ⟨21788910191833866053278967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14525940127889244035519311 21788910191833866053278967)
          ·
            refine ⟨32683365287750799079918451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21788910191833866053278967 32683365287750799079918451)
            ·
              refine ⟨49025047931626198619877677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32683365287750799079918451 49025047931626198619877677)
              ·
                refine ⟨18384392974359824482454129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49025047931626198619877677 18384392974359824482454129)
                ·
                  refine ⟨13788294730769868361840597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18384392974359824482454129 13788294730769868361840597)
                  ·
                    refine ⟨323163157752418789730639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13788294730769868361840597 323163157752418789730639)
                    ·
                      rfl

theorem cell22_944037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_944037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944037 prefixEnd_944037 := by exact prefixLift 944037
  have htrace : WordTrace (prefixWord ++ tailWord_944037) baseStart_944037 baseEnd_944037 := by
    simpa [prefixWord, tailWord_944037, baseEnd_944037] using wordTrace_append hprefix tailTrace_944037
  have hstable : (prefixWord ++ tailWord_944037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944037).length < 2 ^ (prefixWord ++ tailWord_944037).sum := by decide
  have hdescent : baseEnd_944037 < baseStart_944037 := by decide
  rcases family_descends (prefixWord ++ tailWord_944037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944039 : List Nat := [1, 1, 6, 1, 2, 1, 2, 8]
def baseStart_944039 : Nat := 118140960795 + 944039 * 2 ^ 59
def prefixEnd_944039 : Nat := 4983230072969 + 3 ^ 40 * 944039 * 2
def baseEnd_944039 : Nat := 35907093599254605686737

theorem tailTrace_944039 : CollatzResearch.WordTrace tailWord_944039 prefixEnd_944039 35907093599254605686737 := by
  unfold tailWord_944039
  simp only [CollatzResearch.WordTrace]
  refine ⟨34431931026915406870211171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22954620684610271246807447 34431931026915406870211171)
  ·
    refine ⟨51647896540373110305316757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34431931026915406870211171 51647896540373110305316757)
    ·
      refine ⟨2420995150329989545561723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51647896540373110305316757 2420995150329989545561723)
      ·
        refine ⟨3631492725494984318342585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2420995150329989545561723 3631492725494984318342585)
        ·
          refine ⟨2723619544121238238756939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3631492725494984318342585 2723619544121238238756939)
          ·
            refine ⟨4085429316181857358135409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2723619544121238238756939 4085429316181857358135409)
            ·
              refine ⟨3064071987136393018601557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4085429316181857358135409 3064071987136393018601557)
              ·
                refine ⟨35907093599254605686737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3064071987136393018601557 35907093599254605686737)
                ·
                  rfl

theorem cell22_944039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 8].length) (baseStart_944039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944039 prefixEnd_944039 := by exact prefixLift 944039
  have htrace : WordTrace (prefixWord ++ tailWord_944039) baseStart_944039 baseEnd_944039 := by
    simpa [prefixWord, tailWord_944039, baseEnd_944039] using wordTrace_append hprefix tailTrace_944039
  have hstable : (prefixWord ++ tailWord_944039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944039).length < 2 ^ (prefixWord ++ tailWord_944039).sum := by decide
  have hdescent : baseEnd_944039 < baseStart_944039 := by decide
  rcases family_descends (prefixWord ++ tailWord_944039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944060 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_944060 : Nat := 118140960795 + 944060 * 2 ^ 59
def prefixEnd_944060 : Nat := 4983230072969 + 3 ^ 40 * 944060 * 2
def baseEnd_944060 : Nat := 323171031122454396405569

theorem tailTrace_944060 : CollatzResearch.WordTrace tailWord_944060 prefixEnd_944060 323171031122454396405569 := by
  unfold tailWord_944060
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216348479919663728362817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22955131306559551637817089 17216348479919663728362817)
  ·
    refine ⟨12912261359939747796272113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17216348479919663728362817 12912261359939747796272113)
    ·
      refine ⟨9684196019954810847204085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12912261359939747796272113 9684196019954810847204085)
      ·
        refine ⟨907893376870763516925383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9684196019954810847204085 907893376870763516925383)
        ·
          refine ⟨1361840065306145275388075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907893376870763516925383 1361840065306145275388075)
          ·
            refine ⟨2042760097959217913082113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361840065306145275388075 2042760097959217913082113)
            ·
              refine ⟨1532070073469413434811585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2042760097959217913082113 1532070073469413434811585)
              ·
                refine ⟨1149052555102060076108689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532070073469413434811585 1149052555102060076108689)
                ·
                  refine ⟨861789416326545057081517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149052555102060076108689 861789416326545057081517)
                  ·
                    refine ⟨323171031122454396405569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861789416326545057081517 323171031122454396405569)
                    ·
                      rfl

theorem cell22_944060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_944060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944060 prefixEnd_944060 := by exact prefixLift 944060
  have htrace : WordTrace (prefixWord ++ tailWord_944060) baseStart_944060 baseEnd_944060 := by
    simpa [prefixWord, tailWord_944060, baseEnd_944060] using wordTrace_append hprefix tailTrace_944060
  have hstable : (prefixWord ++ tailWord_944060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944060).length < 2 ^ (prefixWord ++ tailWord_944060).sum := by decide
  have hdescent : baseEnd_944060 < baseStart_944060 := by decide
  rcases family_descends (prefixWord ++ tailWord_944060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944092 : List Nat := [2, 2, 6, 1, 1, 2, 1, 1, 2, 4]
def baseStart_944092 : Nat := 118140960795 + 944092 * 2 ^ 59
def prefixEnd_944092 : Nat := 4983230072969 + 3 ^ 40 * 944092 * 2
def baseEnd_944092 : Nat := 323181985376416979605471

theorem tailTrace_944092 : CollatzResearch.WordTrace tailWord_944092 prefixEnd_944092 323181985376416979605471 := by
  unfold tailWord_944092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17216932047861698460945265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22955909397148931281260353 17216932047861698460945265)
  ·
    refine ⟨12912699035896273845708949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17216932047861698460945265 12912699035896273845708949)
    ·
      refine ⟨605282767307637836517607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12912699035896273845708949 605282767307637836517607)
      ·
        refine ⟨907924150961456754776411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605282767307637836517607 907924150961456754776411)
        ·
          refine ⟨1361886226442185132164617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907924150961456754776411 1361886226442185132164617)
          ·
            refine ⟨1021414669831638849123463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1361886226442185132164617 1021414669831638849123463)
            ·
              refine ⟨1532122004747458273685195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021414669831638849123463 1532122004747458273685195)
              ·
                refine ⟨2298183007121187410527793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532122004747458273685195 2298183007121187410527793)
                ·
                  refine ⟨1723637255340890557895845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298183007121187410527793 1723637255340890557895845)
                  ·
                    refine ⟨323181985376416979605471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723637255340890557895845 323181985376416979605471)
                    ·
                      rfl

theorem cell22_944092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_944092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944092 prefixEnd_944092 := by exact prefixLift 944092
  have htrace : WordTrace (prefixWord ++ tailWord_944092) baseStart_944092 baseEnd_944092 := by
    simpa [prefixWord, tailWord_944092, baseEnd_944092] using wordTrace_append hprefix tailTrace_944092
  have hstable : (prefixWord ++ tailWord_944092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944092).length < 2 ^ (prefixWord ++ tailWord_944092).sum := by decide
  have hdescent : baseEnd_944092 < baseStart_944092 := by decide
  rcases family_descends (prefixWord ++ tailWord_944092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944159 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_944159 : Nat := 118140960795 + 944159 * 2 ^ 59
def prefixEnd_944159 : Nat := 4983230072969 + 3 ^ 40 * 944159 * 2
def baseEnd_944159 : Nat := 323204920845651138180265

theorem tailTrace_944159 : CollatzResearch.WordTrace tailWord_944159 prefixEnd_944159 323204920845651138180265 := by
  unfold tailWord_944159
  simp only [CollatzResearch.WordTrace]
  refine ⟨34436307786480667364579531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22957538524320444909719687 34436307786480667364579531)
  ·
    refine ⟨51654461679721001046869297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34436307786480667364579531 51654461679721001046869297)
    ·
      refine ⟨38740846259790750785151973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51654461679721001046869297 38740846259790750785151973)
      ·
        refine ⟨7263908673710765772215995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38740846259790750785151973 7263908673710765772215995)
        ·
          refine ⟨10895863010566148658323993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7263908673710765772215995 10895863010566148658323993)
          ·
            refine ⟨8171897257924611493742995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10895863010566148658323993 8171897257924611493742995)
            ·
              refine ⟨12257845886886917240614493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8171897257924611493742995 12257845886886917240614493)
              ·
                refine ⟨4596692207582593965230435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12257845886886917240614493 4596692207582593965230435)
                ·
                  refine ⟨6895038311373890947845653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4596692207582593965230435 6895038311373890947845653)
                  ·
                    refine ⟨323204920845651138180265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6895038311373890947845653 323204920845651138180265)
                    ·
                      rfl

theorem cell22_944159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_944159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944159 prefixEnd_944159 := by exact prefixLift 944159
  have htrace : WordTrace (prefixWord ++ tailWord_944159) baseStart_944159 baseEnd_944159 := by
    simpa [prefixWord, tailWord_944159, baseEnd_944159] using wordTrace_append hprefix tailTrace_944159
  have hstable : (prefixWord ++ tailWord_944159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944159).length < 2 ^ (prefixWord ++ tailWord_944159).sum := by decide
  have hdescent : baseEnd_944159 < baseStart_944159 := by decide
  rcases family_descends (prefixWord ++ tailWord_944159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944176 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_944176 : Nat := 118140960795 + 944176 * 2 ^ 59
def prefixEnd_944176 : Nat := 4983230072969 + 3 ^ 40 * 944176 * 2
def baseEnd_944176 : Nat := 323210740293068760505213

theorem tailTrace_944176 : CollatzResearch.WordTrace tailWord_944176 prefixEnd_944176 323210740293068760505213 := by
  unfold tailWord_944176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218463913709539633974191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22957951884946052845298921 17218463913709539633974191)
  ·
    refine ⟨25827695870564309450961287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17218463913709539633974191 25827695870564309450961287)
    ·
      refine ⟨38741543805846464176441931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25827695870564309450961287 38741543805846464176441931)
      ·
        refine ⟨58112315708769696264662897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38741543805846464176441931 58112315708769696264662897)
        ·
          refine ⟨43584236781577272198497173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58112315708769696264662897 43584236781577272198497173)
          ·
            refine ⟨2043011099136434634304555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43584236781577272198497173 2043011099136434634304555)
            ·
              refine ⟨3064516648704651951456833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043011099136434634304555 3064516648704651951456833)
              ·
                refine ⟨2298387486528488963592625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3064516648704651951456833 2298387486528488963592625)
                ·
                  refine ⟨1723790614896366722694469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2298387486528488963592625 1723790614896366722694469)
                  ·
                    refine ⟨323210740293068760505213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1723790614896366722694469 323210740293068760505213)
                    ·
                      rfl

theorem cell22_944176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_944176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944176 prefixEnd_944176 := by exact prefixLift 944176
  have htrace : WordTrace (prefixWord ++ tailWord_944176) baseStart_944176 baseEnd_944176 := by
    simpa [prefixWord, tailWord_944176, baseEnd_944176] using wordTrace_append hprefix tailTrace_944176
  have hstable : (prefixWord ++ tailWord_944176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944176).length < 2 ^ (prefixWord ++ tailWord_944176).sum := by decide
  have hdescent : baseEnd_944176 < baseStart_944176 := by decide
  rcases family_descends (prefixWord ++ tailWord_944176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944180 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 6]
def baseStart_944180 : Nat := 118140960795 + 944180 * 2 ^ 59
def prefixEnd_944180 : Nat := 4983230072969 + 3 ^ 40 * 944180 * 2
def baseEnd_944180 : Nat := 107737369858271361135067

theorem tailTrace_944180 : CollatzResearch.WordTrace tailWord_944180 prefixEnd_944180 107737369858271361135067 := by
  unfold tailWord_944180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17218536859702293975546997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22958049146269725300729329 17218536859702293975546997)
  ·
    refine ⟨1614237830597090060207531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17218536859702293975546997 1614237830597090060207531)
    ·
      refine ⟨2421356745895635090311297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614237830597090060207531 2421356745895635090311297)
      ·
        refine ⟨1816017559421726317733473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2421356745895635090311297 1816017559421726317733473)
        ·
          refine ⟨1362013169566294738300105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816017559421726317733473 1362013169566294738300105)
          ·
            refine ⟨1021509877174721053725079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1362013169566294738300105 1021509877174721053725079)
            ·
              refine ⟨1532264815762081580587619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021509877174721053725079 1532264815762081580587619)
              ·
                refine ⟨2298397223643122370881429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532264815762081580587619 2298397223643122370881429)
                ·
                  refine ⟨107737369858271361135067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2298397223643122370881429 107737369858271361135067)
                  ·
                    rfl

theorem cell22_944180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_944180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944180 prefixEnd_944180 := by exact prefixLift 944180
  have htrace : WordTrace (prefixWord ++ tailWord_944180) baseStart_944180 baseEnd_944180 := by
    simpa [prefixWord, tailWord_944180, baseEnd_944180] using wordTrace_append hprefix tailTrace_944180
  have hstable : (prefixWord ++ tailWord_944180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944180).length < 2 ^ (prefixWord ++ tailWord_944180).sum := by decide
  have hdescent : baseEnd_944180 < baseStart_944180 := by decide
  rcases family_descends (prefixWord ++ tailWord_944180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944236 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 5]
def baseStart_944236 : Nat := 118140960795 + 944236 * 2 ^ 59
def prefixEnd_944236 : Nat := 4983230072969 + 3 ^ 40 * 944236 * 2
def baseEnd_944236 : Nat := 107743759839749534668343

theorem tailTrace_944236 : CollatzResearch.WordTrace tailWord_944236 prefixEnd_944236 107743759839749534668343 := by
  unfold tailWord_944236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219558103600854757566281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22959410804801139676755041 17219558103600854757566281)
  ·
    refine ⟨12914668577700641068174711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17219558103600854757566281 12914668577700641068174711)
    ·
      refine ⟨19372002866550961602262067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12914668577700641068174711 19372002866550961602262067)
      ·
        refine ⟨29058004299826442403393101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19372002866550961602262067 29058004299826442403393101)
        ·
          refine ⟨10896751612434915901272413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29058004299826442403393101 10896751612434915901272413)
          ·
            refine ⟨4086281854663093462977155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10896751612434915901272413 4086281854663093462977155)
            ·
              refine ⟨6129422781994640194465733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086281854663093462977155 6129422781994640194465733)
              ·
                refine ⟨1149266771623995036462325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6129422781994640194465733 1149266771623995036462325)
                ·
                  refine ⟨107743759839749534668343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1149266771623995036462325 107743759839749534668343)
                  ·
                    rfl

theorem cell22_944236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_944236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944236 prefixEnd_944236 := by exact prefixLift 944236
  have htrace : WordTrace (prefixWord ++ tailWord_944236) baseStart_944236 baseEnd_944236 := by
    simpa [prefixWord, tailWord_944236, baseEnd_944236] using wordTrace_append hprefix tailTrace_944236
  have hstable : (prefixWord ++ tailWord_944236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944236).length < 2 ^ (prefixWord ++ tailWord_944236).sum := by decide
  have hdescent : baseEnd_944236 < baseStart_944236 := by decide
  rcases family_descends (prefixWord ++ tailWord_944236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944240 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 1, 3]
def baseStart_944240 : Nat := 118140960795 + 944240 * 2 ^ 59
def prefixEnd_944240 : Nat := 4983230072969 + 3 ^ 40 * 944240 * 2
def baseEnd_944240 : Nat := 323232648800993926905017

theorem tailTrace_944240 : CollatzResearch.WordTrace tailWord_944240 prefixEnd_944240 323232648800993926905017 := by
  unfold tailWord_944240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17219631049593609099139087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22959508066124812132185449 17219631049593609099139087)
  ·
    refine ⟨25829446574390413648708631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17219631049593609099139087 25829446574390413648708631)
    ·
      refine ⟨38744169861585620473062947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25829446574390413648708631 38744169861585620473062947)
      ·
        refine ⟨58116254792378430709594421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38744169861585620473062947 58116254792378430709594421)
        ·
          refine ⟨5448398886785477879024477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58116254792378430709594421 5448398886785477879024477)
          ·
            refine ⟨2043149582544554204634179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5448398886785477879024477 2043149582544554204634179)
            ·
              refine ⟨3064724373816831306951269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043149582544554204634179 3064724373816831306951269)
              ·
                refine ⟨574635820090655870053363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3064724373816831306951269 574635820090655870053363)
                ·
                  refine ⟨861953730135983805080045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574635820090655870053363 861953730135983805080045)
                  ·
                    refine ⟨323232648800993926905017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 861953730135983805080045 323232648800993926905017)
                    ·
                      rfl

theorem cell22_944240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_944240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944240 prefixEnd_944240 := by exact prefixLift 944240
  have htrace : WordTrace (prefixWord ++ tailWord_944240) baseStart_944240 baseEnd_944240 := by
    simpa [prefixWord, tailWord_944240, baseEnd_944240] using wordTrace_append hprefix tailTrace_944240
  have hstable : (prefixWord ++ tailWord_944240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944240).length < 2 ^ (prefixWord ++ tailWord_944240).sum := by decide
  have hdescent : baseEnd_944240 < baseStart_944240 := by decide
  rcases family_descends (prefixWord ++ tailWord_944240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944311 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_944311 : Nat := 118140960795 + 944311 * 2 ^ 59
def prefixEnd_944311 : Nat := 4983230072969 + 3 ^ 40 * 944311 * 2
def baseEnd_944311 : Nat := 323256953551973408379799

theorem tailTrace_944311 : CollatzResearch.WordTrace tailWord_944311 prefixEnd_944311 323256953551973408379799 := by
  unfold tailWord_944311
  simp only [CollatzResearch.WordTrace]
  refine ⟨34441851681929997324112787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22961234454619998216075191 34441851681929997324112787)
  ·
    refine ⟨51662777522894995986169181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34441851681929997324112787 51662777522894995986169181)
    ·
      refine ⟨19373541571085623494813443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51662777522894995986169181 19373541571085623494813443)
      ·
        refine ⟨29060312356628435242220165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19373541571085623494813443 29060312356628435242220165)
        ·
          refine ⟨5448808566867831607916281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29060312356628435242220165 5448808566867831607916281)
          ·
            refine ⟨4086606425150873705937211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5448808566867831607916281 4086606425150873705937211)
            ·
              refine ⟨6129909637726310558905817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4086606425150873705937211 6129909637726310558905817)
              ·
                refine ⟨4597432228294732919179363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6129909637726310558905817 4597432228294732919179363)
                ·
                  refine ⟨6896148342442099378769045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4597432228294732919179363 6896148342442099378769045)
                  ·
                    refine ⟨323256953551973408379799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6896148342442099378769045 323256953551973408379799)
                    ·
                      rfl

theorem cell22_944311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_944311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944311 prefixEnd_944311 := by exact prefixLift 944311
  have htrace : WordTrace (prefixWord ++ tailWord_944311) baseStart_944311 baseEnd_944311 := by
    simpa [prefixWord, tailWord_944311, baseEnd_944311] using wordTrace_append hprefix tailTrace_944311
  have hstable : (prefixWord ++ tailWord_944311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944311).length < 2 ^ (prefixWord ++ tailWord_944311).sum := by decide
  have hdescent : baseEnd_944311 < baseStart_944311 := by decide
  rcases family_descends (prefixWord ++ tailWord_944311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944356 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 6]
def baseStart_944356 : Nat := 118140960795 + 944356 * 2 ^ 59
def prefixEnd_944356 : Nat := 4983230072969 + 3 ^ 40 * 944356 * 2
def baseEnd_944356 : Nat := 323272357971608291004661

theorem tailTrace_944356 : CollatzResearch.WordTrace tailWord_944356 prefixEnd_944356 323272357971608291004661 := by
  unfold tailWord_944356
  simp only [CollatzResearch.WordTrace]
  refine ⟨17221746483383485004750461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22962328644511313339667281 17221746483383485004750461)
  ·
    refine ⟨6458154931268806876781423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17221746483383485004750461 6458154931268806876781423)
    ·
      refine ⟨9687232396903210315172135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6458154931268806876781423 9687232396903210315172135)
      ·
        refine ⟨14530848595354815472758203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9687232396903210315172135 14530848595354815472758203)
        ·
          refine ⟨21796272893032223209137305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14530848595354815472758203 21796272893032223209137305)
          ·
            refine ⟨16347204669774167406852979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21796272893032223209137305 16347204669774167406852979)
            ·
              refine ⟨24520807004661251110279469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16347204669774167406852979 24520807004661251110279469)
              ·
                refine ⟨9195302626747969166354801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24520807004661251110279469 9195302626747969166354801)
                ·
                  refine ⟨6896476970060976874766101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9195302626747969166354801 6896476970060976874766101)
                  ·
                    refine ⟨323272357971608291004661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6896476970060976874766101 323272357971608291004661)
                    ·
                      rfl

theorem cell22_944356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_944356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944356 prefixEnd_944356 := by exact prefixLift 944356
  have htrace : WordTrace (prefixWord ++ tailWord_944356) baseStart_944356 baseEnd_944356 := by
    simpa [prefixWord, tailWord_944356, baseEnd_944356] using wordTrace_append hprefix tailTrace_944356
  have hstable : (prefixWord ++ tailWord_944356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944356).length < 2 ^ (prefixWord ++ tailWord_944356).sum := by decide
  have hdescent : baseEnd_944356 < baseStart_944356 := by decide
  rcases family_descends (prefixWord ++ tailWord_944356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944465 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 4, 3]
def baseStart_944465 : Nat := 118140960795 + 944465 * 2 ^ 59
def prefixEnd_944465 : Nat := 4983230072969 + 3 ^ 40 * 944465 * 2
def baseEnd_944465 : Nat := 323309670899168340029327

theorem tailTrace_944465 : CollatzResearch.WordTrace tailWord_944465 prefixEnd_944465 323309670899168340029327 := by
  unfold tailWord_944465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34447468523372081625218849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22964979015581387750145899 34447468523372081625218849)
  ·
    refine ⟨25835601392529061218914137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34447468523372081625218849 25835601392529061218914137)
    ·
      refine ⟨19376701044396795914185603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25835601392529061218914137 19376701044396795914185603)
      ·
        refine ⟨29065051566595193871278405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19376701044396795914185603 29065051566595193871278405)
        ·
          refine ⟨5449697168736598850864701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29065051566595193871278405 5449697168736598850864701)
          ·
            refine ⟨2043636438276224569074263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5449697168736598850864701 2043636438276224569074263)
            ·
              refine ⟨3065454657414336853611395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043636438276224569074263 3065454657414336853611395)
              ·
                refine ⟨4598181986121505280417093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065454657414336853611395 4598181986121505280417093)
                ·
                  refine ⟨862159122397782240078205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4598181986121505280417093 862159122397782240078205)
                  ·
                    refine ⟨323309670899168340029327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862159122397782240078205 323309670899168340029327)
                    ·
                      rfl

theorem cell22_944465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_944465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944465 prefixEnd_944465 := by exact prefixLift 944465
  have htrace : WordTrace (prefixWord ++ tailWord_944465) baseStart_944465 baseEnd_944465 := by
    simpa [prefixWord, tailWord_944465, baseEnd_944465] using wordTrace_append hprefix tailTrace_944465
  have hstable : (prefixWord ++ tailWord_944465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944465).length < 2 ^ (prefixWord ++ tailWord_944465).sum := by decide
  have hdescent : baseEnd_944465 < baseStart_944465 := by decide
  rcases family_descends (prefixWord ++ tailWord_944465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944482 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_944482 : Nat := 118140960795 + 944482 * 2 ^ 59
def prefixEnd_944482 : Nat := 4983230072969 + 3 ^ 40 * 944482 * 2
def baseEnd_944482 : Nat := 323315490346585962354275

theorem tailTrace_944482 : CollatzResearch.WordTrace tailWord_944482 prefixEnd_944482 323315490346585962354275 := by
  unfold tailWord_944482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612022141077623382146925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22965392376206995685725133 8612022141077623382146925)
  ·
    refine ⟨3229508302904108768305097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8612022141077623382146925 3229508302904108768305097)
    ·
      refine ⟨2422131227178081576228823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3229508302904108768305097 2422131227178081576228823)
      ·
        refine ⟨3633196840767122364343235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422131227178081576228823 3633196840767122364343235)
        ·
          refine ⟨5449795261150683546514853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633196840767122364343235 5449795261150683546514853)
          ·
            refine ⟨1021836611465753164971535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5449795261150683546514853 1021836611465753164971535)
            ·
              refine ⟨1532754917198629747457303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021836611465753164971535 1532754917198629747457303)
              ·
                refine ⟨2299132375797944621185955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1532754917198629747457303 2299132375797944621185955)
                ·
                  refine ⟨3448698563696916931778933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2299132375797944621185955 3448698563696916931778933)
                  ·
                    refine ⟨323315490346585962354275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3448698563696916931778933 323315490346585962354275)
                    ·
                      rfl

theorem cell22_944482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_944482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944482 prefixEnd_944482 := by exact prefixLift 944482
  have htrace : WordTrace (prefixWord ++ tailWord_944482) baseStart_944482 baseEnd_944482 := by
    simpa [prefixWord, tailWord_944482, baseEnd_944482] using wordTrace_append hprefix tailTrace_944482
  have hstable : (prefixWord ++ tailWord_944482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944482).length < 2 ^ (prefixWord ++ tailWord_944482).sum := by decide
  have hdescent : baseEnd_944482 < baseStart_944482 := by decide
  rcases family_descends (prefixWord ++ tailWord_944482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944493 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_944493 : Nat := 118140960795 + 944493 * 2 ^ 59
def prefixEnd_944493 : Nat := 4983230072969 + 3 ^ 40 * 944493 * 2
def baseEnd_944493 : Nat := 323319255871385600329241

theorem tailTrace_944493 : CollatzResearch.WordTrace tailWord_944493 prefixEnd_944493 323319255871385600329241 := by
  unfold tailWord_944493
  simp only [CollatzResearch.WordTrace]
  refine ⟨34448489767270642407238133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22965659844847094938158755 34448489767270642407238133)
  ·
    refine ⟨3229545915681622725678575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34448489767270642407238133 3229545915681622725678575)
    ·
      refine ⟨4844318873522434088517863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3229545915681622725678575 4844318873522434088517863)
      ·
        refine ⟨7266478310283651132776795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4844318873522434088517863 7266478310283651132776795)
        ·
          refine ⟨10899717465425476699165193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7266478310283651132776795 10899717465425476699165193)
          ·
            refine ⟨8174788099069107524373895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10899717465425476699165193 8174788099069107524373895)
            ·
              refine ⟨12262182148603661286560843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8174788099069107524373895 12262182148603661286560843)
              ·
                refine ⟨18393273222905491929841265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12262182148603661286560843 18393273222905491929841265)
                ·
                  refine ⟨13794954917179118947380949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18393273222905491929841265 13794954917179118947380949)
                  ·
                    refine ⟨323319255871385600329241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13794954917179118947380949 323319255871385600329241)
                    ·
                      rfl

theorem cell22_944493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_944493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944493 prefixEnd_944493 := by exact prefixLift 944493
  have htrace : WordTrace (prefixWord ++ tailWord_944493) baseStart_944493 baseEnd_944493 := by
    simpa [prefixWord, tailWord_944493, baseEnd_944493] using wordTrace_append hprefix tailTrace_944493
  have hstable : (prefixWord ++ tailWord_944493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944493).length < 2 ^ (prefixWord ++ tailWord_944493).sum := by decide
  have hdescent : baseEnd_944493 < baseStart_944493 := by decide
  rcases family_descends (prefixWord ++ tailWord_944493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944514 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 2, 4]
def baseStart_944514 : Nat := 118140960795 + 944514 * 2 ^ 59
def prefixEnd_944514 : Nat := 4983230072969 + 3 ^ 40 * 944514 * 2
def baseEnd_944514 : Nat := 323326444600548545554177

theorem tailTrace_944514 : CollatzResearch.WordTrace tailWord_944514 prefixEnd_944514 323326444600548545554177 := by
  unfold tailWord_944514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612313925048640748438149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22966170466796375329168397 8612313925048640748438149)
  ·
    refine ⟨1614808860946620140332153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8612313925048640748438149 1614808860946620140332153)
    ·
      refine ⟨1211106645709965105249115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1614808860946620140332153 1211106645709965105249115)
      ·
        refine ⟨1816659968564947657873673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211106645709965105249115 1816659968564947657873673)
        ·
          refine ⟨1362494976423710743405255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1816659968564947657873673 1362494976423710743405255)
          ·
            refine ⟨2043742464635566115107883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362494976423710743405255 2043742464635566115107883)
            ·
              refine ⟨3065613696953349172661825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2043742464635566115107883 3065613696953349172661825)
              ·
                refine ⟨2299210272715011879496369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3065613696953349172661825 2299210272715011879496369)
                ·
                  refine ⟨1724407704536258909622277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2299210272715011879496369 1724407704536258909622277)
                  ·
                    refine ⟨323326444600548545554177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724407704536258909622277 323326444600548545554177)
                    ·
                      rfl

theorem cell22_944514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_944514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944514 prefixEnd_944514 := by exact prefixLift 944514
  have htrace : WordTrace (prefixWord ++ tailWord_944514) baseStart_944514 baseEnd_944514 := by
    simpa [prefixWord, tailWord_944514, baseEnd_944514] using wordTrace_append hprefix tailTrace_944514
  have hstable : (prefixWord ++ tailWord_944514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944514).length < 2 ^ (prefixWord ++ tailWord_944514).sum := by decide
  have hdescent : baseEnd_944514 < baseStart_944514 := by decide
  rcases family_descends (prefixWord ++ tailWord_944514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944523 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 7]
def baseStart_944523 : Nat := 118140960795 + 944523 * 2 ^ 59
def prefixEnd_944523 : Nat := 4983230072969 + 3 ^ 40 * 944523 * 2
def baseEnd_944523 : Nat := 107776508494825174026383

theorem tailTrace_944523 : CollatzResearch.WordTrace tailWord_944523 prefixEnd_944523 107776508494825174026383 := by
  unfold tailWord_944523
  simp only [CollatzResearch.WordTrace]
  refine ⟨34449583957161957530830223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22966389304774638353886815 34449583957161957530830223)
  ·
    refine ⟨51674375935742936296245335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34449583957161957530830223 51674375935742936296245335)
    ·
      refine ⟨77511563903614404444368003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51674375935742936296245335 77511563903614404444368003)
      ·
        refine ⟨116267345855421606666552005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77511563903614404444368003 116267345855421606666552005)
        ·
          refine ⟨21800127347891551249978501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116267345855421606666552005 21800127347891551249978501)
          ·
            refine ⟨4087523877729665859370969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21800127347891551249978501 4087523877729665859370969)
            ·
              refine ⟨3065642908297249394528227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4087523877729665859370969 3065642908297249394528227)
              ·
                refine ⟨4598464362445874091792341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065642908297249394528227 4598464362445874091792341)
                ·
                  refine ⟨107776508494825174026383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4598464362445874091792341 107776508494825174026383)
                  ·
                    rfl

theorem cell22_944523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_944523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944523 prefixEnd_944523 := by exact prefixLift 944523
  have htrace : WordTrace (prefixWord ++ tailWord_944523) baseStart_944523 baseEnd_944523 := by
    simpa [prefixWord, tailWord_944523, baseEnd_944523] using wordTrace_append hprefix tailTrace_944523
  have hstable : (prefixWord ++ tailWord_944523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944523).length < 2 ^ (prefixWord ++ tailWord_944523).sum := by decide
  have hdescent : baseEnd_944523 < baseStart_944523 := by decide
  rcases family_descends (prefixWord ++ tailWord_944523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944570 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 1, 4]
def baseStart_944570 : Nat := 118140960795 + 944570 * 2 ^ 59
def prefixEnd_944570 : Nat := 4983230072969 + 3 ^ 40 * 944570 * 2
def baseEnd_944570 : Nat := 323345614544983066154005

theorem tailTrace_944570 : CollatzResearch.WordTrace tailWord_944570 prefixEnd_944570 323345614544983066154005 := by
  unfold tailWord_944570
  simp only [CollatzResearch.WordTrace]
  refine ⟨8612824546997921139447791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22967532125327789705194109 8612824546997921139447791)
  ·
    refine ⟨12919236820496881709171687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8612824546997921139447791 12919236820496881709171687)
    ·
      refine ⟨19378855230745322563757531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12919236820496881709171687 19378855230745322563757531)
      ·
        refine ⟨29068282846117983845636297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19378855230745322563757531 29068282846117983845636297)
        ·
          refine ⟨21801212134588487884227223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29068282846117983845636297 21801212134588487884227223)
          ·
            refine ⟨32701818201882731826340835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21801212134588487884227223 32701818201882731826340835)
            ·
              refine ⟨49052727302824097739511253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32701818201882731826340835 49052727302824097739511253)
              ·
                refine ⟨1149673296159939790769795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49052727302824097739511253 1149673296159939790769795)
                ·
                  refine ⟨1724509944239909686154693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149673296159939790769795 1724509944239909686154693)
                  ·
                    refine ⟨323345614544983066154005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724509944239909686154693 323345614544983066154005)
                    ·
                      rfl

theorem cell22_944570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_944570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944570 prefixEnd_944570 := by exact prefixLift 944570
  have htrace : WordTrace (prefixWord ++ tailWord_944570) baseStart_944570 baseEnd_944570 := by
    simpa [prefixWord, tailWord_944570, baseEnd_944570] using wordTrace_append hprefix tailTrace_944570
  have hstable : (prefixWord ++ tailWord_944570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944570).length < 2 ^ (prefixWord ++ tailWord_944570).sum := by decide
  have hdescent : baseEnd_944570 < baseStart_944570 := by decide
  rcases family_descends (prefixWord ++ tailWord_944570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944600 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_944600 : Nat := 118140960795 + 944600 * 2 ^ 59
def prefixEnd_944600 : Nat := 4983230072969 + 3 ^ 40 * 944600 * 2
def baseEnd_944600 : Nat := 323355884158072987903913

theorem tailTrace_944600 : CollatzResearch.WordTrace tailWord_944600 prefixEnd_944600 323355884158072987903913 := by
  unfold tailWord_944600
  simp only [CollatzResearch.WordTrace]
  refine ⟨17226196188941499840691627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22968261585255333120922169 17226196188941499840691627)
  ·
    refine ⟨25839294283412249761037441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17226196188941499840691627 25839294283412249761037441)
    ·
      refine ⟨19379470712559187320778081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25839294283412249761037441 19379470712559187320778081)
      ·
        refine ⟨14534603034419390490583561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19379470712559187320778081 14534603034419390490583561)
        ·
          refine ⟨10900952275814542867937671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14534603034419390490583561 10900952275814542867937671)
          ·
            refine ⟨16351428413721814301906507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10900952275814542867937671 16351428413721814301906507)
            ·
              refine ⟨24527142620582721452859761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16351428413721814301906507 24527142620582721452859761)
              ·
                refine ⟨18395356965437041089644821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24527142620582721452859761 18395356965437041089644821)
                ·
                  refine ⟨862282357754861301077101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 18395356965437041089644821 862282357754861301077101)
                  ·
                    refine ⟨323355884158072987903913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862282357754861301077101 323355884158072987903913)
                    ·
                      rfl

theorem cell22_944600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_944600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944600 prefixEnd_944600 := by exact prefixLift 944600
  have htrace : WordTrace (prefixWord ++ tailWord_944600) baseStart_944600 baseEnd_944600 := by
    simpa [prefixWord, tailWord_944600, baseEnd_944600] using wordTrace_append hprefix tailTrace_944600
  have hstable : (prefixWord ++ tailWord_944600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944600).length < 2 ^ (prefixWord ++ tailWord_944600).sum := by decide
  have hdescent : baseEnd_944600 < baseStart_944600 := by decide
  rcases family_descends (prefixWord ++ tailWord_944600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944615 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_944615 : Nat := 118140960795 + 944615 * 2 ^ 59
def prefixEnd_944615 : Nat := 4983230072969 + 3 ^ 40 * 944615 * 2
def baseEnd_944615 : Nat := 323361018964617948778867

theorem tailTrace_944615 : CollatzResearch.WordTrace tailWord_944615 prefixEnd_944615 323361018964617948778867 := by
  unfold tailWord_944615
  simp only [CollatzResearch.WordTrace]
  refine ⟨34452939472828657243179299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22968626315219104828786199 34452939472828657243179299)
  ·
    refine ⟨51679409209242985864768949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34452939472828657243179299 51679409209242985864768949)
    ·
      refine ⟨4844944613366529924822089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51679409209242985864768949 4844944613366529924822089)
      ·
        refine ⟨3633708460024897443616567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4844944613366529924822089 3633708460024897443616567)
        ·
          refine ⟨5450562690037346165424851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3633708460024897443616567 5450562690037346165424851)
          ·
            refine ⟨8175844035056019248137277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450562690037346165424851 8175844035056019248137277)
            ·
              refine ⟨3065941513146007218051479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8175844035056019248137277 3065941513146007218051479)
              ·
                refine ⟨4598912269719010827077219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3065941513146007218051479 4598912269719010827077219)
                ·
                  refine ⟨6898368404578516240615829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4598912269719010827077219 6898368404578516240615829)
                  ·
                    refine ⟨323361018964617948778867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6898368404578516240615829 323361018964617948778867)
                    ·
                      rfl

theorem cell22_944615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_944615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944615 prefixEnd_944615 := by exact prefixLift 944615
  have htrace : WordTrace (prefixWord ++ tailWord_944615) baseStart_944615 baseEnd_944615 := by
    simpa [prefixWord, tailWord_944615, baseEnd_944615] using wordTrace_append hprefix tailTrace_944615
  have hstable : (prefixWord ++ tailWord_944615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944615).length < 2 ^ (prefixWord ++ tailWord_944615).sum := by decide
  have hdescent : baseEnd_944615 < baseStart_944615 := by decide
  rcases family_descends (prefixWord ++ tailWord_944615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944621 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_944621 : Nat := 118140960795 + 944621 * 2 ^ 59
def prefixEnd_944621 : Nat := 4983230072969 + 3 ^ 40 * 944621 * 2
def baseEnd_944621 : Nat := 323363072887235933128849

theorem tailTrace_944621 : CollatzResearch.WordTrace tailWord_944621 prefixEnd_944621 323363072887235933128849 := by
  unfold tailWord_944621
  simp only [CollatzResearch.WordTrace]
  refine ⟨34453158310806920267897717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22968772207204613511931811 34453158310806920267897717)
  ·
    refine ⟨3229983591638148775115411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34453158310806920267897717 3229983591638148775115411)
    ·
      refine ⟨4844975387457223162673117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3229983591638148775115411 4844975387457223162673117)
      ·
        refine ⟨1816865770296458686002419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4844975387457223162673117 1816865770296458686002419)
        ·
          refine ⟨2725298655444688029003629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816865770296458686002419 2725298655444688029003629)
          ·
            refine ⟨1021986995791758010876361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2725298655444688029003629 1021986995791758010876361)
            ·
              refine ⟨766490246843818508157271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021986995791758010876361 766490246843818508157271)
              ·
                refine ⟨1149735370265727762235907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766490246843818508157271 1149735370265727762235907)
                ·
                  refine ⟨1724603055398591643353861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149735370265727762235907 1724603055398591643353861)
                  ·
                    refine ⟨323363072887235933128849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724603055398591643353861 323363072887235933128849)
                    ·
                      rfl

theorem cell22_944621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_944621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944621 prefixEnd_944621 := by exact prefixLift 944621
  have htrace : WordTrace (prefixWord ++ tailWord_944621) baseStart_944621 baseEnd_944621 := by
    simpa [prefixWord, tailWord_944621, baseEnd_944621] using wordTrace_append hprefix tailTrace_944621
  have hstable : (prefixWord ++ tailWord_944621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944621).length < 2 ^ (prefixWord ++ tailWord_944621).sum := by decide
  have hdescent : baseEnd_944621 < baseStart_944621 := by decide
  rcases family_descends (prefixWord ++ tailWord_944621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944630 : List Nat := [5, 1, 1, 1, 2, 1, 11]
def baseStart_944630 : Nat := 118140960795 + 944630 * 2 ^ 59
def prefixEnd_944630 : Nat := 4983230072969 + 3 ^ 40 * 944630 * 2
def baseEnd_944630 : Nat := 11976524213746774431623

theorem tailTrace_944630 : CollatzResearch.WordTrace tailWord_944630 prefixEnd_944630 11976524213746774431623 := by
  unfold tailWord_944630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2153342910485894675310959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22968991045182876536650229 2153342910485894675310959)
  ·
    refine ⟨3230014365728842012966439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2153342910485894675310959 3230014365728842012966439)
    ·
      refine ⟨4845021548593263019449659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230014365728842012966439 4845021548593263019449659)
      ·
        refine ⟨7267532322889894529174489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845021548593263019449659 7267532322889894529174489)
        ·
          refine ⟨5450649242167420896880867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7267532322889894529174489 5450649242167420896880867)
          ·
            refine ⟨8175973863251131345321301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5450649242167420896880867 8175973863251131345321301)
            ·
              refine ⟨11976524213746774431623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 8175973863251131345321301 11976524213746774431623)
              ·
                rfl

theorem cell22_944630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 11].length) (baseStart_944630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944630 prefixEnd_944630 := by exact prefixLift 944630
  have htrace : WordTrace (prefixWord ++ tailWord_944630) baseStart_944630 baseEnd_944630 := by
    simpa [prefixWord, tailWord_944630, baseEnd_944630] using wordTrace_append hprefix tailTrace_944630
  have hstable : (prefixWord ++ tailWord_944630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944630).length < 2 ^ (prefixWord ++ tailWord_944630).sum := by decide
  have hdescent : baseEnd_944630 < baseStart_944630 := by decide
  rcases family_descends (prefixWord ++ tailWord_944630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944675 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 7]
def baseStart_944675 : Nat := 118140960795 + 944675 * 2 ^ 59
def prefixEnd_944675 : Nat := 4983230072969 + 3 ^ 40 * 944675 * 2
def baseEnd_944675 : Nat := 107793852730265930759561

theorem tailTrace_944675 : CollatzResearch.WordTrace tailWord_944675 prefixEnd_944675 107793852730265930759561 := by
  unfold tailWord_944675
  simp only [CollatzResearch.WordTrace]
  refine ⟨34455127852611287490363479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22970085235074191660242319 34455127852611287490363479)
  ·
    refine ⟨51682691778916931235545219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34455127852611287490363479 51682691778916931235545219)
    ·
      refine ⟨77524037668375396853317829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51682691778916931235545219 77524037668375396853317829)
      ·
        refine ⟨14535757062820386909997093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77524037668375396853317829 14535757062820386909997093)
        ·
          refine ⟨2725454449278822545624455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14535757062820386909997093 2725454449278822545624455)
          ·
            refine ⟨4088181673918233818436683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2725454449278822545624455 4088181673918233818436683)
            ·
              refine ⟨6132272510877350727655025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4088181673918233818436683 6132272510877350727655025)
              ·
                refine ⟨4599204383158013045741269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6132272510877350727655025 4599204383158013045741269)
                ·
                  refine ⟨107793852730265930759561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4599204383158013045741269 107793852730265930759561)
                  ·
                    rfl

theorem cell22_944675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_944675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944675 prefixEnd_944675 := by exact prefixLift 944675
  have htrace : WordTrace (prefixWord ++ tailWord_944675) baseStart_944675 baseEnd_944675 := by
    simpa [prefixWord, tailWord_944675, baseEnd_944675] using wordTrace_append hprefix tailTrace_944675
  have hstable : (prefixWord ++ tailWord_944675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944675).length < 2 ^ (prefixWord ++ tailWord_944675).sum := by decide
  have hdescent : baseEnd_944675 < baseStart_944675 := by decide
  rcases family_descends (prefixWord ++ tailWord_944675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944690 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 4, 5]
def baseStart_944690 : Nat := 118140960795 + 944690 * 2 ^ 59
def prefixEnd_944690 : Nat := 4983230072969 + 3 ^ 40 * 944690 * 2
def baseEnd_944690 : Nat := 323386692997342753153637

theorem tailTrace_944690 : CollatzResearch.WordTrace tailWord_944690 prefixEnd_944690 323386692997342753153637 := by
  unfold tailWord_944690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613918736889236263039881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22970449965037963368106349 8613918736889236263039881)
  ·
    refine ⟨6460439052666927197279911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8613918736889236263039881 6460439052666927197279911)
    ·
      refine ⟨9690658579000390795919867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6460439052666927197279911 9690658579000390795919867)
      ·
        refine ⟨14535987868500586193879801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9690658579000390795919867 14535987868500586193879801)
        ·
          refine ⟨10901990901375439645409851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14535987868500586193879801 10901990901375439645409851)
          ·
            refine ⟨16352986352063159468114777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10901990901375439645409851 16352986352063159468114777)
            ·
              refine ⟨12264739764047369601086083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16352986352063159468114777 12264739764047369601086083)
              ·
                refine ⟨18397109646071054401629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12264739764047369601086083 18397109646071054401629125)
                ·
                  refine ⟨3449458058638322700305461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18397109646071054401629125 3449458058638322700305461)
                  ·
                    refine ⟨323386692997342753153637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3449458058638322700305461 323386692997342753153637)
                    ·
                      rfl

theorem cell22_944690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_944690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944690 prefixEnd_944690 := by exact prefixLift 944690
  have htrace : WordTrace (prefixWord ++ tailWord_944690) baseStart_944690 baseEnd_944690 := by
    simpa [prefixWord, tailWord_944690, baseEnd_944690] using wordTrace_append hprefix tailTrace_944690
  have hstable : (prefixWord ++ tailWord_944690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944690).length < 2 ^ (prefixWord ++ tailWord_944690).sum := by decide
  have hdescent : baseEnd_944690 < baseStart_944690 := by decide
  rcases family_descends (prefixWord ++ tailWord_944690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944696 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 1, 3]
def baseStart_944696 : Nat := 118140960795 + 944696 * 2 ^ 59
def prefixEnd_944696 : Nat := 4983230072969 + 3 ^ 40 * 944696 * 2
def baseEnd_944696 : Nat := 323388746919960737503619

theorem tailTrace_944696 : CollatzResearch.WordTrace tailWord_944696 prefixEnd_944696 323388746919960737503619 := by
  unfold tailWord_944696
  simp only [CollatzResearch.WordTrace]
  refine ⟨17227946892767604038438971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22970595857023472051251961 17227946892767604038438971)
  ·
    refine ⟨25841920339151406057658457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17227946892767604038438971 25841920339151406057658457)
    ·
      refine ⟨19381440254363554543243843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25841920339151406057658457 19381440254363554543243843)
      ·
        refine ⟨29072160381545331814865765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381440254363554543243843 29072160381545331814865765)
        ·
          refine ⟨5451030071539749715287331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29072160381545331814865765 5451030071539749715287331)
          ·
            refine ⟨8176545107309624572930997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451030071539749715287331 8176545107309624572930997)
            ·
              refine ⟨766551103810277303712281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8176545107309624572930997 766551103810277303712281)
              ·
                refine ⟨574913327857707977784211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 766551103810277303712281 574913327857707977784211)
                ·
                  refine ⟨862369991786561966676317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 574913327857707977784211 862369991786561966676317)
                  ·
                    refine ⟨323388746919960737503619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862369991786561966676317 323388746919960737503619)
                    ·
                      rfl

theorem cell22_944696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_944696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944696 prefixEnd_944696 := by exact prefixLift 944696
  have htrace : WordTrace (prefixWord ++ tailWord_944696) baseStart_944696 baseEnd_944696 := by
    simpa [prefixWord, tailWord_944696, baseEnd_944696] using wordTrace_append hprefix tailTrace_944696
  have hstable : (prefixWord ++ tailWord_944696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944696).length < 2 ^ (prefixWord ++ tailWord_944696).sum := by decide
  have hdescent : baseEnd_944696 < baseStart_944696 := by decide
  rcases family_descends (prefixWord ++ tailWord_944696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944709 : List Nat := [1, 3, 1, 1, 1, 7, 2, 1, 5]
def baseStart_944709 : Nat := 118140960795 + 944709 * 2 ^ 59
def prefixEnd_944709 : Nat := 4983230072969 + 3 ^ 40 * 944709 * 2
def baseEnd_944709 : Nat := 107797732361877678976193

theorem tailTrace_944709 : CollatzResearch.WordTrace tailWord_944709 prefixEnd_944709 107797732361877678976193 := by
  unfold tailWord_944709
  simp only [CollatzResearch.WordTrace]
  refine ⟨34456367934488111297101181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22970911956325407531400787 34456367934488111297101181)
  ·
    refine ⟨12921137975433041736412943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34456367934488111297101181 12921137975433041736412943)
    ·
      refine ⟨19381706963149562604619415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12921137975433041736412943 19381706963149562604619415)
      ·
        refine ⟨29072560444724343906929123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19381706963149562604619415 29072560444724343906929123)
        ·
          refine ⟨43608840667086515860393685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29072560444724343906929123 43608840667086515860393685)
          ·
            refine ⟨1022082203134840215477977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43608840667086515860393685 1022082203134840215477977)
            ·
              refine ⟨766561652351130161608483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022082203134840215477977 766561652351130161608483)
              ·
                refine ⟨1149842478526695242412725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766561652351130161608483 1149842478526695242412725)
                ·
                  refine ⟨107797732361877678976193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1149842478526695242412725 107797732361877678976193)
                  ·
                    rfl

theorem cell22_944709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_944709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944709 prefixEnd_944709 := by exact prefixLift 944709
  have htrace : WordTrace (prefixWord ++ tailWord_944709) baseStart_944709 baseEnd_944709 := by
    simpa [prefixWord, tailWord_944709, baseEnd_944709] using wordTrace_append hprefix tailTrace_944709
  have hstable : (prefixWord ++ tailWord_944709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944709).length < 2 ^ (prefixWord ++ tailWord_944709).sum := by decide
  have hdescent : baseEnd_944709 < baseStart_944709 := by decide
  rcases family_descends (prefixWord ++ tailWord_944709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944722 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_944722 : Nat := 118140960795 + 944722 * 2 ^ 59
def prefixEnd_944722 : Nat := 4983230072969 + 3 ^ 40 * 944722 * 2
def baseEnd_944722 : Nat := 323397647251305336353539

theorem tailTrace_944722 : CollatzResearch.WordTrace tailWord_944722 prefixEnd_944722 323397647251305336353539 := by
  unfold tailWord_944722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8614210520860253629331105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22971228055627343011549613 8614210520860253629331105)
  ·
    refine ⟨6460657890645190221998329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8614210520860253629331105 6460657890645190221998329)
    ·
      refine ⟨4845493417983892666498747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6460657890645190221998329 4845493417983892666498747)
      ·
        refine ⟨7268240126975838999748121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4845493417983892666498747 7268240126975838999748121)
        ·
          refine ⟨5451180095231879249811091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7268240126975838999748121 5451180095231879249811091)
          ·
            refine ⟨8176770142847818874716637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451180095231879249811091 8176770142847818874716637)
            ·
              refine ⟨3066288803567932078018739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8176770142847818874716637 3066288803567932078018739)
              ·
                refine ⟨4599433205351898117028109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066288803567932078018739 4599433205351898117028109)
                ·
                  refine ⟨1724787452006961793885541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4599433205351898117028109 1724787452006961793885541)
                  ·
                    refine ⟨323397647251305336353539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724787452006961793885541 323397647251305336353539)
                    ·
                      rfl

theorem cell22_944722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_944722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944722 prefixEnd_944722 := by exact prefixLift 944722
  have htrace : WordTrace (prefixWord ++ tailWord_944722) baseStart_944722 baseEnd_944722 := by
    simpa [prefixWord, tailWord_944722, baseEnd_944722] using wordTrace_append hprefix tailTrace_944722
  have hstable : (prefixWord ++ tailWord_944722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944722).length < 2 ^ (prefixWord ++ tailWord_944722).sum := by decide
  have hdescent : baseEnd_944722 < baseStart_944722 := by decide
  rcases family_descends (prefixWord ++ tailWord_944722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944739 : List Nat := [1, 1, 1, 5, 1, 2, 5, 1, 1, 4]
def baseStart_944739 : Nat := 118140960795 + 944739 * 2 ^ 59
def prefixEnd_944739 : Nat := 4983230072969 + 3 ^ 40 * 944739 * 2
def baseEnd_944739 : Nat := 323403466698722958678487

theorem tailTrace_944739 : CollatzResearch.WordTrace tailWord_944739 prefixEnd_944739 323403466698722958678487 := by
  unfold tailWord_944739
  simp only [CollatzResearch.WordTrace]
  refine ⟨34457462124379426420693271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22971641416252950947128847 34457462124379426420693271)
  ·
    refine ⟨51686193186569139631039907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34457462124379426420693271 51686193186569139631039907)
    ·
      refine ⟨77529289779853709446559861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51686193186569139631039907 77529289779853709446559861)
      ·
        refine ⟨7268370916861285260614987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77529289779853709446559861 7268370916861285260614987)
        ·
          refine ⟨10902556375291927890922481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7268370916861285260614987 10902556375291927890922481)
          ·
            refine ⟨8176917281468945918191861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10902556375291927890922481 8176917281468945918191861)
            ·
              refine ⟨766585995137713679830487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8176917281468945918191861 766585995137713679830487)
              ·
                refine ⟨1149878992706570519745731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 766585995137713679830487 1149878992706570519745731)
                ·
                  refine ⟨1724818489059855779618597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1149878992706570519745731 1724818489059855779618597)
                  ·
                    refine ⟨323403466698722958678487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1724818489059855779618597 323403466698722958678487)
                    ·
                      rfl

theorem cell22_944739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 1, 1, 4].length) (baseStart_944739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944739 prefixEnd_944739 := by exact prefixLift 944739
  have htrace : WordTrace (prefixWord ++ tailWord_944739) baseStart_944739 baseEnd_944739 := by
    simpa [prefixWord, tailWord_944739, baseEnd_944739] using wordTrace_append hprefix tailTrace_944739
  have hstable : (prefixWord ++ tailWord_944739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944739).length < 2 ^ (prefixWord ++ tailWord_944739).sum := by decide
  have hdescent : baseEnd_944739 < baseStart_944739 := by decide
  rcases family_descends (prefixWord ++ tailWord_944739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944769 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 2, 3]
def baseStart_944769 : Nat := 118140960795 + 944769 * 2 ^ 59
def prefixEnd_944769 : Nat := 4983230072969 + 3 ^ 40 * 944769 * 2
def baseEnd_944769 : Nat := 323413736311812880428395

theorem tailTrace_944769 : CollatzResearch.WordTrace tailWord_944769 prefixEnd_944769 323413736311812880428395 := by
  unfold tailWord_944769
  simp only [CollatzResearch.WordTrace]
  refine ⟨34458556314270741544285361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22972370876180494362856907 34458556314270741544285361)
  ·
    refine ⟨25843917235703056158214021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34458556314270741544285361 25843917235703056158214021)
    ·
      refine ⟨4845734481694323029665129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25843917235703056158214021 4845734481694323029665129)
      ·
        refine ⟨3634300861270742272248847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4845734481694323029665129 3634300861270742272248847)
        ·
          refine ⟨5451451291906113408373271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3634300861270742272248847 5451451291906113408373271)
          ·
            refine ⟨8177176937859170112559907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5451451291906113408373271 8177176937859170112559907)
            ·
              refine ⟨12265765406788755168839861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8177176937859170112559907 12265765406788755168839861)
              ·
                refine ⟨1149915506886445797078737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12265765406788755168839861 1149915506886445797078737)
                ·
                  refine ⟨862436630164834347809053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1149915506886445797078737 862436630164834347809053)
                  ·
                    refine ⟨323413736311812880428395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862436630164834347809053 323413736311812880428395)
                    ·
                      rfl

theorem cell22_944769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_944769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944769 prefixEnd_944769 := by exact prefixLift 944769
  have htrace : WordTrace (prefixWord ++ tailWord_944769) baseStart_944769 baseEnd_944769 := by
    simpa [prefixWord, tailWord_944769, baseEnd_944769] using wordTrace_append hprefix tailTrace_944769
  have hstable : (prefixWord ++ tailWord_944769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944769).length < 2 ^ (prefixWord ++ tailWord_944769).sum := by decide
  have hdescent : baseEnd_944769 < baseStart_944769 := by decide
  rcases family_descends (prefixWord ++ tailWord_944769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944780 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_944780 : Nat := 118140960795 + 944780 * 2 ^ 59
def prefixEnd_944780 : Nat := 4983230072969 + 3 ^ 40 * 944780 * 2
def baseEnd_944780 : Nat := 323417501836612518403361

theorem tailTrace_944780 : CollatzResearch.WordTrace tailWord_944780 prefixEnd_944780 323417501836612518403361 := by
  unfold tailWord_944780
  simp only [CollatzResearch.WordTrace]
  refine ⟨17229478758615445211467897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22972638344820593615290529 17229478758615445211467897)
  ·
    refine ⟨12922109068961583908600923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17229478758615445211467897 12922109068961583908600923)
    ·
      refine ⟨19383163603442375862901385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12922109068961583908600923 19383163603442375862901385)
      ·
        refine ⟨14537372702581781897176039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19383163603442375862901385 14537372702581781897176039)
        ·
          refine ⟨21806059053872672845764059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14537372702581781897176039 21806059053872672845764059)
          ·
            refine ⟨32709088580809009268646089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21806059053872672845764059 32709088580809009268646089)
            ·
              refine ⟨24531816435606756951484567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32709088580809009268646089 24531816435606756951484567)
              ·
                refine ⟨36797724653410135427226851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24531816435606756951484567 36797724653410135427226851)
                ·
                  refine ⟨55196586980115203140840277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36797724653410135427226851 55196586980115203140840277)
                  ·
                    refine ⟨323417501836612518403361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55196586980115203140840277 323417501836612518403361)
                    ·
                      rfl

theorem cell22_944780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_944780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944780 prefixEnd_944780 := by exact prefixLift 944780
  have htrace : WordTrace (prefixWord ++ tailWord_944780) baseStart_944780 baseEnd_944780 := by
    simpa [prefixWord, tailWord_944780, baseEnd_944780] using wordTrace_append hprefix tailTrace_944780
  have hstable : (prefixWord ++ tailWord_944780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944780).length < 2 ^ (prefixWord ++ tailWord_944780).sum := by decide
  have hdescent : baseEnd_944780 < baseStart_944780 := by decide
  rcases family_descends (prefixWord ++ tailWord_944780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944833 : List Nat := [1, 2, 6, 2, 1, 2, 2, 6]
def baseStart_944833 : Nat := 118140960795 + 944833 * 2 ^ 59
def prefixEnd_944833 : Nat := 4983230072969 + 3 ^ 40 * 944833 * 2
def baseEnd_944833 : Nat := 35937293868859782980911

theorem tailTrace_944833 : CollatzResearch.WordTrace tailWord_944833 prefixEnd_944833 35937293868859782980911 := by
  unfold tailWord_944833
  simp only [CollatzResearch.WordTrace]
  refine ⟨34460890586038880474615153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22973927057359253649743435 34460890586038880474615153)
  ·
    refine ⟨25845667939529160355961365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34460890586038880474615153 25845667939529160355961365)
    ·
      refine ⟨1211515684665429391685689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25845667939529160355961365 1211515684665429391685689)
      ·
        refine ⟨908636763499072043764267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1211515684665429391685689 908636763499072043764267)
        ·
          refine ⟨1362955145248608065646401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908636763499072043764267 1362955145248608065646401)
          ·
            refine ⟨1022216358936456049234801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1362955145248608065646401 1022216358936456049234801)
            ·
              refine ⟨766662269202342036926101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1022216358936456049234801 766662269202342036926101)
              ·
                refine ⟨35937293868859782980911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 766662269202342036926101 35937293868859782980911)
                ·
                  rfl

theorem cell22_944833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 6].length) (baseStart_944833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944833 prefixEnd_944833 := by exact prefixLift 944833
  have htrace : WordTrace (prefixWord ++ tailWord_944833) baseStart_944833 baseEnd_944833 := by
    simpa [prefixWord, tailWord_944833, baseEnd_944833] using wordTrace_append hprefix tailTrace_944833
  have hstable : (prefixWord ++ tailWord_944833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944833).length < 2 ^ (prefixWord ++ tailWord_944833).sum := by decide
  have hdescent : baseEnd_944833 < baseStart_944833 := by decide
  rcases family_descends (prefixWord ++ tailWord_944833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944887 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_944887 : Nat := 118140960795 + 944887 * 2 ^ 59
def prefixEnd_944887 : Nat := 4983230072969 + 3 ^ 40 * 944887 * 2
def baseEnd_944887 : Nat := 323454130123299905978033

theorem tailTrace_944887 : CollatzResearch.WordTrace tailWord_944887 prefixEnd_944887 323454130123299905978033 := by
  unfold tailWord_944887
  simp only [CollatzResearch.WordTrace]
  refine ⟨34462860127843247697080915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22975240085228831798053943 34462860127843247697080915)
  ·
    refine ⟨51694290191764871545621373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34462860127843247697080915 51694290191764871545621373)
    ·
      refine ⟨19385358821911826829608015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51694290191764871545621373 19385358821911826829608015)
      ·
        refine ⟨29078038232867740244412023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19385358821911826829608015 29078038232867740244412023)
        ·
          refine ⟨43617057349301610366618035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29078038232867740244412023 43617057349301610366618035)
          ·
            refine ⟨65425586023952415549927053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43617057349301610366618035 65425586023952415549927053)
            ·
              refine ⟨24534594758982155831222645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65425586023952415549927053 24534594758982155831222645)
              ·
                refine ⟨2300118258654577109177123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24534594758982155831222645 2300118258654577109177123)
                ·
                  refine ⟨3450177387981865663765685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300118258654577109177123 3450177387981865663765685)
                  ·
                    refine ⟨323454130123299905978033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3450177387981865663765685 323454130123299905978033)
                    ·
                      rfl

theorem cell22_944887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_944887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944887 prefixEnd_944887 := by exact prefixLift 944887
  have htrace : WordTrace (prefixWord ++ tailWord_944887) baseStart_944887 baseEnd_944887 := by
    simpa [prefixWord, tailWord_944887, baseEnd_944887] using wordTrace_append hprefix tailTrace_944887
  have hstable : (prefixWord ++ tailWord_944887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944887).length < 2 ^ (prefixWord ++ tailWord_944887).sum := by decide
  have hdescent : baseEnd_944887 < baseStart_944887 := by decide
  rcases family_descends (prefixWord ++ tailWord_944887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944904 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_944904 : Nat := 118140960795 + 944904 * 2 ^ 59
def prefixEnd_944904 : Nat := 4983230072969 + 3 ^ 40 * 944904 * 2
def baseEnd_944904 : Nat := 323459949570717528302981

theorem tailTrace_944904 : CollatzResearch.WordTrace tailWord_944904 prefixEnd_944904 323459949570717528302981 := by
  unfold tailWord_944904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17231740084390829800224883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22975653445854439733633177 17231740084390829800224883)
  ·
    refine ⟨25847610126586244700337325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17231740084390829800224883 25847610126586244700337325)
    ·
      refine ⟨9692853797469841762626497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25847610126586244700337325 9692853797469841762626497)
      ·
        refine ⟨7269640348102381321969873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9692853797469841762626497 7269640348102381321969873)
        ·
          refine ⟨5452230261076785991477405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7269640348102381321969873 5452230261076785991477405)
          ·
            refine ⟨2044586347903794746804027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5452230261076785991477405 2044586347903794746804027)
            ·
              refine ⟨3066879521855692120206041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044586347903794746804027 3066879521855692120206041)
              ·
                refine ⟨2300159641391769090154531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3066879521855692120206041 2300159641391769090154531)
                ·
                  refine ⟨3450239462087653635231797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300159641391769090154531 3450239462087653635231797)
                  ·
                    refine ⟨323459949570717528302981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3450239462087653635231797 323459949570717528302981)
                    ·
                      rfl

theorem cell22_944904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_944904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944904 prefixEnd_944904 := by exact prefixLift 944904
  have htrace : WordTrace (prefixWord ++ tailWord_944904) baseStart_944904 baseEnd_944904 := by
    simpa [prefixWord, tailWord_944904, baseEnd_944904] using wordTrace_append hprefix tailTrace_944904
  have hstable : (prefixWord ++ tailWord_944904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944904).length < 2 ^ (prefixWord ++ tailWord_944904).sum := by decide
  have hdescent : baseEnd_944904 < baseStart_944904 := by decide
  rcases family_descends (prefixWord ++ tailWord_944904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944938 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 1, 5]
def baseStart_944938 : Nat := 118140960795 + 944938 * 2 ^ 59
def prefixEnd_944938 : Nat := 4983230072969 + 3 ^ 40 * 944938 * 2
def baseEnd_944938 : Nat := 323471588465552772952877

theorem tailTrace_944938 : CollatzResearch.WordTrace tailWord_944938 prefixEnd_944938 323471588465552772952877 := by
  unfold tailWord_944938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8616180062664620851796867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22976480167105655604791645 8616180062664620851796867)
  ·
    refine ⟨12924270093996931277695301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8616180062664620851796867 12924270093996931277695301)
    ·
      refine ⟨2423300642624424614567869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12924270093996931277695301 2423300642624424614567869)
      ·
        refine ⟨908737740984159230462951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2423300642624424614567869 908737740984159230462951)
        ·
          refine ⟨1363106611476238845694427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908737740984159230462951 1363106611476238845694427)
          ·
            refine ⟨2044659917214358268541641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363106611476238845694427 2044659917214358268541641)
            ·
              refine ⟨1533494937910768701406231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044659917214358268541641 1533494937910768701406231)
              ·
                refine ⟨2300242406866153052109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1533494937910768701406231 2300242406866153052109347)
                ·
                  refine ⟨3450363610299229578164021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300242406866153052109347 3450363610299229578164021)
                  ·
                    refine ⟨323471588465552772952877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3450363610299229578164021 323471588465552772952877)
                    ·
                      rfl

theorem cell22_944938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_944938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944938 prefixEnd_944938 := by exact prefixLift 944938
  have htrace : WordTrace (prefixWord ++ tailWord_944938) baseStart_944938 baseEnd_944938 := by
    simpa [prefixWord, tailWord_944938, baseEnd_944938] using wordTrace_append hprefix tailTrace_944938
  have hstable : (prefixWord ++ tailWord_944938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944938).length < 2 ^ (prefixWord ++ tailWord_944938).sum := by decide
  have hdescent : baseEnd_944938 < baseStart_944938 := by decide
  rcases family_descends (prefixWord ++ tailWord_944938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_944983 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 1, 3]
def baseStart_944983 : Nat := 118140960795 + 944983 * 2 ^ 59
def prefixEnd_944983 : Nat := 4983230072969 + 3 ^ 40 * 944983 * 2
def baseEnd_944983 : Nat := 323486992885187655577739

theorem tailTrace_944983 : CollatzResearch.WordTrace tailWord_944983 prefixEnd_944983 323486992885187655577739 := by
  unfold tailWord_944983
  simp only [CollatzResearch.WordTrace]
  refine ⟨34466361535495456092575603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22977574356996970728383735 34466361535495456092575603)
  ·
    refine ⟨51699542303243184138863405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34466361535495456092575603 51699542303243184138863405)
    ·
      refine ⟨19387328363716194052073777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51699542303243184138863405 19387328363716194052073777)
      ·
        refine ⟨14540496272787145539055333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19387328363716194052073777 14540496272787145539055333)
        ·
          refine ⟨2726343051147589788572875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14540496272787145539055333 2726343051147589788572875)
          ·
            refine ⟨4089514576721384682859313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726343051147589788572875 4089514576721384682859313)
            ·
              refine ⟨3067135932541038512144485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4089514576721384682859313 3067135932541038512144485)
              ·
                refine ⟨575087987351444721027091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3067135932541038512144485 575087987351444721027091)
                ·
                  refine ⟨862631981027167081540637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575087987351444721027091 862631981027167081540637)
                  ·
                    refine ⟨323486992885187655577739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862631981027167081540637 323486992885187655577739)
                    ·
                      rfl

theorem cell22_944983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_944983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_944983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_944983 prefixEnd_944983 := by exact prefixLift 944983
  have htrace : WordTrace (prefixWord ++ tailWord_944983) baseStart_944983 baseEnd_944983 := by
    simpa [prefixWord, tailWord_944983, baseEnd_944983] using wordTrace_append hprefix tailTrace_944983
  have hstable : (prefixWord ++ tailWord_944983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_944983).length < 2 ^ (prefixWord ++ tailWord_944983).sum := by decide
  have hdescent : baseEnd_944983 < baseStart_944983 := by decide
  rcases family_descends (prefixWord ++ tailWord_944983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945099 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_945099 : Nat := 118140960795 + 945099 * 2 ^ 59
def prefixEnd_945099 : Nat := 4983230072969 + 3 ^ 40 * 945099 * 2
def baseEnd_945099 : Nat := 323526702055802019677383

theorem tailTrace_945099 : CollatzResearch.WordTrace tailWord_945099 prefixEnd_945099 323526702055802019677383 := by
  unfold tailWord_945099
  simp only [CollatzResearch.WordTrace]
  refine ⟨34470592403075207903798351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22980394935383471935865567 34470592403075207903798351)
  ·
    refine ⟨51705888604612811855697527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34470592403075207903798351 51705888604612811855697527)
    ·
      refine ⟨77558832906919217783546291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51705888604612811855697527 77558832906919217783546291)
      ·
        refine ⟨116338249360378826675319437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77558832906919217783546291 116338249360378826675319437)
        ·
          refine ⟨43626843510142060003244789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116338249360378826675319437 43626843510142060003244789)
          ·
            refine ⟨4090016579075818125304199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43626843510142060003244789 4090016579075818125304199)
            ·
              refine ⟨6135024868613727187956299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090016579075818125304199 6135024868613727187956299)
              ·
                refine ⟨9202537302920590781934449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6135024868613727187956299 9202537302920590781934449)
                ·
                  refine ⟨6901902977190443086450837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9202537302920590781934449 6901902977190443086450837)
                  ·
                    refine ⟨323526702055802019677383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6901902977190443086450837 323526702055802019677383)
                    ·
                      rfl

theorem cell22_945099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_945099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945099 prefixEnd_945099 := by exact prefixLift 945099
  have htrace : WordTrace (prefixWord ++ tailWord_945099) baseStart_945099 baseEnd_945099 := by
    simpa [prefixWord, tailWord_945099, baseEnd_945099] using wordTrace_append hprefix tailTrace_945099
  have hstable : (prefixWord ++ tailWord_945099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945099).length < 2 ^ (prefixWord ++ tailWord_945099).sum := by decide
  have hdescent : baseEnd_945099 < baseStart_945099 := by decide
  rcases family_descends (prefixWord ++ tailWord_945099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945135 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 1, 3]
def baseStart_945135 : Nat := 118140960795 + 945135 * 2 ^ 59
def prefixEnd_945135 : Nat := 4983230072969 + 3 ^ 40 * 945135 * 2
def baseEnd_945135 : Nat := 323539025591509925777273

theorem tailTrace_945135 : CollatzResearch.WordTrace tailWord_945135 prefixEnd_945135 323539025591509925777273 := by
  unfold tailWord_945135
  simp only [CollatzResearch.WordTrace]
  refine ⟨34471905430944786052108859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22981270287296524034739239 34471905430944786052108859)
  ·
    refine ⟨51707858146417179078163289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34471905430944786052108859 51707858146417179078163289)
    ·
      refine ⟨38780893609812884308622467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51707858146417179078163289 38780893609812884308622467)
      ·
        refine ⟨58171340414719326462933701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38780893609812884308622467 58171340414719326462933701)
        ·
          refine ⟨10907126327759873711800069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58171340414719326462933701 10907126327759873711800069)
          ·
            refine ⟨2045086186454976320962513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10907126327759873711800069 2045086186454976320962513)
            ·
              refine ⟨1533814639841232240721885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2045086186454976320962513 1533814639841232240721885)
              ·
                refine ⟨575180489940462090270707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1533814639841232240721885 575180489940462090270707)
                ·
                  refine ⟨862770734910693135406061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575180489940462090270707 862770734910693135406061)
                  ·
                    refine ⟨323539025591509925777273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862770734910693135406061 323539025591509925777273)
                    ·
                      rfl

theorem cell22_945135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_945135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945135 prefixEnd_945135 := by exact prefixLift 945135
  have htrace : WordTrace (prefixWord ++ tailWord_945135) baseStart_945135 baseEnd_945135 := by
    simpa [prefixWord, tailWord_945135, baseEnd_945135] using wordTrace_append hprefix tailTrace_945135
  have hstable : (prefixWord ++ tailWord_945135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945135).length < 2 ^ (prefixWord ++ tailWord_945135).sum := by decide
  have hdescent : baseEnd_945135 < baseStart_945135 := by decide
  rcases family_descends (prefixWord ++ tailWord_945135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945148 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 5]
def baseStart_945148 : Nat := 118140960795 + 945148 * 2 ^ 59
def prefixEnd_945148 : Nat := 4983230072969 + 3 ^ 40 * 945148 * 2
def baseEnd_945148 : Nat := 107847825252394075067411

theorem tailTrace_945148 : CollatzResearch.WordTrace tailWord_945148 prefixEnd_945148 107847825252394075067411 := by
  unfold tailWord_945148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236189789948844636166049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22981586386598459514888065 17236189789948844636166049)
  ·
    refine ⟨12927142342461633477124537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17236189789948844636166049 12927142342461633477124537)
    ·
      refine ⟨9695356756846225107843403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12927142342461633477124537 9695356756846225107843403)
      ·
        refine ⟨14543035135269337661765105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9695356756846225107843403 14543035135269337661765105)
        ·
          refine ⟨10907276351452003246323829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14543035135269337661765105 10907276351452003246323829)
          ·
            refine ⟨1022557157948625304342859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10907276351452003246323829 1022557157948625304342859)
            ·
              refine ⟨1533835736922937956514289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1022557157948625304342859 1533835736922937956514289)
              ·
                refine ⟨1150376802692203467385717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533835736922937956514289 1150376802692203467385717)
                ·
                  refine ⟨107847825252394075067411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1150376802692203467385717 107847825252394075067411)
                  ·
                    rfl

theorem cell22_945148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_945148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945148 prefixEnd_945148 := by exact prefixLift 945148
  have htrace : WordTrace (prefixWord ++ tailWord_945148) baseStart_945148 baseEnd_945148 := by
    simpa [prefixWord, tailWord_945148, baseEnd_945148] using wordTrace_append hprefix tailTrace_945148
  have hstable : (prefixWord ++ tailWord_945148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945148).length < 2 ^ (prefixWord ++ tailWord_945148).sum := by decide
  have hdescent : baseEnd_945148 < baseStart_945148 := by decide
  rcases family_descends (prefixWord ++ tailWord_945148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945176 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 6]
def baseStart_945176 : Nat := 118140960795 + 945176 * 2 ^ 59
def prefixEnd_945176 : Nat := 4983230072969 + 3 ^ 40 * 945176 * 2
def baseEnd_945176 : Nat := 107851020243133161834049

theorem tailTrace_945176 : CollatzResearch.WordTrace tailWord_945176 prefixEnd_945176 107851020243133161834049 := by
  unfold tailWord_945176
  simp only [CollatzResearch.WordTrace]
  refine ⟨17236700411898125027175691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22982267215864166702900921 17236700411898125027175691)
  ·
    refine ⟨25855050617847187540763537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17236700411898125027175691 25855050617847187540763537)
    ·
      refine ⟨19391287963385390655572653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25855050617847187540763537 19391287963385390655572653)
      ·
        refine ⟨7271732986269521495839745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19391287963385390655572653 7271732986269521495839745)
        ·
          refine ⟨5453799739702141121879809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7271732986269521495839745 5453799739702141121879809)
          ·
            refine ⟨4090349804776605841409857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5453799739702141121879809 4090349804776605841409857)
            ·
              refine ⟨3067762353582454381057393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090349804776605841409857 3067762353582454381057393)
              ·
                refine ⟨2300821765186840785793045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3067762353582454381057393 2300821765186840785793045)
                ·
                  refine ⟨107851020243133161834049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2300821765186840785793045 107851020243133161834049)
                  ·
                    rfl

theorem cell22_945176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_945176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945176 prefixEnd_945176 := by exact prefixLift 945176
  have htrace : WordTrace (prefixWord ++ tailWord_945176) baseStart_945176 baseEnd_945176 := by
    simpa [prefixWord, tailWord_945176, baseEnd_945176] using wordTrace_append hprefix tailTrace_945176
  have hstable : (prefixWord ++ tailWord_945176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945176).length < 2 ^ (prefixWord ++ tailWord_945176).sum := by decide
  have hdescent : baseEnd_945176 < baseStart_945176 := by decide
  rcases family_descends (prefixWord ++ tailWord_945176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945178 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 1, 4]
def baseStart_945178 : Nat := 118140960795 + 945178 * 2 ^ 59
def prefixEnd_945178 : Nat := 4983230072969 + 3 ^ 40 * 945178 * 2
def baseEnd_945178 : Nat := 323553745370272146952141

theorem tailTrace_945178 : CollatzResearch.WordTrace tailWord_945178 prefixEnd_945178 323553745370272146952141 := by
  unfold tailWord_945178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8618368442447251098981047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22982315846526002930616125 8618368442447251098981047)
  ·
    refine ⟨12927552663670876648471571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8618368442447251098981047 12927552663670876648471571)
    ·
      refine ⟨19391328995506314972707357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12927552663670876648471571 19391328995506314972707357)
      ·
        refine ⟨7271748373314868114765259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19391328995506314972707357 7271748373314868114765259)
        ·
          refine ⟨10907622559972302172147889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271748373314868114765259 10907622559972302172147889)
          ·
            refine ⟨8180716919979226629110917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10907622559972302172147889 8180716919979226629110917)
            ·
              refine ⟨1533884422496104992958297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8180716919979226629110917 1533884422496104992958297)
              ·
                refine ⟨1150413316872078744718723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1533884422496104992958297 1150413316872078744718723)
                ·
                  refine ⟨1725619975308118117078085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1150413316872078744718723 1725619975308118117078085)
                  ·
                    refine ⟨323553745370272146952141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1725619975308118117078085 323553745370272146952141)
                    ·
                      rfl

theorem cell22_945178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_945178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945178 prefixEnd_945178 := by exact prefixLift 945178
  have htrace : WordTrace (prefixWord ++ tailWord_945178) baseStart_945178 baseEnd_945178 := by
    simpa [prefixWord, tailWord_945178, baseEnd_945178] using wordTrace_append hprefix tailTrace_945178
  have hstable : (prefixWord ++ tailWord_945178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945178).length < 2 ^ (prefixWord ++ tailWord_945178).sum := by decide
  have hdescent : baseEnd_945178 < baseStart_945178 := by decide
  rcases family_descends (prefixWord ++ tailWord_945178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945208 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_945208 : Nat := 118140960795 + 945208 * 2 ^ 59
def prefixEnd_945208 : Nat := 4983230072969 + 3 ^ 40 * 945208 * 2
def baseEnd_945208 : Nat := 323564014983362068702049

theorem tailTrace_945208 : CollatzResearch.WordTrace tailWord_945208 prefixEnd_945208 323564014983362068702049 := by
  unfold tailWord_945208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17237283979840159759758139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22983045306453546346344185 17237283979840159759758139)
  ·
    refine ⟨25855925969760239639637209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17237283979840159759758139 25855925969760239639637209)
    ·
      refine ⟨19391944477320179729727907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25855925969760239639637209 19391944477320179729727907)
      ·
        refine ⟨29087916715980269594591861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19391944477320179729727907 29087916715980269594591861)
        ·
          refine ⟨2726992192123150274492987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29087916715980269594591861 2726992192123150274492987)
          ·
            refine ⟨4090488288184725411739481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2726992192123150274492987 4090488288184725411739481)
            ·
              refine ⟨3067866216138544058804611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4090488288184725411739481 3067866216138544058804611)
              ·
                refine ⟨4601799324207816088206917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3067866216138544058804611 4601799324207816088206917)
                ·
                  refine ⟨862837373288965516538797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4601799324207816088206917 862837373288965516538797)
                  ·
                    refine ⟨323564014983362068702049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862837373288965516538797 323564014983362068702049)
                    ·
                      rfl

theorem cell22_945208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_945208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945208 prefixEnd_945208 := by exact prefixLift 945208
  have htrace : WordTrace (prefixWord ++ tailWord_945208) baseStart_945208 baseEnd_945208 := by
    simpa [prefixWord, tailWord_945208, baseEnd_945208] using wordTrace_append hprefix tailTrace_945208
  have hstable : (prefixWord ++ tailWord_945208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945208).length < 2 ^ (prefixWord ++ tailWord_945208).sum := by decide
  have hdescent : baseEnd_945208 < baseStart_945208 := by decide
  rcases family_descends (prefixWord ++ tailWord_945208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945236 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_945236 : Nat := 118140960795 + 945236 * 2 ^ 59
def prefixEnd_945236 : Nat := 4983230072969 + 3 ^ 40 * 945236 * 2
def baseEnd_945236 : Nat := 323573599955579329001963

theorem tailTrace_945236 : CollatzResearch.WordTrace tailWord_945236 prefixEnd_945236 323573599955579329001963 := by
  unfold tailWord_945236
  simp only [CollatzResearch.WordTrace]
  refine ⟨17237794601789440150767781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22983726135719253534357041 17237794601789440150767781)
  ·
    refine ⟨3232086487835520028268959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17237794601789440150767781 3232086487835520028268959)
    ·
      refine ⟨4848129731753280042403439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232086487835520028268959 4848129731753280042403439)
      ·
        refine ⟨7272194597629920063605159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4848129731753280042403439 7272194597629920063605159)
        ·
          refine ⟨10908291896444880095407739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7272194597629920063605159 10908291896444880095407739)
          ·
            refine ⟨16362437844667320143111609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10908291896444880095407739 16362437844667320143111609)
            ·
              refine ⟨12271828383500490107333707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16362437844667320143111609 12271828383500490107333707)
              ·
                refine ⟨18407742575250735161000561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12271828383500490107333707 18407742575250735161000561)
                ·
                  refine ⟨13805806931438051370750421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18407742575250735161000561 13805806931438051370750421)
                  ·
                    refine ⟨323573599955579329001963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13805806931438051370750421 323573599955579329001963)
                    ·
                      rfl

theorem cell22_945236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_945236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945236 prefixEnd_945236 := by exact prefixLift 945236
  have htrace : WordTrace (prefixWord ++ tailWord_945236) baseStart_945236 baseEnd_945236 := by
    simpa [prefixWord, tailWord_945236, baseEnd_945236] using wordTrace_append hprefix tailTrace_945236
  have hstable : (prefixWord ++ tailWord_945236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945236).length < 2 ^ (prefixWord ++ tailWord_945236).sum := by decide
  have hdescent : baseEnd_945236 < baseStart_945236 := by decide
  rcases family_descends (prefixWord ++ tailWord_945236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945270 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_945270 : Nat := 118140960795 + 945270 * 2 ^ 59
def prefixEnd_945270 : Nat := 4983230072969 + 3 ^ 40 * 945270 * 2
def baseEnd_945270 : Nat := 323585238850414573651859

theorem tailTrace_945270 : CollatzResearch.WordTrace tailWord_945270 prefixEnd_945270 323585238850414573651859 := by
  unfold tailWord_945270
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154801830340981506767079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22984552856970469405515509 2154801830340981506767079)
  ·
    refine ⟨3232202745511472260150619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2154801830340981506767079 3232202745511472260150619)
    ·
      refine ⟨4848304118267208390225929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3232202745511472260150619 4848304118267208390225929)
      ·
        refine ⟨3636228088700406292669447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4848304118267208390225929 3636228088700406292669447)
        ·
          refine ⟨5454342133050609439004171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3636228088700406292669447 5454342133050609439004171)
          ·
            refine ⟨8181513199575914158506257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5454342133050609439004171 8181513199575914158506257)
            ·
              refine ⟨6136134899681935618879693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8181513199575914158506257 6136134899681935618879693)
              ·
                refine ⟨2301050587380725857079885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6136134899681935618879693 2301050587380725857079885)
                ·
                  refine ⟨862893970267772196404957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2301050587380725857079885 862893970267772196404957)
                  ·
                    refine ⟨323585238850414573651859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 862893970267772196404957 323585238850414573651859)
                    ·
                      rfl

theorem cell22_945270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_945270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945270 prefixEnd_945270 := by exact prefixLift 945270
  have htrace : WordTrace (prefixWord ++ tailWord_945270) baseStart_945270 baseEnd_945270 := by
    simpa [prefixWord, tailWord_945270, baseEnd_945270] using wordTrace_append hprefix tailTrace_945270
  have hstable : (prefixWord ++ tailWord_945270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945270).length < 2 ^ (prefixWord ++ tailWord_945270).sum := by decide
  have hdescent : baseEnd_945270 < baseStart_945270 := by decide
  rcases family_descends (prefixWord ++ tailWord_945270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945343 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 1, 5]
def baseStart_945343 : Nat := 118140960795 + 945343 * 2 ^ 59
def prefixEnd_945343 : Nat := 4983230072969 + 3 ^ 40 * 945343 * 2
def baseEnd_945343 : Nat := 323610228242266716576635

theorem tailTrace_945343 : CollatzResearch.WordTrace tailWord_945343 prefixEnd_945343 323610228242266716576635 := by
  unfold tailWord_945343
  simp only [CollatzResearch.WordTrace]
  refine ⟨34479491814191237575680683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22986327876127491717120455 34479491814191237575680683)
  ·
    refine ⟨51719237721286856363521025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34479491814191237575680683 51719237721286856363521025)
    ·
      refine ⟨38789428290965142272640769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51719237721286856363521025 38789428290965142272640769)
      ·
        refine ⟨29092071218223856704480577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38789428290965142272640769 29092071218223856704480577)
        ·
          refine ⟨21819053413667892528360433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29092071218223856704480577 21819053413667892528360433)
          ·
            refine ⟨16364290060250919396270325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21819053413667892528360433 16364290060250919396270325)
            ·
              refine ⟨1534152193148523693400343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16364290060250919396270325 1534152193148523693400343)
              ·
                refine ⟨2301228289722785540100515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534152193148523693400343 2301228289722785540100515)
                ·
                  refine ⟨3451842434584178310150773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2301228289722785540100515 3451842434584178310150773)
                  ·
                    refine ⟨323610228242266716576635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3451842434584178310150773 323610228242266716576635)
                    ·
                      rfl

theorem cell22_945343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_945343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945343 prefixEnd_945343 := by exact prefixLift 945343
  have htrace : WordTrace (prefixWord ++ tailWord_945343) baseStart_945343 baseEnd_945343 := by
    simpa [prefixWord, tailWord_945343, baseEnd_945343] using wordTrace_append hprefix tailTrace_945343
  have hstable : (prefixWord ++ tailWord_945343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945343).length < 2 ^ (prefixWord ++ tailWord_945343).sum := by decide
  have hdescent : baseEnd_945343 < baseStart_945343 := by decide
  rcases family_descends (prefixWord ++ tailWord_945343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945345 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 6]
def baseStart_945345 : Nat := 118140960795 + 945345 * 2 ^ 59
def prefixEnd_945345 : Nat := 4983230072969 + 3 ^ 40 * 945345 * 2
def baseEnd_945345 : Nat := 107870304294379792675543

theorem tailTrace_945345 : CollatzResearch.WordTrace tailWord_945345 prefixEnd_945345 107870304294379792675543 := by
  unfold tailWord_945345
  simp only [CollatzResearch.WordTrace]
  refine ⟨34479564760183991917253489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22986376506789327944835659 34479564760183991917253489)
  ·
    refine ⟨25859673570137993937940117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34479564760183991917253489 25859673570137993937940117)
    ·
      refine ⟨1212172198600218465840943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25859673570137993937940117 1212172198600218465840943)
      ·
        refine ⟨1818258297900327698761415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1212172198600218465840943 1818258297900327698761415)
        ·
          refine ⟨2727387446850491548142123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818258297900327698761415 2727387446850491548142123)
          ·
            refine ⟨4091081170275737322213185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727387446850491548142123 4091081170275737322213185)
            ·
              refine ⟨3068310877706802991659889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4091081170275737322213185 3068310877706802991659889)
              ·
                refine ⟨2301233158280102243744917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3068310877706802991659889 2301233158280102243744917)
                ·
                  refine ⟨107870304294379792675543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2301233158280102243744917 107870304294379792675543)
                  ·
                    rfl

theorem cell22_945345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 6].length) (baseStart_945345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945345 prefixEnd_945345 := by exact prefixLift 945345
  have htrace : WordTrace (prefixWord ++ tailWord_945345) baseStart_945345 baseEnd_945345 := by
    simpa [prefixWord, tailWord_945345, baseEnd_945345] using wordTrace_append hprefix tailTrace_945345
  have hstable : (prefixWord ++ tailWord_945345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945345).length < 2 ^ (prefixWord ++ tailWord_945345).sum := by decide
  have hdescent : baseEnd_945345 < baseStart_945345 := by decide
  rcases family_descends (prefixWord ++ tailWord_945345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_945371 : Nat := 118140960795 + 945371 * 2 ^ 59
def prefixEnd_945371 : Nat := 4983230072969 + 3 ^ 40 * 945371 * 2
def baseEnd_945371 : Nat := 323619813214483976876549

theorem tailTrace_945371 : CollatzResearch.WordTrace tailWord_945371 prefixEnd_945371 323619813214483976876549 := by
  unfold tailWord_945371
  simp only [CollatzResearch.WordTrace]
  refine ⟨34480513058089798357699967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22987008705393198905133311 34480513058089798357699967)
  ·
    refine ⟨51720769587134697536549951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34480513058089798357699967 51720769587134697536549951)
    ·
      refine ⟨77581154380702046304824927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51720769587134697536549951 77581154380702046304824927)
      ·
        refine ⟨116371731571053069457237391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77581154380702046304824927 116371731571053069457237391)
        ·
          refine ⟨174557597356579604185856087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116371731571053069457237391 174557597356579604185856087)
          ·
            refine ⟨261836396034869406278784131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174557597356579604185856087 261836396034869406278784131)
            ·
              refine ⟨392754594052304109418176197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261836396034869406278784131 392754594052304109418176197)
              ·
                refine ⟨73641486384807020515908037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 392754594052304109418176197 73641486384807020515908037)
                ·
                  refine ⟨13807778697151316346732757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73641486384807020515908037 13807778697151316346732757)
                  ·
                    refine ⟨323619813214483976876549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13807778697151316346732757 323619813214483976876549)
                    ·
                      rfl

theorem cell22_945371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_945371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945371 prefixEnd_945371 := by exact prefixLift 945371
  have htrace : WordTrace (prefixWord ++ tailWord_945371) baseStart_945371 baseEnd_945371 := by
    simpa [prefixWord, tailWord_945371, baseEnd_945371] using wordTrace_append hprefix tailTrace_945371
  have hstable : (prefixWord ++ tailWord_945371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945371).length < 2 ^ (prefixWord ++ tailWord_945371).sum := by decide
  have hdescent : baseEnd_945371 < baseStart_945371 := by decide
  rcases family_descends (prefixWord ++ tailWord_945371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945439 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 1, 3]
def baseStart_945439 : Nat := 118140960795 + 945439 * 2 ^ 59
def prefixEnd_945439 : Nat := 4983230072969 + 3 ^ 40 * 945439 * 2
def baseEnd_945439 : Nat := 323643091004154466176341

theorem tailTrace_945439 : CollatzResearch.WordTrace tailWord_945439 prefixEnd_945439 323643091004154466176341 := by
  unfold tailWord_945439
  simp only [CollatzResearch.WordTrace]
  refine ⟨34482993221843445971175371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22988662147895630647450247 34482993221843445971175371)
  ·
    refine ⟨51724489832765168956763057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34482993221843445971175371 51724489832765168956763057)
    ·
      refine ⟨38793367374573876717572293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51724489832765168956763057 38793367374573876717572293)
      ·
        refine ⟨7273756382732601884544805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38793367374573876717572293 7273756382732601884544805)
        ·
          refine ⟨1363829321762362853352151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7273756382732601884544805 1363829321762362853352151)
          ·
            refine ⟨2045743982643544280028227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1363829321762362853352151 2045743982643544280028227)
            ·
              refine ⟨3068615973965316420042341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2045743982643544280028227 3068615973965316420042341)
              ·
                refine ⟨575365495118496828757939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3068615973965316420042341 575365495118496828757939)
                ·
                  refine ⟨863048242677745243136909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575365495118496828757939 863048242677745243136909)
                  ·
                    refine ⟨323643091004154466176341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863048242677745243136909 323643091004154466176341)
                    ·
                      rfl

theorem cell22_945439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_945439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945439 prefixEnd_945439 := by exact prefixLift 945439
  have htrace : WordTrace (prefixWord ++ tailWord_945439) baseStart_945439 baseEnd_945439 := by
    simpa [prefixWord, tailWord_945439, baseEnd_945439] using wordTrace_append hprefix tailTrace_945439
  have hstable : (prefixWord ++ tailWord_945439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945439).length < 2 ^ (prefixWord ++ tailWord_945439).sum := by decide
  have hdescent : baseEnd_945439 < baseStart_945439 := by decide
  rcases family_descends (prefixWord ++ tailWord_945439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945450 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_945450 : Nat := 118140960795 + 945450 * 2 ^ 59
def prefixEnd_945450 : Nat := 4983230072969 + 3 ^ 40 * 945450 * 2
def baseEnd_945450 : Nat := 323646856528954104151307

theorem tailTrace_945450 : CollatzResearch.WordTrace tailWord_945450 prefixEnd_945450 323646856528954104151307 := by
  unfold tailWord_945450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8620848606200898712456451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22988929616535729899883869 8620848606200898712456451)
  ·
    refine ⟨12931272909301348068684677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8620848606200898712456451 12931272909301348068684677)
    ·
      refine ⟨2424613670494002762878377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12931272909301348068684677 2424613670494002762878377)
      ·
        refine ⟨1818460252870502072158783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424613670494002762878377 1818460252870502072158783)
        ·
          refine ⟨2727690379305753108238175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818460252870502072158783 2727690379305753108238175)
          ·
            refine ⟨4091535568958629662357263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2727690379305753108238175 4091535568958629662357263)
            ·
              refine ⟨6137303353437944493535895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4091535568958629662357263 6137303353437944493535895)
              ·
                refine ⟨9205955030156916740303843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6137303353437944493535895 9205955030156916740303843)
                ·
                  refine ⟨13808932545235375110455765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9205955030156916740303843 13808932545235375110455765)
                  ·
                    refine ⟨323646856528954104151307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13808932545235375110455765 323646856528954104151307)
                    ·
                      rfl

theorem cell22_945450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_945450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945450 prefixEnd_945450 := by exact prefixLift 945450
  have htrace : WordTrace (prefixWord ++ tailWord_945450) baseStart_945450 baseEnd_945450 := by
    simpa [prefixWord, tailWord_945450, baseEnd_945450] using wordTrace_append hprefix tailTrace_945450
  have hstable : (prefixWord ++ tailWord_945450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945450).length < 2 ^ (prefixWord ++ tailWord_945450).sum := by decide
  have hdescent : baseEnd_945450 < baseStart_945450 := by decide
  rcases family_descends (prefixWord ++ tailWord_945450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945557 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 3, 3]
def baseStart_945557 : Nat := 118140960795 + 945557 * 2 ^ 59
def prefixEnd_945557 : Nat := 4983230072969 + 3 ^ 40 * 945557 * 2
def baseEnd_945557 : Nat := 323683484815641491725979

theorem tailTrace_945557 : CollatzResearch.WordTrace tailWord_945557 prefixEnd_945557 323683484815641491725979 := by
  unfold tailWord_945557
  simp only [CollatzResearch.WordTrace]
  refine ⟨34487297035415952123970925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22991531356943968082647283 34487297035415952123970925)
  ·
    refine ⟨12932736388280982046489097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34487297035415952123970925 12932736388280982046489097)
    ·
      refine ⟨9699552291210736534866823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12932736388280982046489097 9699552291210736534866823)
      ·
        refine ⟨14549328436816104802300235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9699552291210736534866823 14549328436816104802300235)
        ·
          refine ⟨21823992655224157203450353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14549328436816104802300235 21823992655224157203450353)
          ·
            refine ⟨16367994491418117902587765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21823992655224157203450353 16367994491418117902587765)
            ·
              refine ⟨1534499483570448553367603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16367994491418117902587765 1534499483570448553367603)
              ·
                refine ⟨2301749225355672830051405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534499483570448553367603 2301749225355672830051405)
                ·
                  refine ⟨863155959508377311269277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2301749225355672830051405 863155959508377311269277)
                  ·
                    refine ⟨323683484815641491725979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863155959508377311269277 323683484815641491725979)
                    ·
                      rfl

theorem cell22_945557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 3].length) (baseStart_945557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945557 prefixEnd_945557 := by exact prefixLift 945557
  have htrace : WordTrace (prefixWord ++ tailWord_945557) baseStart_945557 baseEnd_945557 := by
    simpa [prefixWord, tailWord_945557, baseEnd_945557] using wordTrace_append hprefix tailTrace_945557
  have hstable : (prefixWord ++ tailWord_945557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945557).length < 2 ^ (prefixWord ++ tailWord_945557).sum := by decide
  have hdescent : baseEnd_945557 < baseStart_945557 := by decide
  rcases family_descends (prefixWord ++ tailWord_945557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945604 : List Nat := [2, 3, 3, 2, 1, 2, 2, 2, 5]
def baseStart_945604 : Nat := 118140960795 + 945604 * 2 ^ 59
def prefixEnd_945604 : Nat := 4983230072969 + 3 ^ 40 * 945604 * 2
def baseEnd_945604 : Nat := 107899857958716345266945

theorem tailTrace_945604 : CollatzResearch.WordTrace tailWord_945604 prefixEnd_945604 107899857958716345266945 := by
  unfold tailWord_945604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17244505633122839575465933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22992674177497119433954577 17244505633122839575465933)
  ·
    refine ⟨6466689612421064840799725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17244505633122839575465933 6466689612421064840799725)
    ·
      refine ⟨2425008604657899315299897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6466689612421064840799725 2425008604657899315299897)
      ·
        refine ⟨1818756453493424486474923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425008604657899315299897 1818756453493424486474923)
        ·
          refine ⟨2728134680240136729712385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818756453493424486474923 2728134680240136729712385)
          ·
            refine ⟨2046101010180102547284289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728134680240136729712385 2046101010180102547284289)
            ·
              refine ⟨1534575757635076910463217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046101010180102547284289 1534575757635076910463217)
              ·
                refine ⟨1150931818226307682847413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1534575757635076910463217 1150931818226307682847413)
                ·
                  refine ⟨107899857958716345266945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1150931818226307682847413 107899857958716345266945)
                  ·
                    rfl

theorem cell22_945604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_945604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945604 prefixEnd_945604 := by exact prefixLift 945604
  have htrace : WordTrace (prefixWord ++ tailWord_945604) baseStart_945604 baseEnd_945604 := by
    simpa [prefixWord, tailWord_945604, baseEnd_945604] using wordTrace_append hprefix tailTrace_945604
  have hstable : (prefixWord ++ tailWord_945604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945604).length < 2 ^ (prefixWord ++ tailWord_945604).sum := by decide
  have hdescent : baseEnd_945604 < baseStart_945604 := by decide
  rcases family_descends (prefixWord ++ tailWord_945604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945649 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 4]
def baseStart_945649 : Nat := 118140960795 + 945649 * 2 ^ 59
def prefixEnd_945649 : Nat := 4983230072969 + 3 ^ 40 * 945649 * 2
def baseEnd_945649 : Nat := 107904992765261306141899

theorem tailTrace_945649 : CollatzResearch.WordTrace tailWord_945649 prefixEnd_945649 107904992765261306141899 := by
  unfold tailWord_945649
  simp only [CollatzResearch.WordTrace]
  refine ⟨34490652551082651836320001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22993768367388434557546667 34490652551082651836320001)
  ·
    refine ⟨25867989413311988877240001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34490652551082651836320001 25867989413311988877240001)
    ·
      refine ⟨19400992059983991657930001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25867989413311988877240001 19400992059983991657930001)
      ·
        refine ⟨14550744044987993743447501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19400992059983991657930001 14550744044987993743447501)
        ·
          refine ⟨5456529016870497653792813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14550744044987993743447501 5456529016870497653792813)
          ·
            refine ⟨2046198381326436620172305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5456529016870497653792813 2046198381326436620172305)
            ·
              refine ⟨1534648785994827465129229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046198381326436620172305 1534648785994827465129229)
              ·
                refine ⟨575493294748060299423461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1534648785994827465129229 575493294748060299423461)
                ·
                  refine ⟨107904992765261306141899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575493294748060299423461 107904992765261306141899)
                  ·
                    rfl

theorem cell22_945649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 4].length) (baseStart_945649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945649 prefixEnd_945649 := by exact prefixLift 945649
  have htrace : WordTrace (prefixWord ++ tailWord_945649) baseStart_945649 baseEnd_945649 := by
    simpa [prefixWord, tailWord_945649, baseEnd_945649] using wordTrace_append hprefix tailTrace_945649
  have hstable : (prefixWord ++ tailWord_945649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945649).length < 2 ^ (prefixWord ++ tailWord_945649).sum := by decide
  have hdescent : baseEnd_945649 < baseStart_945649 := by decide
  rcases family_descends (prefixWord ++ tailWord_945649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945666 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_945666 : Nat := 118140960795 + 945666 * 2 ^ 59
def prefixEnd_945666 : Nat := 4983230072969 + 3 ^ 40 * 945666 * 2
def baseEnd_945666 : Nat := 107906932581067180250215

theorem tailTrace_945666 : CollatzResearch.WordTrace tailWord_945666 prefixEnd_945666 107906932581067180250215 := by
  unfold tailWord_945666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622818148005265934922213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22994181728014042493125901 8622818148005265934922213)
  ·
    refine ⟨1616778402750987362797915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8622818148005265934922213 1616778402750987362797915)
    ·
      refine ⟨2425167604126481044196873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616778402750987362797915 2425167604126481044196873)
      ·
        refine ⟨1818875703094860783147655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2425167604126481044196873 1818875703094860783147655)
        ·
          refine ⟨2728313554642291174721483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818875703094860783147655 2728313554642291174721483)
          ·
            refine ⟨4092470331963436762082225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728313554642291174721483 4092470331963436762082225)
            ·
              refine ⟨3069352748972577571561669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4092470331963436762082225 3069352748972577571561669)
              ·
                refine ⟨575503640432358294667813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3069352748972577571561669 575503640432358294667813)
                ·
                  refine ⟨107906932581067180250215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575503640432358294667813 107906932581067180250215)
                  ·
                    rfl

theorem cell22_945666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_945666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945666 prefixEnd_945666 := by exact prefixLift 945666
  have htrace : WordTrace (prefixWord ++ tailWord_945666) baseStart_945666 baseEnd_945666 := by
    simpa [prefixWord, tailWord_945666, baseEnd_945666] using wordTrace_append hprefix tailTrace_945666
  have hstable : (prefixWord ++ tailWord_945666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945666).length < 2 ^ (prefixWord ++ tailWord_945666).sum := by decide
  have hdescent : baseEnd_945666 < baseStart_945666 := by decide
  rcases family_descends (prefixWord ++ tailWord_945666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945722 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_945722 : Nat := 118140960795 + 945722 * 2 ^ 59
def prefixEnd_945722 : Nat := 4983230072969 + 3 ^ 40 * 945722 * 2
def baseEnd_945722 : Nat := 107913322562545353783491

theorem tailTrace_945722 : CollatzResearch.WordTrace tailWord_945722 prefixEnd_945722 107913322562545353783491 := by
  unfold tailWord_945722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8623328769954546325931855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22995543386545456869151613 8623328769954546325931855)
  ·
    refine ⟨12934993154931819488897783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8623328769954546325931855 12934993154931819488897783)
    ·
      refine ⟨19402489732397729233346675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12934993154931819488897783 19402489732397729233346675)
      ·
        refine ⟨29103734598596593850020013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19402489732397729233346675 29103734598596593850020013)
        ·
          refine ⟨10913900474473722693757505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29103734598596593850020013 10913900474473722693757505)
          ·
            refine ⟨8185425355855292020318129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10913900474473722693757505 8185425355855292020318129)
            ·
              refine ⟨6139069016891469015238597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8185425355855292020318129 6139069016891469015238597)
              ·
                refine ⟨1151075440667150440357237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6139069016891469015238597 1151075440667150440357237)
                ·
                  refine ⟨107913322562545353783491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1151075440667150440357237 107913322562545353783491)
                  ·
                    rfl

theorem cell22_945722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_945722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945722 prefixEnd_945722 := by exact prefixLift 945722
  have htrace : WordTrace (prefixWord ++ tailWord_945722) baseStart_945722 baseEnd_945722 := by
    simpa [prefixWord, tailWord_945722, baseEnd_945722] using wordTrace_append hprefix tailTrace_945722
  have hstable : (prefixWord ++ tailWord_945722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945722).length < 2 ^ (prefixWord ++ tailWord_945722).sum := by decide
  have hdescent : baseEnd_945722 < baseStart_945722 := by decide
  rcases family_descends (prefixWord ++ tailWord_945722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945797 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_945797 : Nat := 118140960795 + 945797 * 2 ^ 59
def prefixEnd_945797 : Nat := 4983230072969 + 3 ^ 40 * 945797 * 2
def baseEnd_945797 : Nat := 323765641720360865725243

theorem tailTrace_945797 : CollatzResearch.WordTrace tailWord_945797 prefixEnd_945797 323765641720360865725243 := by
  unfold tailWord_945797
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496050554546473112707645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22997367036364315408471763 34496050554546473112707645)
  ·
    refine ⟨12936018957954927417265367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34496050554546473112707645 12936018957954927417265367)
    ·
      refine ⟨19404028436932391125898051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12936018957954927417265367 19404028436932391125898051)
      ·
        refine ⟨29106042655398586688847077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19404028436932391125898051 29106042655398586688847077)
        ·
          refine ⟨5457382997887235004158827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29106042655398586688847077 5457382997887235004158827)
          ·
            refine ⟨8186074496830852506238241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5457382997887235004158827 8186074496830852506238241)
            ·
              refine ⟨6139555872623139379678681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8186074496830852506238241 6139555872623139379678681)
              ·
                refine ⟨4604666904467354534759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6139555872623139379678681 4604666904467354534759011)
                ·
                  refine ⟨6907000356701031802138517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4604666904467354534759011 6907000356701031802138517)
                  ·
                    refine ⟨323765641720360865725243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6907000356701031802138517 323765641720360865725243)
                    ·
                      rfl

theorem cell22_945797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_945797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945797 prefixEnd_945797 := by exact prefixLift 945797
  have htrace : WordTrace (prefixWord ++ tailWord_945797) baseStart_945797 baseEnd_945797 := by
    simpa [prefixWord, tailWord_945797, baseEnd_945797] using wordTrace_append hprefix tailTrace_945797
  have hstable : (prefixWord ++ tailWord_945797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945797).length < 2 ^ (prefixWord ++ tailWord_945797).sum := by decide
  have hdescent : baseEnd_945797 < baseStart_945797 := by decide
  rcases family_descends (prefixWord ++ tailWord_945797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945799 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 1, 5]
def baseStart_945799 : Nat := 118140960795 + 945799 * 2 ^ 59
def prefixEnd_945799 : Nat := 4983230072969 + 3 ^ 40 * 945799 * 2
def baseEnd_945799 : Nat := 323766326361233527175237

theorem tailTrace_945799 : CollatzResearch.WordTrace tailWord_945799 prefixEnd_945799 323766326361233527175237 := by
  unfold tailWord_945799
  simp only [CollatzResearch.WordTrace]
  refine ⟨34496123500539227454280451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22997415667026151636186967 34496123500539227454280451)
  ·
    refine ⟨51744185250808841181420677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34496123500539227454280451 51744185250808841181420677)
    ·
      refine ⟨9702034734526657721516377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51744185250808841181420677 9702034734526657721516377)
      ·
        refine ⟨7276526050894993291137283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9702034734526657721516377 7276526050894993291137283)
        ·
          refine ⟨10914789076342489936705925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7276526050894993291137283 10914789076342489936705925)
          ·
            refine ⟨2046522951814216863132361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10914789076342489936705925 2046522951814216863132361)
            ·
              refine ⟨1534892213860662647349271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2046522951814216863132361 1534892213860662647349271)
              ·
                refine ⟨2302338320790993971023907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1534892213860662647349271 2302338320790993971023907)
                ·
                  refine ⟨3453507481186490956535861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302338320790993971023907 3453507481186490956535861)
                  ·
                    refine ⟨323766326361233527175237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3453507481186490956535861 323766326361233527175237)
                    ·
                      rfl

theorem cell22_945799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_945799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945799 prefixEnd_945799 := by exact prefixLift 945799
  have htrace : WordTrace (prefixWord ++ tailWord_945799) baseStart_945799 baseEnd_945799 := by
    simpa [prefixWord, tailWord_945799, baseEnd_945799] using wordTrace_append hprefix tailTrace_945799
  have hstable : (prefixWord ++ tailWord_945799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945799).length < 2 ^ (prefixWord ++ tailWord_945799).sum := by decide
  have hdescent : baseEnd_945799 < baseStart_945799 := by decide
  rcases family_descends (prefixWord ++ tailWord_945799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945820 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 1, 4]
def baseStart_945820 : Nat := 118140960795 + 945820 * 2 ^ 59
def prefixEnd_945820 : Nat := 4983230072969 + 3 ^ 40 * 945820 * 2
def baseEnd_945820 : Nat := 323773515090396472400173

theorem tailTrace_945820 : CollatzResearch.WordTrace tailWord_945820 prefixEnd_945820 323773515090396472400173 := by
  unfold tailWord_945820
  simp only [CollatzResearch.WordTrace]
  refine ⟨17248444716731574020397457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22997926288975432027196609 17248444716731574020397457)
  ·
    refine ⟨12936333537548680515298093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17248444716731574020397457 12936333537548680515298093)
    ·
      refine ⟨4851125076580755193236785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12936333537548680515298093 4851125076580755193236785)
      ·
        refine ⟨3638343807435566394927589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4851125076580755193236785 3638343807435566394927589)
        ·
          refine ⟨682189463894168699048923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3638343807435566394927589 682189463894168699048923)
          ·
            refine ⟨1023284195841253048573385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682189463894168699048923 1023284195841253048573385)
            ·
              refine ⟨767463146880939786430039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023284195841253048573385 767463146880939786430039)
              ·
                refine ⟨1151194720321409679645059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 767463146880939786430039 1151194720321409679645059)
                ·
                  refine ⟨1726792080482114519467589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151194720321409679645059 1726792080482114519467589)
                  ·
                    refine ⟨323773515090396472400173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1726792080482114519467589 323773515090396472400173)
                    ·
                      rfl

theorem cell22_945820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_945820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945820 prefixEnd_945820 := by exact prefixLift 945820
  have htrace : WordTrace (prefixWord ++ tailWord_945820) baseStart_945820 baseEnd_945820 := by
    simpa [prefixWord, tailWord_945820, baseEnd_945820] using wordTrace_append hprefix tailTrace_945820
  have hstable : (prefixWord ++ tailWord_945820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945820).length < 2 ^ (prefixWord ++ tailWord_945820).sum := by decide
  have hdescent : baseEnd_945820 < baseStart_945820 := by decide
  rcases family_descends (prefixWord ++ tailWord_945820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945842 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_945842 : Nat := 118140960795 + 945842 * 2 ^ 59
def prefixEnd_945842 : Nat := 4983230072969 + 3 ^ 40 * 945842 * 2
def baseEnd_945842 : Nat := 323781046139995748350105

theorem tailTrace_945842 : CollatzResearch.WordTrace tailWord_945842 prefixEnd_945842 323781046139995748350105 := by
  unfold tailWord_945842
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624422959845861449523945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22998461226255630532063853 8624422959845861449523945)
  ·
    refine ⟨6468317219884396087142959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8624422959845861449523945 6468317219884396087142959)
    ·
      refine ⟨9702475829826594130714439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468317219884396087142959 9702475829826594130714439)
      ·
        refine ⟨14553713744739891196071659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9702475829826594130714439 14553713744739891196071659)
        ·
          refine ⟨21830570617109836794107489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14553713744739891196071659 21830570617109836794107489)
          ·
            refine ⟨16372927962832377595580617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21830570617109836794107489 16372927962832377595580617)
            ·
              refine ⟨12279695972124283196685463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16372927962832377595580617 12279695972124283196685463)
              ·
                refine ⟨18419543958186424795028195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12279695972124283196685463 18419543958186424795028195)
                ·
                  refine ⟨27629315937279637192542293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18419543958186424795028195 27629315937279637192542293)
                  ·
                    refine ⟨323781046139995748350105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27629315937279637192542293 323781046139995748350105)
                    ·
                      rfl

theorem cell22_945842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_945842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945842 prefixEnd_945842 := by exact prefixLift 945842
  have htrace : WordTrace (prefixWord ++ tailWord_945842) baseStart_945842 baseEnd_945842 := by
    simpa [prefixWord, tailWord_945842, baseEnd_945842] using wordTrace_append hprefix tailTrace_945842
  have hstable : (prefixWord ++ tailWord_945842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945842).length < 2 ^ (prefixWord ++ tailWord_945842).sum := by decide
  have hdescent : baseEnd_945842 < baseStart_945842 := by decide
  rcases family_descends (prefixWord ++ tailWord_945842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945872 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_945872 : Nat := 118140960795 + 945872 * 2 ^ 59
def prefixEnd_945872 : Nat := 4983230072969 + 3 ^ 40 * 945872 * 2
def baseEnd_945872 : Nat := 323791315753085670100013

theorem tailTrace_945872 : CollatzResearch.WordTrace tailWord_945872 prefixEnd_945872 323791315753085670100013 := by
  unfold tailWord_945872
  simp only [CollatzResearch.WordTrace]
  refine ⟨17249393014637380460843935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22999190686183173947791913 17249393014637380460843935)
  ·
    refine ⟨25874089521956070691265903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17249393014637380460843935 25874089521956070691265903)
    ·
      refine ⟨38811134282934106036898855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25874089521956070691265903 38811134282934106036898855)
      ·
        refine ⟨58216701424401159055348283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38811134282934106036898855 58216701424401159055348283)
        ·
          refine ⟨87325052136601738583022425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58216701424401159055348283 87325052136601738583022425)
          ·
            refine ⟨65493789102451303937266819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87325052136601738583022425 65493789102451303937266819)
            ·
              refine ⟨98240683653676955905900229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65493789102451303937266819 98240683653676955905900229)
              ·
                refine ⟨18420128185064429232356293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98240683653676955905900229 18420128185064429232356293)
                ·
                  refine ⟨3453774034699580481066805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18420128185064429232356293 3453774034699580481066805)
                  ·
                    refine ⟨323791315753085670100013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3453774034699580481066805 323791315753085670100013)
                    ·
                      rfl

theorem cell22_945872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_945872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945872 prefixEnd_945872 := by exact prefixLift 945872
  have htrace : WordTrace (prefixWord ++ tailWord_945872) baseStart_945872 baseEnd_945872 := by
    simpa [prefixWord, tailWord_945872, baseEnd_945872] using wordTrace_append hprefix tailTrace_945872
  have hstable : (prefixWord ++ tailWord_945872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945872).length < 2 ^ (prefixWord ++ tailWord_945872).sum := by decide
  have hdescent : baseEnd_945872 < baseStart_945872 := by decide
  rcases family_descends (prefixWord ++ tailWord_945872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945874 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 7]
def baseStart_945874 : Nat := 118140960795 + 945874 * 2 ^ 59
def prefixEnd_945874 : Nat := 4983230072969 + 3 ^ 40 * 945874 * 2
def baseEnd_945874 : Nat := 107930666797986110516669

theorem tailTrace_945874 : CollatzResearch.WordTrace tailWord_945874 prefixEnd_945874 107930666797986110516669 := by
  unfold tailWord_945874
  simp only [CollatzResearch.WordTrace]
  refine ⟨8624714743816878815815169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22999239316845010175507117 8624714743816878815815169)
  ·
    refine ⟨6468536057862659111861377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8624714743816878815815169 6468536057862659111861377)
    ·
      refine ⟨4851402043396994333896033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6468536057862659111861377 4851402043396994333896033)
      ·
        refine ⟨3638551532547745750422025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4851402043396994333896033 3638551532547745750422025)
        ·
          refine ⟨2728913649410809312816519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3638551532547745750422025 2728913649410809312816519)
          ·
            refine ⟨4093370474116213969224779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2728913649410809312816519 4093370474116213969224779)
            ·
              refine ⟨6140055711174320953837169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4093370474116213969224779 6140055711174320953837169)
              ·
                refine ⟨4605041783380740715377877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6140055711174320953837169 4605041783380740715377877)
                ·
                  refine ⟨107930666797986110516669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4605041783380740715377877 107930666797986110516669)
                  ·
                    rfl

theorem cell22_945874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_945874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945874 prefixEnd_945874 := by exact prefixLift 945874
  have htrace : WordTrace (prefixWord ++ tailWord_945874) baseStart_945874 baseEnd_945874 := by
    simpa [prefixWord, tailWord_945874, baseEnd_945874] using wordTrace_append hprefix tailTrace_945874
  have hstable : (prefixWord ++ tailWord_945874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945874).length < 2 ^ (prefixWord ++ tailWord_945874).sum := by decide
  have hdescent : baseEnd_945874 < baseStart_945874 := by decide
  rcases family_descends (prefixWord ++ tailWord_945874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945895 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 3, 3]
def baseStart_945895 : Nat := 118140960795 + 945895 * 2 ^ 59
def prefixEnd_945895 : Nat := 4983230072969 + 3 ^ 40 * 945895 * 2
def baseEnd_945895 : Nat := 323799189123121276774943

theorem tailTrace_945895 : CollatzResearch.WordTrace tailWord_945895 prefixEnd_945895 323799189123121276774943 := by
  unfold tailWord_945895
  simp only [CollatzResearch.WordTrace]
  refine ⟨34499624908191435849775139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22999749938794290566516759 34499624908191435849775139)
  ·
    refine ⟨51749437362287153774662709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34499624908191435849775139 51749437362287153774662709)
    ·
      refine ⟨4851509752714420666374629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51749437362287153774662709 4851509752714420666374629)
      ·
        refine ⟨909658078633953874945243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4851509752714420666374629 909658078633953874945243)
        ·
          refine ⟨1364487117950930812417865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909658078633953874945243 1364487117950930812417865)
          ·
            refine ⟨1023365338463198109313399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364487117950930812417865 1023365338463198109313399)
            ·
              refine ⟨1535048007694797163970099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023365338463198109313399 1535048007694797163970099)
              ·
                refine ⟨2302572011542195745955149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535048007694797163970099 2302572011542195745955149)
                ·
                  refine ⟨863464504328323404733181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2302572011542195745955149 863464504328323404733181)
                  ·
                    refine ⟨323799189123121276774943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863464504328323404733181 323799189123121276774943)
                    ·
                      rfl

theorem cell22_945895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_945895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945895 prefixEnd_945895 := by exact prefixLift 945895
  have htrace : WordTrace (prefixWord ++ tailWord_945895) baseStart_945895 baseEnd_945895 := by
    simpa [prefixWord, tailWord_945895, baseEnd_945895] using wordTrace_append hprefix tailTrace_945895
  have hstable : (prefixWord ++ tailWord_945895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945895).length < 2 ^ (prefixWord ++ tailWord_945895).sum := by decide
  have hdescent : baseEnd_945895 < baseStart_945895 := by decide
  rcases family_descends (prefixWord ++ tailWord_945895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945921 : List Nat := [1, 2, 4, 1, 1, 1, 5, 2, 1, 4]
def baseStart_945921 : Nat := 118140960795 + 945921 * 2 ^ 59
def prefixEnd_945921 : Nat := 4983230072969 + 3 ^ 40 * 945921 * 2
def baseEnd_945921 : Nat := 323808089454465875624863

theorem tailTrace_945921 : CollatzResearch.WordTrace tailWord_945921 prefixEnd_945921 323808089454465875624863 := by
  unfold tailWord_945921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34500573206097242290221617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23000382137398161526814411 34500573206097242290221617)
  ·
    refine ⟨25875429904572931717666213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34500573206097242290221617 25875429904572931717666213)
    ·
      refine ⟨4851643107107424697062415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25875429904572931717666213 4851643107107424697062415)
      ·
        refine ⟨7277464660661137045593623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851643107107424697062415 7277464660661137045593623)
        ·
          refine ⟨10916196990991705568390435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277464660661137045593623 10916196990991705568390435)
          ·
            refine ⟨16374295486487558352585653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916196990991705568390435 16374295486487558352585653)
            ·
              refine ⟨1535090201858208595554905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16374295486487558352585653 1535090201858208595554905)
              ·
                refine ⟨1151317651393656446666179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535090201858208595554905 1151317651393656446666179)
                ·
                  refine ⟨1726976477090484669999269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151317651393656446666179 1726976477090484669999269)
                  ·
                    refine ⟨323808089454465875624863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1726976477090484669999269 323808089454465875624863)
                    ·
                      rfl

theorem cell22_945921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_945921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945921 prefixEnd_945921 := by exact prefixLift 945921
  have htrace : WordTrace (prefixWord ++ tailWord_945921) baseStart_945921 baseEnd_945921 := by
    simpa [prefixWord, tailWord_945921, baseEnd_945921] using wordTrace_append hprefix tailTrace_945921
  have hstable : (prefixWord ++ tailWord_945921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945921).length < 2 ^ (prefixWord ++ tailWord_945921).sum := by decide
  have hdescent : baseEnd_945921 < baseStart_945921 := by decide
  rcases family_descends (prefixWord ++ tailWord_945921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945934 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_945934 : Nat := 118140960795 + 945934 * 2 ^ 59
def prefixEnd_945934 : Nat := 4983230072969 + 3 ^ 40 * 945934 * 2
def baseEnd_945934 : Nat := 323812539620138175049823

theorem tailTrace_945934 : CollatzResearch.WordTrace tailWord_945934 prefixEnd_945934 323812539620138175049823 := by
  unfold tailWord_945934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4312630919381268188805607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23000698236700097006963237 4312630919381268188805607)
  ·
    refine ⟨6468946379071902283208411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4312630919381268188805607 6468946379071902283208411)
    ·
      refine ⟨9703419568607853424812617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468946379071902283208411 9703419568607853424812617)
      ·
        refine ⟨7277564676455890068609463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703419568607853424812617 7277564676455890068609463)
        ·
          refine ⟨10916347014683835102914195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277564676455890068609463 10916347014683835102914195)
          ·
            refine ⟨16374520522025752654371293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916347014683835102914195 16374520522025752654371293)
            ·
              refine ⟨6140445195759657245389235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16374520522025752654371293 6140445195759657245389235)
              ·
                refine ⟨9210667793639485868083853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140445195759657245389235 9210667793639485868083853)
                ·
                  refine ⟨3454000422614807200531445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9210667793639485868083853 3454000422614807200531445)
                  ·
                    refine ⟨323812539620138175049823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3454000422614807200531445 323812539620138175049823)
                    ·
                      rfl

theorem cell22_945934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_945934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945934 prefixEnd_945934 := by exact prefixLift 945934
  have htrace : WordTrace (prefixWord ++ tailWord_945934) baseStart_945934 baseEnd_945934 := by
    simpa [prefixWord, tailWord_945934, baseEnd_945934] using wordTrace_append hprefix tailTrace_945934
  have hstable : (prefixWord ++ tailWord_945934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945934).length < 2 ^ (prefixWord ++ tailWord_945934).sum := by decide
  have hdescent : baseEnd_945934 < baseStart_945934 := by decide
  rcases family_descends (prefixWord ++ tailWord_945934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945953 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 4]
def baseStart_945953 : Nat := 118140960795 + 945953 * 2 ^ 59
def prefixEnd_945953 : Nat := 4983230072969 + 3 ^ 40 * 945953 * 2
def baseEnd_945953 : Nat := 107939681236142819608255

theorem tailTrace_945953 : CollatzResearch.WordTrace tailWord_945953 prefixEnd_945953 107939681236142819608255 := by
  unfold tailWord_945953
  simp only [CollatzResearch.WordTrace]
  refine ⟨34501740341981311755386513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23001160227987541170257675 34501740341981311755386513)
  ·
    refine ⟨25876305256485983816539885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34501740341981311755386513 25876305256485983816539885)
    ·
      refine ⟨9703614471182243931202457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25876305256485983816539885 9703614471182243931202457)
      ·
        refine ⟨7277710853386682948401843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703614471182243931202457 7277710853386682948401843)
        ·
          refine ⟨10916566280080024422602765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277710853386682948401843 10916566280080024422602765)
          ·
            refine ⟨4093712355030009158476037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10916566280080024422602765 4093712355030009158476037)
            ·
              refine ⟨767571066568126717214257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4093712355030009158476037 767571066568126717214257)
              ·
                refine ⟨575678299926095037910693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767571066568126717214257 575678299926095037910693)
                ·
                  refine ⟨107939681236142819608255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575678299926095037910693 107939681236142819608255)
                  ·
                    rfl

theorem cell22_945953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_945953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945953 prefixEnd_945953 := by exact prefixLift 945953
  have htrace : WordTrace (prefixWord ++ tailWord_945953) baseStart_945953 baseEnd_945953 := by
    simpa [prefixWord, tailWord_945953, baseEnd_945953] using wordTrace_append hprefix tailTrace_945953
  have hstable : (prefixWord ++ tailWord_945953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945953).length < 2 ^ (prefixWord ++ tailWord_945953).sum := by decide
  have hdescent : baseEnd_945953 < baseStart_945953 := by decide
  rcases family_descends (prefixWord ++ tailWord_945953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945964 : List Nat := [2, 2, 1, 1, 1, 5, 3, 7]
def baseStart_945964 : Nat := 118140960795 + 945964 * 2 ^ 59
def prefixEnd_945964 : Nat := 4983230072969 + 3 ^ 40 * 945964 * 2
def baseEnd_945964 : Nat := 35980312137025344088859

theorem tailTrace_945964 : CollatzResearch.WordTrace tailWord_945964 prefixEnd_945964 35980312137025344088859 := by
  unfold tailWord_945964
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251070772470730317018473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23001427696627640422691297 17251070772470730317018473)
  ·
    refine ⟨12938303079353047737763855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17251070772470730317018473 12938303079353047737763855)
    ·
      refine ⟨19407454619029571606645783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12938303079353047737763855 19407454619029571606645783)
      ·
        refine ⟨29111181928544357409968675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19407454619029571606645783 29111181928544357409968675)
        ·
          refine ⟨43666772892816536114953013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29111181928544357409968675 43666772892816536114953013)
          ·
            refine ⟨4093759958701550260776845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43666772892816536114953013 4093759958701550260776845)
            ·
              refine ⟨1535159984513081347791317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4093759958701550260776845 1535159984513081347791317)
              ·
                refine ⟨35980312137025344088859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1535159984513081347791317 35980312137025344088859)
                ·
                  rfl

theorem cell22_945964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 7].length) (baseStart_945964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945964 prefixEnd_945964 := by exact prefixLift 945964
  have htrace : WordTrace (prefixWord ++ tailWord_945964) baseStart_945964 baseEnd_945964 := by
    simpa [prefixWord, tailWord_945964, baseEnd_945964] using wordTrace_append hprefix tailTrace_945964
  have hstable : (prefixWord ++ tailWord_945964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945964).length < 2 ^ (prefixWord ++ tailWord_945964).sum := by decide
  have hdescent : baseEnd_945964 < baseStart_945964 := by decide
  rcases family_descends (prefixWord ++ tailWord_945964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_945983 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 2, 4]
def baseStart_945983 : Nat := 118140960795 + 945983 * 2 ^ 59
def prefixEnd_945983 : Nat := 4983230072969 + 3 ^ 40 * 945983 * 2
def baseEnd_945983 : Nat := 323829313321518380574673

theorem tailTrace_945983 : CollatzResearch.WordTrace tailWord_945983 prefixEnd_945983 323829313321518380574673 := by
  unfold tailWord_945983
  simp only [CollatzResearch.WordTrace]
  refine ⟨34502834531872626878978603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23001889687915084585985735 34502834531872626878978603)
  ·
    refine ⟨51754251797808940318467905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34502834531872626878978603 51754251797808940318467905)
    ·
      refine ⟨38815688848356705238850929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51754251797808940318467905 38815688848356705238850929)
      ·
        refine ⟨29111766636267528929138197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38815688848356705238850929 29111766636267528929138197)
        ·
          refine ⟨1364614061075040418553353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29111766636267528929138197 1364614061075040418553353)
          ·
            refine ⟨1023460545806280313915015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364614061075040418553353 1023460545806280313915015)
            ·
              refine ⟨1535190818709420470872523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023460545806280313915015 1535190818709420470872523)
              ·
                refine ⟨2302786228064130706308785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535190818709420470872523 2302786228064130706308785)
                ·
                  refine ⟨1727089671048098029731589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302786228064130706308785 1727089671048098029731589)
                  ·
                    refine ⟨323829313321518380574673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1727089671048098029731589 323829313321518380574673)
                    ·
                      rfl

theorem cell22_945983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_945983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_945983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_945983 prefixEnd_945983 := by exact prefixLift 945983
  have htrace : WordTrace (prefixWord ++ tailWord_945983) baseStart_945983 baseEnd_945983 := by
    simpa [prefixWord, tailWord_945983, baseEnd_945983] using wordTrace_append hprefix tailTrace_945983
  have hstable : (prefixWord ++ tailWord_945983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_945983).length < 2 ^ (prefixWord ++ tailWord_945983).sum := by decide
  have hdescent : baseEnd_945983 < baseStart_945983 := by decide
  rcases family_descends (prefixWord ++ tailWord_945983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946009 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 7]
def baseStart_946009 : Nat := 118140960795 + 946009 * 2 ^ 59
def prefixEnd_946009 : Nat := 4983230072969 + 3 ^ 40 * 946009 * 2
def baseEnd_946009 : Nat := 107946071217620993141531

theorem tailTrace_946009 : CollatzResearch.WordTrace tailWord_946009 prefixEnd_946009 107946071217620993141531 := by
  unfold tailWord_946009
  simp only [CollatzResearch.WordTrace]
  refine ⟨34503782829778433319425081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23002521886518955546283387 34503782829778433319425081)
  ·
    refine ⟨25877837122333824989568811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34503782829778433319425081 25877837122333824989568811)
    ·
      refine ⟨38816755683500737484353217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25877837122333824989568811 38816755683500737484353217)
      ·
        refine ⟨29112566762625553113264913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38816755683500737484353217 29112566762625553113264913)
        ·
          refine ⟨21834425071969164834948685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29112566762625553113264913 21834425071969164834948685)
          ·
            refine ⟨8187909401988436813105757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21834425071969164834948685 8187909401988436813105757)
            ·
              refine ⟨3070466025745663804914659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8187909401988436813105757 3070466025745663804914659)
              ·
                refine ⟨4605699038618495707371989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070466025745663804914659 4605699038618495707371989)
                ·
                  refine ⟨107946071217620993141531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4605699038618495707371989 107946071217620993141531)
                  ·
                    rfl

theorem cell22_946009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_946009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946009 prefixEnd_946009 := by exact prefixLift 946009
  have htrace : WordTrace (prefixWord ++ tailWord_946009) baseStart_946009 baseEnd_946009 := by
    simpa [prefixWord, tailWord_946009, baseEnd_946009] using wordTrace_append hprefix tailTrace_946009
  have hstable : (prefixWord ++ tailWord_946009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946009).length < 2 ^ (prefixWord ++ tailWord_946009).sum := by decide
  have hdescent : baseEnd_946009 < baseStart_946009 := by decide
  rcases family_descends (prefixWord ++ tailWord_946009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946071 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 6]
def baseStart_946071 : Nat := 118140960795 + 946071 * 2 ^ 59
def prefixEnd_946071 : Nat := 4983230072969 + 3 ^ 40 * 946071 * 2
def baseEnd_946071 : Nat := 107953145839971828124801

theorem tailTrace_946071 : CollatzResearch.WordTrace tailWord_946071 prefixEnd_946071 107953145839971828124801 := by
  unfold tailWord_946071
  simp only [CollatzResearch.WordTrace]
  refine ⟨34506044155553817908182067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23004029437035878605454711 34506044155553817908182067)
  ·
    refine ⟨51759066233330726862273101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34506044155553817908182067 51759066233330726862273101)
    ·
      refine ⟨19409649837499022573352413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51759066233330726862273101 19409649837499022573352413)
      ·
        refine ⟨7278618689062133465007155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19409649837499022573352413 7278618689062133465007155)
        ·
          refine ⟨10917928033593200197510733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7278618689062133465007155 10917928033593200197510733)
          ·
            refine ⟨4094223012597450074066525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10917928033593200197510733 4094223012597450074066525)
            ·
              refine ⟨1535333629724043777774947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094223012597450074066525 1535333629724043777774947)
              ·
                refine ⟨2303000444586065666662421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535333629724043777774947 2303000444586065666662421)
                ·
                  refine ⟨107953145839971828124801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2303000444586065666662421 107953145839971828124801)
                  ·
                    rfl

theorem cell22_946071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 6].length) (baseStart_946071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946071 prefixEnd_946071 := by exact prefixLift 946071
  have htrace : WordTrace (prefixWord ++ tailWord_946071) baseStart_946071 baseEnd_946071 := by
    simpa [prefixWord, tailWord_946071, baseEnd_946071] using wordTrace_append hprefix tailTrace_946071
  have hstable : (prefixWord ++ tailWord_946071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946071).length < 2 ^ (prefixWord ++ tailWord_946071).sum := by decide
  have hdescent : baseEnd_946071 < baseStart_946071 := by decide
  rcases family_descends (prefixWord ++ tailWord_946071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946099 : List Nat := [1, 1, 1, 2, 3, 1, 3, 10]
def baseStart_946099 : Nat := 118140960795 + 946099 * 2 ^ 59
def prefixEnd_946099 : Nat := 4983230072969 + 3 ^ 40 * 946099 * 2
def baseEnd_946099 : Nat := 35985446943570304963813

theorem tailTrace_946099 : CollatzResearch.WordTrace tailWord_946099 prefixEnd_946099 35985446943570304963813 := by
  unfold tailWord_946099
  simp only [CollatzResearch.WordTrace]
  refine ⟨34507065399452378690201351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23004710266301585793467567 34507065399452378690201351)
  ·
    refine ⟨51760598099178568035302027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34507065399452378690201351 51760598099178568035302027)
    ·
      refine ⟨77640897148767852052953041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51760598099178568035302027 77640897148767852052953041)
      ·
        refine ⟨58230672861575889039714781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77640897148767852052953041 58230672861575889039714781)
        ·
          refine ⟨21836502323090958389893043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58230672861575889039714781 21836502323090958389893043)
          ·
            refine ⟨32754753484636437584839565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21836502323090958389893043 32754753484636437584839565)
            ·
              refine ⟨12283032556738664094314837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32754753484636437584839565 12283032556738664094314837)
              ·
                refine ⟨35985446943570304963813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12283032556738664094314837 35985446943570304963813)
                ·
                  rfl

theorem cell22_946099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 10].length) (baseStart_946099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946099 prefixEnd_946099 := by exact prefixLift 946099
  have htrace : WordTrace (prefixWord ++ tailWord_946099) baseStart_946099 baseEnd_946099 := by
    simpa [prefixWord, tailWord_946099, baseEnd_946099] using wordTrace_append hprefix tailTrace_946099
  have hstable : (prefixWord ++ tailWord_946099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946099).length < 2 ^ (prefixWord ++ tailWord_946099).sum := by decide
  have hdescent : baseEnd_946099 < baseStart_946099 := by decide
  rcases family_descends (prefixWord ++ tailWord_946099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946120 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_946120 : Nat := 118140960795 + 946120 * 2 ^ 59
def prefixEnd_946120 : Nat := 4983230072969 + 3 ^ 40 * 946120 * 2
def baseEnd_946120 : Nat := 323876211221295689899253

theorem tailTrace_946120 : CollatzResearch.WordTrace tailWord_946120 prefixEnd_946120 323876211221295689899253 := by
  unfold tailWord_946120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17253915666188149638357907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23005220888250866184477209 17253915666188149638357907)
  ·
    refine ⟨25880873499282224457536861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17253915666188149638357907 25880873499282224457536861)
    ·
      refine ⟨9705327562230834171576323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25880873499282224457536861 9705327562230834171576323)
      ·
        refine ⟨14557991343346251257364485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705327562230834171576323 14557991343346251257364485)
        ·
          refine ⟨2729623376877422110755841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14557991343346251257364485 2729623376877422110755841)
          ·
            refine ⟨2047217532658066583066881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2729623376877422110755841 2047217532658066583066881)
            ·
              refine ⟨1535413149493549937300161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047217532658066583066881 1535413149493549937300161)
              ·
                refine ⟨1151559862120162452975121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535413149493549937300161 1151559862120162452975121)
                ·
                  refine ⟨863669896590121839731341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1151559862120162452975121 863669896590121839731341)
                  ·
                    refine ⟨323876211221295689899253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863669896590121839731341 323876211221295689899253)
                    ·
                      rfl

theorem cell22_946120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_946120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946120 prefixEnd_946120 := by exact prefixLift 946120
  have htrace : WordTrace (prefixWord ++ tailWord_946120) baseStart_946120 baseEnd_946120 := by
    simpa [prefixWord, tailWord_946120, baseEnd_946120] using wordTrace_append hprefix tailTrace_946120
  have hstable : (prefixWord ++ tailWord_946120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946120).length < 2 ^ (prefixWord ++ tailWord_946120).sum := by decide
  have hdescent : baseEnd_946120 < baseStart_946120 := by decide
  rcases family_descends (prefixWord ++ tailWord_946120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946133 : List Nat := [1, 3, 2, 3, 2, 3, 1, 7]
def baseStart_946133 : Nat := 118140960795 + 946133 * 2 ^ 59
def prefixEnd_946133 : Nat := 4983230072969 + 3 ^ 40 * 946133 * 2
def baseEnd_946133 : Nat := 35986740154107554369357

theorem tailTrace_946133 : CollatzResearch.WordTrace tailWord_946133 prefixEnd_946133 35986740154107554369357 := by
  unfold tailWord_946133
  simp only [CollatzResearch.WordTrace]
  refine ⟨34508305481329202496939053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23005536987552801664626035 34508305481329202496939053)
  ·
    refine ⟨12940614555498450936352145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34508305481329202496939053 12940614555498450936352145)
    ·
      refine ⟨9705460916623838202264109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12940614555498450936352145 9705460916623838202264109)
      ·
        refine ⟨3639547843733939325849041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9705460916623838202264109 3639547843733939325849041)
        ·
          refine ⟨2729660882800454494386781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3639547843733939325849041 2729660882800454494386781)
          ·
            refine ⟨1023622831050170435395043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2729660882800454494386781 1023622831050170435395043)
            ·
              refine ⟨1535434246575255653092565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023622831050170435395043 1535434246575255653092565)
              ·
                refine ⟨35986740154107554369357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1535434246575255653092565 35986740154107554369357)
                ·
                  rfl

theorem cell22_946133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 7].length) (baseStart_946133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946133 prefixEnd_946133 := by exact prefixLift 946133
  have htrace : WordTrace (prefixWord ++ tailWord_946133) baseStart_946133 baseEnd_946133 := by
    simpa [prefixWord, tailWord_946133, baseEnd_946133] using wordTrace_append hprefix tailTrace_946133
  have hstable : (prefixWord ++ tailWord_946133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946133).length < 2 ^ (prefixWord ++ tailWord_946133).sum := by decide
  have hdescent : baseEnd_946133 < baseStart_946133 := by decide
  rcases family_descends (prefixWord ++ tailWord_946133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946148 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 3, 3]
def baseStart_946148 : Nat := 118140960795 + 946148 * 2 ^ 59
def prefixEnd_946148 : Nat := 4983230072969 + 3 ^ 40 * 946148 * 2
def baseEnd_946148 : Nat := 323885796193512950199167

theorem tailTrace_946148 : CollatzResearch.WordTrace tailWord_946148 prefixEnd_946148 323885796193512950199167 := by
  unfold tailWord_946148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17254426288137430029367549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23005901717516573372490065 17254426288137430029367549)
  ·
    refine ⟨6470409858051536261012831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17254426288137430029367549 6470409858051536261012831)
    ·
      refine ⟨9705614787077304391519247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6470409858051536261012831 9705614787077304391519247)
      ·
        refine ⟨14558422180615956587278871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9705614787077304391519247 14558422180615956587278871)
        ·
          refine ⟨21837633270923934880918307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14558422180615956587278871 21837633270923934880918307)
          ·
            refine ⟨32756449906385902321377461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21837633270923934880918307 32756449906385902321377461)
            ·
              refine ⟨3070917178723678342629137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32756449906385902321377461 3070917178723678342629137)
              ·
                refine ⟨2303187884042758756971853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070917178723678342629137 2303187884042758756971853)
                ·
                  refine ⟨863695456516034533864445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2303187884042758756971853 863695456516034533864445)
                  ·
                    refine ⟨323885796193512950199167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863695456516034533864445 323885796193512950199167)
                    ·
                      rfl

theorem cell22_946148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_946148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946148 prefixEnd_946148 := by exact prefixLift 946148
  have htrace : WordTrace (prefixWord ++ tailWord_946148) baseStart_946148 baseEnd_946148 := by
    simpa [prefixWord, tailWord_946148, baseEnd_946148] using wordTrace_append hprefix tailTrace_946148
  have hstable : (prefixWord ++ tailWord_946148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946148).length < 2 ^ (prefixWord ++ tailWord_946148).sum := by decide
  have hdescent : baseEnd_946148 < baseStart_946148 := by decide
  rcases family_descends (prefixWord ++ tailWord_946148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946216 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 1, 3]
def baseStart_946216 : Nat := 118140960795 + 946216 * 2 ^ 59
def prefixEnd_946216 : Nat := 4983230072969 + 3 ^ 40 * 946216 * 2
def baseEnd_946216 : Nat := 323909073983183439498959

theorem tailTrace_946216 : CollatzResearch.WordTrace tailWord_946216 prefixEnd_946216 323909073983183439498959 := by
  unfold tailWord_946216
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255666370014253836105251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23007555160019005114807001 17255666370014253836105251)
  ·
    refine ⟨25883499555021380754157877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17255666370014253836105251 25883499555021380754157877)
    ·
      refine ⟨2426578083283254445702301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25883499555021380754157877 2426578083283254445702301)
      ·
        refine ⟨909966781231220417138363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2426578083283254445702301 909966781231220417138363)
        ·
          refine ⟨1364950171846830625707545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 909966781231220417138363 1364950171846830625707545)
          ·
            refine ⟨1023712628885122969280659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1364950171846830625707545 1023712628885122969280659)
            ·
              refine ⟨1535568943327684453920989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023712628885122969280659 1535568943327684453920989)
              ·
                refine ⟨575838353747881670220371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535568943327684453920989 575838353747881670220371)
                ·
                  refine ⟨863757530621822505330557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 575838353747881670220371 863757530621822505330557)
                  ·
                    refine ⟨323909073983183439498959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863757530621822505330557 323909073983183439498959)
                    ·
                      rfl

theorem cell22_946216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_946216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946216 prefixEnd_946216 := by exact prefixLift 946216
  have htrace : WordTrace (prefixWord ++ tailWord_946216) baseStart_946216 baseEnd_946216 := by
    simpa [prefixWord, tailWord_946216, baseEnd_946216] using wordTrace_append hprefix tailTrace_946216
  have hstable : (prefixWord ++ tailWord_946216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946216).length < 2 ^ (prefixWord ++ tailWord_946216).sum := by decide
  have hdescent : baseEnd_946216 < baseStart_946216 := by decide
  rcases family_descends (prefixWord ++ tailWord_946216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 4]
def baseStart_946223 : Nat := 118140960795 + 946223 * 2 ^ 59
def prefixEnd_946223 : Nat := 4983230072969 + 3 ^ 40 * 946223 * 2
def baseEnd_946223 : Nat := 107970490075412584857979

theorem tailTrace_946223 : CollatzResearch.WordTrace tailWord_946223 prefixEnd_946223 107970490075412584857979 := by
  unfold tailWord_946223
  simp only [CollatzResearch.WordTrace]
  refine ⟨34511588051003147867715323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23007725367335431911810215 34511588051003147867715323)
  ·
    refine ⟨51767382076504721801572985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34511588051003147867715323 51767382076504721801572985)
    ·
      refine ⟨38825536557378541351179739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51767382076504721801572985 38825536557378541351179739)
      ·
        refine ⟨58238304836067812026769609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38825536557378541351179739 58238304836067812026769609)
        ·
          refine ⟨43678728627050859020077207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58238304836067812026769609 43678728627050859020077207)
          ·
            refine ⟨65518092940576288530115811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43678728627050859020077207 65518092940576288530115811)
            ·
              refine ⟨98277139410864432795173717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65518092940576288530115811 98277139410864432795173717)
              ·
                refine ⟨575842613735533785909221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 98277139410864432795173717 575842613735533785909221)
                ·
                  refine ⟨107970490075412584857979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575842613735533785909221 107970490075412584857979)
                  ·
                    rfl

theorem cell22_946223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 4].length) (baseStart_946223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946223 prefixEnd_946223 := by exact prefixLift 946223
  have htrace : WordTrace (prefixWord ++ tailWord_946223) baseStart_946223 baseEnd_946223 := by
    simpa [prefixWord, tailWord_946223, baseEnd_946223] using wordTrace_append hprefix tailTrace_946223
  have hstable : (prefixWord ++ tailWord_946223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946223).length < 2 ^ (prefixWord ++ tailWord_946223).sum := by decide
  have hdescent : baseEnd_946223 < baseStart_946223 := by decide
  rcases family_descends (prefixWord ++ tailWord_946223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946268 : List Nat := [2, 2, 4, 1, 1, 2, 2, 8]
def baseStart_946268 : Nat := 118140960795 + 946268 * 2 ^ 59
def prefixEnd_946268 : Nat := 4983230072969 + 3 ^ 40 * 946268 * 2
def baseEnd_946268 : Nat := 35991874960652515244311

theorem tailTrace_946268 : CollatzResearch.WordTrace tailWord_946268 prefixEnd_946268 35991874960652515244311 := by
  unfold tailWord_946268
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256614667920060276551729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23008819557226747035402305 17256614667920060276551729)
  ·
    refine ⟨12942461000940045207413797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17256614667920060276551729 12942461000940045207413797)
    ·
      refine ⟨2426711437676258476390087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12942461000940045207413797 2426711437676258476390087)
      ·
        refine ⟨3640067156514387714585131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426711437676258476390087 3640067156514387714585131)
        ·
          refine ⟨5460100734771581571877697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640067156514387714585131 5460100734771581571877697)
          ·
            refine ⟨4095075551078686178908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5460100734771581571877697 4095075551078686178908273)
            ·
              refine ⟨3071306663309014634181205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095075551078686178908273 3071306663309014634181205)
              ·
                refine ⟨35991874960652515244311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3071306663309014634181205 35991874960652515244311)
                ·
                  rfl

theorem cell22_946268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 8].length) (baseStart_946268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946268 prefixEnd_946268 := by exact prefixLift 946268
  have htrace : WordTrace (prefixWord ++ tailWord_946268) baseStart_946268 baseEnd_946268 := by
    simpa [prefixWord, tailWord_946268, baseEnd_946268] using wordTrace_append hprefix tailTrace_946268
  have hstable : (prefixWord ++ tailWord_946268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946268).length < 2 ^ (prefixWord ++ tailWord_946268).sum := by decide
  have hdescent : baseEnd_946268 < baseStart_946268 := by decide
  rcases family_descends (prefixWord ++ tailWord_946268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946313 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 5]
def baseStart_946313 : Nat := 118140960795 + 946313 * 2 ^ 59
def prefixEnd_946313 : Nat := 4983230072969 + 3 ^ 40 * 946313 * 2
def baseEnd_946313 : Nat := 107980759688502506607887

theorem tailTrace_946313 : CollatzResearch.WordTrace tailWord_946313 prefixEnd_946313 107980759688502506607887 := by
  unfold tailWord_946313
  simp only [CollatzResearch.WordTrace]
  refine ⟨34514870620677093238491593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23009913747118062158994395 34514870620677093238491593)
  ·
    refine ⟨25886152965507819928868695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34514870620677093238491593 25886152965507819928868695)
    ·
      refine ⟨38829229448261729893303043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25886152965507819928868695 38829229448261729893303043)
      ·
        refine ⟨58243844172392594839954565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38829229448261729893303043 58243844172392594839954565)
        ·
          refine ⟨10920720782323611532491481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58243844172392594839954565 10920720782323611532491481)
          ·
            refine ⟨8190540586742708649368611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10920720782323611532491481 8190540586742708649368611)
            ·
              refine ⟨12285810880114062974052917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8190540586742708649368611 12285810880114062974052917)
              ·
                refine ⟨1151794770010693403817461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12285810880114062974052917 1151794770010693403817461)
                ·
                  refine ⟨107980759688502506607887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1151794770010693403817461 107980759688502506607887)
                  ·
                    rfl

theorem cell22_946313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_946313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946313 prefixEnd_946313 := by exact prefixLift 946313
  have htrace : WordTrace (prefixWord ++ tailWord_946313) baseStart_946313 baseEnd_946313 := by
    simpa [prefixWord, tailWord_946313, baseEnd_946313] using wordTrace_append hprefix tailTrace_946313
  have hstable : (prefixWord ++ tailWord_946313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946313).length < 2 ^ (prefixWord ++ tailWord_946313).sum := by decide
  have hdescent : baseEnd_946313 < baseStart_946313 := by decide
  rcases family_descends (prefixWord ++ tailWord_946313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946392 : List Nat := [2, 1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_946392 : Nat := 118140960795 + 946392 * 2 ^ 59
def prefixEnd_946392 : Nat := 4983230072969 + 3 ^ 40 * 946392 * 2
def baseEnd_946392 : Nat := 107989774126659215699473

theorem tailTrace_946392 : CollatzResearch.WordTrace tailWord_946392 prefixEnd_946392 107989774126659215699473 := by
  unfold tailWord_946392
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258875993695444865308715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23011834658260593153744953 17258875993695444865308715)
  ·
    refine ⟨25888313990543167297963073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17258875993695444865308715 25888313990543167297963073)
    ·
      refine ⟨19416235492907375473472305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25888313990543167297963073 19416235492907375473472305)
      ·
        refine ⟨14562176619680531605104229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19416235492907375473472305 14562176619680531605104229)
        ·
          refine ⟨2730408116190099675957043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14562176619680531605104229 2730408116190099675957043)
          ·
            refine ⟨4095612174285149513935565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730408116190099675957043 4095612174285149513935565)
            ·
              refine ⟨1535854565356931067725837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4095612174285149513935565 1535854565356931067725837)
              ·
                refine ⟨575945462008849150397189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1535854565356931067725837 575945462008849150397189)
                ·
                  refine ⟨107989774126659215699473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 575945462008849150397189 107989774126659215699473)
                  ·
                    rfl

theorem cell22_946392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_946392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946392 prefixEnd_946392 := by exact prefixLift 946392
  have htrace : WordTrace (prefixWord ++ tailWord_946392) baseStart_946392 baseEnd_946392 := by
    simpa [prefixWord, tailWord_946392, baseEnd_946392] using wordTrace_append hprefix tailTrace_946392
  have hstable : (prefixWord ++ tailWord_946392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946392).length < 2 ^ (prefixWord ++ tailWord_946392).sum := by decide
  have hdescent : baseEnd_946392 < baseStart_946392 := by decide
  rcases family_descends (prefixWord ++ tailWord_946392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946405 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 4, 4]
def baseStart_946405 : Nat := 118140960795 + 946405 * 2 ^ 59
def prefixEnd_946405 : Nat := 4983230072969 + 3 ^ 40 * 946405 * 2
def baseEnd_946405 : Nat := 323973772545649946523379

theorem tailTrace_946405 : CollatzResearch.WordTrace tailWord_946405 prefixEnd_946405 323973772545649946523379 := by
  unfold tailWord_946405
  simp only [CollatzResearch.WordTrace]
  refine ⟨34518226136343792950840669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23012150757562528633893779 34518226136343792950840669)
  ·
    refine ⟨12944334801128922356565251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34518226136343792950840669 12944334801128922356565251)
    ·
      refine ⟨19416502201693383534847877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944334801128922356565251 19416502201693383534847877)
      ·
        refine ⟨3640594162817509412783977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19416502201693383534847877 3640594162817509412783977)
        ·
          refine ⟨2730445622113132059587983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3640594162817509412783977 2730445622113132059587983)
          ·
            refine ⟨4095668433169698089381975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730445622113132059587983 4095668433169698089381975)
            ·
              refine ⟨6143502649754547134072963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095668433169698089381975 6143502649754547134072963)
              ·
                refine ⟨9215253974631820701109445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143502649754547134072963 9215253974631820701109445)
                ·
                  refine ⟨1727860120243466381458021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9215253974631820701109445 1727860120243466381458021)
                  ·
                    refine ⟨323973772545649946523379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1727860120243466381458021 323973772545649946523379)
                    ·
                      rfl

theorem cell22_946405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_946405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946405 prefixEnd_946405 := by exact prefixLift 946405
  have htrace : WordTrace (prefixWord ++ tailWord_946405) baseStart_946405 baseEnd_946405 := by
    simpa [prefixWord, tailWord_946405, baseEnd_946405] using wordTrace_append hprefix tailTrace_946405
  have hstable : (prefixWord ++ tailWord_946405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946405).length < 2 ^ (prefixWord ++ tailWord_946405).sum := by decide
  have hdescent : baseEnd_946405 < baseStart_946405 := by decide
  rcases family_descends (prefixWord ++ tailWord_946405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946407 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 4, 3]
def baseStart_946407 : Nat := 118140960795 + 946407 * 2 ^ 59
def prefixEnd_946407 : Nat := 4983230072969 + 3 ^ 40 * 946407 * 2
def baseEnd_946407 : Nat := 323974457186522607973373

theorem tailTrace_946407 : CollatzResearch.WordTrace tailWord_946407 prefixEnd_946407 323974457186522607973373 := by
  unfold tailWord_946407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34518299082336547292413475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23012199388224364861608983 34518299082336547292413475)
  ·
    refine ⟨51777448623504820938620213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34518299082336547292413475 51777448623504820938620213)
    ·
      refine ⟨4854135808453576962995645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51777448623504820938620213 4854135808453576962995645)
      ·
        refine ⟨1820300928170091361123367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4854135808453576962995645 1820300928170091361123367)
        ·
          refine ⟨2730451392255137041685051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820300928170091361123367 2730451392255137041685051)
          ·
            refine ⟨4095677088382705562527577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730451392255137041685051 4095677088382705562527577)
            ·
              refine ⟨3071757816287029171895683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095677088382705562527577 3071757816287029171895683)
              ·
                refine ⟨4607636724430543757843525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071757816287029171895683 4607636724430543757843525)
                ·
                  refine ⟨863931885830726954595661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4607636724430543757843525 863931885830726954595661)
                  ·
                    refine ⟨323974457186522607973373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863931885830726954595661 323974457186522607973373)
                    ·
                      rfl

theorem cell22_946407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_946407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946407 prefixEnd_946407 := by exact prefixLift 946407
  have htrace : WordTrace (prefixWord ++ tailWord_946407) baseStart_946407 baseEnd_946407 := by
    simpa [prefixWord, tailWord_946407, baseEnd_946407] using wordTrace_append hprefix tailTrace_946407
  have hstable : (prefixWord ++ tailWord_946407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946407).length < 2 ^ (prefixWord ++ tailWord_946407).sum := by decide
  have hdescent : baseEnd_946407 < baseStart_946407 := by decide
  rcases family_descends (prefixWord ++ tailWord_946407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946435 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 5, 3]
def baseStart_946435 : Nat := 118140960795 + 946435 * 2 ^ 59
def prefixEnd_946435 : Nat := 4983230072969 + 3 ^ 40 * 946435 * 2
def baseEnd_946435 : Nat := 323984042158739868273287

theorem tailTrace_946435 : CollatzResearch.WordTrace tailWord_946435 prefixEnd_946435 323984042158739868273287 := by
  unfold tailWord_946435
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519320326235108074432759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23012880217490072049621839 34519320326235108074432759)
  ·
    refine ⟨51778980489352662111649139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34519320326235108074432759 51778980489352662111649139)
    ·
      refine ⟨77668470734028993167473709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51778980489352662111649139 77668470734028993167473709)
      ·
        refine ⟨29125676525260872437802641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77668470734028993167473709 29125676525260872437802641)
        ·
          refine ⟨21844257393945654328351981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29125676525260872437802641 21844257393945654328351981)
          ·
            refine ⟨8191596522729620373131993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21844257393945654328351981 8191596522729620373131993)
            ·
              refine ⟨6143697392047215279848995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8191596522729620373131993 6143697392047215279848995)
              ·
                refine ⟨9215546088070822919773493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143697392047215279848995 9215546088070822919773493)
                ·
                  refine ⟨863957445756639648728765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9215546088070822919773493 863957445756639648728765)
                  ·
                    refine ⟨323984042158739868273287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 863957445756639648728765 323984042158739868273287)
                    ·
                      rfl

theorem cell22_946435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 5, 3].length) (baseStart_946435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946435 prefixEnd_946435 := by exact prefixLift 946435
  have htrace : WordTrace (prefixWord ++ tailWord_946435) baseStart_946435 baseEnd_946435 := by
    simpa [prefixWord, tailWord_946435, baseEnd_946435] using wordTrace_append hprefix tailTrace_946435
  have hstable : (prefixWord ++ tailWord_946435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946435).length < 2 ^ (prefixWord ++ tailWord_946435).sum := by decide
  have hdescent : baseEnd_946435 < baseStart_946435 := by decide
  rcases family_descends (prefixWord ++ tailWord_946435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946439 : List Nat := [1, 1, 4, 5, 1, 1, 2, 1, 2, 4]
def baseStart_946439 : Nat := 118140960795 + 946439 * 2 ^ 59
def prefixEnd_946439 : Nat := 4983230072969 + 3 ^ 40 * 946439 * 2
def baseEnd_946439 : Nat := 323985411440485191173275

theorem tailTrace_946439 : CollatzResearch.WordTrace tailWord_946439 prefixEnd_946439 323985411440485191173275 := by
  unfold tailWord_946439
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519466218220616757578371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23012977478813744505052247 34519466218220616757578371)
  ·
    refine ⟨51779199327330925136367557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34519466218220616757578371 51779199327330925136367557)
    ·
      refine ⟨9708599873874548463068917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51779199327330925136367557 9708599873874548463068917)
      ·
        refine ⟨910181238175738918412711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9708599873874548463068917 910181238175738918412711)
        ·
          refine ⟨1365271857263608377619067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910181238175738918412711 1365271857263608377619067)
          ·
            refine ⟨2047907785895412566428601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365271857263608377619067 2047907785895412566428601)
            ·
              refine ⟨1535930839421559424821451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047907785895412566428601 1535930839421559424821451)
              ·
                refine ⟨2303896259132339137232177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535930839421559424821451 2303896259132339137232177)
                ·
                  refine ⟨1727922194349254352924133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2303896259132339137232177 1727922194349254352924133)
                  ·
                    refine ⟨323985411440485191173275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1727922194349254352924133 323985411440485191173275)
                    ·
                      rfl

theorem cell22_946439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_946439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946439 prefixEnd_946439 := by exact prefixLift 946439
  have htrace : WordTrace (prefixWord ++ tailWord_946439) baseStart_946439 baseEnd_946439 := by
    simpa [prefixWord, tailWord_946439, baseEnd_946439] using wordTrace_append hprefix tailTrace_946439
  have hstable : (prefixWord ++ tailWord_946439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946439).length < 2 ^ (prefixWord ++ tailWord_946439).sum := by decide
  have hdescent : baseEnd_946439 < baseStart_946439 := by decide
  rcases family_descends (prefixWord ++ tailWord_946439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946465 : List Nat := [1, 2, 3, 2, 1, 1, 3, 4, 5]
def baseStart_946465 : Nat := 118140960795 + 946465 * 2 ^ 59
def prefixEnd_946465 : Nat := 4983230072969 + 3 ^ 40 * 946465 * 2
def baseEnd_946465 : Nat := 107998103923943263341065

theorem tailTrace_946465 : CollatzResearch.WordTrace tailWord_946465 prefixEnd_946465 107998103923943263341065 := by
  unfold tailWord_946465
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520414516126423198024849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23013609677417615465349899 34520414516126423198024849)
  ·
    refine ⟨25890310887094817398518637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34520414516126423198024849 25890310887094817398518637)
    ·
      refine ⟨9708866582660556524444489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25890310887094817398518637 9708866582660556524444489)
      ·
        refine ⟨7281649936995417393333367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9708866582660556524444489 7281649936995417393333367)
        ·
          refine ⟨10922474905493126090000051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7281649936995417393333367 10922474905493126090000051)
          ·
            refine ⟨16383712358239689135000077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10922474905493126090000051 16383712358239689135000077)
            ·
              refine ⟨6143892134339883425625029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16383712358239689135000077 6143892134339883425625029)
              ·
                refine ⟨1151979775188728142304693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6143892134339883425625029 1151979775188728142304693)
                ·
                  refine ⟨107998103923943263341065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1151979775188728142304693 107998103923943263341065)
                  ·
                    rfl

theorem cell22_946465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 5].length) (baseStart_946465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946465 prefixEnd_946465 := by exact prefixLift 946465
  have htrace : WordTrace (prefixWord ++ tailWord_946465) baseStart_946465 baseEnd_946465 := by
    simpa [prefixWord, tailWord_946465, baseEnd_946465] using wordTrace_append hprefix tailTrace_946465
  have hstable : (prefixWord ++ tailWord_946465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946465).length < 2 ^ (prefixWord ++ tailWord_946465).sum := by decide
  have hdescent : baseEnd_946465 < baseStart_946465 := by decide
  rcases family_descends (prefixWord ++ tailWord_946465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946471 : List Nat := [1, 1, 8, 1, 1, 2, 1, 7]
def baseStart_946471 : Nat := 118140960795 + 946471 * 2 ^ 59
def prefixEnd_946471 : Nat := 4983230072969 + 3 ^ 40 * 946471 * 2
def baseEnd_946471 : Nat := 35999596188271974930353

theorem tailTrace_946471 : CollatzResearch.WordTrace tailWord_946471 prefixEnd_946471 35999596188271974930353 := by
  unfold tailWord_946471
  simp only [CollatzResearch.WordTrace]
  refine ⟨34520633354104686222743267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23013755569403124148495511 34520633354104686222743267)
  ·
    refine ⟨51780950031157029334114901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34520633354104686222743267 51780950031157029334114901)
    ·
      refine ⟨606808008177621437509159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 51780950031157029334114901 606808008177621437509159)
      ·
        refine ⟨910212012266432156263739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606808008177621437509159 910212012266432156263739)
        ·
          refine ⟨1365318018399648234395609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910212012266432156263739 1365318018399648234395609)
          ·
            refine ⟨1023988513799736175796707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365318018399648234395609 1023988513799736175796707)
            ·
              refine ⟨1535982770699604263695061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1023988513799736175796707 1535982770699604263695061)
              ·
                refine ⟨35999596188271974930353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1535982770699604263695061 35999596188271974930353)
                ·
                  rfl

theorem cell22_946471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 7].length) (baseStart_946471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946471 prefixEnd_946471 := by exact prefixLift 946471
  have htrace : WordTrace (prefixWord ++ tailWord_946471) baseStart_946471 baseEnd_946471 := by
    simpa [prefixWord, tailWord_946471, baseEnd_946471] using wordTrace_append hprefix tailTrace_946471
  have hstable : (prefixWord ++ tailWord_946471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946471).length < 2 ^ (prefixWord ++ tailWord_946471).sum := by decide
  have hdescent : baseEnd_946471 < baseStart_946471 := by decide
  rcases family_descends (prefixWord ++ tailWord_946471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946495 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 3, 4]
def baseStart_946495 : Nat := 118140960795 + 946495 * 2 ^ 59
def prefixEnd_946495 : Nat := 4983230072969 + 3 ^ 40 * 946495 * 2
def baseEnd_946495 : Nat := 324004581384919711773103

theorem tailTrace_946495 : CollatzResearch.WordTrace tailWord_946495 prefixEnd_946495 324004581384919711773103 := by
  unfold tailWord_946495
  simp only [CollatzResearch.WordTrace]
  refine ⟨34521508706017738321616939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23014339137345158881077959 34521508706017738321616939)
  ·
    refine ⟨51782263059026607482425409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34521508706017738321616939 51782263059026607482425409)
    ·
      refine ⟨38836697294269955611819057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51782263059026607482425409 38836697294269955611819057)
      ·
        refine ⟨29127522970702466708864293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38836697294269955611819057 29127522970702466708864293)
        ·
          refine ⟨5461410557006712507912055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29127522970702466708864293 5461410557006712507912055)
          ·
            refine ⟨8192115835510068761868083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461410557006712507912055 8192115835510068761868083)
            ·
              refine ⟨12288173753265103142802125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8192115835510068761868083 12288173753265103142802125)
              ·
                refine ⟨4608065157474413678550797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12288173753265103142802125 4608065157474413678550797)
                ·
                  refine ⟨1728024434052905129456549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4608065157474413678550797 1728024434052905129456549)
                  ·
                    refine ⟨324004581384919711773103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1728024434052905129456549 324004581384919711773103)
                    ·
                      rfl

theorem cell22_946495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_946495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946495 prefixEnd_946495 := by exact prefixLift 946495
  have htrace : WordTrace (prefixWord ++ tailWord_946495) baseStart_946495 baseEnd_946495 := by
    simpa [prefixWord, tailWord_946495, baseEnd_946495] using wordTrace_append hprefix tailTrace_946495
  have hstable : (prefixWord ++ tailWord_946495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946495).length < 2 ^ (prefixWord ++ tailWord_946495).sum := by decide
  have hdescent : baseEnd_946495 < baseStart_946495 := by decide
  rcases family_descends (prefixWord ++ tailWord_946495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946512 : List Nat := [2, 1, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_946512 : Nat := 118140960795 + 946512 * 2 ^ 59
def prefixEnd_946512 : Nat := 4983230072969 + 3 ^ 40 * 946512 * 2
def baseEnd_946512 : Nat := 324010400832337334098051

theorem tailTrace_946512 : CollatzResearch.WordTrace tailWord_946512 prefixEnd_946512 324010400832337334098051 := by
  unfold tailWord_946512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17261064373478075112492895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23014752497970766816657193 17261064373478075112492895)
  ·
    refine ⟨25891596560217112668739343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17261064373478075112492895 25891596560217112668739343)
    ·
      refine ⟨38837394840325669003109015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25891596560217112668739343 38837394840325669003109015)
      ·
        refine ⟨58256092260488503504663523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38837394840325669003109015 58256092260488503504663523)
        ·
          refine ⟨87384138390732755256995285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58256092260488503504663523 87384138390732755256995285)
          ·
            refine ⟨2048065743532798951335827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 87384138390732755256995285 2048065743532798951335827)
            ·
              refine ⟨3072098615299198427003741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048065743532798951335827 3072098615299198427003741)
              ·
                refine ⟨1152036980737199410126403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3072098615299198427003741 1152036980737199410126403)
                ·
                  refine ⟨1728055471105799115189605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152036980737199410126403 1728055471105799115189605)
                  ·
                    refine ⟨324010400832337334098051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1728055471105799115189605 324010400832337334098051)
                    ·
                      rfl

theorem cell22_946512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_946512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946512 prefixEnd_946512 := by exact prefixLift 946512
  have htrace : WordTrace (prefixWord ++ tailWord_946512) baseStart_946512 baseEnd_946512 := by
    simpa [prefixWord, tailWord_946512, baseEnd_946512] using wordTrace_append hprefix tailTrace_946512
  have hstable : (prefixWord ++ tailWord_946512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946512).length < 2 ^ (prefixWord ++ tailWord_946512).sum := by decide
  have hdescent : baseEnd_946512 < baseStart_946512 := by decide
  rcases family_descends (prefixWord ++ tailWord_946512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946527 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 4]
def baseStart_946527 : Nat := 118140960795 + 946527 * 2 ^ 59
def prefixEnd_946527 : Nat := 4983230072969 + 3 ^ 40 * 946527 * 2
def baseEnd_946527 : Nat := 108005178546294098324335

theorem tailTrace_946527 : CollatzResearch.WordTrace tailWord_946527 prefixEnd_946527 108005178546294098324335 := by
  unfold tailWord_946527
  simp only [CollatzResearch.WordTrace]
  refine ⟨34522675841901807786781835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23015117227934538524521223 34522675841901807786781835)
  ·
    refine ⟨51784013762852711680172753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34522675841901807786781835 51784013762852711680172753)
    ·
      refine ⟨38838010322139533760129565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51784013762852711680172753 38838010322139533760129565)
      ·
        refine ⟨14564253870802325160048587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38838010322139533760129565 14564253870802325160048587)
        ·
          refine ⟨21846380806203487740072881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564253870802325160048587 21846380806203487740072881)
          ·
            refine ⟨16384785604652615805054661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21846380806203487740072881 16384785604652615805054661)
            ·
              refine ⟨3072147300872365463447749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16384785604652615805054661 3072147300872365463447749)
              ·
                refine ⟨576027618913568524396453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3072147300872365463447749 576027618913568524396453)
                ·
                  refine ⟨108005178546294098324335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576027618913568524396453 108005178546294098324335)
                  ·
                    rfl

theorem cell22_946527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 4].length) (baseStart_946527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946527 prefixEnd_946527 := by exact prefixLift 946527
  have htrace : WordTrace (prefixWord ++ tailWord_946527) baseStart_946527 baseEnd_946527 := by
    simpa [prefixWord, tailWord_946527, baseEnd_946527] using wordTrace_append hprefix tailTrace_946527
  have hstable : (prefixWord ++ tailWord_946527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946527).length < 2 ^ (prefixWord ++ tailWord_946527).sum := by decide
  have hdescent : baseEnd_946527 < baseStart_946527 := by decide
  rcases family_descends (prefixWord ++ tailWord_946527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946555 : List Nat := [1, 1, 1, 1, 1, 8, 1, 8]
def baseStart_946555 : Nat := 118140960795 + 946555 * 2 ^ 59
def prefixEnd_946555 : Nat := 4983230072969 + 3 ^ 40 * 946555 * 2
def baseEnd_946555 : Nat := 36002791179011061696991

theorem tailTrace_946555 : CollatzResearch.WordTrace tailWord_946555 prefixEnd_946555 36002791179011061696991 := by
  unfold tailWord_946555
  simp only [CollatzResearch.WordTrace]
  refine ⟨34523697085800368568801119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23015798057200245712534079 34523697085800368568801119)
  ·
    refine ⟨51785545628700552853201679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34523697085800368568801119 51785545628700552853201679)
    ·
      refine ⟨77678318443050829279802519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51785545628700552853201679 77678318443050829279802519)
      ·
        refine ⟨116517477664576243919703779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77678318443050829279802519 116517477664576243919703779)
        ·
          refine ⟨174776216496864365879555669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116517477664576243919703779 174776216496864365879555669)
          ·
            refine ⟨2048158787072629287651043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 174776216496864365879555669 2048158787072629287651043)
            ·
              refine ⟨3072238180608943931476565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048158787072629287651043 3072238180608943931476565)
              ·
                refine ⟨36002791179011061696991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3072238180608943931476565 36002791179011061696991)
                ·
                  rfl

theorem cell22_946555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 8].length) (baseStart_946555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946555 prefixEnd_946555 := by exact prefixLift 946555
  have htrace : WordTrace (prefixWord ++ tailWord_946555) baseStart_946555 baseEnd_946555 := by
    simpa [prefixWord, tailWord_946555, baseEnd_946555] using wordTrace_append hprefix tailTrace_946555
  have hstable : (prefixWord ++ tailWord_946555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946555).length < 2 ^ (prefixWord ++ tailWord_946555).sum := by decide
  have hdescent : baseEnd_946555 < baseStart_946555 := by decide
  rcases family_descends (prefixWord ++ tailWord_946555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946561 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 4]
def baseStart_946561 : Nat := 118140960795 + 946561 * 2 ^ 59
def prefixEnd_946561 : Nat := 4983230072969 + 3 ^ 40 * 946561 * 2
def baseEnd_946561 : Nat := 108009058177905846540967

theorem tailTrace_946561 : CollatzResearch.WordTrace tailWord_946561 prefixEnd_946561 108009058177905846540967 := by
  unfold tailWord_946561
  simp only [CollatzResearch.WordTrace]
  refine ⟨34523915923778631593519537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23015943949185754395679691 34523915923778631593519537)
  ·
    refine ⟨25892936942833973695139653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34523915923778631593519537 25892936942833973695139653)
    ·
      refine ⟨4854925676781370067838685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25892936942833973695139653 4854925676781370067838685)
      ·
        refine ⟨1820597128793013775439507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4854925676781370067838685 1820597128793013775439507)
        ·
          refine ⟨2730895693189520663159261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820597128793013775439507 2730895693189520663159261)
          ·
            refine ⟨1024085884946070248684723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2730895693189520663159261 1024085884946070248684723)
            ·
              refine ⟨1536128827419105373027085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024085884946070248684723 1536128827419105373027085)
              ·
                refine ⟨576048310282164514885157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536128827419105373027085 576048310282164514885157)
                ·
                  refine ⟨108009058177905846540967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576048310282164514885157 108009058177905846540967)
                  ·
                    rfl

theorem cell22_946561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 4].length) (baseStart_946561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946561 prefixEnd_946561 := by exact prefixLift 946561
  have htrace : WordTrace (prefixWord ++ tailWord_946561) baseStart_946561 baseEnd_946561 := by
    simpa [prefixWord, tailWord_946561, baseEnd_946561] using wordTrace_append hprefix tailTrace_946561
  have hstable : (prefixWord ++ tailWord_946561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946561).length < 2 ^ (prefixWord ++ tailWord_946561).sum := by decide
  have hdescent : baseEnd_946561 < baseStart_946561 := by decide
  rcases family_descends (prefixWord ++ tailWord_946561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946574 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_946574 : Nat := 118140960795 + 946574 * 2 ^ 59
def prefixEnd_946574 : Nat := 4983230072969 + 3 ^ 40 * 946574 * 2
def baseEnd_946574 : Nat := 324031624699389839047861

theorem tailTrace_946574 : CollatzResearch.WordTrace tailWord_946574 prefixEnd_946574 324031624699389839047861 := by
  unfold tailWord_946574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315548759091441851717847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23016260048487689875828517 4315548759091441851717847)
  ·
    refine ⟨6473323138637162777576771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315548759091441851717847 6473323138637162777576771)
    ·
      refine ⟨9709984707955744166365157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473323138637162777576771 9709984707955744166365157)
      ·
        refine ⟨1820622132741702031193467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9709984707955744166365157 1820622132741702031193467)
        ·
          refine ⟨2730933199112553046790201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820622132741702031193467 2730933199112553046790201)
          ·
            refine ⟨2048199899334414785092651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730933199112553046790201 2048199899334414785092651)
            ·
              refine ⟨3072299849001622177638977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048199899334414785092651 3072299849001622177638977)
              ·
                refine ⟨2304224886751216633229233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3072299849001622177638977 2304224886751216633229233)
                ·
                  refine ⟨1728168665063412474921925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2304224886751216633229233 1728168665063412474921925)
                  ·
                    refine ⟨324031624699389839047861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1728168665063412474921925 324031624699389839047861)
                    ·
                      rfl

theorem cell22_946574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_946574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946574 prefixEnd_946574 := by exact prefixLift 946574
  have htrace : WordTrace (prefixWord ++ tailWord_946574) baseStart_946574 baseEnd_946574 := by
    simpa [prefixWord, tailWord_946574, baseEnd_946574] using wordTrace_append hprefix tailTrace_946574
  have hstable : (prefixWord ++ tailWord_946574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946574).length < 2 ^ (prefixWord ++ tailWord_946574).sum := by decide
  have hdescent : baseEnd_946574 < baseStart_946574 := by decide
  rcases family_descends (prefixWord ++ tailWord_946574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946585 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 2, 6]
def baseStart_946585 : Nat := 118140960795 + 946585 * 2 ^ 59
def prefixEnd_946585 : Nat := 4983230072969 + 3 ^ 40 * 946585 * 2
def baseEnd_946585 : Nat := 324035390224189477022827

theorem tailTrace_946585 : CollatzResearch.WordTrace tailWord_946585 prefixEnd_946585 324035390224189477022827 := by
  unfold tailWord_946585
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524791275691683692393209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23016527517127789128262139 34524791275691683692393209)
  ·
    refine ⟨25893593456768762769294907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34524791275691683692393209 25893593456768762769294907)
    ·
      refine ⟨38840390185153144153942361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25893593456768762769294907 38840390185153144153942361)
      ·
        refine ⟨29130292638864858115456771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38840390185153144153942361 29130292638864858115456771)
        ·
          refine ⟨43695438958297287173185157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29130292638864858115456771 43695438958297287173185157)
          ·
            refine ⟨8192894804680741344972217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43695438958297287173185157 8192894804680741344972217)
            ·
              refine ⟨6144671103510556008729163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8192894804680741344972217 6144671103510556008729163)
              ·
                refine ⟨9217006655265834013093745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144671103510556008729163 9217006655265834013093745)
                ·
                  refine ⟨6912754991449375509820309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9217006655265834013093745 6912754991449375509820309)
                  ·
                    refine ⟨324035390224189477022827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6912754991449375509820309 324035390224189477022827)
                    ·
                      rfl

theorem cell22_946585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_946585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946585 prefixEnd_946585 := by exact prefixLift 946585
  have htrace : WordTrace (prefixWord ++ tailWord_946585) baseStart_946585 baseEnd_946585 := by
    simpa [prefixWord, tailWord_946585, baseEnd_946585] using wordTrace_append hprefix tailTrace_946585
  have hstable : (prefixWord ++ tailWord_946585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946585).length < 2 ^ (prefixWord ++ tailWord_946585).sum := by decide
  have hdescent : baseEnd_946585 < baseStart_946585 := by decide
  rcases family_descends (prefixWord ++ tailWord_946585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946722 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_946722 : Nat := 118140960795 + 946722 * 2 ^ 59
def prefixEnd_946722 : Nat := 4983230072969 + 3 ^ 40 * 946722 * 2
def baseEnd_946722 : Nat := 324082288123966786347407

theorem tailTrace_946722 : CollatzResearch.WordTrace tailWord_946722 prefixEnd_946722 324082288123966786347407 := by
  unfold tailWord_946722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8632447019048839022532605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23019858717463570726753613 8632447019048839022532605)
  ·
    refine ⟨3237167632143314633449727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8632447019048839022532605 3237167632143314633449727)
    ·
      refine ⟨4855751448214971950174591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3237167632143314633449727 4855751448214971950174591)
      ·
        refine ⟨7283627172322457925261887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4855751448214971950174591 7283627172322457925261887)
        ·
          refine ⟨10925440758483686887892831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7283627172322457925261887 10925440758483686887892831)
          ·
            refine ⟨16388161137725530331839247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10925440758483686887892831 16388161137725530331839247)
            ·
              refine ⟨24582241706588295497758871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16388161137725530331839247 24582241706588295497758871)
              ·
                refine ⟨36873362559882443246638307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24582241706588295497758871 36873362559882443246638307)
                ·
                  refine ⟨55310043839823664869957461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36873362559882443246638307 55310043839823664869957461)
                  ·
                    refine ⟨324082288123966786347407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 55310043839823664869957461 324082288123966786347407)
                    ·
                      rfl

theorem cell22_946722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_946722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946722 prefixEnd_946722 := by exact prefixLift 946722
  have htrace : WordTrace (prefixWord ++ tailWord_946722) baseStart_946722 baseEnd_946722 := by
    simpa [prefixWord, tailWord_946722, baseEnd_946722] using wordTrace_append hprefix tailTrace_946722
  have hstable : (prefixWord ++ tailWord_946722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946722).length < 2 ^ (prefixWord ++ tailWord_946722).sum := by decide
  have hdescent : baseEnd_946722 < baseStart_946722 := by decide
  rcases family_descends (prefixWord ++ tailWord_946722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946752 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_946752 : Nat := 118140960795 + 946752 * 2 ^ 59
def prefixEnd_946752 : Nat := 4983230072969 + 3 ^ 40 * 946752 * 2
def baseEnd_946752 : Nat := 108030852579018902699105

theorem tailTrace_946752 : CollatzResearch.WordTrace tailWord_946752 prefixEnd_946752 108030852579018902699105 := by
  unfold tailWord_946752
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265441133043335606861255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23020588177391114142481673 17265441133043335606861255)
  ·
    refine ⟨25898161699565003410291883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17265441133043335606861255 25898161699565003410291883)
    ·
      refine ⟨38847242549347505115437825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25898161699565003410291883 38847242549347505115437825)
      ·
        refine ⟨29135431912010628836578369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38847242549347505115437825 29135431912010628836578369)
        ·
          refine ⟨21851573934007971627433777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29135431912010628836578369 21851573934007971627433777)
          ·
            refine ⟨16388680450505978720575333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21851573934007971627433777 16388680450505978720575333)
            ·
              refine ⟨3072877584469871010107875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16388680450505978720575333 3072877584469871010107875)
              ·
                refine ⟨4609316376704806515161813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072877584469871010107875 4609316376704806515161813)
                ·
                  refine ⟨108030852579018902699105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4609316376704806515161813 108030852579018902699105)
                  ·
                    rfl

theorem cell22_946752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_946752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946752 prefixEnd_946752 := by exact prefixLift 946752
  have htrace : WordTrace (prefixWord ++ tailWord_946752) baseStart_946752 baseEnd_946752 := by
    simpa [prefixWord, tailWord_946752, baseEnd_946752] using wordTrace_append hprefix tailTrace_946752
  have hstable : (prefixWord ++ tailWord_946752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946752).length < 2 ^ (prefixWord ++ tailWord_946752).sum := by decide
  have hdescent : baseEnd_946752 < baseStart_946752 := by decide
  rcases family_descends (prefixWord ++ tailWord_946752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946767 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 2, 5]
def baseStart_946767 : Nat := 118140960795 + 946767 * 2 ^ 59
def prefixEnd_946767 : Nat := 4983230072969 + 3 ^ 40 * 946767 * 2
def baseEnd_946767 : Nat := 324097692543601668972269

theorem tailTrace_946767 : CollatzResearch.WordTrace tailWord_946767 prefixEnd_946767 324097692543601668972269 := by
  unfold tailWord_946767
  simp only [CollatzResearch.WordTrace]
  refine ⟨34531429361032328775518555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23020952907354885850345703 34531429361032328775518555)
  ·
    refine ⟨51797144041548493163277833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34531429361032328775518555 51797144041548493163277833)
    ·
      refine ⟨38847858031161369872458375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51797144041548493163277833 38847858031161369872458375)
      ·
        refine ⟨58271787046742054808687563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38847858031161369872458375 58271787046742054808687563)
        ·
          refine ⟨87407680570113082213031345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58271787046742054808687563 87407680570113082213031345)
          ·
            refine ⟨65555760427584811659773509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87407680570113082213031345 65555760427584811659773509)
            ·
              refine ⟨12291705080172152186207533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65555760427584811659773509 12291705080172152186207533)
              ·
                refine ⟨4609389405064557069827825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12291705080172152186207533 4609389405064557069827825)
                ·
                  refine ⟨3457042053798417802370869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609389405064557069827825 3457042053798417802370869)
                  ·
                    refine ⟨324097692543601668972269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3457042053798417802370869 324097692543601668972269)
                    ·
                      rfl

theorem cell22_946767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_946767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946767 prefixEnd_946767 := by exact prefixLift 946767
  have htrace : WordTrace (prefixWord ++ tailWord_946767) baseStart_946767 baseEnd_946767 := by
    simpa [prefixWord, tailWord_946767, baseEnd_946767] using wordTrace_append hprefix tailTrace_946767
  have hstable : (prefixWord ++ tailWord_946767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946767).length < 2 ^ (prefixWord ++ tailWord_946767).sum := by decide
  have hdescent : baseEnd_946767 < baseStart_946767 := by decide
  rcases family_descends (prefixWord ++ tailWord_946767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946769 : List Nat := [1, 2, 2, 1, 3, 4, 1, 3, 5]
def baseStart_946769 : Nat := 118140960795 + 946769 * 2 ^ 59
def prefixEnd_946769 : Nat := 4983230072969 + 3 ^ 40 * 946769 * 2
def baseEnd_946769 : Nat := 108032792394824776807421

theorem tailTrace_946769 : CollatzResearch.WordTrace tailWord_946769 prefixEnd_946769 108032792394824776807421 := by
  unfold tailWord_946769
  simp only [CollatzResearch.WordTrace]
  refine ⟨34531502307025083117091361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23021001538016722078060907 34531502307025083117091361)
  ·
    refine ⟨25898626730268812337818521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34531502307025083117091361 25898626730268812337818521)
    ·
      refine ⟨19423970047701609253363891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25898626730268812337818521 19423970047701609253363891)
      ·
        refine ⟨29135955071552413880045837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19423970047701609253363891 29135955071552413880045837)
        ·
          refine ⟨10925983151832155205017189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29135955071552413880045837 10925983151832155205017189)
          ·
            refine ⟨2048621840968529100940723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10925983151832155205017189 2048621840968529100940723)
            ·
              refine ⟨3072932761452793651411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048621840968529100940723 3072932761452793651411085)
              ·
                refine ⟨1152349785544797619279157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3072932761452793651411085 1152349785544797619279157)
                ·
                  refine ⟨108032792394824776807421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1152349785544797619279157 108032792394824776807421)
                  ·
                    rfl

theorem cell22_946769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_946769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946769 prefixEnd_946769 := by exact prefixLift 946769
  have htrace : WordTrace (prefixWord ++ tailWord_946769) baseStart_946769 baseEnd_946769 := by
    simpa [prefixWord, tailWord_946769, baseEnd_946769] using wordTrace_append hprefix tailTrace_946769
  have hstable : (prefixWord ++ tailWord_946769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946769).length < 2 ^ (prefixWord ++ tailWord_946769).sum := by decide
  have hdescent : baseEnd_946769 < baseStart_946769 := by decide
  rcases family_descends (prefixWord ++ tailWord_946769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946799 : List Nat := [1, 1, 2, 1, 3, 2, 2, 5, 1, 4]
def baseStart_946799 : Nat := 118140960795 + 946799 * 2 ^ 59
def prefixEnd_946799 : Nat := 4983230072969 + 3 ^ 40 * 946799 * 2
def baseEnd_946799 : Nat := 324108646797564252172171

theorem tailTrace_946799 : CollatzResearch.WordTrace tailWord_946799 prefixEnd_946799 324108646797564252172171 := by
  unfold tailWord_946799
  simp only [CollatzResearch.WordTrace]
  refine ⟨34532596496916398240683451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23021730997944265493788967 34532596496916398240683451)
  ·
    refine ⟨51798894745374597361025177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34532596496916398240683451 51798894745374597361025177)
    ·
      refine ⟨38849171059030948020768883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51798894745374597361025177 38849171059030948020768883)
      ·
        refine ⟨58273756588546422031153325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38849171059030948020768883 58273756588546422031153325)
        ·
          refine ⟨21852658720704908261682497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58273756588546422031153325 21852658720704908261682497)
          ·
            refine ⟨16389494040528681196261873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21852658720704908261682497 16389494040528681196261873)
            ·
              refine ⟨12292120530396510897196405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16389494040528681196261873 12292120530396510897196405)
              ·
                refine ⟨1152386299724672896612163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12292120530396510897196405 1152386299724672896612163)
                ·
                  refine ⟨1728579449587009344918245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152386299724672896612163 1728579449587009344918245)
                  ·
                    refine ⟨324108646797564252172171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1728579449587009344918245 324108646797564252172171)
                    ·
                      rfl

theorem cell22_946799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_946799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946799 prefixEnd_946799 := by exact prefixLift 946799
  have htrace : WordTrace (prefixWord ++ tailWord_946799) baseStart_946799 baseEnd_946799 := by
    simpa [prefixWord, tailWord_946799, baseEnd_946799] using wordTrace_append hprefix tailTrace_946799
  have hstable : (prefixWord ++ tailWord_946799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946799).length < 2 ^ (prefixWord ++ tailWord_946799).sum := by decide
  have hdescent : baseEnd_946799 < baseStart_946799 := by decide
  rcases family_descends (prefixWord ++ tailWord_946799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946846 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_946846 : Nat := 118140960795 + 946846 * 2 ^ 59
def prefixEnd_946846 : Nat := 4983230072969 + 3 ^ 40 * 946846 * 2
def baseEnd_946846 : Nat := 324124735858071796247027

theorem tailTrace_946846 : CollatzResearch.WordTrace tailWord_946846 prefixEnd_946846 324124735858071796247027 := by
  unfold tailWord_946846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316788840968265658455549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23022873818497416845096261 4316788840968265658455549)
  ·
    refine ⟨1618795815363099621920831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4316788840968265658455549 1618795815363099621920831)
    ·
      refine ⟨2428193723044649432881247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618795815363099621920831 2428193723044649432881247)
      ·
        refine ⟨3642290584566974149321871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428193723044649432881247 3642290584566974149321871)
        ·
          refine ⟨5463435876850461223982807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642290584566974149321871 5463435876850461223982807)
          ·
            refine ⟨8195153815275691835974211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463435876850461223982807 8195153815275691835974211)
            ·
              refine ⟨12292730722913537753961317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195153815275691835974211 12292730722913537753961317)
              ·
                refine ⟨2304887010546288328867747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12292730722913537753961317 2304887010546288328867747)
                ·
                  refine ⟨3457330515819432493301621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304887010546288328867747 3457330515819432493301621)
                  ·
                    refine ⟨324124735858071796247027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3457330515819432493301621 324124735858071796247027)
                    ·
                      rfl

theorem cell22_946846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_946846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946846 prefixEnd_946846 := by exact prefixLift 946846
  have htrace : WordTrace (prefixWord ++ tailWord_946846) baseStart_946846 baseEnd_946846 := by
    simpa [prefixWord, tailWord_946846, baseEnd_946846] using wordTrace_append hprefix tailTrace_946846
  have hstable : (prefixWord ++ tailWord_946846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946846).length < 2 ^ (prefixWord ++ tailWord_946846).sum := by decide
  have hdescent : baseEnd_946846 < baseStart_946846 := by decide
  rcases family_descends (prefixWord ++ tailWord_946846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946848 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_946848 : Nat := 118140960795 + 946848 * 2 ^ 59
def prefixEnd_946848 : Nat := 4983230072969 + 3 ^ 40 * 946848 * 2
def baseEnd_946848 : Nat := 108041806832981485899007

theorem tailTrace_946848 : CollatzResearch.WordTrace tailWord_946848 prefixEnd_946848 108041806832981485899007 := by
  unfold tailWord_946848
  simp only [CollatzResearch.WordTrace]
  refine ⟨17267191836869439804608599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23022922449159253072811465 17267191836869439804608599)
  ·
    refine ⟨25900787755304159706912899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17267191836869439804608599 25900787755304159706912899)
    ·
      refine ⟨38851181632956239560369349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25900787755304159706912899 38851181632956239560369349)
      ·
        refine ⟨7284596556179294917569253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38851181632956239560369349 7284596556179294917569253)
        ·
          refine ⟨1365861854283617797044235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7284596556179294917569253 1365861854283617797044235)
          ·
            refine ⟨2048792781425426695566353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365861854283617797044235 2048792781425426695566353)
            ·
              refine ⟨1536594586069070021674765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048792781425426695566353 1536594586069070021674765)
              ·
                refine ⟨576222969775901258128037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536594586069070021674765 576222969775901258128037)
                ·
                  refine ⟨108041806832981485899007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576222969775901258128037 108041806832981485899007)
                  ·
                    rfl

theorem cell22_946848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_946848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946848 prefixEnd_946848 := by exact prefixLift 946848
  have htrace : WordTrace (prefixWord ++ tailWord_946848) baseStart_946848 baseEnd_946848 := by
    simpa [prefixWord, tailWord_946848, baseEnd_946848] using wordTrace_append hprefix tailTrace_946848
  have hstable : (prefixWord ++ tailWord_946848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946848).length < 2 ^ (prefixWord ++ tailWord_946848).sum := by decide
  have hdescent : baseEnd_946848 < baseStart_946848 := by decide
  rcases family_descends (prefixWord ++ tailWord_946848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946863 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 2, 3]
def baseStart_946863 : Nat := 118140960795 + 946863 * 2 ^ 59
def prefixEnd_946863 : Nat := 4983230072969 + 3 ^ 40 * 946863 * 2
def baseEnd_946863 : Nat := 324130555305489418571975

theorem tailTrace_946863 : CollatzResearch.WordTrace tailWord_946863 prefixEnd_946863 324130555305489418571975 := by
  unfold tailWord_946863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34534930768684537171013243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23023287179123024780675495 34534930768684537171013243)
  ·
    refine ⟨51802396153026805756519865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34534930768684537171013243 51802396153026805756519865)
    ·
      refine ⟨38851797114770104317389899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51802396153026805756519865 38851797114770104317389899)
      ·
        refine ⟨58277695672155156476084849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38851797114770104317389899 58277695672155156476084849)
        ·
          refine ⟨43708271754116367357063637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58277695672155156476084849 43708271754116367357063637)
          ·
            refine ⟨1024412619237102359931179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43708271754116367357063637 1024412619237102359931179)
            ·
              refine ⟨1536618928855653539896769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024412619237102359931179 1536618928855653539896769)
              ·
                refine ⟨1152464196641740154922577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536618928855653539896769 1152464196641740154922577)
                ·
                  refine ⟨864348147481305116191933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1152464196641740154922577 864348147481305116191933)
                  ·
                    refine ⟨324130555305489418571975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864348147481305116191933 324130555305489418571975)
                    ·
                      rfl

theorem cell22_946863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_946863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946863 prefixEnd_946863 := by exact prefixLift 946863
  have htrace : WordTrace (prefixWord ++ tailWord_946863) baseStart_946863 baseEnd_946863 := by
    simpa [prefixWord, tailWord_946863, baseEnd_946863] using wordTrace_append hprefix tailTrace_946863
  have hstable : (prefixWord ++ tailWord_946863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946863).length < 2 ^ (prefixWord ++ tailWord_946863).sum := by decide
  have hdescent : baseEnd_946863 < baseStart_946863 := by decide
  rcases family_descends (prefixWord ++ tailWord_946863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946893 : List Nat := [1, 6, 2, 1, 2, 1, 1, 8]
def baseStart_946893 : Nat := 118140960795 + 946893 * 2 ^ 59
def prefixEnd_946893 : Nat := 4983230072969 + 3 ^ 40 * 946893 * 2
def baseEnd_946893 : Nat := 36015647213175482257987

theorem tailTrace_946893 : CollatzResearch.WordTrace tailWord_946893 prefixEnd_946893 36015647213175482257987 := by
  unfold tailWord_946893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34536024958575852294605333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23024016639050568196403555 34536024958575852294605333)
  ·
    refine ⟨1618876169933243076309625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34536024958575852294605333 1618876169933243076309625)
    ·
      refine ⟨1214157127449932307232219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618876169933243076309625 1214157127449932307232219)
      ·
        refine ⟨1821235691174898460848329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214157127449932307232219 1821235691174898460848329)
        ·
          refine ⟨1365926768381173845636247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1821235691174898460848329 1365926768381173845636247)
          ·
            refine ⟨2048890152571760768454371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365926768381173845636247 2048890152571760768454371)
            ·
              refine ⟨3073335228857641152681557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048890152571760768454371 3073335228857641152681557)
              ·
                refine ⟨36015647213175482257987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3073335228857641152681557 36015647213175482257987)
                ·
                  rfl

theorem cell22_946893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 8].length) (baseStart_946893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946893 prefixEnd_946893 := by exact prefixLift 946893
  have htrace : WordTrace (prefixWord ++ tailWord_946893) baseStart_946893 baseEnd_946893 := by
    simpa [prefixWord, tailWord_946893, baseEnd_946893] using wordTrace_append hprefix tailTrace_946893
  have hstable : (prefixWord ++ tailWord_946893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946893).length < 2 ^ (prefixWord ++ tailWord_946893).sum := by decide
  have hdescent : baseEnd_946893 < baseStart_946893 := by decide
  rcases family_descends (prefixWord ++ tailWord_946893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946904 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 7]
def baseStart_946904 : Nat := 118140960795 + 946904 * 2 ^ 59
def prefixEnd_946904 : Nat := 4983230072969 + 3 ^ 40 * 946904 * 2
def baseEnd_946904 : Nat := 108048196814459659432283

theorem tailTrace_946904 : CollatzResearch.WordTrace tailWord_946904 prefixEnd_946904 108048196814459659432283 := by
  unfold tailWord_946904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17268213080768000586627883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23024284107690667448837177 17268213080768000586627883)
  ·
    refine ⟨25902319621152000879941825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17268213080768000586627883 25902319621152000879941825)
    ·
      refine ⟨19426739715864000659956369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25902319621152000879941825 19426739715864000659956369)
      ·
        refine ⟨14570054786898000494967277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19426739715864000659956369 14570054786898000494967277)
        ·
          refine ⟨5463770545086750185612729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14570054786898000494967277 5463770545086750185612729)
          ·
            refine ⟨4097827908815062639209547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5463770545086750185612729 4097827908815062639209547)
            ·
              refine ⟨6146741863222593958814321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097827908815062639209547 6146741863222593958814321)
              ·
                refine ⟨4610056397416945469110741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6146741863222593958814321 4610056397416945469110741)
                ·
                  refine ⟨108048196814459659432283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4610056397416945469110741 108048196814459659432283)
                  ·
                    rfl

theorem cell22_946904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_946904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946904 prefixEnd_946904 := by exact prefixLift 946904
  have htrace : WordTrace (prefixWord ++ tailWord_946904) baseStart_946904 baseEnd_946904 := by
    simpa [prefixWord, tailWord_946904, baseEnd_946904] using wordTrace_append hprefix tailTrace_946904
  have hstable : (prefixWord ++ tailWord_946904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946904).length < 2 ^ (prefixWord ++ tailWord_946904).sum := by decide
  have hdescent : baseEnd_946904 < baseStart_946904 := by decide
  rcases family_descends (prefixWord ++ tailWord_946904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946949 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 6]
def baseStart_946949 : Nat := 118140960795 + 946949 * 2 ^ 59
def prefixEnd_946949 : Nat := 4983230072969 + 3 ^ 40 * 946949 * 2
def baseEnd_946949 : Nat := 108053331621004620307237

theorem tailTrace_946949 : CollatzResearch.WordTrace tailWord_946949 prefixEnd_946949 108053331621004620307237 := by
  unfold tailWord_946949
  simp only [CollatzResearch.WordTrace]
  refine ⟨34538067446372973858643901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23025378297581982572429267 34538067446372973858643901)
  ·
    refine ⟨12951775292389865196991463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34538067446372973858643901 12951775292389865196991463)
    ·
      refine ⟨19427662938584797795487195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12951775292389865196991463 19427662938584797795487195)
      ·
        refine ⟨29141494407877196693230793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19427662938584797795487195 29141494407877196693230793)
        ·
          refine ⟨21856120805907897519923095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29141494407877196693230793 21856120805907897519923095)
          ·
            refine ⟨32784181208861846279884643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21856120805907897519923095 32784181208861846279884643)
            ·
              refine ⟨49176271813292769419826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32784181208861846279884643 49176271813292769419826965)
              ·
                refine ⟨2305137741248098566554389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49176271813292769419826965 2305137741248098566554389)
                ·
                  refine ⟨108053331621004620307237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2305137741248098566554389 108053331621004620307237)
                  ·
                    rfl

theorem cell22_946949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_946949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946949 prefixEnd_946949 := by exact prefixLift 946949
  have htrace : WordTrace (prefixWord ++ tailWord_946949) baseStart_946949 baseEnd_946949 := by
    simpa [prefixWord, tailWord_946949, baseEnd_946949] using wordTrace_append hprefix tailTrace_946949
  have hstable : (prefixWord ++ tailWord_946949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946949).length < 2 ^ (prefixWord ++ tailWord_946949).sum := by decide
  have hdescent : baseEnd_946949 < baseStart_946949 := by decide
  rcases family_descends (prefixWord ++ tailWord_946949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_946979 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 3, 6]
def baseStart_946979 : Nat := 118140960795 + 946979 * 2 ^ 59
def prefixEnd_946979 : Nat := 4983230072969 + 3 ^ 40 * 946979 * 2
def baseEnd_946979 : Nat := 324170264476103782671619

theorem tailTrace_946979 : CollatzResearch.WordTrace tailWord_946979 prefixEnd_946979 324170264476103782671619 := by
  unfold tailWord_946979
  simp only [CollatzResearch.WordTrace]
  refine ⟨34539161636264288982235991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026107757509525988157327 34539161636264288982235991)
  ·
    refine ⟨51808742454396433473353987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34539161636264288982235991 51808742454396433473353987)
    ·
      refine ⟨77713113681594650210030981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51808742454396433473353987 77713113681594650210030981)
      ·
        refine ⟨14571208815298996914380809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77713113681594650210030981 14571208815298996914380809)
        ·
          refine ⟨10928406611474247685785607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14571208815298996914380809 10928406611474247685785607)
          ·
            refine ⟨16392609917211371528678411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10928406611474247685785607 16392609917211371528678411)
            ·
              refine ⟨24588914875817057293017617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16392609917211371528678411 24588914875817057293017617)
              ·
                refine ⟨18441686156862792969763213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24588914875817057293017617 18441686156862792969763213)
                ·
                  refine ⟨6915632308823547363661205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18441686156862792969763213 6915632308823547363661205)
                  ·
                    refine ⟨324170264476103782671619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6915632308823547363661205 324170264476103782671619)
                    ·
                      rfl

theorem cell22_946979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 6].length) (baseStart_946979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_946979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_946979 prefixEnd_946979 := by exact prefixLift 946979
  have htrace : WordTrace (prefixWord ++ tailWord_946979) baseStart_946979 baseEnd_946979 := by
    simpa [prefixWord, tailWord_946979, baseEnd_946979] using wordTrace_append hprefix tailTrace_946979
  have hstable : (prefixWord ++ tailWord_946979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_946979).length < 2 ^ (prefixWord ++ tailWord_946979).sum := by decide
  have hdescent : baseEnd_946979 < baseStart_946979 := by decide
  rcases family_descends (prefixWord ++ tailWord_946979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947011 : List Nat := [1, 1, 1, 3, 1, 4, 5, 6]
def baseStart_947011 : Nat := 118140960795 + 947011 * 2 ^ 59
def prefixEnd_947011 : Nat := 4983230072969 + 3 ^ 40 * 947011 * 2
def baseEnd_947011 : Nat := 36020135414451818430169

theorem tailTrace_947011 : CollatzResearch.WordTrace tailWord_947011 prefixEnd_947011 36020135414451818430169 := by
  unfold tailWord_947011
  simp only [CollatzResearch.WordTrace]
  refine ⟨34540328772148358447400887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23026885848098905631600591 34540328772148358447400887)
  ·
    refine ⟨51810493158222537671101331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34540328772148358447400887 51810493158222537671101331)
    ·
      refine ⟨77715739737333806506651997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51810493158222537671101331 77715739737333806506651997)
      ·
        refine ⟨29143402401500177439994499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77715739737333806506651997 29143402401500177439994499)
        ·
          refine ⟨43715103602250266159991749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29143402401500177439994499 43715103602250266159991749)
          ·
            refine ⟨8196581925421924904998453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43715103602250266159991749 8196581925421924904998453)
            ·
              refine ⟨768429555508305459843605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8196581925421924904998453 768429555508305459843605)
              ·
                refine ⟨36020135414451818430169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 768429555508305459843605 36020135414451818430169)
                ·
                  rfl

theorem cell22_947011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 6].length) (baseStart_947011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947011 prefixEnd_947011 := by exact prefixLift 947011
  have htrace : WordTrace (prefixWord ++ tailWord_947011) baseStart_947011 baseEnd_947011 := by
    simpa [prefixWord, tailWord_947011, baseEnd_947011] using wordTrace_append hprefix tailTrace_947011
  have hstable : (prefixWord ++ tailWord_947011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947011).length < 2 ^ (prefixWord ++ tailWord_947011).sum := by decide
  have hdescent : baseEnd_947011 < baseStart_947011 := by decide
  rcases family_descends (prefixWord ++ tailWord_947011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947043 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 3, 3]
def baseStart_947043 : Nat := 118140960795 + 947043 * 2 ^ 59
def prefixEnd_947043 : Nat := 4983230072969 + 3 ^ 40 * 947043 * 2
def baseEnd_947043 : Nat := 324192172984028949071423

theorem tailTrace_947043 : CollatzResearch.WordTrace tailWord_947043 prefixEnd_947043 324192172984028949071423 := by
  unfold tailWord_947043
  simp only [CollatzResearch.WordTrace]
  refine ⟨34541495908032427912565783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23027663938688285275043855 34541495908032427912565783)
  ·
    refine ⟨51812243862048641868848675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34541495908032427912565783 51812243862048641868848675)
    ·
      refine ⟨77718365793072962803273013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51812243862048641868848675 77718365793072962803273013)
      ·
        refine ⟨7286096793100590262806845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77718365793072962803273013 7286096793100590262806845)
        ·
          refine ⟨2732286297412721348552567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7286096793100590262806845 2732286297412721348552567)
          ·
            refine ⟨4098429446119082022828851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732286297412721348552567 4098429446119082022828851)
            ·
              refine ⟨6147644169178623034243277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098429446119082022828851 6147644169178623034243277)
              ·
                refine ⟨2305366563441983637841229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6147644169178623034243277 2305366563441983637841229)
                ·
                  refine ⟨864512461290743864190461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2305366563441983637841229 864512461290743864190461)
                  ·
                    refine ⟨324192172984028949071423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864512461290743864190461 324192172984028949071423)
                    ·
                      rfl

theorem cell22_947043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 3, 3].length) (baseStart_947043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947043 prefixEnd_947043 := by exact prefixLift 947043
  have htrace : WordTrace (prefixWord ++ tailWord_947043) baseStart_947043 baseEnd_947043 := by
    simpa [prefixWord, tailWord_947043, baseEnd_947043] using wordTrace_append hprefix tailTrace_947043
  have hstable : (prefixWord ++ tailWord_947043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947043).length < 2 ^ (prefixWord ++ tailWord_947043).sum := by decide
  have hdescent : baseEnd_947043 < baseStart_947043 := by decide
  rcases family_descends (prefixWord ++ tailWord_947043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947056 : List Nat := [2, 1, 1, 1, 4, 1, 2, 5, 5]
def baseStart_947056 : Nat := 118140960795 + 947056 * 2 ^ 59
def prefixEnd_947056 : Nat := 4983230072969 + 3 ^ 40 * 947056 * 2
def baseEnd_947056 : Nat := 108065541049900416165461

theorem tailTrace_947056 : CollatzResearch.WordTrace tailWord_947056 prefixEnd_947056 108065541049900416165461 := by
  unfold tailWord_947056
  simp only [CollatzResearch.WordTrace]
  refine ⟨17270985028492665566394511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23027980037990220755192681 17270985028492665566394511)
  ·
    refine ⟨25906477542738998349591767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17270985028492665566394511 25906477542738998349591767)
    ·
      refine ⟨38859716314108497524387651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25906477542738998349591767 38859716314108497524387651)
      ·
        refine ⟨58289574471162746286581477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38859716314108497524387651 58289574471162746286581477)
        ·
          refine ⟨10929295213343014928734027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58289574471162746286581477 10929295213343014928734027)
          ·
            refine ⟨16393942820014522393101041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929295213343014928734027 16393942820014522393101041)
            ·
              refine ⟨12295457115010891794825781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16393942820014522393101041 12295457115010891794825781)
              ·
                refine ⟨1152699104532271105764917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12295457115010891794825781 1152699104532271105764917)
                ·
                  refine ⟨108065541049900416165461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1152699104532271105764917 108065541049900416165461)
                  ·
                    rfl

theorem cell22_947056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_947056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947056 prefixEnd_947056 := by exact prefixLift 947056
  have htrace : WordTrace (prefixWord ++ tailWord_947056) baseStart_947056 baseEnd_947056 := by
    simpa [prefixWord, tailWord_947056, baseEnd_947056] using wordTrace_append hprefix tailTrace_947056
  have hstable : (prefixWord ++ tailWord_947056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947056).length < 2 ^ (prefixWord ++ tailWord_947056).sum := by decide
  have hdescent : baseEnd_947056 < baseStart_947056 := by decide
  rcases family_descends (prefixWord ++ tailWord_947056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947077 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 1, 3]
def baseStart_947077 : Nat := 118140960795 + 947077 * 2 ^ 59
def prefixEnd_947077 : Nat := 4983230072969 + 3 ^ 40 * 947077 * 2
def baseEnd_947077 : Nat := 324203811878864193721319

theorem tailTrace_947077 : CollatzResearch.WordTrace tailWord_947077 prefixEnd_947077 324203811878864193721319 := by
  unfold tailWord_947077
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542735989909251719303485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23028490659939501146202323 34542735989909251719303485)
  ·
    refine ⟨12953525996215969394738807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34542735989909251719303485 12953525996215969394738807)
    ·
      refine ⟨19430288994323954092108211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953525996215969394738807 19430288994323954092108211)
      ·
        refine ⟨29145433491485931138162317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19430288994323954092108211 29145433491485931138162317)
        ·
          refine ⟨10929537559307224176810869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29145433491485931138162317 10929537559307224176810869)
          ·
            refine ⟨1024644146185052266576019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10929537559307224176810869 1024644146185052266576019)
            ·
              refine ⟨1536966219277578399864029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024644146185052266576019 1536966219277578399864029)
              ·
                refine ⟨576362332229091899949011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1536966219277578399864029 576362332229091899949011)
                ·
                  refine ⟨864543498343637849923517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576362332229091899949011 864543498343637849923517)
                  ·
                    refine ⟨324203811878864193721319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864543498343637849923517 324203811878864193721319)
                    ·
                      rfl

theorem cell22_947077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_947077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947077 prefixEnd_947077 := by exact prefixLift 947077
  have htrace : WordTrace (prefixWord ++ tailWord_947077) baseStart_947077 baseEnd_947077 := by
    simpa [prefixWord, tailWord_947077, baseEnd_947077] using wordTrace_append hprefix tailTrace_947077
  have hstable : (prefixWord ++ tailWord_947077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947077).length < 2 ^ (prefixWord ++ tailWord_947077).sum := by decide
  have hdescent : baseEnd_947077 < baseStart_947077 := by decide
  rcases family_descends (prefixWord ++ tailWord_947077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947094 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_947094 : Nat := 118140960795 + 947094 * 2 ^ 59
def prefixEnd_947094 : Nat := 4983230072969 + 3 ^ 40 * 947094 * 2
def baseEnd_947094 : Nat := 324209631326281816046267

theorem tailTrace_947094 : CollatzResearch.WordTrace tailWord_947094 prefixEnd_947094 324209631326281816046267 := by
  unfold tailWord_947094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158959751927978976417021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23028904020565109081781557 2158959751927978976417021)
  ·
    refine ⟨809609906972992116156383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2158959751927978976417021 809609906972992116156383)
    ·
      refine ⟨1214414860459488174234575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809609906972992116156383 1214414860459488174234575)
      ·
        refine ⟨1821622290689232261351863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214414860459488174234575 1821622290689232261351863)
        ·
          refine ⟨2732433436033848392027795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1821622290689232261351863 2732433436033848392027795)
          ·
            refine ⟨4098650154050772588041693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732433436033848392027795 4098650154050772588041693)
            ·
              refine ⟨1536993807769039720515635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4098650154050772588041693 1536993807769039720515635)
              ·
                refine ⟨2305490711653559580773453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536993807769039720515635 2305490711653559580773453)
                ·
                  refine ⟨864559016870084842790045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2305490711653559580773453 864559016870084842790045)
                  ·
                    refine ⟨324209631326281816046267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864559016870084842790045 324209631326281816046267)
                    ·
                      rfl

theorem cell22_947094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_947094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947094 prefixEnd_947094 := by exact prefixLift 947094
  have htrace : WordTrace (prefixWord ++ tailWord_947094) baseStart_947094 baseEnd_947094 := by
    simpa [prefixWord, tailWord_947094, baseEnd_947094] using wordTrace_append hprefix tailTrace_947094
  have hstable : (prefixWord ++ tailWord_947094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947094).length < 2 ^ (prefixWord ++ tailWord_947094).sum := by decide
  have hdescent : baseEnd_947094 < baseStart_947094 := by decide
  rcases family_descends (prefixWord ++ tailWord_947094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947148 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_947148 : Nat := 118140960795 + 947148 * 2 ^ 59
def prefixEnd_947148 : Nat := 4983230072969 + 3 ^ 40 * 947148 * 2
def baseEnd_947148 : Nat := 324228116629843675196101

theorem tailTrace_947148 : CollatzResearch.WordTrace tailWord_947148 prefixEnd_947148 324228116629843675196101 := by
  unfold tailWord_947148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17272662786326015422569049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23030217048434687230092065 17272662786326015422569049)
  ·
    refine ⟨12954497089744511566926787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17272662786326015422569049 12954497089744511566926787)
    ·
      refine ⟨19431745634616767350390181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12954497089744511566926787 19431745634616767350390181)
      ·
        refine ⟨3643452306490643878198159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19431745634616767350390181 3643452306490643878198159)
        ·
          refine ⟨5465178459735965817297239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3643452306490643878198159 5465178459735965817297239)
          ·
            refine ⟨8197767689603948725945859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5465178459735965817297239 8197767689603948725945859)
            ·
              refine ⟨12296651534405923088918789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8197767689603948725945859 12296651534405923088918789)
              ·
                refine ⟨2305622162701110579172273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12296651534405923088918789 2305622162701110579172273)
                ·
                  refine ⟨1729216622025832934379205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2305622162701110579172273 1729216622025832934379205)
                  ·
                    refine ⟨324228116629843675196101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729216622025832934379205 324228116629843675196101)
                    ·
                      rfl

theorem cell22_947148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_947148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947148 prefixEnd_947148 := by exact prefixLift 947148
  have htrace : WordTrace (prefixWord ++ tailWord_947148) baseStart_947148 baseEnd_947148 := by
    simpa [prefixWord, tailWord_947148, baseEnd_947148] using wordTrace_append hprefix tailTrace_947148
  have hstable : (prefixWord ++ tailWord_947148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947148).length < 2 ^ (prefixWord ++ tailWord_947148).sum := by decide
  have hdescent : baseEnd_947148 < baseStart_947148 := by decide
  rcases family_descends (prefixWord ++ tailWord_947148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947150 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_947150 : Nat := 118140960795 + 947150 * 2 ^ 59
def prefixEnd_947150 : Nat := 4983230072969 + 3 ^ 40 * 947150 * 2
def baseEnd_947150 : Nat := 324228801270716336646095

theorem tailTrace_947150 : CollatzResearch.WordTrace tailWord_947150 prefixEnd_947150 324228801270716336646095 := by
  unfold tailWord_947150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318174814830598148338863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23030265679096523457807269 4318174814830598148338863)
  ·
    refine ⟨6477262222245897222508295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318174814830598148338863 6477262222245897222508295)
    ·
      refine ⟨9715893333368845833762443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6477262222245897222508295 9715893333368845833762443)
      ·
        refine ⟨14573840000053268750643665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9715893333368845833762443 14573840000053268750643665)
        ·
          refine ⟨10930380000039951562982749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14573840000053268750643665 10930380000039951562982749)
          ·
            refine ⟨4098892500014981836118531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10930380000039951562982749 4098892500014981836118531)
            ·
              refine ⟨6148338750022472754177797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098892500014981836118531 6148338750022472754177797)
              ·
                refine ⟨1152813515629213641408337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6148338750022472754177797 1152813515629213641408337)
                ·
                  refine ⟨864610136721910231056253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1152813515629213641408337 864610136721910231056253)
                  ·
                    refine ⟨324228801270716336646095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864610136721910231056253 324228801270716336646095)
                    ·
                      rfl

theorem cell22_947150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_947150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947150 prefixEnd_947150 := by exact prefixLift 947150
  have htrace : WordTrace (prefixWord ++ tailWord_947150) baseStart_947150 baseEnd_947150 := by
    simpa [prefixWord, tailWord_947150, baseEnd_947150] using wordTrace_append hprefix tailTrace_947150
  have hstable : (prefixWord ++ tailWord_947150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947150).length < 2 ^ (prefixWord ++ tailWord_947150).sum := by decide
  have hdescent : baseEnd_947150 < baseStart_947150 := by decide
  rcases family_descends (prefixWord ++ tailWord_947150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947182 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 2, 4]
def baseStart_947182 : Nat := 118140960795 + 947182 * 2 ^ 59
def prefixEnd_947182 : Nat := 4983230072969 + 3 ^ 40 * 947182 * 2
def baseEnd_947182 : Nat := 324239755524678919845997

theorem tailTrace_947182 : CollatzResearch.WordTrace tailWord_947182 prefixEnd_947182 324239755524678919845997 := by
  unfold tailWord_947182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318320706816106831484475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23031043769685903101250533 4318320706816106831484475)
  ·
    refine ⟨6477481060224160247226713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4318320706816106831484475 6477481060224160247226713)
    ·
      refine ⟨4858110795168120185420035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6477481060224160247226713 4858110795168120185420035)
      ·
        refine ⟨7287166192752180278130053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4858110795168120185420035 7287166192752180278130053)
        ·
          refine ⟨1366343661141033802149385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7287166192752180278130053 1366343661141033802149385)
          ·
            refine ⟨1024757745855775351612039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1366343661141033802149385 1024757745855775351612039)
            ·
              refine ⟨1537136618783663027418059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024757745855775351612039 1537136618783663027418059)
              ·
                refine ⟨2305704928175494541127089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537136618783663027418059 2305704928175494541127089)
                ·
                  refine ⟨1729278696131620905845317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2305704928175494541127089 1729278696131620905845317)
                  ·
                    refine ⟨324239755524678919845997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729278696131620905845317 324239755524678919845997)
                    ·
                      rfl

theorem cell22_947182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_947182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947182 prefixEnd_947182 := by exact prefixLift 947182
  have htrace : WordTrace (prefixWord ++ tailWord_947182) baseStart_947182 baseEnd_947182 := by
    simpa [prefixWord, tailWord_947182, baseEnd_947182] using wordTrace_append hprefix tailTrace_947182
  have hstable : (prefixWord ++ tailWord_947182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947182).length < 2 ^ (prefixWord ++ tailWord_947182).sum := by decide
  have hdescent : baseEnd_947182 < baseStart_947182 := by decide
  rcases family_descends (prefixWord ++ tailWord_947182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947208 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_947208 : Nat := 118140960795 + 947208 * 2 ^ 59
def prefixEnd_947208 : Nat := 4983230072969 + 3 ^ 40 * 947208 * 2
def baseEnd_947208 : Nat := 108082885285341172898639

theorem tailTrace_947208 : CollatzResearch.WordTrace tailWord_947208 prefixEnd_947208 108082885285341172898639 := by
  unfold tailWord_947208
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273756976217330546161139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23031675968289774061548185 17273756976217330546161139)
  ·
    refine ⟨25910635464325995819241709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17273756976217330546161139 25910635464325995819241709)
    ·
      refine ⟨9716488299122248432215641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25910635464325995819241709 9716488299122248432215641)
      ·
        refine ⟨7287366224341686324161731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9716488299122248432215641 7287366224341686324161731)
        ·
          refine ⟨10931049336512529486242597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7287366224341686324161731 10931049336512529486242597)
          ·
            refine ⟨2049571750596099278670487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10931049336512529486242597 2049571750596099278670487)
            ·
              refine ⟨3074357625894148918005731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049571750596099278670487 3074357625894148918005731)
              ·
                refine ⟨4611536438841223377008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074357625894148918005731 4611536438841223377008597)
                ·
                  refine ⟨108082885285341172898639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4611536438841223377008597 108082885285341172898639)
                  ·
                    rfl

theorem cell22_947208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_947208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947208 prefixEnd_947208 := by exact prefixLift 947208
  have htrace : WordTrace (prefixWord ++ tailWord_947208) baseStart_947208 baseEnd_947208 := by
    simpa [prefixWord, tailWord_947208, baseEnd_947208] using wordTrace_append hprefix tailTrace_947208
  have hstable : (prefixWord ++ tailWord_947208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947208).length < 2 ^ (prefixWord ++ tailWord_947208).sum := by decide
  have hdescent : baseEnd_947208 < baseStart_947208 := by decide
  rcases family_descends (prefixWord ++ tailWord_947208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947212 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 1, 3]
def baseStart_947212 : Nat := 118140960795 + 947212 * 2 ^ 59
def prefixEnd_947212 : Nat := 4983230072969 + 3 ^ 40 * 947212 * 2
def baseEnd_947212 : Nat := 324250025137768841595905

theorem tailTrace_947212 : CollatzResearch.WordTrace tailWord_947212 prefixEnd_947212 324250025137768841595905 := by
  unfold tailWord_947212
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273829922210084887733945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23031773229613446516978593 17273829922210084887733945)
  ·
    refine ⟨12955372441657563665800459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17273829922210084887733945 12955372441657563665800459)
    ·
      refine ⟨19433058662486345498700689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12955372441657563665800459 19433058662486345498700689)
      ·
        refine ⟨14574793996864759124025517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19433058662486345498700689 14574793996864759124025517)
        ·
          refine ⟨5465547748824284671509569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14574793996864759124025517 5465547748824284671509569)
          ·
            refine ⟨4099160811618213503632177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5465547748824284671509569 4099160811618213503632177)
            ·
              refine ⟨3074370608713660127724133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099160811618213503632177 3074370608713660127724133)
              ·
                refine ⟨576444489133811273948275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3074370608713660127724133 576444489133811273948275)
                ·
                  refine ⟨864666733700716910922413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576444489133811273948275 864666733700716910922413)
                  ·
                    refine ⟨324250025137768841595905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864666733700716910922413 324250025137768841595905)
                    ·
                      rfl

theorem cell22_947212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_947212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947212 prefixEnd_947212 := by exact prefixLift 947212
  have htrace : WordTrace (prefixWord ++ tailWord_947212) baseStart_947212 baseEnd_947212 := by
    simpa [prefixWord, tailWord_947212, baseEnd_947212] using wordTrace_append hprefix tailTrace_947212
  have hstable : (prefixWord ++ tailWord_947212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947212).length < 2 ^ (prefixWord ++ tailWord_947212).sum := by decide
  have hdescent : baseEnd_947212 < baseStart_947212 := by decide
  rcases family_descends (prefixWord ++ tailWord_947212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947218 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_947218 : Nat := 118140960795 + 947218 * 2 ^ 59
def prefixEnd_947218 : Nat := 4983230072969 + 3 ^ 40 * 947218 * 2
def baseEnd_947218 : Nat := 324252079060386825945887

theorem tailTrace_947218 : CollatzResearch.WordTrace tailWord_947218 prefixEnd_947218 324252079060386825945887 := by
  unfold tailWord_947218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8636969670599608200046577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23031919121598955200124205 8636969670599608200046577)
  ·
    refine ⟨6477727252949706150034933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8636969670599608200046577 6477727252949706150034933)
    ·
      refine ⟨607286929964034951565775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6477727252949706150034933 607286929964034951565775)
      ·
        refine ⟨910930394946052427348663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607286929964034951565775 910930394946052427348663)
        ·
          refine ⟨1366395592419078641022995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910930394946052427348663 1366395592419078641022995)
          ·
            refine ⟨2049593388628617961534493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366395592419078641022995 2049593388628617961534493)
            ·
              refine ⟨768597520735731735575435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2049593388628617961534493 768597520735731735575435)
              ·
                refine ⟨1152896281103597603363153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 768597520735731735575435 1152896281103597603363153)
                ·
                  refine ⟨864672210827698202522365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1152896281103597603363153 864672210827698202522365)
                  ·
                    refine ⟨324252079060386825945887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864672210827698202522365 324252079060386825945887)
                    ·
                      rfl

theorem cell22_947218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_947218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947218 prefixEnd_947218 := by exact prefixLift 947218
  have htrace : WordTrace (prefixWord ++ tailWord_947218) baseStart_947218 baseEnd_947218 := by
    simpa [prefixWord, tailWord_947218, baseEnd_947218] using wordTrace_append hprefix tailTrace_947218
  have hstable : (prefixWord ++ tailWord_947218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947218).length < 2 ^ (prefixWord ++ tailWord_947218).sum := by decide
  have hdescent : baseEnd_947218 < baseStart_947218 := by decide
  rcases family_descends (prefixWord ++ tailWord_947218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947321 : List Nat := [1, 2, 1, 3, 6, 1, 2, 2, 4]
def baseStart_947321 : Nat := 118140960795 + 947321 * 2 ^ 59
def prefixEnd_947321 : Nat := 4983230072969 + 3 ^ 40 * 947321 * 2
def baseEnd_947321 : Nat := 108095779355109630206857

theorem tailTrace_947321 : CollatzResearch.WordTrace tailWord_947321 prefixEnd_947321 108095779355109630206857 := by
  unfold tailWord_947321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34551635401025281391185817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23034423600683520927457211 34551635401025281391185817)
  ·
    refine ⟨25913726550768961043389363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34551635401025281391185817 25913726550768961043389363)
    ·
      refine ⟨38870589826153441565084045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25913726550768961043389363 38870589826153441565084045)
      ·
        refine ⟨14576471184807540586906517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38870589826153441565084045 14576471184807540586906517)
        ·
          refine ⟨683272086787853465011243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14576471184807540586906517 683272086787853465011243)
          ·
            refine ⟨1024908130181780197516865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683272086787853465011243 1024908130181780197516865)
            ·
              refine ⟨768681097636335148137649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1024908130181780197516865 768681097636335148137649)
              ·
                refine ⟨576510823227251361103237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768681097636335148137649 576510823227251361103237)
                ·
                  refine ⟨108095779355109630206857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576510823227251361103237 108095779355109630206857)
                  ·
                    rfl

theorem cell22_947321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_947321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947321 prefixEnd_947321 := by exact prefixLift 947321
  have htrace : WordTrace (prefixWord ++ tailWord_947321) baseStart_947321 baseEnd_947321 := by
    simpa [prefixWord, tailWord_947321, baseEnd_947321] using wordTrace_append hprefix tailTrace_947321
  have hstable : (prefixWord ++ tailWord_947321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947321).length < 2 ^ (prefixWord ++ tailWord_947321).sum := by decide
  have hdescent : baseEnd_947321 < baseStart_947321 := by decide
  rcases family_descends (prefixWord ++ tailWord_947321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947328 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_947328 : Nat := 118140960795 + 947328 * 2 ^ 59
def prefixEnd_947328 : Nat := 4983230072969 + 3 ^ 40 * 947328 * 2
def baseEnd_947328 : Nat := 324289734308383205695549

theorem tailTrace_947328 : CollatzResearch.WordTrace tailWord_947328 prefixEnd_947328 324289734308383205695549 := by
  unfold tailWord_947328
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275945355999960793345319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23034593807999947724460425 17275945355999960793345319)
  ·
    refine ⟨25913918033999941190017979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275945355999960793345319 25913918033999941190017979)
    ·
      refine ⟨38870877050999911785026969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25913918033999941190017979 38870877050999911785026969)
      ·
        refine ⟨29153157788249933838770227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38870877050999911785026969 29153157788249933838770227)
        ·
          refine ⟨43729736682374900758155341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29153157788249933838770227 43729736682374900758155341)
          ·
            refine ⟨16398651255890587784308253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43729736682374900758155341 16398651255890587784308253)
            ·
              refine ⟨6149494220958970419115595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16398651255890587784308253 6149494220958970419115595)
              ·
                refine ⟨9224241331438455628673393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6149494220958970419115595 9224241331438455628673393)
                ·
                  refine ⟨6918180998578841721505045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9224241331438455628673393 6918180998578841721505045)
                  ·
                    refine ⟨324289734308383205695549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6918180998578841721505045 324289734308383205695549)
                    ·
                      rfl

theorem cell22_947328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_947328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947328 prefixEnd_947328 := by exact prefixLift 947328
  have htrace : WordTrace (prefixWord ++ tailWord_947328) baseStart_947328 baseEnd_947328 := by
    simpa [prefixWord, tailWord_947328, baseEnd_947328] using wordTrace_append hprefix tailTrace_947328
  have hstable : (prefixWord ++ tailWord_947328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947328).length < 2 ^ (prefixWord ++ tailWord_947328).sum := by decide
  have hdescent : baseEnd_947328 < baseStart_947328 := by decide
  rcases family_descends (prefixWord ++ tailWord_947328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947364 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_947364 : Nat := 118140960795 + 947364 * 2 ^ 59
def prefixEnd_947364 : Nat := 4983230072969 + 3 ^ 40 * 947364 * 2
def baseEnd_947364 : Nat := 324302057844091111795439

theorem tailTrace_947364 : CollatzResearch.WordTrace tailWord_947364 prefixEnd_947364 324302057844091111795439 := by
  unfold tailWord_947364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17276601869934749867500573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23035469159912999823334097 17276601869934749867500573)
  ·
    refine ⟨6478725701225531200312715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17276601869934749867500573 6478725701225531200312715)
    ·
      refine ⟨9718088551838296800469073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478725701225531200312715 9718088551838296800469073)
      ·
        refine ⟨7288566413878722600351805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9718088551838296800469073 7288566413878722600351805)
        ·
          refine ⟨2733212405204520975131927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7288566413878722600351805 2733212405204520975131927)
          ·
            refine ⟨4099818607806781462697891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733212405204520975131927 4099818607806781462697891)
            ·
              refine ⟨6149727911710172194046837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4099818607806781462697891 6149727911710172194046837)
              ·
                refine ⟨576536991722828643191891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6149727911710172194046837 576536991722828643191891)
                ·
                  refine ⟨864805487584242964787837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576536991722828643191891 864805487584242964787837)
                  ·
                    refine ⟨324302057844091111795439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 864805487584242964787837 324302057844091111795439)
                    ·
                      rfl

theorem cell22_947364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_947364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947364 prefixEnd_947364 := by exact prefixLift 947364
  have htrace : WordTrace (prefixWord ++ tailWord_947364) baseStart_947364 baseEnd_947364 := by
    simpa [prefixWord, tailWord_947364, baseEnd_947364] using wordTrace_append hprefix tailTrace_947364
  have hstable : (prefixWord ++ tailWord_947364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947364).length < 2 ^ (prefixWord ++ tailWord_947364).sum := by decide
  have hdescent : baseEnd_947364 < baseStart_947364 := by decide
  rcases family_descends (prefixWord ++ tailWord_947364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947377 : List Nat := [1, 2, 2, 5, 1, 1, 3, 2, 5]
def baseStart_947377 : Nat := 118140960795 + 947377 * 2 ^ 59
def prefixEnd_947377 : Nat := 4983230072969 + 3 ^ 40 * 947377 * 2
def baseEnd_947377 : Nat := 108102169336587803740133

theorem tailTrace_947377 : CollatzResearch.WordTrace tailWord_947377 prefixEnd_947377 108102169336587803740133 := by
  unfold tailWord_947377
  simp only [CollatzResearch.WordTrace]
  refine ⟨34553677888822402955224385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23035785259214935303482923 34553677888822402955224385)
  ·
    refine ⟨25915258416616802216418289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34553677888822402955224385 25915258416616802216418289)
    ·
      refine ⟨19436443812462601662313717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25915258416616802216418289 19436443812462601662313717)
      ·
        refine ⟨1822166607418368905841911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19436443812462601662313717 1822166607418368905841911)
        ·
          refine ⟨2733249911127553358762867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822166607418368905841911 2733249911127553358762867)
          ·
            refine ⟨4099874866691330038144301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733249911127553358762867 4099874866691330038144301)
            ·
              refine ⟨1537453075009248764304113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4099874866691330038144301 1537453075009248764304113)
              ·
                refine ⟨1153089806256936573228085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537453075009248764304113 1153089806256936573228085)
                ·
                  refine ⟨108102169336587803740133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1153089806256936573228085 108102169336587803740133)
                  ·
                    rfl

theorem cell22_947377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 5].length) (baseStart_947377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947377 prefixEnd_947377 := by exact prefixLift 947377
  have htrace : WordTrace (prefixWord ++ tailWord_947377) baseStart_947377 baseEnd_947377 := by
    simpa [prefixWord, tailWord_947377, baseEnd_947377] using wordTrace_append hprefix tailTrace_947377
  have hstable : (prefixWord ++ tailWord_947377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947377).length < 2 ^ (prefixWord ++ tailWord_947377).sum := by decide
  have hdescent : baseEnd_947377 < baseStart_947377 := by decide
  rcases family_descends (prefixWord ++ tailWord_947377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947435 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 4, 4]
def baseStart_947435 : Nat := 118140960795 + 947435 * 2 ^ 59
def prefixEnd_947435 : Nat := 4983230072969 + 3 ^ 40 * 947435 * 2
def baseEnd_947435 : Nat := 324326362595070593270221

theorem tailTrace_947435 : CollatzResearch.WordTrace tailWord_947435 prefixEnd_947435 324326362595070593270221 := by
  unfold tailWord_947435
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555793322612278860835759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23037195548408185907223839 34555793322612278860835759)
  ·
    refine ⟨51833689983918418291253639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34555793322612278860835759 51833689983918418291253639)
    ·
      refine ⟨77750534975877627436880459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51833689983918418291253639 77750534975877627436880459)
      ·
        refine ⟨116625802463816441155320689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77750534975877627436880459 116625802463816441155320689)
        ·
          refine ⟨87469351847862330866490517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116625802463816441155320689 87469351847862330866490517)
          ·
            refine ⟨4100125867868546759366743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87469351847862330866490517 4100125867868546759366743)
            ·
              refine ⟨6150188801802820139050115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100125867868546759366743 6150188801802820139050115)
              ·
                refine ⟨9225283202704230208575173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150188801802820139050115 9225283202704230208575173)
                ·
                  refine ⟨1729740600507043164107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9225283202704230208575173 1729740600507043164107845)
                  ·
                    refine ⟨324326362595070593270221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729740600507043164107845 324326362595070593270221)
                    ·
                      rfl

theorem cell22_947435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 4].length) (baseStart_947435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947435 prefixEnd_947435 := by exact prefixLift 947435
  have htrace : WordTrace (prefixWord ++ tailWord_947435) baseStart_947435 baseEnd_947435 := by
    simpa [prefixWord, tailWord_947435, baseEnd_947435] using wordTrace_append hprefix tailTrace_947435
  have hstable : (prefixWord ++ tailWord_947435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947435).length < 2 ^ (prefixWord ++ tailWord_947435).sum := by decide
  have hdescent : baseEnd_947435 < baseStart_947435 := by decide
  rcases family_descends (prefixWord ++ tailWord_947435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947439 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 6]
def baseStart_947439 : Nat := 118140960795 + 947439 * 2 ^ 59
def prefixEnd_947439 : Nat := 4983230072969 + 3 ^ 40 * 947439 * 2
def baseEnd_947439 : Nat := 108109243958938638723403

theorem tailTrace_947439 : CollatzResearch.WordTrace tailWord_947439 prefixEnd_947439 108109243958938638723403 := by
  unfold tailWord_947439
  simp only [CollatzResearch.WordTrace]
  refine ⟨34555939214597787543981371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23037292809731858362654247 34555939214597787543981371)
  ·
    refine ⟨51833908821896681315972057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34555939214597787543981371 51833908821896681315972057)
    ·
      refine ⟨38875431616422510986979043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51833908821896681315972057 38875431616422510986979043)
      ·
        refine ⟨58313147424633766480468565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38875431616422510986979043 58313147424633766480468565)
        ·
          refine ⟨683357196382426950942991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 58313147424633766480468565 683357196382426950942991)
          ·
            refine ⟨1025035794573640426414487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683357196382426950942991 1025035794573640426414487)
            ·
              refine ⟨1537553691860460639621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025035794573640426414487 1537553691860460639621731)
              ·
                refine ⟨2306330537790690959432597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537553691860460639621731 2306330537790690959432597)
                ·
                  refine ⟨108109243958938638723403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2306330537790690959432597 108109243958938638723403)
                  ·
                    rfl

theorem cell22_947439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 6].length) (baseStart_947439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947439 prefixEnd_947439 := by exact prefixLift 947439
  have htrace : WordTrace (prefixWord ++ tailWord_947439) baseStart_947439 baseEnd_947439 := by
    simpa [prefixWord, tailWord_947439, baseEnd_947439] using wordTrace_append hprefix tailTrace_947439
  have hstable : (prefixWord ++ tailWord_947439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947439).length < 2 ^ (prefixWord ++ tailWord_947439).sum := by decide
  have hdescent : baseEnd_947439 < baseStart_947439 := by decide
  rcases family_descends (prefixWord ++ tailWord_947439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947450 : List Nat := [3, 1, 1, 1, 1, 4, 4, 7]
def baseStart_947450 : Nat := 118140960795 + 947450 * 2 ^ 59
def prefixEnd_947450 : Nat := 4983230072969 + 3 ^ 40 * 947450 * 2
def baseEnd_947450 : Nat := 36036833044623950460575

theorem tailTrace_947450 : CollatzResearch.WordTrace tailWord_947450 prefixEnd_947450 36036833044623950460575 := by
  unfold tailWord_947450
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639085104389484105657951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23037560278371957615087869 8639085104389484105657951)
  ·
    refine ⟨12958627656584226158486927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8639085104389484105657951 12958627656584226158486927)
    ·
      refine ⟨19437941484876339237730391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958627656584226158486927 19437941484876339237730391)
      ·
        refine ⟨29156912227314508856595587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19437941484876339237730391 29156912227314508856595587)
        ·
          refine ⟨43735368340971763284893381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29156912227314508856595587 43735368340971763284893381)
          ·
            refine ⟨8200381563932205615917509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43735368340971763284893381 8200381563932205615917509)
            ·
              refine ⟨1537571543237288552984533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8200381563932205615917509 1537571543237288552984533)
              ·
                refine ⟨36036833044623950460575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1537571543237288552984533 36036833044623950460575)
                ·
                  rfl

theorem cell22_947450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_947450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947450 prefixEnd_947450 := by exact prefixLift 947450
  have htrace : WordTrace (prefixWord ++ tailWord_947450) baseStart_947450 baseEnd_947450 := by
    simpa [prefixWord, tailWord_947450, baseEnd_947450] using wordTrace_append hprefix tailTrace_947450
  have hstable : (prefixWord ++ tailWord_947450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947450).length < 2 ^ (prefixWord ++ tailWord_947450).sum := by decide
  have hdescent : baseEnd_947450 < baseStart_947450 := by decide
  rcases family_descends (prefixWord ++ tailWord_947450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947458 : List Nat := [3, 4, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_947458 : Nat := 118140960795 + 947458 * 2 ^ 59
def prefixEnd_947458 : Nat := 4983230072969 + 3 ^ 40 * 947458 * 2
def baseEnd_947458 : Nat := 324334235965106199945151

theorem tailTrace_947458 : CollatzResearch.WordTrace tailWord_947458 prefixEnd_947458 324334235965106199945151 := by
  unfold tailWord_947458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639158050382238447230757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23037754801019302525948685 8639158050382238447230757)
  ·
    refine ⟨1619842134446669708855767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8639158050382238447230757 1619842134446669708855767)
    ·
      refine ⟨2429763201670004563283651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619842134446669708855767 2429763201670004563283651)
      ·
        refine ⟨3644644802505006844925477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429763201670004563283651 3644644802505006844925477)
        ·
          refine ⟨683370900469688783423527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3644644802505006844925477 683370900469688783423527)
          ·
            refine ⟨1025056350704533175135291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683370900469688783423527 1025056350704533175135291)
            ·
              refine ⟨1537584526056799762702937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025056350704533175135291 1537584526056799762702937)
              ·
                refine ⟨1153188394542599822027203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537584526056799762702937 1153188394542599822027203)
                ·
                  refine ⟨1729782591813899733040805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153188394542599822027203 1729782591813899733040805)
                  ·
                    refine ⟨324334235965106199945151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729782591813899733040805 324334235965106199945151)
                    ·
                      rfl

theorem cell22_947458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_947458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947458 prefixEnd_947458 := by exact prefixLift 947458
  have htrace : WordTrace (prefixWord ++ tailWord_947458) baseStart_947458 baseEnd_947458 := by
    simpa [prefixWord, tailWord_947458, baseEnd_947458] using wordTrace_append hprefix tailTrace_947458
  have hstable : (prefixWord ++ tailWord_947458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947458).length < 2 ^ (prefixWord ++ tailWord_947458).sum := by decide
  have hdescent : baseEnd_947458 < baseStart_947458 := by decide
  rcases family_descends (prefixWord ++ tailWord_947458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947557 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 6]
def baseStart_947557 : Nat := 118140960795 + 947557 * 2 ^ 59
def prefixEnd_947557 : Nat := 4983230072969 + 3 ^ 40 * 947557 * 2
def baseEnd_947557 : Nat := 108122708562767647239949

theorem tailTrace_947557 : CollatzResearch.WordTrace tailWord_947557 prefixEnd_947557 108122708562767647239949 := by
  unfold tailWord_947557
  simp only [CollatzResearch.WordTrace]
  refine ⟨34560243028170293696776925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23040162018780195797851283 34560243028170293696776925)
  ·
    refine ⟨12960091135563860136291347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34560243028170293696776925 12960091135563860136291347)
    ·
      refine ⟨19440136703345790204437021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12960091135563860136291347 19440136703345790204437021)
      ·
        refine ⟨7290051263754671326663883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19440136703345790204437021 7290051263754671326663883)
        ·
          refine ⟨10935076895632006989995825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7290051263754671326663883 10935076895632006989995825)
          ·
            refine ⟨8201307671724005242496869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10935076895632006989995825 8201307671724005242496869)
            ·
              refine ⟨1537745188448250982968163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8201307671724005242496869 1537745188448250982968163)
              ·
                refine ⟨2306617782672376474452245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537745188448250982968163 2306617782672376474452245)
                ·
                  refine ⟨108122708562767647239949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2306617782672376474452245 108122708562767647239949)
                  ·
                    rfl

theorem cell22_947557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 6].length) (baseStart_947557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947557 prefixEnd_947557 := by exact prefixLift 947557
  have htrace : WordTrace (prefixWord ++ tailWord_947557) baseStart_947557 baseEnd_947557 := by
    simpa [prefixWord, tailWord_947557, baseEnd_947557] using wordTrace_append hprefix tailTrace_947557
  have hstable : (prefixWord ++ tailWord_947557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947557).length < 2 ^ (prefixWord ++ tailWord_947557).sum := by decide
  have hdescent : baseEnd_947557 < baseStart_947557 := by decide
  rcases family_descends (prefixWord ++ tailWord_947557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947587 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 6]
def baseStart_947587 : Nat := 118140960795 + 947587 * 2 ^ 59
def prefixEnd_947587 : Nat := 4983230072969 + 3 ^ 40 * 947587 * 2
def baseEnd_947587 : Nat := 324378395301392863469755

theorem tailTrace_947587 : CollatzResearch.WordTrace tailWord_947587 prefixEnd_947587 324378395301392863469755 := by
  unfold tailWord_947587
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561337218061608820369015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23040891478707739213579343 34561337218061608820369015)
  ·
    refine ⟨51842005827092413230553523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34561337218061608820369015 51842005827092413230553523)
    ·
      refine ⟨77763008740638619845830285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51842005827092413230553523 77763008740638619845830285)
      ·
        refine ⟨29161128277739482442186357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77763008740638619845830285 29161128277739482442186357)
        ·
          refine ⟨2733855776038076478954971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29161128277739482442186357 2733855776038076478954971)
          ·
            refine ⟨4100783664057114718432457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733855776038076478954971 4100783664057114718432457)
            ·
              refine ⟨3075587748042836038824343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4100783664057114718432457 3075587748042836038824343)
              ·
                refine ⟨4613381622064254058236515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3075587748042836038824343 4613381622064254058236515)
                ·
                  refine ⟨6920072433096381087354773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613381622064254058236515 6920072433096381087354773)
                  ·
                    refine ⟨324378395301392863469755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6920072433096381087354773 324378395301392863469755)
                    ·
                      rfl

theorem cell22_947587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 6].length) (baseStart_947587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947587 prefixEnd_947587 := by exact prefixLift 947587
  have htrace : WordTrace (prefixWord ++ tailWord_947587) baseStart_947587 baseEnd_947587 := by
    simpa [prefixWord, tailWord_947587, baseEnd_947587] using wordTrace_append hprefix tailTrace_947587
  have hstable : (prefixWord ++ tailWord_947587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947587).length < 2 ^ (prefixWord ++ tailWord_947587).sum := by decide
  have hdescent : baseEnd_947587 < baseStart_947587 := by decide
  rcases family_descends (prefixWord ++ tailWord_947587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947591 : List Nat := [1, 1, 4, 2, 2, 4, 1, 3, 4]
def baseStart_947591 : Nat := 118140960795 + 947591 * 2 ^ 59
def prefixEnd_947591 : Nat := 4983230072969 + 3 ^ 40 * 947591 * 2
def baseEnd_947591 : Nat := 108126588194379395456581

theorem tailTrace_947591 : CollatzResearch.WordTrace tailWord_947591 prefixEnd_947591 108126588194379395456581 := by
  unfold tailWord_947591
  simp only [CollatzResearch.WordTrace]
  refine ⟨34561483110047117503514627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23040988740031411669009751 34561483110047117503514627)
  ·
    refine ⟨51842224665070676255271941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34561483110047117503514627 51842224665070676255271941)
    ·
      refine ⟨9720417124700751797863489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51842224665070676255271941 9720417124700751797863489)
      ·
        refine ⟨7290312843525563848397617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9720417124700751797863489 7290312843525563848397617)
        ·
          refine ⟨5467734632644172886298213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7290312843525563848397617 5467734632644172886298213)
          ·
            refine ⟨1025200243620782416180915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5467734632644172886298213 1025200243620782416180915)
            ·
              refine ⟨1537800365431173624271373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025200243620782416180915 1537800365431173624271373)
              ·
                refine ⟨576675137036690109101765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1537800365431173624271373 576675137036690109101765)
                ·
                  refine ⟨108126588194379395456581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576675137036690109101765 108126588194379395456581)
                  ·
                    rfl

theorem cell22_947591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 3, 4].length) (baseStart_947591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947591 prefixEnd_947591 := by exact prefixLift 947591
  have htrace : WordTrace (prefixWord ++ tailWord_947591) baseStart_947591 baseEnd_947591 := by
    simpa [prefixWord, tailWord_947591, baseEnd_947591] using wordTrace_append hprefix tailTrace_947591
  have hstable : (prefixWord ++ tailWord_947591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947591).length < 2 ^ (prefixWord ++ tailWord_947591).sum := by decide
  have hdescent : baseEnd_947591 < baseStart_947591 := by decide
  rcases family_descends (prefixWord ++ tailWord_947591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947604 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_947604 : Nat := 118140960795 + 947604 * 2 ^ 59
def prefixEnd_947604 : Nat := 4983230072969 + 3 ^ 40 * 947604 * 2
def baseEnd_947604 : Nat := 324384214748810485794703

theorem tailTrace_947604 : CollatzResearch.WordTrace tailWord_947604 prefixEnd_947604 324384214748810485794703 := by
  unfold tailWord_947604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17280978629500010361868933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23041304839333347149158577 17280978629500010361868933)
  ·
    refine ⟨3240183493031251942850425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17280978629500010361868933 3240183493031251942850425)
    ·
      refine ⟨2430137619773438957137819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3240183493031251942850425 2430137619773438957137819)
      ·
        refine ⟨3645206429660158435706729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430137619773438957137819 3645206429660158435706729)
        ·
          refine ⟨2733904822245118826780047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645206429660158435706729 2733904822245118826780047)
          ·
            refine ⟨4100857233367678240170071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733904822245118826780047 4100857233367678240170071)
            ·
              refine ⟨6151285850051517360255107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100857233367678240170071 6151285850051517360255107)
              ·
                refine ⟨9226928775077276040382661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151285850051517360255107 9226928775077276040382661)
                ·
                  refine ⟨1730049145326989257571749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9226928775077276040382661 1730049145326989257571749)
                  ·
                    refine ⟨324384214748810485794703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730049145326989257571749 324384214748810485794703)
                    ·
                      rfl

theorem cell22_947604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_947604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947604 prefixEnd_947604 := by exact prefixLift 947604
  have htrace : WordTrace (prefixWord ++ tailWord_947604) baseStart_947604 baseEnd_947604 := by
    simpa [prefixWord, tailWord_947604, baseEnd_947604] using wordTrace_append hprefix tailTrace_947604
  have hstable : (prefixWord ++ tailWord_947604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947604).length < 2 ^ (prefixWord ++ tailWord_947604).sum := by decide
  have hdescent : baseEnd_947604 < baseStart_947604 := by decide
  rcases family_descends (prefixWord ++ tailWord_947604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947608 : List Nat := [2, 1, 2, 5, 2, 1, 3, 2, 4]
def baseStart_947608 : Nat := 118140960795 + 947608 * 2 ^ 59
def prefixEnd_947608 : Nat := 4983230072969 + 3 ^ 40 * 947608 * 2
def baseEnd_947608 : Nat := 108128528010185269564897

theorem tailTrace_947608 : CollatzResearch.WordTrace tailWord_947608 prefixEnd_947608 108128528010185269564897 := by
  unfold tailWord_947608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281051575492764703441739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23041402100657019604588985 17281051575492764703441739)
  ·
    refine ⟨25921577363239147055162609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17281051575492764703441739 25921577363239147055162609)
    ·
      refine ⟨19441183022429360291371957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25921577363239147055162609 19441183022429360291371957)
      ·
        refine ⟨1822610908352752527316121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19441183022429360291371957 1822610908352752527316121)
        ·
          refine ⟨1366958181264564395487091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1822610908352752527316121 1366958181264564395487091)
          ·
            refine ⟨2050437271896846593230637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366958181264564395487091 2050437271896846593230637)
            ·
              refine ⟨768913976961317472461489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2050437271896846593230637 768913976961317472461489)
              ·
                refine ⟨576685482720988104346117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 768913976961317472461489 576685482720988104346117)
                ·
                  refine ⟨108128528010185269564897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 576685482720988104346117 108128528010185269564897)
                  ·
                    rfl

theorem cell22_947608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 4].length) (baseStart_947608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947608 prefixEnd_947608 := by exact prefixLift 947608
  have htrace : WordTrace (prefixWord ++ tailWord_947608) baseStart_947608 baseEnd_947608 := by
    simpa [prefixWord, tailWord_947608, baseEnd_947608] using wordTrace_append hprefix tailTrace_947608
  have hstable : (prefixWord ++ tailWord_947608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947608).length < 2 ^ (prefixWord ++ tailWord_947608).sum := by decide
  have hdescent : baseEnd_947608 < baseStart_947608 := by decide
  rcases family_descends (prefixWord ++ tailWord_947608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947694 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_947694 : Nat := 118140960795 + 947694 * 2 ^ 59
def prefixEnd_947694 : Nat := 4983230072969 + 3 ^ 40 * 947694 * 2
def baseEnd_947694 : Nat := 324415023588080251044427

theorem tailTrace_947694 : CollatzResearch.WordTrace tailWord_947694 prefixEnd_947694 324415023588080251044427 := by
  unfold tailWord_947694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320654978584245761814267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23043493219115977396342757 4320654978584245761814267)
  ·
    refine ⟨6480982467876368642721401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4320654978584245761814267 6480982467876368642721401)
    ·
      refine ⟨4860736850907276482041051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6480982467876368642721401 4860736850907276482041051)
      ·
        refine ⟨7291105276360914723061577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860736850907276482041051 7291105276360914723061577)
        ·
          refine ⟨5468328957270686042296183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7291105276360914723061577 5468328957270686042296183)
          ·
            refine ⟨8202493435906029063444275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468328957270686042296183 8202493435906029063444275)
            ·
              refine ⟨12303740153859043595166413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202493435906029063444275 12303740153859043595166413)
              ·
                refine ⟨4613902557697141348187405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12303740153859043595166413 4613902557697141348187405)
                ·
                  refine ⟨1730213459136428005570277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4613902557697141348187405 1730213459136428005570277)
                  ·
                    refine ⟨324415023588080251044427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730213459136428005570277 324415023588080251044427)
                    ·
                      rfl

theorem cell22_947694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_947694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947694 prefixEnd_947694 := by exact prefixLift 947694
  have htrace : WordTrace (prefixWord ++ tailWord_947694) baseStart_947694 baseEnd_947694 := by
    simpa [prefixWord, tailWord_947694, baseEnd_947694] using wordTrace_append hprefix tailTrace_947694
  have hstable : (prefixWord ++ tailWord_947694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947694).length < 2 ^ (prefixWord ++ tailWord_947694).sum := by decide
  have hdescent : baseEnd_947694 < baseStart_947694 := by decide
  rcases family_descends (prefixWord ++ tailWord_947694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947726 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_947726 : Nat := 118140960795 + 947726 * 2 ^ 59
def prefixEnd_947726 : Nat := 4983230072969 + 3 ^ 40 * 947726 * 2
def baseEnd_947726 : Nat := 108141992614014278081443

theorem tailTrace_947726 : CollatzResearch.WordTrace tailWord_947726 prefixEnd_947726 108141992614014278081443 := by
  unfold tailWord_947726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320800870569754444959879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23044271309705357039786021 4320800870569754444959879)
  ·
    refine ⟨6481201305854631667439819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4320800870569754444959879 6481201305854631667439819)
    ·
      refine ⟨9721801958781947501159729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481201305854631667439819 9721801958781947501159729)
      ·
        refine ⟨7291351469086460625869797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721801958781947501159729 7291351469086460625869797)
        ·
          refine ⟨1367128400453711367350587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7291351469086460625869797 1367128400453711367350587)
          ·
            refine ⟨2050692600680567051025881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367128400453711367350587 2050692600680567051025881)
            ·
              refine ⟨1538019450510425288269411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050692600680567051025881 1538019450510425288269411)
              ·
                refine ⟨2307029175765637932404117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538019450510425288269411 2307029175765637932404117)
                ·
                  refine ⟨108141992614014278081443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2307029175765637932404117 108141992614014278081443)
                  ·
                    rfl

theorem cell22_947726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_947726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947726 prefixEnd_947726 := by exact prefixLift 947726
  have htrace : WordTrace (prefixWord ++ tailWord_947726) baseStart_947726 baseEnd_947726 := by
    simpa [prefixWord, tailWord_947726, baseEnd_947726] using wordTrace_append hprefix tailTrace_947726
  have hstable : (prefixWord ++ tailWord_947726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947726).length < 2 ^ (prefixWord ++ tailWord_947726).sum := by decide
  have hdescent : baseEnd_947726 < baseStart_947726 := by decide
  rcases family_descends (prefixWord ++ tailWord_947726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947754 : List Nat := [3, 1, 4, 1, 1, 1, 3, 8]
def baseStart_947754 : Nat := 118140960795 + 947754 * 2 ^ 59
def prefixEnd_947754 : Nat := 4983230072969 + 3 ^ 40 * 947754 * 2
def baseEnd_947754 : Nat := 36048395868251121616027

theorem tailTrace_947754 : CollatzResearch.WordTrace tailWord_947754 prefixEnd_947754 36048395868251121616027 := by
  unfold tailWord_947754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641857052114149085424579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23044952138971064227798877 8641857052114149085424579)
  ·
    refine ⟨12962785578171223628136869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8641857052114149085424579 12962785578171223628136869)
    ·
      refine ⟨2430522295907104430275663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12962785578171223628136869 2430522295907104430275663)
      ·
        refine ⟨3645783443860656645413495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430522295907104430275663 3645783443860656645413495)
        ·
          refine ⟨5468675165790984968120243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645783443860656645413495 5468675165790984968120243)
          ·
            refine ⟨8203012748686477452180365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468675165790984968120243 8203012748686477452180365)
            ·
              refine ⟨3076129780757429044567637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8203012748686477452180365 3076129780757429044567637)
              ·
                refine ⟨36048395868251121616027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3076129780757429044567637 36048395868251121616027)
                ·
                  rfl

theorem cell22_947754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_947754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947754 prefixEnd_947754 := by exact prefixLift 947754
  have htrace : WordTrace (prefixWord ++ tailWord_947754) baseStart_947754 baseEnd_947754 := by
    simpa [prefixWord, tailWord_947754, baseEnd_947754] using wordTrace_append hprefix tailTrace_947754
  have hstable : (prefixWord ++ tailWord_947754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947754).length < 2 ^ (prefixWord ++ tailWord_947754).sum := by decide
  have hdescent : baseEnd_947754 < baseStart_947754 := by decide
  rcases family_descends (prefixWord ++ tailWord_947754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947837 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 1, 3]
def baseStart_947837 : Nat := 118140960795 + 947837 * 2 ^ 59
def prefixEnd_947837 : Nat := 4983230072969 + 3 ^ 40 * 947837 * 2
def baseEnd_947837 : Nat := 324463975410475544718989

theorem tailTrace_947837 : CollatzResearch.WordTrace tailWord_947837 prefixEnd_947837 324463975410475544718989 := by
  unfold tailWord_947837
  simp only [CollatzResearch.WordTrace]
  refine ⟨34570455467155901516969765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23046970311437267677979843 34570455467155901516969765)
  ·
    refine ⟨6481960400091731534431831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34570455467155901516969765 6481960400091731534431831)
    ·
      refine ⟨9722940600137597301647747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481960400091731534431831 9722940600137597301647747)
      ·
        refine ⟨14584410900206395952471621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9722940600137597301647747 14584410900206395952471621)
        ·
          refine ⟨2734577043788699241088429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14584410900206395952471621 2734577043788699241088429)
          ·
            refine ⟨1025466391420762215408161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2734577043788699241088429 1025466391420762215408161)
            ·
              refine ⟨769099793565571661556121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025466391420762215408161 769099793565571661556121)
              ·
                refine ⟨576824845174178746167091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769099793565571661556121 576824845174178746167091)
                ·
                  refine ⟨865237267761268119250637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 576824845174178746167091 865237267761268119250637)
                  ·
                    refine ⟨324463975410475544718989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865237267761268119250637 324463975410475544718989)
                    ·
                      rfl

theorem cell22_947837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_947837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947837 prefixEnd_947837 := by exact prefixLift 947837
  have htrace : WordTrace (prefixWord ++ tailWord_947837) baseStart_947837 baseEnd_947837 := by
    simpa [prefixWord, tailWord_947837, baseEnd_947837] using wordTrace_append hprefix tailTrace_947837
  have hstable : (prefixWord ++ tailWord_947837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947837).length < 2 ^ (prefixWord ++ tailWord_947837).sum := by decide
  have hdescent : baseEnd_947837 < baseStart_947837 := by decide
  rcases family_descends (prefixWord ++ tailWord_947837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947848 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_947848 : Nat := 118140960795 + 947848 * 2 ^ 59
def prefixEnd_947848 : Nat := 4983230072969 + 3 ^ 40 * 947848 * 2
def baseEnd_947848 : Nat := 324467740935275182693955

theorem tailTrace_947848 : CollatzResearch.WordTrace tailWord_947848 prefixEnd_947848 324467740935275182693955 := by
  unfold tailWord_947848
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285428335058025197810099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23047237780077366930413465 17285428335058025197810099)
  ·
    refine ⟨25928142502587037796715149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17285428335058025197810099 25928142502587037796715149)
    ·
      refine ⟨9723053438470139173768181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25928142502587037796715149 9723053438470139173768181)
      ·
        refine ⟨911536259856575547540767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9723053438470139173768181 911536259856575547540767)
        ·
          refine ⟨1367304389784863321311151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911536259856575547540767 1367304389784863321311151)
          ·
            refine ⟨2050956584677294981966727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367304389784863321311151 2050956584677294981966727)
            ·
              refine ⟨3076434877015942472950091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050956584677294981966727 3076434877015942472950091)
              ·
                refine ⟨4614652315523913709425137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076434877015942472950091 4614652315523913709425137)
                ·
                  refine ⟨3460989236642935282068853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4614652315523913709425137 3460989236642935282068853)
                  ·
                    refine ⟨324467740935275182693955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3460989236642935282068853 324467740935275182693955)
                    ·
                      rfl

theorem cell22_947848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_947848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947848 prefixEnd_947848 := by exact prefixLift 947848
  have htrace : WordTrace (prefixWord ++ tailWord_947848) baseStart_947848 baseEnd_947848 := by
    simpa [prefixWord, tailWord_947848, baseEnd_947848] using wordTrace_append hprefix tailTrace_947848
  have hstable : (prefixWord ++ tailWord_947848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947848).length < 2 ^ (prefixWord ++ tailWord_947848).sum := by decide
  have hdescent : baseEnd_947848 < baseStart_947848 := by decide
  rcases family_descends (prefixWord ++ tailWord_947848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947876 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 1, 5]
def baseStart_947876 : Nat := 118140960795 + 947876 * 2 ^ 59
def prefixEnd_947876 : Nat := 4983230072969 + 3 ^ 40 * 947876 * 2
def baseEnd_947876 : Nat := 324477325907492442993869

theorem tailTrace_947876 : CollatzResearch.WordTrace tailWord_947876 prefixEnd_947876 324477325907492442993869 := by
  unfold tailWord_947876
  simp only [CollatzResearch.WordTrace]
  refine ⟨17285938957007305588819741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23047918609343074118426321 17285938957007305588819741)
  ·
    refine ⟨6482227108877739595807403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17285938957007305588819741 6482227108877739595807403)
    ·
      refine ⟨9723340663316609393711105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6482227108877739595807403 9723340663316609393711105)
      ·
        refine ⟨7292505497487457045283329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9723340663316609393711105 7292505497487457045283329)
        ·
          refine ⟨5469379123115592783962497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7292505497487457045283329 5469379123115592783962497)
          ·
            refine ⟨4102034342336694587971873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5469379123115592783962497 4102034342336694587971873)
            ·
              refine ⟨3076525756752520940978905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102034342336694587971873 3076525756752520940978905)
              ·
                refine ⟨2307394317564390705734179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076525756752520940978905 2307394317564390705734179)
                ·
                  refine ⟨3461091476346586058601269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307394317564390705734179 3461091476346586058601269)
                  ·
                    refine ⟨324477325907492442993869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3461091476346586058601269 324477325907492442993869)
                    ·
                      rfl

theorem cell22_947876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_947876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947876 prefixEnd_947876 := by exact prefixLift 947876
  have htrace : WordTrace (prefixWord ++ tailWord_947876) baseStart_947876 baseEnd_947876 := by
    simpa [prefixWord, tailWord_947876, baseEnd_947876] using wordTrace_append hprefix tailTrace_947876
  have hstable : (prefixWord ++ tailWord_947876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947876).length < 2 ^ (prefixWord ++ tailWord_947876).sum := by decide
  have hdescent : baseEnd_947876 < baseStart_947876 := by decide
  rcases family_descends (prefixWord ++ tailWord_947876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947919 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 6]
def baseStart_947919 : Nat := 118140960795 + 947919 * 2 ^ 59
def prefixEnd_947919 : Nat := 4983230072969 + 3 ^ 40 * 947919 * 2
def baseEnd_947919 : Nat := 324492045686254664168737

theorem tailTrace_947919 : CollatzResearch.WordTrace tailWord_947919 prefixEnd_947919 324492045686254664168737 := by
  unfold tailWord_947919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34573446252858829521454811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23048964168572553014303207 34573446252858829521454811)
  ·
    refine ⟨51860169379288244282182217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34573446252858829521454811 51860169379288244282182217)
    ·
      refine ⟨38895127034466183211636663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51860169379288244282182217 38895127034466183211636663)
      ·
        refine ⟨58342690551699274817454995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38895127034466183211636663 58342690551699274817454995)
        ·
          refine ⟨87514035827548912226182493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58342690551699274817454995 87514035827548912226182493)
          ·
            refine ⟨32817763435330842084818435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87514035827548912226182493 32817763435330842084818435)
            ·
              refine ⟨49226645152996263127227653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32817763435330842084818435 49226645152996263127227653)
              ·
                refine ⟨9229995966186799336355185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49226645152996263127227653 9229995966186799336355185)
                ·
                  refine ⟨6922496974640099502266389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9229995966186799336355185 6922496974640099502266389)
                  ·
                    refine ⟨324492045686254664168737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6922496974640099502266389 324492045686254664168737)
                    ·
                      rfl

theorem cell22_947919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_947919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947919 prefixEnd_947919 := by exact prefixLift 947919
  have htrace : WordTrace (prefixWord ++ tailWord_947919) baseStart_947919 baseEnd_947919 := by
    simpa [prefixWord, tailWord_947919, baseEnd_947919] using wordTrace_append hprefix tailTrace_947919
  have hstable : (prefixWord ++ tailWord_947919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947919).length < 2 ^ (prefixWord ++ tailWord_947919).sum := by decide
  have hdescent : baseEnd_947919 < baseStart_947919 := by decide
  rcases family_descends (prefixWord ++ tailWord_947919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_947951 : List Nat := [1, 1, 2, 1, 5, 1, 2, 4, 5]
def baseStart_947951 : Nat := 118140960795 + 947951 * 2 ^ 59
def prefixEnd_947951 : Nat := 4983230072969 + 3 ^ 40 * 947951 * 2
def baseEnd_947951 : Nat := 108167666646739082456213

theorem tailTrace_947951 : CollatzResearch.WordTrace tailWord_947951 prefixEnd_947951 108167666646739082456213 := by
  unfold tailWord_947951
  simp only [CollatzResearch.WordTrace]
  refine ⟨34574613388742898986619707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23049742259161932657746471 34574613388742898986619707)
  ·
    refine ⟨51861920083114348479929561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34574613388742898986619707 51861920083114348479929561)
    ·
      refine ⟨38896440062335761359947171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51861920083114348479929561 38896440062335761359947171)
      ·
        refine ⟨58344660093503642039920757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38896440062335761359947171 58344660093503642039920757)
        ·
          refine ⟨5469811883765966441242571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58344660093503642039920757 5469811883765966441242571)
          ·
            refine ⟨8204717825648949661863857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5469811883765966441242571 8204717825648949661863857)
            ·
              refine ⟨6153538369236712246397893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8204717825648949661863857 6153538369236712246397893)
              ·
                refine ⟨1153788444231883546199605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6153538369236712246397893 1153788444231883546199605)
                ·
                  refine ⟨108167666646739082456213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1153788444231883546199605 108167666646739082456213)
                  ·
                    rfl

theorem cell22_947951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 4, 5].length) (baseStart_947951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_947951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_947951 prefixEnd_947951 := by exact prefixLift 947951
  have htrace : WordTrace (prefixWord ++ tailWord_947951) baseStart_947951 baseEnd_947951 := by
    simpa [prefixWord, tailWord_947951, baseEnd_947951] using wordTrace_append hprefix tailTrace_947951
  have hstable : (prefixWord ++ tailWord_947951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_947951).length < 2 ^ (prefixWord ++ tailWord_947951).sum := by decide
  have hdescent : baseEnd_947951 < baseStart_947951 := by decide
  rcases family_descends (prefixWord ++ tailWord_947951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948045 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_948045 : Nat := 118140960795 + 948045 * 2 ^ 59
def prefixEnd_948045 : Nat := 4983230072969 + 3 ^ 40 * 948045 * 2
def baseEnd_948045 : Nat := 324535178061232335518351

theorem tailTrace_948045 : CollatzResearch.WordTrace tailWord_948045 prefixEnd_948045 324535178061232335518351 := by
  unfold tailWord_948045
  simp only [CollatzResearch.WordTrace]
  refine ⟨34578041850402353040541589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23052027900268235360361059 34578041850402353040541589)
  ·
    refine ⟨1620845711737610298775387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34578041850402353040541589 1620845711737610298775387)
    ·
      refine ⟨2431268567606415448163081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620845711737610298775387 2431268567606415448163081)
      ·
        refine ⟨1823451425704811586122311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2431268567606415448163081 1823451425704811586122311)
        ·
          refine ⟨2735177138557217379183467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823451425704811586122311 2735177138557217379183467)
          ·
            refine ⟨4102765707835826068775201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735177138557217379183467 4102765707835826068775201)
            ·
              refine ⟨3077074280876869551581401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102765707835826068775201 3077074280876869551581401)
              ·
                refine ⟨2307805710657652163686051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077074280876869551581401 2307805710657652163686051)
                ·
                  refine ⟨3461708565986478245529077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307805710657652163686051 3461708565986478245529077)
                  ·
                    refine ⟨324535178061232335518351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3461708565986478245529077 324535178061232335518351)
                    ·
                      rfl

theorem cell22_948045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_948045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948045 prefixEnd_948045 := by exact prefixLift 948045
  have htrace : WordTrace (prefixWord ++ tailWord_948045) baseStart_948045 baseEnd_948045 := by
    simpa [prefixWord, tailWord_948045, baseEnd_948045] using wordTrace_append hprefix tailTrace_948045
  have hstable : (prefixWord ++ tailWord_948045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948045).length < 2 ^ (prefixWord ++ tailWord_948045).sum := by decide
  have hdescent : baseEnd_948045 < baseStart_948045 := by decide
  rcases family_descends (prefixWord ++ tailWord_948045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948193 : List Nat := [1, 2, 3, 1, 2, 1, 5, 7]
def baseStart_948193 : Nat := 118140960795 + 948193 * 2 ^ 59
def prefixEnd_948193 : Nat := 4983230072969 + 3 ^ 40 * 948193 * 2
def baseEnd_948193 : Nat := 36065093498423253646433

theorem tailTrace_948193 : CollatzResearch.WordTrace tailWord_948193 prefixEnd_948193 36065093498423253646433 := by
  unfold tailWord_948193
  simp only [CollatzResearch.WordTrace]
  refine ⟨34583439853866174316929233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23055626569244116211286155 34583439853866174316929233)
  ·
    refine ⟨25937579890399630737696925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34583439853866174316929233 25937579890399630737696925)
    ·
      refine ⟨9726592458899861526636347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25937579890399630737696925 9726592458899861526636347)
      ·
        refine ⟨14589888688349792289954521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9726592458899861526636347 14589888688349792289954521)
        ·
          refine ⟨10942416516262344217465891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14589888688349792289954521 10942416516262344217465891)
          ·
            refine ⟨16413624774393516326198837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10942416516262344217465891 16413624774393516326198837)
            ·
              refine ⟨1538777322599392155581141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16413624774393516326198837 1538777322599392155581141)
              ·
                refine ⟨36065093498423253646433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1538777322599392155581141 36065093498423253646433)
                ·
                  rfl

theorem cell22_948193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 7].length) (baseStart_948193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948193 prefixEnd_948193 := by exact prefixLift 948193
  have htrace : WordTrace (prefixWord ++ tailWord_948193) baseStart_948193 baseEnd_948193 := by
    simpa [prefixWord, tailWord_948193, baseEnd_948193] using wordTrace_append hprefix tailTrace_948193
  have hstable : (prefixWord ++ tailWord_948193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948193).length < 2 ^ (prefixWord ++ tailWord_948193).sum := by decide
  have hdescent : baseEnd_948193 < baseStart_948193 := by decide
  rcases family_descends (prefixWord ++ tailWord_948193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948225 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_948225 : Nat := 118140960795 + 948225 * 2 ^ 59
def prefixEnd_948225 : Nat := 4983230072969 + 3 ^ 40 * 948225 * 2
def baseEnd_948225 : Nat := 324596795739771866017799

theorem tailTrace_948225 : CollatzResearch.WordTrace tailWord_948225 prefixEnd_948225 324596795739771866017799 := by
  unfold tailWord_948225
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584606989750243782094129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23056404659833495854729419 34584606989750243782094129)
  ·
    refine ⟨25938455242312682836570597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34584606989750243782094129 25938455242312682836570597)
    ·
      refine ⟨4863460357933628031856987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25938455242312682836570597 4863460357933628031856987)
      ·
        refine ⟨7295190536900442047785481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863460357933628031856987 7295190536900442047785481)
        ·
          refine ⟨5471392902675331535839111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295190536900442047785481 5471392902675331535839111)
          ·
            refine ⟨8207089354012997303758667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471392902675331535839111 8207089354012997303758667)
            ·
              refine ⟨12310634031019495955638001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207089354012997303758667 12310634031019495955638001)
              ·
                refine ⟨9232975523264621966728501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12310634031019495955638001 9232975523264621966728501)
                ·
                  refine ⟨865591455306058309380797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9232975523264621966728501 865591455306058309380797)
                  ·
                    refine ⟨324596795739771866017799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865591455306058309380797 324596795739771866017799)
                    ·
                      rfl

theorem cell22_948225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_948225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948225 prefixEnd_948225 := by exact prefixLift 948225
  have htrace : WordTrace (prefixWord ++ tailWord_948225) baseStart_948225 baseEnd_948225 := by
    simpa [prefixWord, tailWord_948225, baseEnd_948225] using wordTrace_append hprefix tailTrace_948225
  have hstable : (prefixWord ++ tailWord_948225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948225).length < 2 ^ (prefixWord ++ tailWord_948225).sum := by decide
  have hdescent : baseEnd_948225 < baseStart_948225 := by decide
  rcases family_descends (prefixWord ++ tailWord_948225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948300 : List Nat := [2, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_948300 : Nat := 118140960795 + 948300 * 2 ^ 59
def prefixEnd_948300 : Nat := 4983230072969 + 3 ^ 40 * 948300 * 2
def baseEnd_948300 : Nat := 108207489924165556797523

theorem tailTrace_948300 : CollatzResearch.WordTrace tailWord_948300 prefixEnd_948300 108207489924165556797523 := by
  unfold tailWord_948300
  simp only [CollatzResearch.WordTrace]
  refine ⟨17293671232239265795537177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23058228309652354394049569 17293671232239265795537177)
  ·
    refine ⟨12970253424179449346652883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17293671232239265795537177 12970253424179449346652883)
    ·
      refine ⟨19455380136269174019979325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12970253424179449346652883 19455380136269174019979325)
      ·
        refine ⟨7295767551100940257492247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19455380136269174019979325 7295767551100940257492247)
        ·
          refine ⟨10943651326651410386238371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7295767551100940257492247 10943651326651410386238371)
          ·
            refine ⟨16415476989977115579357557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10943651326651410386238371 16415476989977115579357557)
            ·
              refine ⟨1538950967810354585564771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16415476989977115579357557 1538950967810354585564771)
              ·
                refine ⟨2308426451715531878347157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538950967810354585564771 2308426451715531878347157)
                ·
                  refine ⟨108207489924165556797523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2308426451715531878347157 108207489924165556797523)
                  ·
                    rfl

theorem cell22_948300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_948300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948300 prefixEnd_948300 := by exact prefixLift 948300
  have htrace : WordTrace (prefixWord ++ tailWord_948300) baseStart_948300 baseEnd_948300 := by
    simpa [prefixWord, tailWord_948300, baseEnd_948300] using wordTrace_append hprefix tailTrace_948300
  have hstable : (prefixWord ++ tailWord_948300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948300).length < 2 ^ (prefixWord ++ tailWord_948300).sum := by decide
  have hdescent : baseEnd_948300 < baseStart_948300 := by decide
  rcases family_descends (prefixWord ++ tailWord_948300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948306 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_948306 : Nat := 118140960795 + 948306 * 2 ^ 59
def prefixEnd_948306 : Nat := 4983230072969 + 3 ^ 40 * 948306 * 2
def baseEnd_948306 : Nat := 108208174565038218247517

theorem tailTrace_948306 : CollatzResearch.WordTrace tailWord_948306 prefixEnd_948306 108208174565038218247517 := by
  unfold tailWord_948306
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646890325614198653948193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23058374201637863077195181 8646890325614198653948193)
  ·
    refine ⟨6485167744210648990461145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8646890325614198653948193 6485167744210648990461145)
    ·
      refine ⟨4863875808157986742845859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6485167744210648990461145 4863875808157986742845859)
      ·
        refine ⟨7295813712236980114268789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863875808157986742845859 7295813712236980114268789)
        ·
          refine ⟨683982535522216885712699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7295813712236980114268789 683982535522216885712699)
          ·
            refine ⟨1025973803283325328569049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683982535522216885712699 1025973803283325328569049)
            ·
              refine ⟨769480352462493996426787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1025973803283325328569049 769480352462493996426787)
              ·
                refine ⟨1154220528693740994640181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769480352462493996426787 1154220528693740994640181)
                ·
                  refine ⟨108208174565038218247517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154220528693740994640181 108208174565038218247517)
                  ·
                    rfl

theorem cell22_948306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_948306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948306 prefixEnd_948306 := by exact prefixLift 948306
  have htrace : WordTrace (prefixWord ++ tailWord_948306) baseStart_948306 baseEnd_948306 := by
    simpa [prefixWord, tailWord_948306, baseEnd_948306] using wordTrace_append hprefix tailTrace_948306
  have hstable : (prefixWord ++ tailWord_948306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948306).length < 2 ^ (prefixWord ++ tailWord_948306).sum := by decide
  have hdescent : baseEnd_948306 < baseStart_948306 := by decide
  rcases family_descends (prefixWord ++ tailWord_948306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948349 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_948349 : Nat := 118140960795 + 948349 * 2 ^ 59
def prefixEnd_948349 : Nat := 4983230072969 + 3 ^ 40 * 948349 * 2
def baseEnd_948349 : Nat := 324639243473876875917419

theorem tailTrace_948349 : CollatzResearch.WordTrace tailWord_948349 prefixEnd_948349 324639243473876875917419 := by
  unfold tailWord_948349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34589129641301012959608101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23059419760867341973072067 34589129641301012959608101)
  ·
    refine ⟨6485461807743939929926519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34589129641301012959608101 6485461807743939929926519)
    ·
      refine ⟨9728192711615909894889779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6485461807743939929926519 9728192711615909894889779)
      ·
        refine ⟨14592289067423864842334669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728192711615909894889779 14592289067423864842334669)
        ·
          refine ⟨5472108400283949315875501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14592289067423864842334669 5472108400283949315875501)
          ·
            refine ⟨2052040650106480993453313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5472108400283949315875501 2052040650106480993453313)
            ·
              refine ⟨1539030487579860745089985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052040650106480993453313 1539030487579860745089985)
              ·
                refine ⟨1154272865684895558817489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539030487579860745089985 1154272865684895558817489)
                ·
                  refine ⟨865704649263671669113117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1154272865684895558817489 865704649263671669113117)
                  ·
                    refine ⟨324639243473876875917419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865704649263671669113117 324639243473876875917419)
                    ·
                      rfl

theorem cell22_948349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_948349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948349 prefixEnd_948349 := by exact prefixLift 948349
  have htrace : WordTrace (prefixWord ++ tailWord_948349) baseStart_948349 baseEnd_948349 := by
    simpa [prefixWord, tailWord_948349, baseEnd_948349] using wordTrace_append hprefix tailTrace_948349
  have hstable : (prefixWord ++ tailWord_948349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948349).length < 2 ^ (prefixWord ++ tailWord_948349).sum := by decide
  have hdescent : baseEnd_948349 < baseStart_948349 := by decide
  rcases family_descends (prefixWord ++ tailWord_948349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948362 : List Nat := [3, 1, 2, 3, 1, 4, 1, 7]
def baseStart_948362 : Nat := 118140960795 + 948362 * 2 ^ 59
def prefixEnd_948362 : Nat := 4983230072969 + 3 ^ 40 * 948362 * 2
def baseEnd_948362 : Nat := 36071521515505463926931

theorem tailTrace_948362 : CollatzResearch.WordTrace tailWord_948362 prefixEnd_948362 36071521515505463926931 := by
  unfold tailWord_948362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8647400947563479044957835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23059735860169277453220893 8647400947563479044957835)
  ·
    refine ⟨12971101421345218567436753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8647400947563479044957835 12971101421345218567436753)
    ·
      refine ⟨9728326066008913925577565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12971101421345218567436753 9728326066008913925577565)
      ·
        refine ⟨3648122274753342722091587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9728326066008913925577565 3648122274753342722091587)
        ·
          refine ⟨5472183412130014083137381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648122274753342722091587 5472183412130014083137381)
          ·
            refine ⟨1026034389774377640588259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5472183412130014083137381 1026034389774377640588259)
            ·
              refine ⟨1539051584661566460882389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026034389774377640588259 1539051584661566460882389)
              ·
                refine ⟨36071521515505463926931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1539051584661566460882389 36071521515505463926931)
                ·
                  rfl

theorem cell22_948362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_948362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948362 prefixEnd_948362 := by exact prefixLift 948362
  have htrace : WordTrace (prefixWord ++ tailWord_948362) baseStart_948362 baseEnd_948362 := by
    simpa [prefixWord, tailWord_948362, baseEnd_948362] using wordTrace_append hprefix tailTrace_948362
  have hstable : (prefixWord ++ tailWord_948362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948362).length < 2 ^ (prefixWord ++ tailWord_948362).sum := by decide
  have hdescent : baseEnd_948362 < baseStart_948362 := by decide
  rcases family_descends (prefixWord ++ tailWord_948362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948407 : List Nat := [1, 1, 3, 1, 4, 2, 3, 2, 5]
def baseStart_948407 : Nat := 118140960795 + 948407 * 2 ^ 59
def prefixEnd_948407 : Nat := 4983230072969 + 3 ^ 40 * 948407 * 2
def baseEnd_948407 : Nat := 108219699353061352655747

theorem tailTrace_948407 : CollatzResearch.WordTrace tailWord_948407 prefixEnd_948407 108219699353061352655747 := by
  unfold tailWord_948407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34591245075090888865219475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23060830050060592576812983 34591245075090888865219475)
  ·
    refine ⟨51886867612636333297829213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34591245075090888865219475 51886867612636333297829213)
    ·
      refine ⟨19457575354738624986685955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51886867612636333297829213 19457575354738624986685955)
      ·
        refine ⟨29186363032107937480028933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19457575354738624986685955 29186363032107937480028933)
        ·
          refine ⟨5472443068520238277505425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29186363032107937480028933 5472443068520238277505425)
          ·
            refine ⟨4104332301390178708129069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5472443068520238277505425 4104332301390178708129069)
            ·
              refine ⟨1539124613021317015548401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4104332301390178708129069 1539124613021317015548401)
              ·
                refine ⟨1154343459765987761661301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539124613021317015548401 1154343459765987761661301)
                ·
                  refine ⟨108219699353061352655747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154343459765987761661301 108219699353061352655747)
                  ·
                    rfl

theorem cell22_948407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 2, 5].length) (baseStart_948407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948407 prefixEnd_948407 := by exact prefixLift 948407
  have htrace : WordTrace (prefixWord ++ tailWord_948407) baseStart_948407 baseEnd_948407 := by
    simpa [prefixWord, tailWord_948407, baseEnd_948407] using wordTrace_append hprefix tailTrace_948407
  have hstable : (prefixWord ++ tailWord_948407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948407).length < 2 ^ (prefixWord ++ tailWord_948407).sum := by decide
  have hdescent : baseEnd_948407 < baseStart_948407 := by decide
  rcases family_descends (prefixWord ++ tailWord_948407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948467 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 4, 3]
def baseStart_948467 : Nat := 118140960795 + 948467 * 2 ^ 59
def prefixEnd_948467 : Nat := 4983230072969 + 3 ^ 40 * 948467 * 2
def baseEnd_948467 : Nat := 324679637285363901467057

theorem tailTrace_948467 : CollatzResearch.WordTrace tailWord_948467 prefixEnd_948467 324679637285363901467057 := by
  unfold tailWord_948467
  simp only [CollatzResearch.WordTrace]
  refine ⟨34593433454873519112403655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23062288969915679408269103 34593433454873519112403655)
  ·
    refine ⟨51890150182310278668605483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34593433454873519112403655 51890150182310278668605483)
    ·
      refine ⟨77835225273465418002908225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51890150182310278668605483 77835225273465418002908225)
      ·
        refine ⟨58376418955099063502181169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77835225273465418002908225 58376418955099063502181169)
        ·
          refine ⟨43782314216324297626635877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58376418955099063502181169 43782314216324297626635877)
          ·
            refine ⟨8209183915560805804994227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43782314216324297626635877 8209183915560805804994227)
            ·
              refine ⟨12313775873341208707491341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209183915560805804994227 12313775873341208707491341)
              ·
                refine ⟨4617665952502953265309253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12313775873341208707491341 4617665952502953265309253)
                ·
                  refine ⟨865812366094303737245485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4617665952502953265309253 865812366094303737245485)
                  ·
                    refine ⟨324679637285363901467057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865812366094303737245485 324679637285363901467057)
                    ·
                      rfl

theorem cell22_948467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 3].length) (baseStart_948467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948467 prefixEnd_948467 := by exact prefixLift 948467
  have htrace : WordTrace (prefixWord ++ tailWord_948467) baseStart_948467 baseEnd_948467 := by
    simpa [prefixWord, tailWord_948467, baseEnd_948467] using wordTrace_append hprefix tailTrace_948467
  have hstable : (prefixWord ++ tailWord_948467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948467).length < 2 ^ (prefixWord ++ tailWord_948467).sum := by decide
  have hdescent : baseEnd_948467 < baseStart_948467 := by decide
  rcases family_descends (prefixWord ++ tailWord_948467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948480 : List Nat := [2, 1, 1, 2, 1, 1, 5, 9]
def baseStart_948480 : Nat := 118140960795 + 948480 * 2 ^ 59
def prefixEnd_948480 : Nat := 4983230072969 + 3 ^ 40 * 948480 * 2
def baseEnd_948480 : Nat := 36076009716781800099113

theorem tailTrace_948480 : CollatzResearch.WordTrace tailWord_948480 prefixEnd_948480 36076009716781800099113 := by
  unfold tailWord_948480
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296953801913211166313447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23062605069217614888417929 17296953801913211166313447)
  ·
    refine ⟨25945430702869816749470171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17296953801913211166313447 25945430702869816749470171)
    ·
      refine ⟨38918146054304725124205257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25945430702869816749470171 38918146054304725124205257)
      ·
        refine ⟨29188609540728543843153943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38918146054304725124205257 29188609540728543843153943)
        ·
          refine ⟨43782914311092815764730915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29188609540728543843153943 43782914311092815764730915)
          ·
            refine ⟨65674371466639223647096373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43782914311092815764730915 65674371466639223647096373)
            ·
              refine ⟨6156972324997427216915285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65674371466639223647096373 6156972324997427216915285)
              ·
                refine ⟨36076009716781800099113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6156972324997427216915285 36076009716781800099113)
                ·
                  rfl

theorem cell22_948480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_948480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948480 prefixEnd_948480 := by exact prefixLift 948480
  have htrace : WordTrace (prefixWord ++ tailWord_948480) baseStart_948480 baseEnd_948480 := by
    simpa [prefixWord, tailWord_948480, baseEnd_948480] using wordTrace_append hprefix tailTrace_948480
  have hstable : (prefixWord ++ tailWord_948480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948480).length < 2 ^ (prefixWord ++ tailWord_948480).sum := by decide
  have hdescent : baseEnd_948480 < baseStart_948480 := by decide
  rcases family_descends (prefixWord ++ tailWord_948480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948495 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 7]
def baseStart_948495 : Nat := 118140960795 + 948495 * 2 ^ 59
def prefixEnd_948495 : Nat := 4983230072969 + 3 ^ 40 * 948495 * 2
def baseEnd_948495 : Nat := 324689222257581161766971

theorem tailTrace_948495 : CollatzResearch.WordTrace tailWord_948495 prefixEnd_948495 324689222257581161766971 := by
  unfold tailWord_948495
  simp only [CollatzResearch.WordTrace]
  refine ⟨34594454698772079894422939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23062969799181386596281959 34594454698772079894422939)
  ·
    refine ⟨51891682048158119841634409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34594454698772079894422939 51891682048158119841634409)
    ·
      refine ⟨38918761536118589881225807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51891682048158119841634409 38918761536118589881225807)
      ·
        refine ⟨58378142304177884821838711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38918761536118589881225807 58378142304177884821838711)
        ·
          refine ⟨87567213456266827232758067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58378142304177884821838711 87567213456266827232758067)
          ·
            refine ⟨131350820184400240849137101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87567213456266827232758067 131350820184400240849137101)
            ·
              refine ⟨49256557569150090318426413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131350820184400240849137101 49256557569150090318426413)
              ·
                refine ⟨18471209088431283869409905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49256557569150090318426413 18471209088431283869409905)
                ·
                  refine ⟨13853406816323462902057429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18471209088431283869409905 13853406816323462902057429)
                  ·
                    refine ⟨324689222257581161766971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13853406816323462902057429 324689222257581161766971)
                    ·
                      rfl

theorem cell22_948495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_948495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948495 prefixEnd_948495 := by exact prefixLift 948495
  have htrace : WordTrace (prefixWord ++ tailWord_948495) baseStart_948495 baseEnd_948495 := by
    simpa [prefixWord, tailWord_948495, baseEnd_948495] using wordTrace_append hprefix tailTrace_948495
  have hstable : (prefixWord ++ tailWord_948495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948495).length < 2 ^ (prefixWord ++ tailWord_948495).sum := by decide
  have hdescent : baseEnd_948495 < baseStart_948495 := by decide
  rcases family_descends (prefixWord ++ tailWord_948495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948520 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 4]
def baseStart_948520 : Nat := 118140960795 + 948520 * 2 ^ 59
def prefixEnd_948520 : Nat := 4983230072969 + 3 ^ 40 * 948520 * 2
def baseEnd_948520 : Nat := 108232593422829809963965

theorem tailTrace_948520 : CollatzResearch.WordTrace tailWord_948520 prefixEnd_948520 108232593422829809963965 := by
  unfold tailWord_948520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17297683261840754582041507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23063577682454339442722009 17297683261840754582041507)
  ·
    refine ⟨25946524892761131873062261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17297683261840754582041507 25946524892761131873062261)
    ·
      refine ⟨2432486708696356113099587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25946524892761131873062261 2432486708696356113099587)
      ·
        refine ⟨3648730063044534169649381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432486708696356113099587 3648730063044534169649381)
        ·
          refine ⟨684136886820850156809259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3648730063044534169649381 684136886820850156809259)
          ·
            refine ⟨1026205330231275235213889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684136886820850156809259 1026205330231275235213889)
            ·
              refine ⟨769653997673456426410417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026205330231275235213889 769653997673456426410417)
              ·
                refine ⟨577240498255092319807813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 769653997673456426410417 577240498255092319807813)
                ·
                  refine ⟨108232593422829809963965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577240498255092319807813 108232593422829809963965)
                  ·
                    rfl

theorem cell22_948520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 4].length) (baseStart_948520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948520 prefixEnd_948520 := by exact prefixLift 948520
  have htrace : WordTrace (prefixWord ++ tailWord_948520) baseStart_948520 baseEnd_948520 := by
    simpa [prefixWord, tailWord_948520, baseEnd_948520] using wordTrace_append hprefix tailTrace_948520
  have hstable : (prefixWord ++ tailWord_948520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948520).length < 2 ^ (prefixWord ++ tailWord_948520).sum := by decide
  have hdescent : baseEnd_948520 < baseStart_948520 := by decide
  rcases family_descends (prefixWord ++ tailWord_948520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948576 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_948576 : Nat := 118140960795 + 948576 * 2 ^ 59
def prefixEnd_948576 : Nat := 4983230072969 + 3 ^ 40 * 948576 * 2
def baseEnd_948576 : Nat := 108238983404307983497241

theorem tailTrace_948576 : CollatzResearch.WordTrace tailWord_948576 prefixEnd_948576 108238983404307983497241 := by
  unfold tailWord_948576
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298704505739315364060791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23064939340985753818747721 17298704505739315364060791)
  ·
    refine ⟨25948056758608973046091187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17298704505739315364060791 25948056758608973046091187)
    ·
      refine ⟨38922085137913459569136781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25948056758608973046091187 38922085137913459569136781)
      ·
        refine ⟨14595781926717547338426293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38922085137913459569136781 14595781926717547338426293)
        ·
          refine ⟨1368354555629770062977465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14595781926717547338426293 1368354555629770062977465)
          ·
            refine ⟨1026265916722327547233099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1368354555629770062977465 1026265916722327547233099)
            ·
              refine ⟨1539398875083491320849649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026265916722327547233099 1539398875083491320849649)
              ·
                refine ⟨1154549156312618490637237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539398875083491320849649 1154549156312618490637237)
                ·
                  refine ⟨108238983404307983497241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154549156312618490637237 108238983404307983497241)
                  ·
                    rfl

theorem cell22_948576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_948576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948576 prefixEnd_948576 := by exact prefixLift 948576
  have htrace : WordTrace (prefixWord ++ tailWord_948576) baseStart_948576 baseEnd_948576 := by
    simpa [prefixWord, tailWord_948576, baseEnd_948576] using wordTrace_append hprefix tailTrace_948576
  have hstable : (prefixWord ++ tailWord_948576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948576).length < 2 ^ (prefixWord ++ tailWord_948576).sum := by decide
  have hdescent : baseEnd_948576 < baseStart_948576 := by decide
  rcases family_descends (prefixWord ++ tailWord_948576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948619 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 4, 3]
def baseStart_948619 : Nat := 118140960795 + 948619 * 2 ^ 59
def prefixEnd_948619 : Nat := 4983230072969 + 3 ^ 40 * 948619 * 2
def baseEnd_948619 : Nat := 324731669991686171666591

theorem tailTrace_948619 : CollatzResearch.WordTrace tailWord_948619 prefixEnd_948619 324731669991686171666591 := by
  unfold tailWord_948619
  simp only [CollatzResearch.WordTrace]
  refine ⟨34598977350322849071936911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23065984900215232714624607 34598977350322849071936911)
  ·
    refine ⟨51898466025484273607905367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34598977350322849071936911 51898466025484273607905367)
    ·
      refine ⟨77847699038226410411858051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51898466025484273607905367 77847699038226410411858051)
      ·
        refine ⟨116771548557339615617787077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77847699038226410411858051 116771548557339615617787077)
        ·
          refine ⟨21894665354501177928335077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 116771548557339615617787077 21894665354501177928335077)
          ·
            refine ⟨4105249753968970861562827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21894665354501177928335077 4105249753968970861562827)
            ·
              refine ⟨6157874630953456292344241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105249753968970861562827 6157874630953456292344241)
              ·
                refine ⟨4618405973215092219258181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6157874630953456292344241 4618405973215092219258181)
                ·
                  refine ⟨865951119977829791110909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4618405973215092219258181 865951119977829791110909)
                  ·
                    refine ⟨324731669991686171666591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865951119977829791110909 324731669991686171666591)
                    ·
                      rfl

theorem cell22_948619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 3].length) (baseStart_948619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948619 prefixEnd_948619 := by exact prefixLift 948619
  have htrace : WordTrace (prefixWord ++ tailWord_948619) baseStart_948619 baseEnd_948619 := by
    simpa [prefixWord, tailWord_948619, baseEnd_948619] using wordTrace_append hprefix tailTrace_948619
  have hstable : (prefixWord ++ tailWord_948619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948619).length < 2 ^ (prefixWord ++ tailWord_948619).sum := by decide
  have hdescent : baseEnd_948619 < baseStart_948619 := by decide
  rcases family_descends (prefixWord ++ tailWord_948619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948634 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 4, 4]
def baseStart_948634 : Nat := 118140960795 + 948634 * 2 ^ 59
def prefixEnd_948634 : Nat := 4983230072969 + 3 ^ 40 * 948634 * 2
def baseEnd_948634 : Nat := 324736804798231132541545

theorem tailTrace_948634 : CollatzResearch.WordTrace tailWord_948634 prefixEnd_948634 324736804798231132541545 := by
  unfold tailWord_948634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649881111317126658433239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23066349630179004422488637 8649881111317126658433239)
  ·
    refine ⟨12974821666975689987649859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8649881111317126658433239 12974821666975689987649859)
    ·
      refine ⟨19462232500463534981474789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12974821666975689987649859 19462232500463534981474789)
      ·
        refine ⟨3649168593836912809026523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19462232500463534981474789 3649168593836912809026523)
        ·
          refine ⟨5473752890755369213539785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649168593836912809026523 5473752890755369213539785)
          ·
            refine ⟨4105314668066526910154839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473752890755369213539785 4105314668066526910154839)
            ·
              refine ⟨6157972002099790365232259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105314668066526910154839 6157972002099790365232259)
              ·
                refine ⟨9236958003149685547848389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157972002099790365232259 9236958003149685547848389)
                ·
                  refine ⟨1731929625590566040221573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9236958003149685547848389 1731929625590566040221573)
                  ·
                    refine ⟨324736804798231132541545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731929625590566040221573 324736804798231132541545)
                    ·
                      rfl

theorem cell22_948634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_948634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948634 prefixEnd_948634 := by exact prefixLift 948634
  have htrace : WordTrace (prefixWord ++ tailWord_948634) baseStart_948634 baseEnd_948634 := by
    simpa [prefixWord, tailWord_948634, baseEnd_948634] using wordTrace_append hprefix tailTrace_948634
  have hstable : (prefixWord ++ tailWord_948634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948634).length < 2 ^ (prefixWord ++ tailWord_948634).sum := by decide
  have hdescent : baseEnd_948634 < baseStart_948634 := by decide
  rcases family_descends (prefixWord ++ tailWord_948634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948638 : List Nat := [4, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_948638 : Nat := 118140960795 + 948638 * 2 ^ 59
def prefixEnd_948638 : Nat := 4983230072969 + 3 ^ 40 * 948638 * 2
def baseEnd_948638 : Nat := 108246058026658818480511

theorem tailTrace_948638 : CollatzResearch.WordTrace tailWord_948638 prefixEnd_948638 108246058026658818480511 := by
  unfold tailWord_948638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324958792156751914609821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23066446891502676877919045 4324958792156751914609821)
  ·
    refine ⟨1621859547058781967978683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4324958792156751914609821 1621859547058781967978683)
    ·
      refine ⟨2432789320588172951968025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621859547058781967978683 2432789320588172951968025)
      ·
        refine ⟨1824591990441129713976019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432789320588172951968025 1824591990441129713976019)
        ·
          refine ⟨2736887985661694570964029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824591990441129713976019 2736887985661694570964029)
          ·
            refine ⟨1026332994623135464111511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2736887985661694570964029 1026332994623135464111511)
            ·
              refine ⟨1539499491934703196167267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026332994623135464111511 1539499491934703196167267)
              ·
                refine ⟨2309249237902054794250901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539499491934703196167267 2309249237902054794250901)
                ·
                  refine ⟨108246058026658818480511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2309249237902054794250901 108246058026658818480511)
                  ·
                    rfl

theorem cell22_948638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_948638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948638 prefixEnd_948638 := by exact prefixLift 948638
  have htrace : WordTrace (prefixWord ++ tailWord_948638) baseStart_948638 baseEnd_948638 := by
    simpa [prefixWord, tailWord_948638, baseEnd_948638] using wordTrace_append hprefix tailTrace_948638
  have hstable : (prefixWord ++ tailWord_948638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948638).length < 2 ^ (prefixWord ++ tailWord_948638).sum := by decide
  have hdescent : baseEnd_948638 < baseStart_948638 := by decide
  rcases family_descends (prefixWord ++ tailWord_948638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948664 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_948664 : Nat := 118140960795 + 948664 * 2 ^ 59
def prefixEnd_948664 : Nat := 4983230072969 + 3 ^ 40 * 948664 * 2
def baseEnd_948664 : Nat := 324747074411321054291453

theorem tailTrace_948664 : CollatzResearch.WordTrace tailWord_948664 prefixEnd_948664 324747074411321054291453 := by
  unfold tailWord_948664
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300309317579910878662523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23067079090106547838216697 17300309317579910878662523)
  ·
    refine ⟨25950463976369866317993785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17300309317579910878662523 25950463976369866317993785)
    ·
      refine ⟨19462847982277399738495339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25950463976369866317993785 19462847982277399738495339)
      ·
        refine ⟨29194271973416099607743009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19462847982277399738495339 29194271973416099607743009)
        ·
          refine ⟨21895703980062074705807257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29194271973416099607743009 21895703980062074705807257)
          ·
            refine ⟨16421777985046556029355443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21895703980062074705807257 16421777985046556029355443)
            ·
              refine ⟨24632666977569834044033165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16421777985046556029355443 24632666977569834044033165)
              ·
                refine ⟨9237250116588687766512437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24632666977569834044033165 9237250116588687766512437)
                ·
                  refine ⟨865992198430189478110541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9237250116588687766512437 865992198430189478110541)
                  ·
                    refine ⟨324747074411321054291453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 865992198430189478110541 324747074411321054291453)
                    ·
                      rfl

theorem cell22_948664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_948664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948664 prefixEnd_948664 := by exact prefixLift 948664
  have htrace : WordTrace (prefixWord ++ tailWord_948664) baseStart_948664 baseEnd_948664 := by
    simpa [prefixWord, tailWord_948664, baseEnd_948664] using wordTrace_append hprefix tailTrace_948664
  have hstable : (prefixWord ++ tailWord_948664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948664).length < 2 ^ (prefixWord ++ tailWord_948664).sum := by decide
  have hdescent : baseEnd_948664 < baseStart_948664 := by decide
  rcases family_descends (prefixWord ++ tailWord_948664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948698 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_948698 : Nat := 118140960795 + 948698 * 2 ^ 59
def prefixEnd_948698 : Nat := 4983230072969 + 3 ^ 40 * 948698 * 2
def baseEnd_948698 : Nat := 324758713306156298941349

theorem tailTrace_948698 : CollatzResearch.WordTrace tailWord_948698 prefixEnd_948698 324758713306156298941349 := by
  unfold tailWord_948698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8650464679259161391015687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23067905811357763709375165 8650464679259161391015687)
  ·
    refine ⟨12975697018888742086523531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8650464679259161391015687 12975697018888742086523531)
    ·
      refine ⟨19463545528333113129785297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12975697018888742086523531 19463545528333113129785297)
      ·
        refine ⟨14597659146249834847338973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19463545528333113129785297 14597659146249834847338973)
        ·
          refine ⟨5474122179843688067752115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14597659146249834847338973 5474122179843688067752115)
          ·
            refine ⟨8211183269765532101628173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474122179843688067752115 8211183269765532101628173)
            ·
              refine ⟨3079193726162074538110565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8211183269765532101628173 3079193726162074538110565)
              ·
                refine ⟨577348823655388975895731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3079193726162074538110565 577348823655388975895731)
                ·
                  refine ⟨866023235483083463843597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577348823655388975895731 866023235483083463843597)
                  ·
                    refine ⟨324758713306156298941349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866023235483083463843597 324758713306156298941349)
                    ·
                      rfl

theorem cell22_948698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_948698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948698 prefixEnd_948698 := by exact prefixLift 948698
  have htrace : WordTrace (prefixWord ++ tailWord_948698) baseStart_948698 baseEnd_948698 := by
    simpa [prefixWord, tailWord_948698, baseEnd_948698] using wordTrace_append hprefix tailTrace_948698
  have hstable : (prefixWord ++ tailWord_948698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948698).length < 2 ^ (prefixWord ++ tailWord_948698).sum := by decide
  have hdescent : baseEnd_948698 < baseStart_948698 := by decide
  rcases family_descends (prefixWord ++ tailWord_948698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948769 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_948769 : Nat := 118140960795 + 948769 * 2 ^ 59
def prefixEnd_948769 : Nat := 4983230072969 + 3 ^ 40 * 948769 * 2
def baseEnd_948769 : Nat := 324783018057135780416131

theorem tailTrace_948769 : CollatzResearch.WordTrace tailWord_948769 prefixEnd_948769 324783018057135780416131 := by
  unfold tailWord_948769
  simp only [CollatzResearch.WordTrace]
  refine ⟨34604448299779424689897361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23069632199852949793264907 34604448299779424689897361)
  ·
    refine ⟨25953336224834568517423021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34604448299779424689897361 25953336224834568517423021)
    ·
      refine ⟨9732501084312963194033633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25953336224834568517423021 9732501084312963194033633)
      ·
        refine ⟨7299375813234722395525225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9732501084312963194033633 7299375813234722395525225)
        ·
          refine ⟨5474531859926041796643919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299375813234722395525225 5474531859926041796643919)
          ·
            refine ⟨8211797789889062694965879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474531859926041796643919 8211797789889062694965879)
            ·
              refine ⟨12317696684833594042448819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211797789889062694965879 12317696684833594042448819)
              ·
                refine ⟨18476545027250391063673229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12317696684833594042448819 18476545027250391063673229)
                ·
                  refine ⟨6928704385218896648877461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18476545027250391063673229 6928704385218896648877461)
                  ·
                    refine ⟨324783018057135780416131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6928704385218896648877461 324783018057135780416131)
                    ·
                      rfl

theorem cell22_948769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_948769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948769 prefixEnd_948769 := by exact prefixLift 948769
  have htrace : WordTrace (prefixWord ++ tailWord_948769) baseStart_948769 baseEnd_948769 := by
    simpa [prefixWord, tailWord_948769, baseEnd_948769] using wordTrace_append hprefix tailTrace_948769
  have hstable : (prefixWord ++ tailWord_948769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948769).length < 2 ^ (prefixWord ++ tailWord_948769).sum := by decide
  have hdescent : baseEnd_948769 < baseStart_948769 := by decide
  rcases family_descends (prefixWord ++ tailWord_948769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948771 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 1, 5]
def baseStart_948771 : Nat := 118140960795 + 948771 * 2 ^ 59
def prefixEnd_948771 : Nat := 4983230072969 + 3 ^ 40 * 948771 * 2
def baseEnd_948771 : Nat := 324783702698008441866125

theorem tailTrace_948771 : CollatzResearch.WordTrace tailWord_948771 prefixEnd_948771 324783702698008441866125 := by
  unfold tailWord_948771
  simp only [CollatzResearch.WordTrace]
  refine ⟨34604521245772179031470167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23069680830514786020980111 34604521245772179031470167)
  ·
    refine ⟨51906781868658268547205251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34604521245772179031470167 51906781868658268547205251)
    ·
      refine ⟨77860172802987402820807877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51906781868658268547205251 77860172802987402820807877)
      ·
        refine ⟨14598782400560138028901477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77860172802987402820807877 14598782400560138028901477)
        ·
          refine ⟨2737271700105025880419027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14598782400560138028901477 2737271700105025880419027)
          ·
            refine ⟨4105907550157538820628541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737271700105025880419027 4105907550157538820628541)
            ·
              refine ⟨1539715331309077057735703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4105907550157538820628541 1539715331309077057735703)
              ·
                refine ⟨2309572996963615586603555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539715331309077057735703 2309572996963615586603555)
                ·
                  refine ⟨3464359495445423379905333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309572996963615586603555 3464359495445423379905333)
                  ·
                    refine ⟨324783702698008441866125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3464359495445423379905333 324783702698008441866125)
                    ·
                      rfl

theorem cell22_948771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 5].length) (baseStart_948771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948771 prefixEnd_948771 := by exact prefixLift 948771
  have htrace : WordTrace (prefixWord ++ tailWord_948771) baseStart_948771 baseEnd_948771 := by
    simpa [prefixWord, tailWord_948771, baseEnd_948771] using wordTrace_append hprefix tailTrace_948771
  have hstable : (prefixWord ++ tailWord_948771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948771).length < 2 ^ (prefixWord ++ tailWord_948771).sum := by decide
  have hdescent : baseEnd_948771 < baseStart_948771 := by decide
  rcases family_descends (prefixWord ++ tailWord_948771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948790 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_948790 : Nat := 118140960795 + 948790 * 2 ^ 59
def prefixEnd_948790 : Nat := 4983230072969 + 3 ^ 40 * 948790 * 2
def baseEnd_948790 : Nat := 108263402262099575213689

theorem tailTrace_948790 : CollatzResearch.WordTrace tailWord_948790 prefixEnd_948790 108263402262099575213689 := by
  unfold tailWord_948790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162825889543959079775739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23070142821802230184274549 2162825889543959079775739)
  ·
    refine ⟨3244238834315938619663609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162825889543959079775739 3244238834315938619663609)
    ·
      refine ⟨2433179125736953964747707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3244238834315938619663609 2433179125736953964747707)
      ·
        refine ⟨3649768688605430947121561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433179125736953964747707 3649768688605430947121561)
        ·
          refine ⟨2737326516454073210341171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3649768688605430947121561 2737326516454073210341171)
          ·
            refine ⟨4105989774681109815511757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2737326516454073210341171 4105989774681109815511757)
            ·
              refine ⟨1539746165505416180816909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4105989774681109815511757 1539746165505416180816909)
              ·
                refine ⟨577404812064531067806341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1539746165505416180816909 577404812064531067806341)
                ·
                  refine ⟨108263402262099575213689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577404812064531067806341 108263402262099575213689)
                  ·
                    rfl

theorem cell22_948790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_948790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948790 prefixEnd_948790 := by exact prefixLift 948790
  have htrace : WordTrace (prefixWord ++ tailWord_948790) baseStart_948790 baseEnd_948790 := by
    simpa [prefixWord, tailWord_948790, baseEnd_948790] using wordTrace_append hprefix tailTrace_948790
  have hstable : (prefixWord ++ tailWord_948790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948790).length < 2 ^ (prefixWord ++ tailWord_948790).sum := by decide
  have hdescent : baseEnd_948790 < baseStart_948790 := by decide
  rcases family_descends (prefixWord ++ tailWord_948790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948801 : List Nat := [1, 2, 5, 1, 1, 4, 8]
def baseStart_948801 : Nat := 118140960795 + 948801 * 2 ^ 59
def prefixEnd_948801 : Nat := 4983230072969 + 3 ^ 40 * 948801 * 2
def baseEnd_948801 : Nat := 12029406381892531985779

theorem tailTrace_948801 : CollatzResearch.WordTrace tailWord_948801 prefixEnd_948801 12029406381892531985779 := by
  unfold tailWord_948801
  simp only [CollatzResearch.WordTrace]
  refine ⟨34605615435663494155062257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23070410290442329436708171 34605615435663494155062257)
  ·
    refine ⟨25954211576747620616296693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34605615435663494155062257 25954211576747620616296693)
    ·
      refine ⟨2433207335320089432777815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25954211576747620616296693 2433207335320089432777815)
      ·
        refine ⟨3649811002980134149166723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433207335320089432777815 3649811002980134149166723)
        ·
          refine ⟨5474716504470201223750085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649811002980134149166723 5474716504470201223750085)
          ·
            refine ⟨1026509344588162729453141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5474716504470201223750085 1026509344588162729453141)
            ·
              refine ⟨12029406381892531985779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1026509344588162729453141 12029406381892531985779)
              ·
                rfl

theorem cell22_948801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 8].length) (baseStart_948801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948801 prefixEnd_948801 := by exact prefixLift 948801
  have htrace : WordTrace (prefixWord ++ tailWord_948801) baseStart_948801 baseEnd_948801 := by
    simpa [prefixWord, tailWord_948801, baseEnd_948801] using wordTrace_append hprefix tailTrace_948801
  have hstable : (prefixWord ++ tailWord_948801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948801).length < 2 ^ (prefixWord ++ tailWord_948801).sum := by decide
  have hdescent : baseEnd_948801 < baseStart_948801 := by decide
  rcases family_descends (prefixWord ++ tailWord_948801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948816 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_948816 : Nat := 118140960795 + 948816 * 2 ^ 59
def prefixEnd_948816 : Nat := 4983230072969 + 3 ^ 40 * 948816 * 2
def baseEnd_948816 : Nat := 324799107117643324490987

theorem tailTrace_948816 : CollatzResearch.WordTrace tailWord_948816 prefixEnd_948816 324799107117643324490987 := by
  unfold tailWord_948816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17303081265304575858429151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23070775020406101144572201 17303081265304575858429151)
  ·
    refine ⟨25954621897956863787643727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17303081265304575858429151 25954621897956863787643727)
    ·
      refine ⟨38931932846935295681465591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25954621897956863787643727 38931932846935295681465591)
      ·
        refine ⟨58397899270402943522198387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38931932846935295681465591 58397899270402943522198387)
        ·
          refine ⟨87596848905604415283297581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58397899270402943522198387 87596848905604415283297581)
          ·
            refine ⟨32848818339601655731236593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87596848905604415283297581 32848818339601655731236593)
            ·
              refine ⟨24636613754701241798427445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32848818339601655731236593 24636613754701241798427445)
              ·
                refine ⟨2309682539503241418602573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24636613754701241798427445 2309682539503241418602573)
                ·
                  refine ⟨866130952313715531975965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2309682539503241418602573 866130952313715531975965)
                  ·
                    refine ⟨324799107117643324490987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866130952313715531975965 324799107117643324490987)
                    ·
                      rfl

theorem cell22_948816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_948816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948816 prefixEnd_948816 := by exact prefixLift 948816
  have htrace : WordTrace (prefixWord ++ tailWord_948816) baseStart_948816 baseEnd_948816 := by
    simpa [prefixWord, tailWord_948816, baseEnd_948816] using wordTrace_append hprefix tailTrace_948816
  have hstable : (prefixWord ++ tailWord_948816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948816).length < 2 ^ (prefixWord ++ tailWord_948816).sum := by decide
  have hdescent : baseEnd_948816 < baseStart_948816 := by decide
  rcases family_descends (prefixWord ++ tailWord_948816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948921 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_948921 : Nat := 118140960795 + 948921 * 2 ^ 59
def prefixEnd_948921 : Nat := 4983230072969 + 3 ^ 40 * 948921 * 2
def baseEnd_948921 : Nat := 324835050763458050615665

theorem tailTrace_948921 : CollatzResearch.WordTrace tailWord_948921 prefixEnd_948921 324835050763458050615665 := by
  unfold tailWord_948921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34609992195228754649430617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23073328130152503099620411 34609992195228754649430617)
  ·
    refine ⟨25957494146421565987072963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34609992195228754649430617 25957494146421565987072963)
    ·
      refine ⟨38936241219632348980609445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25957494146421565987072963 38936241219632348980609445)
      ·
        refine ⟨7300545228681065433864271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38936241219632348980609445 7300545228681065433864271)
        ·
          refine ⟨10950817843021598150796407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7300545228681065433864271 10950817843021598150796407)
          ·
            refine ⟨16426226764532397226194611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10950817843021598150796407 16426226764532397226194611)
            ·
              refine ⟨24639340146798595839291917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16426226764532397226194611 24639340146798595839291917)
              ·
                refine ⟨9239752555049473439734469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24639340146798595839291917 9239752555049473439734469)
                ·
                  refine ⟨1732453604071776269950213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9239752555049473439734469 1732453604071776269950213)
                  ·
                    refine ⟨324835050763458050615665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1732453604071776269950213 324835050763458050615665)
                    ·
                      rfl

theorem cell22_948921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_948921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948921 prefixEnd_948921 := by exact prefixLift 948921
  have htrace : WordTrace (prefixWord ++ tailWord_948921) baseStart_948921 baseEnd_948921 := by
    simpa [prefixWord, tailWord_948921, baseEnd_948921] using wordTrace_append hprefix tailTrace_948921
  have hstable : (prefixWord ++ tailWord_948921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948921).length < 2 ^ (prefixWord ++ tailWord_948921).sum := by decide
  have hdescent : baseEnd_948921 < baseStart_948921 := by decide
  rcases family_descends (prefixWord ++ tailWord_948921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948940 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_948940 : Nat := 118140960795 + 948940 * 2 ^ 59
def prefixEnd_948940 : Nat := 4983230072969 + 3 ^ 40 * 948940 * 2
def baseEnd_948940 : Nat := 324841554851748334390607

theorem tailTrace_948940 : CollatzResearch.WordTrace tailWord_948940 prefixEnd_948940 324841554851748334390607 := by
  unfold tailWord_948940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17305342591079960447186137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23073790121439947262914849 17305342591079960447186137)
  ·
    refine ⟨12979006943309970335389603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17305342591079960447186137 12979006943309970335389603)
    ·
      refine ⟨19468510414964955503084405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12979006943309970335389603 19468510414964955503084405)
      ·
        refine ⟨1825172851402964578414163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19468510414964955503084405 1825172851402964578414163)
        ·
          refine ⟨2737759277104446867621245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1825172851402964578414163 2737759277104446867621245)
          ·
            refine ⟨1026659728914167575357967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2737759277104446867621245 1026659728914167575357967)
            ·
              refine ⟨1539989593371251363036951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026659728914167575357967 1539989593371251363036951)
              ·
                refine ⟨2309984390056877044555427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539989593371251363036951 2309984390056877044555427)
                ·
                  refine ⟨3464976585085315566833141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309984390056877044555427 3464976585085315566833141)
                  ·
                    refine ⟨324841554851748334390607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3464976585085315566833141 324841554851748334390607)
                    ·
                      rfl

theorem cell22_948940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_948940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948940 prefixEnd_948940 := by exact prefixLift 948940
  have htrace : WordTrace (prefixWord ++ tailWord_948940) baseStart_948940 baseEnd_948940 := by
    simpa [prefixWord, tailWord_948940, baseEnd_948940] using wordTrace_append hprefix tailTrace_948940
  have hstable : (prefixWord ++ tailWord_948940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948940).length < 2 ^ (prefixWord ++ tailWord_948940).sum := by decide
  have hdescent : baseEnd_948940 < baseStart_948940 := by decide
  rcases family_descends (prefixWord ++ tailWord_948940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_948985 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 1, 3]
def baseStart_948985 : Nat := 118140960795 + 948985 * 2 ^ 59
def prefixEnd_948985 : Nat := 4983230072969 + 3 ^ 40 * 948985 * 2
def baseEnd_948985 : Nat := 324856959271383217015469

theorem tailTrace_948985 : CollatzResearch.WordTrace tailWord_948985 prefixEnd_948985 324856959271383217015469 := by
  unfold tailWord_948985
  simp only [CollatzResearch.WordTrace]
  refine ⟨34612326466996893579760409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23074884311331262386506939 34612326466996893579760409)
  ·
    refine ⟨25959244850247670184820307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34612326466996893579760409 25959244850247670184820307)
    ·
      refine ⟨38938867275371505277230461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25959244850247670184820307 38938867275371505277230461)
      ·
        refine ⟨14602075228264314478961423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38938867275371505277230461 14602075228264314478961423)
        ·
          refine ⟨21903112842396471718442135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14602075228264314478961423 21903112842396471718442135)
          ·
            refine ⟨32854669263594707577663203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21903112842396471718442135 32854669263594707577663203)
            ·
              refine ⟨49282003895392061366494805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32854669263594707577663203 49282003895392061366494805)
              ·
                refine ⟨577523483149125719138611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 49282003895392061366494805 577523483149125719138611)
                ·
                  refine ⟨866285224723688578707917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577523483149125719138611 866285224723688578707917)
                  ·
                    refine ⟨324856959271383217015469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866285224723688578707917 324856959271383217015469)
                    ·
                      rfl

theorem cell22_948985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_948985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_948985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_948985 prefixEnd_948985 := by exact prefixLift 948985
  have htrace : WordTrace (prefixWord ++ tailWord_948985) baseStart_948985 baseEnd_948985 := by
    simpa [prefixWord, tailWord_948985, baseEnd_948985] using wordTrace_append hprefix tailTrace_948985
  have hstable : (prefixWord ++ tailWord_948985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_948985).length < 2 ^ (prefixWord ++ tailWord_948985).sum := by decide
  have hdescent : baseEnd_948985 < baseStart_948985 := by decide
  rcases family_descends (prefixWord ++ tailWord_948985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949092 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_949092 : Nat := 118140960795 + 949092 * 2 ^ 59
def prefixEnd_949092 : Nat := 4983230072969 + 3 ^ 40 * 949092 * 2
def baseEnd_949092 : Nat := 324893587558070604590141

theorem tailTrace_949092 : CollatzResearch.WordTrace tailWord_949092 prefixEnd_949092 324893587558070604590141 := by
  unfold tailWord_949092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17308114538804625426952765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23077486051739500569270353 17308114538804625426952765)
  ·
    refine ⟨6490542952051734535107287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17308114538804625426952765 6490542952051734535107287)
    ·
      refine ⟨9735814428077601802660931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490542952051734535107287 9735814428077601802660931)
      ·
        refine ⟨14603721642116402703991397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9735814428077601802660931 14603721642116402703991397)
        ·
          refine ⟨2738197807896825506998387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14603721642116402703991397 2738197807896825506998387)
          ·
            refine ⟨4107296711845238260497581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2738197807896825506998387 4107296711845238260497581)
            ·
              refine ⟨1540236266941964347686593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4107296711845238260497581 1540236266941964347686593)
              ·
                refine ⟨1155177200206473260764945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540236266941964347686593 1155177200206473260764945)
                ·
                  refine ⟨866382900154854945573709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1155177200206473260764945 866382900154854945573709)
                  ·
                    refine ⟨324893587558070604590141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866382900154854945573709 324893587558070604590141)
                    ·
                      rfl

theorem cell22_949092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_949092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949092 prefixEnd_949092 := by exact prefixLift 949092
  have htrace : WordTrace (prefixWord ++ tailWord_949092) baseStart_949092 baseEnd_949092 := by
    simpa [prefixWord, tailWord_949092, baseEnd_949092] using wordTrace_append hprefix tailTrace_949092
  have hstable : (prefixWord ++ tailWord_949092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949092).length < 2 ^ (prefixWord ++ tailWord_949092).sum := by decide
  have hdescent : baseEnd_949092 < baseStart_949092 := by decide
  rcases family_descends (prefixWord ++ tailWord_949092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949109 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_949109 : Nat := 118140960795 + 949109 * 2 ^ 59
def prefixEnd_949109 : Nat := 4983230072969 + 3 ^ 40 * 949109 * 2
def baseEnd_949109 : Nat := 324899407005488226915089

theorem tailTrace_949109 : CollatzResearch.WordTrace tailWord_949109 prefixEnd_949109 324899407005488226915089 := by
  unfold tailWord_949109
  simp only [CollatzResearch.WordTrace]
  refine ⟨34616849118547662757274381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23077899412365108504849587 34616849118547662757274381)
  ·
    refine ⟨12981318419455373533977893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34616849118547662757274381 12981318419455373533977893)
    ·
      refine ⟨2433997203647882537620855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12981318419455373533977893 2433997203647882537620855)
      ·
        refine ⟨3650995805471823806431283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2433997203647882537620855 3650995805471823806431283)
        ·
          refine ⟨5476493708207735709646925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3650995805471823806431283 5476493708207735709646925)
          ·
            refine ⟨2053685140577900891117597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5476493708207735709646925 2053685140577900891117597)
            ·
              refine ⟨770131927716712834169099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2053685140577900891117597 770131927716712834169099)
              ·
                refine ⟨1155197891575069251253649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770131927716712834169099 1155197891575069251253649)
                ·
                  refine ⟨866398418681301938440237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1155197891575069251253649 866398418681301938440237)
                  ·
                    refine ⟨324899407005488226915089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866398418681301938440237 324899407005488226915089)
                    ·
                      rfl

theorem cell22_949109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_949109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949109 prefixEnd_949109 := by exact prefixLift 949109
  have htrace : WordTrace (prefixWord ++ tailWord_949109) baseStart_949109 baseEnd_949109 := by
    simpa [prefixWord, tailWord_949109, baseEnd_949109] using wordTrace_append hprefix tailTrace_949109
  have hstable : (prefixWord ++ tailWord_949109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949109).length < 2 ^ (prefixWord ++ tailWord_949109).sum := by decide
  have hdescent : baseEnd_949109 < baseStart_949109 := by decide
  rcases family_descends (prefixWord ++ tailWord_949109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949154 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_949154 : Nat := 118140960795 + 949154 * 2 ^ 59
def prefixEnd_949154 : Nat := 4983230072969 + 3 ^ 40 * 949154 * 2
def baseEnd_949154 : Nat := 324914811425123109539951

theorem tailTrace_949154 : CollatzResearch.WordTrace tailWord_949154 prefixEnd_949154 324914811425123109539951 := by
  unfold tailWord_949154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654622600846158860665629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23078993602256423628441677 8654622600846158860665629)
  ·
    refine ⟨3245483475317309572749611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8654622600846158860665629 3245483475317309572749611)
    ·
      refine ⟨4868225212975964359124417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245483475317309572749611 4868225212975964359124417)
      ·
        refine ⟨3651168909731973269343313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4868225212975964359124417 3651168909731973269343313)
        ·
          refine ⟨2738376682298979952007485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3651168909731973269343313 2738376682298979952007485)
          ·
            refine ⟨1026891255862117482002807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2738376682298979952007485 1026891255862117482002807)
            ·
              refine ⟨1540336883793176223004211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026891255862117482002807 1540336883793176223004211)
              ·
                refine ⟨2310505325689764334506317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540336883793176223004211 2310505325689764334506317)
                ·
                  refine ⟨866439497133661625439869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2310505325689764334506317 866439497133661625439869)
                  ·
                    refine ⟨324914811425123109539951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866439497133661625439869 324914811425123109539951)
                    ·
                      rfl

theorem cell22_949154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_949154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949154 prefixEnd_949154 := by exact prefixLift 949154
  have htrace : WordTrace (prefixWord ++ tailWord_949154) baseStart_949154 baseEnd_949154 := by
    simpa [prefixWord, tailWord_949154, baseEnd_949154] using wordTrace_append hprefix tailTrace_949154
  have hstable : (prefixWord ++ tailWord_949154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949154).length < 2 ^ (prefixWord ++ tailWord_949154).sum := by decide
  have hdescent : baseEnd_949154 < baseStart_949154 := by decide
  rcases family_descends (prefixWord ++ tailWord_949154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 5, 4]
def baseStart_949163 : Nat := 118140960795 + 949163 * 2 ^ 59
def prefixEnd_949163 : Nat := 4983230072969 + 3 ^ 40 * 949163 * 2
def baseEnd_949163 : Nat := 324917892309050086064923

theorem tailTrace_949163 : CollatzResearch.WordTrace tailWord_949163 prefixEnd_949163 324917892309050086064923 := by
  unfold tailWord_949163
  simp only [CollatzResearch.WordTrace]
  refine ⟨34618818660352029979740143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23079212440234686653160095 34618818660352029979740143)
  ·
    refine ⟨51928227990528044969610215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34618818660352029979740143 51928227990528044969610215)
    ·
      refine ⟨77892341985792067454415323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51928227990528044969610215 77892341985792067454415323)
      ·
        refine ⟨116838512978688101181622985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77892341985792067454415323 116838512978688101181622985)
        ·
          refine ⟨87628884734016075886217239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116838512978688101181622985 87628884734016075886217239)
          ·
            refine ⟨131443327101024113829325859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87628884734016075886217239 131443327101024113829325859)
            ·
              refine ⟨197164990651536170743988789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131443327101024113829325859 197164990651536170743988789)
              ·
                refine ⟨18484217873581516007248949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 197164990651536170743988789 18484217873581516007248949)
                ·
                  refine ⟨1732895425648267125679589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18484217873581516007248949 1732895425648267125679589)
                  ·
                    refine ⟨324917892309050086064923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1732895425648267125679589 324917892309050086064923)
                    ·
                      rfl

theorem cell22_949163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 4].length) (baseStart_949163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949163 prefixEnd_949163 := by exact prefixLift 949163
  have htrace : WordTrace (prefixWord ++ tailWord_949163) baseStart_949163 baseEnd_949163 := by
    simpa [prefixWord, tailWord_949163, baseEnd_949163] using wordTrace_append hprefix tailTrace_949163
  have hstable : (prefixWord ++ tailWord_949163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949163).length < 2 ^ (prefixWord ++ tailWord_949163).sum := by decide
  have hdescent : baseEnd_949163 < baseStart_949163 := by decide
  rcases family_descends (prefixWord ++ tailWord_949163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949178 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_949178 : Nat := 118140960795 + 949178 * 2 ^ 59
def prefixEnd_949178 : Nat := 4983230072969 + 3 ^ 40 * 949178 * 2
def baseEnd_949178 : Nat := 108307675705198348979959

theorem tailTrace_949178 : CollatzResearch.WordTrace tailWord_949178 prefixEnd_949178 108307675705198348979959 := by
  unfold tailWord_949178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8654841438824421885384047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23079577170198458361024125 8654841438824421885384047)
  ·
    refine ⟨12982262158236632828076071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8654841438824421885384047 12982262158236632828076071)
    ·
      refine ⟨19473393237354949242114107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12982262158236632828076071 19473393237354949242114107)
      ·
        refine ⟨29210089856032423863171161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19473393237354949242114107 29210089856032423863171161)
        ·
          refine ⟨21907567392024317897378371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29210089856032423863171161 21907567392024317897378371)
          ·
            refine ⟨32861351088036476846067557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21907567392024317897378371 32861351088036476846067557)
            ·
              refine ⟨6161503329006839408637667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32861351088036476846067557 6161503329006839408637667)
              ·
                refine ⟨9242254993510259112956501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6161503329006839408637667 9242254993510259112956501)
                ·
                  refine ⟨108307675705198348979959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9242254993510259112956501 108307675705198348979959)
                  ·
                    rfl

theorem cell22_949178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_949178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949178 prefixEnd_949178 := by exact prefixLift 949178
  have htrace : WordTrace (prefixWord ++ tailWord_949178) baseStart_949178 baseEnd_949178 := by
    simpa [prefixWord, tailWord_949178, baseEnd_949178] using wordTrace_append hprefix tailTrace_949178
  have hstable : (prefixWord ++ tailWord_949178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949178).length < 2 ^ (prefixWord ++ tailWord_949178).sum := by decide
  have hdescent : baseEnd_949178 < baseStart_949178 := by decide
  rcases family_descends (prefixWord ++ tailWord_949178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949246 : List Nat := [4, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_949246 : Nat := 118140960795 + 949246 * 2 ^ 59
def prefixEnd_949246 : Nat := 4983230072969 + 3 ^ 40 * 949246 * 2
def baseEnd_949246 : Nat := 108315434968421845413223

theorem tailTrace_949246 : CollatzResearch.WordTrace tailWord_949246 prefixEnd_949246 108315434968421845413223 := by
  unfold tailWord_949246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327730739881416894376449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23081230612700890103341061 4327730739881416894376449)
  ·
    refine ⟨3245798054911062670782337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4327730739881416894376449 3245798054911062670782337)
    ·
      refine ⟨2434348541183297003086753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3245798054911062670782337 2434348541183297003086753)
      ·
        refine ⟨1825761405887472752315065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2434348541183297003086753 1825761405887472752315065)
        ·
          refine ⟨1369321054415604564236299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825761405887472752315065 1369321054415604564236299)
          ·
            refine ⟨2053981581623406846354449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1369321054415604564236299 2053981581623406846354449)
            ·
              refine ⟨1540486186217555134765837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2053981581623406846354449 1540486186217555134765837)
              ·
                refine ⟨577682319831583175537189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1540486186217555134765837 577682319831583175537189)
                ·
                  refine ⟨108315434968421845413223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 577682319831583175537189 108315434968421845413223)
                  ·
                    rfl

theorem cell22_949246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_949246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949246 prefixEnd_949246 := by exact prefixLift 949246
  have htrace : WordTrace (prefixWord ++ tailWord_949246) baseStart_949246 baseEnd_949246 := by
    simpa [prefixWord, tailWord_949246, baseEnd_949246] using wordTrace_append hprefix tailTrace_949246
  have hstable : (prefixWord ++ tailWord_949246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949246).length < 2 ^ (prefixWord ++ tailWord_949246).sum := by decide
  have hdescent : baseEnd_949246 < baseStart_949246 := by decide
  rcases family_descends (prefixWord ++ tailWord_949246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949272 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_949272 : Nat := 118140960795 + 949272 * 2 ^ 59
def prefixEnd_949272 : Nat := 4983230072969 + 3 ^ 40 * 949272 * 2
def baseEnd_949272 : Nat := 324955205236610135089589

theorem tailTrace_949272 : CollatzResearch.WordTrace tailWord_949272 prefixEnd_949272 324955205236610135089589 := by
  unfold tailWord_949272
  simp only [CollatzResearch.WordTrace]
  refine ⟨17311397108478570797729035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23081862811304761063638713 17311397108478570797729035)
  ·
    refine ⟨25967095662717856196593553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17311397108478570797729035 25967095662717856196593553)
    ·
      refine ⟨19475321747038392147445165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25967095662717856196593553 19475321747038392147445165)
      ·
        refine ⟨7303245655139397055291937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19475321747038392147445165 7303245655139397055291937)
        ·
          refine ⟨5477434241354547791468953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7303245655139397055291937 5477434241354547791468953)
          ·
            refine ⟨4108075681015910843601715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477434241354547791468953 4108075681015910843601715)
            ·
              refine ⟨6162113521523866265402573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108075681015910843601715 6162113521523866265402573)
              ·
                refine ⟨2310792570571449849525965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6162113521523866265402573 2310792570571449849525965)
                ·
                  refine ⟨866547213964293693572237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2310792570571449849525965 866547213964293693572237)
                  ·
                    refine ⟨324955205236610135089589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866547213964293693572237 324955205236610135089589)
                    ·
                      rfl

theorem cell22_949272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_949272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949272 prefixEnd_949272 := by exact prefixLift 949272
  have htrace : WordTrace (prefixWord ++ tailWord_949272) baseStart_949272 baseEnd_949272 := by
    simpa [prefixWord, tailWord_949272, baseEnd_949272] using wordTrace_append hprefix tailTrace_949272
  have hstable : (prefixWord ++ tailWord_949272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949272).length < 2 ^ (prefixWord ++ tailWord_949272).sum := by decide
  have hdescent : baseEnd_949272 < baseStart_949272 := by decide
  rcases family_descends (prefixWord ++ tailWord_949272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949302 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_949302 : Nat := 118140960795 + 949302 * 2 ^ 59
def prefixEnd_949302 : Nat := 4983230072969 + 3 ^ 40 * 949302 * 2
def baseEnd_949302 : Nat := 108321824949900018946499

theorem tailTrace_949302 : CollatzResearch.WordTrace tailWord_949302 prefixEnd_949302 108321824949900018946499 := by
  unfold tailWord_949302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163993025428028544940635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23082592271232304479366773 2163993025428028544940635)
  ·
    refine ⟨3245989538142042817410953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163993025428028544940635 3245989538142042817410953)
    ·
      refine ⟨2434492153606532113058215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3245989538142042817410953 2434492153606532113058215)
      ·
        refine ⟨3651738230409798169587323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2434492153606532113058215 3651738230409798169587323)
        ·
          refine ⟨5477607345614697254380985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651738230409798169587323 5477607345614697254380985)
          ·
            refine ⟨4108205509211022940785739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5477607345614697254380985 4108205509211022940785739)
            ·
              refine ⟨6162308263816534411178609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108205509211022940785739 6162308263816534411178609)
              ·
                refine ⟨4621731197862400808383957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6162308263816534411178609 4621731197862400808383957)
                ·
                  refine ⟨108321824949900018946499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4621731197862400808383957 108321824949900018946499)
                  ·
                    rfl

theorem cell22_949302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_949302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949302 prefixEnd_949302 := by exact prefixLift 949302
  have htrace : WordTrace (prefixWord ++ tailWord_949302) baseStart_949302 baseEnd_949302 := by
    simpa [prefixWord, tailWord_949302, baseEnd_949302] using wordTrace_append hprefix tailTrace_949302
  have hstable : (prefixWord ++ tailWord_949302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949302).length < 2 ^ (prefixWord ++ tailWord_949302).sum := by decide
  have hdescent : baseEnd_949302 < baseStart_949302 := by decide
  rcases family_descends (prefixWord ++ tailWord_949302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949362 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_949362 : Nat := 118140960795 + 949362 * 2 ^ 59
def prefixEnd_949362 : Nat := 4983230072969 + 3 ^ 40 * 949362 * 2
def baseEnd_949362 : Nat := 324986014075879900339313

theorem tailTrace_949362 : CollatzResearch.WordTrace tailWord_949362 prefixEnd_949362 324986014075879900339313 := by
  unfold tailWord_949362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8656519196657771741558585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23084051191087391310822893 8656519196657771741558585)
  ·
    refine ⟨6492389397493328806168939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8656519196657771741558585 6492389397493328806168939)
    ·
      refine ⟨9738584096239993209253409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6492389397493328806168939 9738584096239993209253409)
      ·
        refine ⟨7303938072179994906940057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9738584096239993209253409 7303938072179994906940057)
        ·
          refine ⟨5477953554134996180205043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7303938072179994906940057 5477953554134996180205043)
          ·
            refine ⟨8216930331202494270307565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477953554134996180205043 8216930331202494270307565)
            ·
              refine ⟨3081348874200935351365337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8216930331202494270307565 3081348874200935351365337)
              ·
                refine ⟨2311011655650701513524003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081348874200935351365337 2311011655650701513524003)
                ·
                  refine ⟨3466517483476052270286005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2311011655650701513524003 3466517483476052270286005)
                  ·
                    refine ⟨324986014075879900339313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3466517483476052270286005 324986014075879900339313)
                    ·
                      rfl

theorem cell22_949362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_949362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949362 prefixEnd_949362 := by exact prefixLift 949362
  have htrace : WordTrace (prefixWord ++ tailWord_949362) baseStart_949362 baseEnd_949362 := by
    simpa [prefixWord, tailWord_949362, baseEnd_949362] using wordTrace_append hprefix tailTrace_949362
  have hstable : (prefixWord ++ tailWord_949362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949362).length < 2 ^ (prefixWord ++ tailWord_949362).sum := by decide
  have hdescent : baseEnd_949362 < baseStart_949362 := by decide
  rcases family_descends (prefixWord ++ tailWord_949362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949366 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_949366 : Nat := 118140960795 + 949366 * 2 ^ 59
def prefixEnd_949366 : Nat := 4983230072969 + 3 ^ 40 * 949366 * 2
def baseEnd_949366 : Nat := 324987383357625223239301

theorem tailTrace_949366 : CollatzResearch.WordTrace tailWord_949366 prefixEnd_949366 324987383357625223239301 := by
  unfold tailWord_949366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2164138917413537228086247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 23084148452411063766253301 2164138917413537228086247)
  ·
    refine ⟨3246208376120305842129371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2164138917413537228086247 3246208376120305842129371)
    ·
      refine ⟨4869312564180458763194057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3246208376120305842129371 4869312564180458763194057)
      ·
        refine ⟨3651984423135344072395543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4869312564180458763194057 3651984423135344072395543)
        ·
          refine ⟨5477976634703016108593315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3651984423135344072395543 5477976634703016108593315)
          ·
            refine ⟨8216964952054524162889973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5477976634703016108593315 8216964952054524162889973)
            ·
              refine ⟨770340464255111640270935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8216964952054524162889973 770340464255111640270935)
              ·
                refine ⟨1155510696382667460406403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770340464255111640270935 1155510696382667460406403)
                ·
                  refine ⟨1733266044574001190609605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155510696382667460406403 1733266044574001190609605)
                  ·
                    refine ⟨324987383357625223239301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1733266044574001190609605 324987383357625223239301)
                    ·
                      rfl

theorem cell22_949366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_949366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949366 prefixEnd_949366 := by exact prefixLift 949366
  have htrace : WordTrace (prefixWord ++ tailWord_949366) baseStart_949366 baseEnd_949366 := by
    simpa [prefixWord, tailWord_949366, baseEnd_949366] using wordTrace_append hprefix tailTrace_949366
  have hstable : (prefixWord ++ tailWord_949366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949366).length < 2 ^ (prefixWord ++ tailWord_949366).sum := by decide
  have hdescent : baseEnd_949366 < baseStart_949366 := by decide
  rcases family_descends (prefixWord ++ tailWord_949366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949374 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_949374 : Nat := 118140960795 + 949374 * 2 ^ 59
def prefixEnd_949374 : Nat := 4983230072969 + 3 ^ 40 * 949374 * 2
def baseEnd_949374 : Nat := 324990121921115869039277

theorem tailTrace_949374 : CollatzResearch.WordTrace tailWord_949374 prefixEnd_949374 324990121921115869039277 := by
  unfold tailWord_949374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4328314307823451626958897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23084342975058408677114117 4328314307823451626958897)
  ·
    refine ⟨3246235730867588720219173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4328314307823451626958897 3246235730867588720219173)
    ·
      refine ⟨608669199537672885041095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3246235730867588720219173 608669199537672885041095)
      ·
        refine ⟨913003799306509327561643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608669199537672885041095 913003799306509327561643)
        ·
          refine ⟨1369505698959763991342465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913003799306509327561643 1369505698959763991342465)
          ·
            refine ⟨1027129274219822993506849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369505698959763991342465 1027129274219822993506849)
            ·
              refine ⟨770346955664867245130137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027129274219822993506849 770346955664867245130137)
              ·
                refine ⟨577760216748650433847603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770346955664867245130137 577760216748650433847603)
                ·
                  refine ⟨866640325122975650771405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577760216748650433847603 866640325122975650771405)
                  ·
                    refine ⟨324990121921115869039277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866640325122975650771405 324990121921115869039277)
                    ·
                      rfl

theorem cell22_949374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_949374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949374 prefixEnd_949374 := by exact prefixLift 949374
  have htrace : WordTrace (prefixWord ++ tailWord_949374) baseStart_949374 baseEnd_949374 := by
    simpa [prefixWord, tailWord_949374, baseEnd_949374] using wordTrace_append hprefix tailTrace_949374
  have hstable : (prefixWord ++ tailWord_949374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949374).length < 2 ^ (prefixWord ++ tailWord_949374).sum := by decide
  have hdescent : baseEnd_949374 < baseStart_949374 := by decide
  rcases family_descends (prefixWord ++ tailWord_949374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949379 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 2, 3]
def baseStart_949379 : Nat := 118140960795 + 949379 * 2 ^ 59
def prefixEnd_949379 : Nat := 4983230072969 + 3 ^ 40 * 949379 * 2
def baseEnd_949379 : Nat := 324991833523297522664261

theorem tailTrace_949379 : CollatzResearch.WordTrace tailWord_949379 prefixEnd_949379 324991833523297522664261 := by
  unfold tailWord_949379
  simp only [CollatzResearch.WordTrace]
  refine ⟨34626696827569498869603191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23084464551712999246402127 34626696827569498869603191)
  ·
    refine ⟨51940045241354248304404787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34626696827569498869603191 51940045241354248304404787)
    ·
      refine ⟨77910067862031372456607181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51940045241354248304404787 77910067862031372456607181)
      ·
        refine ⟨29216275448261764671227693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77910067862031372456607181 29216275448261764671227693)
        ·
          refine ⟨10956103293098161751710385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29216275448261764671227693 10956103293098161751710385)
          ·
            refine ⟨8217077469823621313782789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10956103293098161751710385 8217077469823621313782789)
            ·
              refine ⟨1540702025591928996334273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8217077469823621313782789 1540702025591928996334273)
              ·
                refine ⟨1155526519193946747250705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1540702025591928996334273 1155526519193946747250705)
                ·
                  refine ⟨866644889395460060438029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1155526519193946747250705 866644889395460060438029)
                  ·
                    refine ⟨324991833523297522664261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866644889395460060438029 324991833523297522664261)
                    ·
                      rfl

theorem cell22_949379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 3].length) (baseStart_949379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949379 prefixEnd_949379 := by exact prefixLift 949379
  have htrace : WordTrace (prefixWord ++ tailWord_949379) baseStart_949379 baseEnd_949379 := by
    simpa [prefixWord, tailWord_949379, baseEnd_949379] using wordTrace_append hprefix tailTrace_949379
  have hstable : (prefixWord ++ tailWord_949379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949379).length < 2 ^ (prefixWord ++ tailWord_949379).sum := by decide
  have hdescent : baseEnd_949379 < baseStart_949379 := by decide
  rcases family_descends (prefixWord ++ tailWord_949379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949441 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_949441 : Nat := 118140960795 + 949441 * 2 ^ 59
def prefixEnd_949441 : Nat := 4983230072969 + 3 ^ 40 * 949441 * 2
def baseEnd_949441 : Nat := 325013057390350027614071

theorem tailTrace_949441 : CollatzResearch.WordTrace tailWord_949441 prefixEnd_949441 325013057390350027614071 := by
  unfold tailWord_949441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34628958153344883458360177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23085972102229922305573451 34628958153344883458360177)
  ·
    refine ⟨25971718615008662593770133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34628958153344883458360177 25971718615008662593770133)
    ·
      refine ⟨1217424310078531059082975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25971718615008662593770133 1217424310078531059082975)
      ·
        refine ⟨1826136465117796588624463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1217424310078531059082975 1826136465117796588624463)
        ·
          refine ⟨2739204697676694882936695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826136465117796588624463 2739204697676694882936695)
          ·
            refine ⟨4108807046515042324405043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739204697676694882936695 4108807046515042324405043)
            ·
              refine ⟨6163210569772563486607565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4108807046515042324405043 6163210569772563486607565)
              ·
                refine ⟨2311203963664711307477837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6163210569772563486607565 2311203963664711307477837)
                ·
                  refine ⟨866701486374266740304189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2311203963664711307477837 866701486374266740304189)
                  ·
                    refine ⟨325013057390350027614071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866701486374266740304189 325013057390350027614071)
                    ·
                      rfl

theorem cell22_949441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_949441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949441 prefixEnd_949441 := by exact prefixLift 949441
  have htrace : WordTrace (prefixWord ++ tailWord_949441) baseStart_949441 baseEnd_949441 := by
    simpa [prefixWord, tailWord_949441, baseEnd_949441] using wordTrace_append hprefix tailTrace_949441
  have hstable : (prefixWord ++ tailWord_949441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949441).length < 2 ^ (prefixWord ++ tailWord_949441).sum := by decide
  have hdescent : baseEnd_949441 < baseStart_949441 := by decide
  rcases family_descends (prefixWord ++ tailWord_949441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949484 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_949484 : Nat := 118140960795 + 949484 * 2 ^ 59
def prefixEnd_949484 : Nat := 4983230072969 + 3 ^ 40 * 949484 * 2
def baseEnd_949484 : Nat := 325027777169112248788939

theorem tailTrace_949484 : CollatzResearch.WordTrace tailWord_949484 prefixEnd_949484 325027777169112248788939 := by
  unfold tailWord_949484
  simp only [CollatzResearch.WordTrace]
  refine ⟨17315263246094550901087753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23087017661459401201450337 17315263246094550901087753)
  ·
    refine ⟨12986447434570913175815815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17315263246094550901087753 12986447434570913175815815)
    ·
      refine ⟨19479671151856369763723723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12986447434570913175815815 19479671151856369763723723)
      ·
        refine ⟨29219506727784554645585585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19479671151856369763723723 29219506727784554645585585)
        ·
          refine ⟨21914630045838415984189189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29219506727784554645585585 21914630045838415984189189)
          ·
            refine ⟨4108993133594702997035473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21914630045838415984189189 4108993133594702997035473)
            ·
              refine ⟨3081744850196027247776605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4108993133594702997035473 3081744850196027247776605)
              ·
                refine ⟨1155654318823510217916227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3081744850196027247776605 1155654318823510217916227)
                ·
                  refine ⟨1733481478235265326874341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155654318823510217916227 1733481478235265326874341)
                  ·
                    refine ⟨325027777169112248788939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1733481478235265326874341 325027777169112248788939)
                    ·
                      rfl

theorem cell22_949484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_949484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949484 prefixEnd_949484 := by exact prefixLift 949484
  have htrace : WordTrace (prefixWord ++ tailWord_949484) baseStart_949484 baseEnd_949484 := by
    simpa [prefixWord, tailWord_949484, baseEnd_949484] using wordTrace_append hprefix tailTrace_949484
  have hstable : (prefixWord ++ tailWord_949484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949484).length < 2 ^ (prefixWord ++ tailWord_949484).sum := by decide
  have hdescent : baseEnd_949484 < baseStart_949484 := by decide
  rcases family_descends (prefixWord ++ tailWord_949484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949492 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_949492 : Nat := 118140960795 + 949492 * 2 ^ 59
def prefixEnd_949492 : Nat := 4983230072969 + 3 ^ 40 * 949492 * 2
def baseEnd_949492 : Nat := 325030515732602894588915

theorem tailTrace_949492 : CollatzResearch.WordTrace tailWord_949492 prefixEnd_949492 325030515732602894588915 := by
  unfold tailWord_949492
  simp only [CollatzResearch.WordTrace]
  refine ⟨17315409138080059584233365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23087212184106746112311153 17315409138080059584233365)
  ·
    refine ⟨811659803347502793010939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17315409138080059584233365 811659803347502793010939)
    ·
      refine ⟨1217489705021254189516409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811659803347502793010939 1217489705021254189516409)
      ·
        refine ⟨913117278765940642137307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1217489705021254189516409 913117278765940642137307)
        ·
          refine ⟨1369675918148910963205961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913117278765940642137307 1369675918148910963205961)
          ·
            refine ⟨1027256938611683222404471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369675918148910963205961 1027256938611683222404471)
            ·
              refine ⟨1540885407917524833606707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027256938611683222404471 1540885407917524833606707)
              ·
                refine ⟨2311328111876287250410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1540885407917524833606707 2311328111876287250410061)
                ·
                  refine ⟨866748041953607718903773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2311328111876287250410061 866748041953607718903773)
                  ·
                    refine ⟨325030515732602894588915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866748041953607718903773 325030515732602894588915)
                    ·
                      rfl

theorem cell22_949492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_949492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949492 prefixEnd_949492 := by exact prefixLift 949492
  have htrace : WordTrace (prefixWord ++ tailWord_949492) baseStart_949492 baseEnd_949492 := by
    simpa [prefixWord, tailWord_949492, baseEnd_949492] using wordTrace_append hprefix tailTrace_949492
  have hstable : (prefixWord ++ tailWord_949492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949492).length < 2 ^ (prefixWord ++ tailWord_949492).sum := by decide
  have hdescent : baseEnd_949492 < baseStart_949492 := by decide
  rcases family_descends (prefixWord ++ tailWord_949492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949527 : List Nat := [1, 1, 3, 4, 1, 1, 1, 10]
def baseStart_949527 : Nat := 118140960795 + 949527 * 2 ^ 59
def prefixEnd_949527 : Nat := 4983230072969 + 3 ^ 40 * 949527 * 2
def baseEnd_949527 : Nat := 36115832994208274440423

theorem tailTrace_949527 : CollatzResearch.WordTrace tailWord_949527 prefixEnd_949527 36115832994208274440423 := by
  unfold tailWord_949527
  simp only [CollatzResearch.WordTrace]
  refine ⟨34632094831033320145990835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23088063220688880097327223 34632094831033320145990835)
  ·
    refine ⟨51948142246549980218986253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34632094831033320145990835 51948142246549980218986253)
    ·
      refine ⟨19480553342456242582119845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51948142246549980218986253 19480553342456242582119845)
      ·
        refine ⟨3652603751710545484147471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19480553342456242582119845 3652603751710545484147471)
        ·
          refine ⟨5478905627565818226221207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3652603751710545484147471 5478905627565818226221207)
          ·
            refine ⟨8218358441348727339331811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5478905627565818226221207 8218358441348727339331811)
            ·
              refine ⟨12327537662023091008997717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8218358441348727339331811 12327537662023091008997717)
              ·
                refine ⟨36115832994208274440423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12327537662023091008997717 36115832994208274440423)
                ·
                  rfl

theorem cell22_949527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 10].length) (baseStart_949527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949527 prefixEnd_949527 := by exact prefixLift 949527
  have htrace : WordTrace (prefixWord ++ tailWord_949527) baseStart_949527 baseEnd_949527 := by
    simpa [prefixWord, tailWord_949527, baseEnd_949527] using wordTrace_append hprefix tailTrace_949527
  have hstable : (prefixWord ++ tailWord_949527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949527).length < 2 ^ (prefixWord ++ tailWord_949527).sum := by decide
  have hdescent : baseEnd_949527 < baseStart_949527 := by decide
  rcases family_descends (prefixWord ++ tailWord_949527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949546 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 2, 4]
def baseStart_949546 : Nat := 118140960795 + 949546 * 2 ^ 59
def prefixEnd_949546 : Nat := 4983230072969 + 3 ^ 40 * 949546 * 2
def baseEnd_949546 : Nat := 325049001036164753738749

theorem tailTrace_949546 : CollatzResearch.WordTrace tailWord_949546 prefixEnd_949546 325049001036164753738749 := by
  unfold tailWord_949546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8658196954491121597733123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23088525211976324260621661 8658196954491121597733123)
  ·
    refine ⟨12987295431736682396599685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8658196954491121597733123 12987295431736682396599685)
    ·
      refine ⟨2435117893450627949362441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12987295431736682396599685 2435117893450627949362441)
      ·
        refine ⟨1826338420087970962021831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2435117893450627949362441 1826338420087970962021831)
        ·
          refine ⟨2739507630131956443032747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826338420087970962021831 2739507630131956443032747)
          ·
            refine ⟨4109261445197934664549121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2739507630131956443032747 4109261445197934664549121)
            ·
              refine ⟨3081946083898450998411841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4109261445197934664549121 3081946083898450998411841)
              ·
                refine ⟨2311459562923838248808881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3081946083898450998411841 2311459562923838248808881)
                ·
                  refine ⟨1733594672192878686606661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2311459562923838248808881 1733594672192878686606661)
                  ·
                    refine ⟨325049001036164753738749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1733594672192878686606661 325049001036164753738749)
                    ·
                      rfl

theorem cell22_949546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_949546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949546 prefixEnd_949546 := by exact prefixLift 949546
  have htrace : WordTrace (prefixWord ++ tailWord_949546) baseStart_949546 baseEnd_949546 := by
    simpa [prefixWord, tailWord_949546, baseEnd_949546] using wordTrace_append hprefix tailTrace_949546
  have hstable : (prefixWord ++ tailWord_949546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949546).length < 2 ^ (prefixWord ++ tailWord_949546).sum := by decide
  have hdescent : baseEnd_949546 < baseStart_949546 := by decide
  rcases family_descends (prefixWord ++ tailWord_949546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949561 : List Nat := [1, 2, 1, 6, 2, 2, 1, 7]
def baseStart_949561 : Nat := 118140960795 + 949561 * 2 ^ 59
def prefixEnd_949561 : Nat := 4983230072969 + 3 ^ 40 * 949561 * 2
def baseEnd_949561 : Nat := 36117126204745523845967

theorem tailTrace_949561 : CollatzResearch.WordTrace tailWord_949561 prefixEnd_949561 36117126204745523845967 := by
  unfold tailWord_949561
  simp only [CollatzResearch.WordTrace]
  refine ⟨34633334912910143952728537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23088889941940095968485691 34633334912910143952728537)
  ·
    refine ⟨25975001184682607964546403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34633334912910143952728537 25975001184682607964546403)
    ·
      refine ⟨38962501777023911946819605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25975001184682607964546403 38962501777023911946819605)
      ·
        refine ⟨1826367270797995872507169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38962501777023911946819605 1826367270797995872507169)
        ·
          refine ⟨1369775453098496904380377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1826367270797995872507169 1369775453098496904380377)
          ·
            refine ⟨1027331589823872678285283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1369775453098496904380377 1027331589823872678285283)
            ·
              refine ⟨1540997384735809017427925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027331589823872678285283 1540997384735809017427925)
              ·
                refine ⟨36117126204745523845967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1540997384735809017427925 36117126204745523845967)
                ·
                  rfl

theorem cell22_949561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 7].length) (baseStart_949561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949561 prefixEnd_949561 := by exact prefixLift 949561
  have htrace : WordTrace (prefixWord ++ tailWord_949561) baseStart_949561 baseEnd_949561 := by
    simpa [prefixWord, tailWord_949561, baseEnd_949561] using wordTrace_append hprefix tailTrace_949561
  have hstable : (prefixWord ++ tailWord_949561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949561).length < 2 ^ (prefixWord ++ tailWord_949561).sum := by decide
  have hdescent : baseEnd_949561 < baseStart_949561 := by decide
  rcases family_descends (prefixWord ++ tailWord_949561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949587 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 7]
def baseStart_949587 : Nat := 118140960795 + 949587 * 2 ^ 59
def prefixEnd_949587 : Nat := 4983230072969 + 3 ^ 40 * 949587 * 2
def baseEnd_949587 : Nat := 325063036174054313463623

theorem tailTrace_949587 : CollatzResearch.WordTrace tailWord_949587 prefixEnd_949587 325063036174054313463623 := by
  unfold tailWord_949587
  simp only [CollatzResearch.WordTrace]
  refine ⟨34634283210815950393175015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23089522140543966928783343 34634283210815950393175015)
  ·
    refine ⟨51951424816223925589762523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34634283210815950393175015 51951424816223925589762523)
    ·
      refine ⟨77927137224335888384643785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51951424816223925589762523 77927137224335888384643785)
      ·
        refine ⟨58445352918251916288482839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77927137224335888384643785 58445352918251916288482839)
        ·
          refine ⟨87668029377377874432724259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58445352918251916288482839 87668029377377874432724259)
          ·
            refine ⟨131502044066066811649086389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87668029377377874432724259 131502044066066811649086389)
            ·
              refine ⟨12328316631193763592101849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131502044066066811649086389 12328316631193763592101849)
              ·
                refine ⟨9246237473395322694076387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12328316631193763592101849 9246237473395322694076387)
                ·
                  refine ⟨13869356210092984041114581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9246237473395322694076387 13869356210092984041114581)
                  ·
                    refine ⟨325063036174054313463623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13869356210092984041114581 325063036174054313463623)
                    ·
                      rfl

theorem cell22_949587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_949587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949587 prefixEnd_949587 := by exact prefixLift 949587
  have htrace : WordTrace (prefixWord ++ tailWord_949587) baseStart_949587 baseEnd_949587 := by
    simpa [prefixWord, tailWord_949587, baseEnd_949587] using wordTrace_append hprefix tailTrace_949587
  have hstable : (prefixWord ++ tailWord_949587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949587).length < 2 ^ (prefixWord ++ tailWord_949587).sum := by decide
  have hdescent : baseEnd_949587 < baseStart_949587 := by decide
  rcases family_descends (prefixWord ++ tailWord_949587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949604 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_949604 : Nat := 118140960795 + 949604 * 2 ^ 59
def prefixEnd_949604 : Nat := 4983230072969 + 3 ^ 40 * 949604 * 2
def baseEnd_949604 : Nat := 325068855621471935788571

theorem tailTrace_949604 : CollatzResearch.WordTrace tailWord_949604 prefixEnd_949604 325068855621471935788571 := by
  unfold tailWord_949604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17317451625877181148271933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23089935501169574864362577 17317451625877181148271933)
  ·
    refine ⟨6494044359703942930601975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17317451625877181148271933 6494044359703942930601975)
    ·
      refine ⟨9741066539555914395902963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6494044359703942930601975 9741066539555914395902963)
      ·
        refine ⟨14611599809333871593854445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9741066539555914395902963 14611599809333871593854445)
        ·
          refine ⟨5479349928500201847695417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14611599809333871593854445 5479349928500201847695417)
          ·
            refine ⟨4109512446375151385771563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5479349928500201847695417 4109512446375151385771563)
            ·
              refine ⟨6164268669562727078657345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109512446375151385771563 6164268669562727078657345)
              ·
                refine ⟨4623201502172045308993009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6164268669562727078657345 4623201502172045308993009)
                ·
                  refine ⟨3467401126629033981744757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4623201502172045308993009 3467401126629033981744757)
                  ·
                    refine ⟨325068855621471935788571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3467401126629033981744757 325068855621471935788571)
                    ·
                      rfl

theorem cell22_949604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_949604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949604 prefixEnd_949604 := by exact prefixLift 949604
  have htrace : WordTrace (prefixWord ++ tailWord_949604) baseStart_949604 baseEnd_949604 := by
    simpa [prefixWord, tailWord_949604, baseEnd_949604] using wordTrace_append hprefix tailTrace_949604
  have hstable : (prefixWord ++ tailWord_949604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949604).length < 2 ^ (prefixWord ++ tailWord_949604).sum := by decide
  have hdescent : baseEnd_949604 < baseStart_949604 := by decide
  rcases family_descends (prefixWord ++ tailWord_949604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949636 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_949636 : Nat := 118140960795 + 949636 * 2 ^ 59
def prefixEnd_949636 : Nat := 4983230072969 + 3 ^ 40 * 949636 * 2
def baseEnd_949636 : Nat := 325079809875434518988473

theorem tailTrace_949636 : CollatzResearch.WordTrace tailWord_949636 prefixEnd_949636 325079809875434518988473 := by
  unfold tailWord_949636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17318035193819215880854381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23090713591758954507805841 17318035193819215880854381)
  ·
    refine ⟨6494263197682205955320393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17318035193819215880854381 6494263197682205955320393)
    ·
      refine ⟨4870697398261654466490295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6494263197682205955320393 4870697398261654466490295)
      ·
        refine ⟨7306046097392481699735443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4870697398261654466490295 7306046097392481699735443)
        ·
          refine ⟨10959069146088722549603165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7306046097392481699735443 10959069146088722549603165)
          ·
            refine ⟨4109650929783270956101187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10959069146088722549603165 4109650929783270956101187)
            ·
              refine ⟨6164476394674906434151781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4109650929783270956101187 6164476394674906434151781)
              ·
                refine ⟨1155839324001544956403459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6164476394674906434151781 1155839324001544956403459)
                ·
                  refine ⟨1733758986002317434605189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1155839324001544956403459 1733758986002317434605189)
                  ·
                    refine ⟨325079809875434518988473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1733758986002317434605189 325079809875434518988473)
                    ·
                      rfl

theorem cell22_949636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_949636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949636 prefixEnd_949636 := by exact prefixLift 949636
  have htrace : WordTrace (prefixWord ++ tailWord_949636) baseStart_949636 baseEnd_949636 := by
    simpa [prefixWord, tailWord_949636, baseEnd_949636] using wordTrace_append hprefix tailTrace_949636
  have hstable : (prefixWord ++ tailWord_949636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949636).length < 2 ^ (prefixWord ++ tailWord_949636).sum := by decide
  have hdescent : baseEnd_949636 < baseStart_949636 := by decide
  rcases family_descends (prefixWord ++ tailWord_949636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949762 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_949762 : Nat := 118140960795 + 949762 * 2 ^ 59
def prefixEnd_949762 : Nat := 4983230072969 + 3 ^ 40 * 949762 * 2
def baseEnd_949762 : Nat := 325122942250412190338087

theorem tailTrace_949762 : CollatzResearch.WordTrace tailWord_949762 prefixEnd_949762 325122942250412190338087 := by
  unfold tailWord_949762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660166496295488820198885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23093777323454636853863693 8660166496295488820198885)
  ·
    refine ⟨1623781218055404153787291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8660166496295488820198885 1623781218055404153787291)
    ·
      refine ⟨2435671827083106230680937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623781218055404153787291 2435671827083106230680937)
      ·
        refine ⟨1826753870312329673010703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2435671827083106230680937 1826753870312329673010703)
        ·
          refine ⟨2740130805468494509516055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1826753870312329673010703 2740130805468494509516055)
          ·
            refine ⟨4110196208202741764274083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740130805468494509516055 4110196208202741764274083)
            ·
              refine ⟨6165294312304112646411125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4110196208202741764274083 6165294312304112646411125)
              ·
                refine ⟨577996341778510560601043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6165294312304112646411125 577996341778510560601043)
                ·
                  refine ⟨866994512667765840901565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 577996341778510560601043 866994512667765840901565)
                  ·
                    refine ⟨325122942250412190338087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 866994512667765840901565 325122942250412190338087)
                    ·
                      rfl

theorem cell22_949762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_949762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949762 prefixEnd_949762 := by exact prefixLift 949762
  have htrace : WordTrace (prefixWord ++ tailWord_949762) baseStart_949762 baseEnd_949762 := by
    simpa [prefixWord, tailWord_949762, baseEnd_949762] using wordTrace_append hprefix tailTrace_949762
  have hstable : (prefixWord ++ tailWord_949762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949762).length < 2 ^ (prefixWord ++ tailWord_949762).sum := by decide
  have hdescent : baseEnd_949762 < baseStart_949762 := by decide
  rcases family_descends (prefixWord ++ tailWord_949762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949769 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 8]
def baseStart_949769 : Nat := 118140960795 + 949769 * 2 ^ 59
def prefixEnd_949769 : Nat := 4983230072969 + 3 ^ 40 * 949769 * 2
def baseEnd_949769 : Nat := 108375112831155501804355

theorem tailTrace_949769 : CollatzResearch.WordTrace tailWord_949769 prefixEnd_949769 108375112831155501804355 := by
  unfold tailWord_949769
  simp only [CollatzResearch.WordTrace]
  refine ⟨34640921296156595476300361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23093947530771063650866907 34640921296156595476300361)
  ·
    refine ⟨25980690972117446607225271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34640921296156595476300361 25980690972117446607225271)
    ·
      refine ⟨38971036458176169910837907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25980690972117446607225271 38971036458176169910837907)
      ·
        refine ⟨58456554687264254866256861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38971036458176169910837907 58456554687264254866256861)
        ·
          refine ⟨21921208007724095574846323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58456554687264254866256861 21921208007724095574846323)
          ·
            refine ⟨32881812011586143362269485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21921208007724095574846323 32881812011586143362269485)
            ·
              refine ⟨12330679504344803760851057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32881812011586143362269485 12330679504344803760851057)
              ·
                refine ⟨9248009628258602820638293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12330679504344803760851057 9248009628258602820638293)
                ·
                  refine ⟨108375112831155501804355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9248009628258602820638293 108375112831155501804355)
                  ·
                    rfl

theorem cell22_949769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_949769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949769 prefixEnd_949769 := by exact prefixLift 949769
  have htrace : WordTrace (prefixWord ++ tailWord_949769) baseStart_949769 baseEnd_949769 := by
    simpa [prefixWord, tailWord_949769, baseEnd_949769] using wordTrace_append hprefix tailTrace_949769
  have hstable : (prefixWord ++ tailWord_949769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949769).length < 2 ^ (prefixWord ++ tailWord_949769).sum := by decide
  have hdescent : baseEnd_949769 < baseStart_949769 := by decide
  rcases family_descends (prefixWord ++ tailWord_949769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949816 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_949816 : Nat := 118140960795 + 949816 * 2 ^ 59
def prefixEnd_949816 : Nat := 4983230072969 + 3 ^ 40 * 949816 * 2
def baseEnd_949816 : Nat := 325141427553974049487921

theorem tailTrace_949816 : CollatzResearch.WordTrace tailWord_949816 prefixEnd_949816 325141427553974049487921 := by
  unfold tailWord_949816
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321317763493161251630651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23095090351324215002174201 17321317763493161251630651)
  ·
    refine ⟨25981976645239741877445977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17321317763493161251630651 25981976645239741877445977)
    ·
      refine ⟨19486482483929806408084483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25981976645239741877445977 19486482483929806408084483)
      ·
        refine ⟨29229723725894709612126725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19486482483929806408084483 29229723725894709612126725)
        ·
          refine ⟨5480573198605258052273761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29229723725894709612126725 5480573198605258052273761)
          ·
            refine ⟨4110429898953943539205321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5480573198605258052273761 4110429898953943539205321)
            ·
              refine ⟨3082822424215457654403991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4110429898953943539205321 3082822424215457654403991)
              ·
                refine ⟨4624233636323186481605987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3082822424215457654403991 4624233636323186481605987)
                ·
                  refine ⟨6936350454484779722408981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4624233636323186481605987 6936350454484779722408981)
                  ·
                    refine ⟨325141427553974049487921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6936350454484779722408981 325141427553974049487921)
                    ·
                      rfl

theorem cell22_949816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_949816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949816 prefixEnd_949816 := by exact prefixLift 949816
  have htrace : WordTrace (prefixWord ++ tailWord_949816) baseStart_949816 baseEnd_949816 := by
    simpa [prefixWord, tailWord_949816, baseEnd_949816] using wordTrace_append hprefix tailTrace_949816
  have hstable : (prefixWord ++ tailWord_949816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949816).length < 2 ^ (prefixWord ++ tailWord_949816).sum := by decide
  have hdescent : baseEnd_949816 < baseStart_949816 := by decide
  rcases family_descends (prefixWord ++ tailWord_949816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949837 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 6]
def baseStart_949837 : Nat := 118140960795 + 949837 * 2 ^ 59
def prefixEnd_949837 : Nat := 4983230072969 + 3 ^ 40 * 949837 * 2
def baseEnd_949837 : Nat := 108382872094378998237619

theorem tailTrace_949837 : CollatzResearch.WordTrace tailWord_949837 prefixEnd_949837 108382872094378998237619 := by
  unfold tailWord_949837
  simp only [CollatzResearch.WordTrace]
  refine ⟨34643401459910243089775765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23095600973273495393183843 34643401459910243089775765)
  ·
    refine ⟨1623909443433292644833239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34643401459910243089775765 1623909443433292644833239)
    ·
      refine ⟨2435864165149938967249859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1623909443433292644833239 2435864165149938967249859)
      ·
        refine ⟨3653796247724908450874789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435864165149938967249859 3653796247724908450874789)
        ·
          refine ⟨685086796448420334539023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3653796247724908450874789 685086796448420334539023)
          ·
            refine ⟨1027630194672630501808535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685086796448420334539023 1027630194672630501808535)
            ·
              refine ⟨1541445292008945752712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027630194672630501808535 1541445292008945752712803)
              ·
                refine ⟨2312167938013418629069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541445292008945752712803 2312167938013418629069205)
                ·
                  refine ⟨108382872094378998237619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2312167938013418629069205 108382872094378998237619)
                  ·
                    rfl

theorem cell22_949837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_949837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949837 prefixEnd_949837 := by exact prefixLift 949837
  have htrace : WordTrace (prefixWord ++ tailWord_949837) baseStart_949837 baseEnd_949837 := by
    simpa [prefixWord, tailWord_949837, baseEnd_949837] using wordTrace_append hprefix tailTrace_949837
  have hstable : (prefixWord ++ tailWord_949837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949837).length < 2 ^ (prefixWord ++ tailWord_949837).sum := by decide
  have hdescent : baseEnd_949837 < baseStart_949837 := by decide
  rcases family_descends (prefixWord ++ tailWord_949837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949852 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_949852 : Nat := 118140960795 + 949852 * 2 ^ 59
def prefixEnd_949852 : Nat := 4983230072969 + 3 ^ 40 * 949852 * 2
def baseEnd_949852 : Nat := 325153751089681955587811

theorem tailTrace_949852 : CollatzResearch.WordTrace tailWord_949852 prefixEnd_949852 325153751089681955587811 := by
  unfold tailWord_949852
  simp only [CollatzResearch.WordTrace]
  refine ⟨17321974277427950325785905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23095965703237267101047873 17321974277427950325785905)
  ·
    refine ⟨12991480708070962744339429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17321974277427950325785905 12991480708070962744339429)
    ·
      refine ⟨2435902632763305514563643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12991480708070962744339429 2435902632763305514563643)
      ·
        refine ⟨3653853949144958271845465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435902632763305514563643 3653853949144958271845465)
        ·
          refine ⟨2740390461858718703884099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3653853949144958271845465 2740390461858718703884099)
          ·
            refine ⟨4110585692788078055826149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740390461858718703884099 4110585692788078055826149)
            ·
              refine ⟨770734817397764635467403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4110585692788078055826149 770734817397764635467403)
              ·
                refine ⟨1156102226096646953201105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770734817397764635467403 1156102226096646953201105)
                ·
                  refine ⟨867076669572485214900829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156102226096646953201105 867076669572485214900829)
                  ·
                    refine ⟨325153751089681955587811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867076669572485214900829 325153751089681955587811)
                    ·
                      rfl

theorem cell22_949852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_949852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949852 prefixEnd_949852 := by exact prefixLift 949852
  have htrace : WordTrace (prefixWord ++ tailWord_949852) baseStart_949852 baseEnd_949852 := by
    simpa [prefixWord, tailWord_949852, baseEnd_949852] using wordTrace_append hprefix tailTrace_949852
  have hstable : (prefixWord ++ tailWord_949852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949852).length < 2 ^ (prefixWord ++ tailWord_949852).sum := by decide
  have hdescent : baseEnd_949852 < baseStart_949852 := by decide
  rcases family_descends (prefixWord ++ tailWord_949852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949863 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 3, 3]
def baseStart_949863 : Nat := 118140960795 + 949863 * 2 ^ 59
def prefixEnd_949863 : Nat := 4983230072969 + 3 ^ 40 * 949863 * 2
def baseEnd_949863 : Nat := 325157516614481593562777

theorem tailTrace_949863 : CollatzResearch.WordTrace tailWord_949863 prefixEnd_949863 325157516614481593562777 := by
  unfold tailWord_949863
  simp only [CollatzResearch.WordTrace]
  refine ⟨34644349757816049530222243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23096233171877366353481495 34644349757816049530222243)
  ·
    refine ⟨51966524636724074295333365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34644349757816049530222243 51966524636724074295333365)
    ·
      refine ⟨4871861684692881965187503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51966524636724074295333365 4871861684692881965187503)
      ·
        refine ⟨7307792527039322947781255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4871861684692881965187503 7307792527039322947781255)
        ·
          refine ⟨10961688790558984421671883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7307792527039322947781255 10961688790558984421671883)
          ·
            refine ⟨16442533185838476632507825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10961688790558984421671883 16442533185838476632507825)
            ·
              refine ⟨12331899889378857474380869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16442533185838476632507825 12331899889378857474380869)
              ·
                refine ⟨2312231229258535776446413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12331899889378857474380869 2312231229258535776446413)
                ·
                  refine ⟨867086710971950916167405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2312231229258535776446413 867086710971950916167405)
                  ·
                    refine ⟨325157516614481593562777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867086710971950916167405 325157516614481593562777)
                    ·
                      rfl

theorem cell22_949863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_949863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949863 prefixEnd_949863 := by exact prefixLift 949863
  have htrace : WordTrace (prefixWord ++ tailWord_949863) baseStart_949863 baseEnd_949863 := by
    simpa [prefixWord, tailWord_949863, baseEnd_949863] using wordTrace_append hprefix tailTrace_949863
  have hstable : (prefixWord ++ tailWord_949863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949863).length < 2 ^ (prefixWord ++ tailWord_949863).sum := by decide
  have hdescent : baseEnd_949863 < baseStart_949863 := by decide
  rcases family_descends (prefixWord ++ tailWord_949863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949891 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 2, 5]
def baseStart_949891 : Nat := 118140960795 + 949891 * 2 ^ 59
def prefixEnd_949891 : Nat := 4983230072969 + 3 ^ 40 * 949891 * 2
def baseEnd_949891 : Nat := 325167101586698853862691

theorem tailTrace_949891 : CollatzResearch.WordTrace tailWord_949891 prefixEnd_949891 325167101586698853862691 := by
  unfold tailWord_949891
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645371001714610312241527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23096914001143073541494351 34645371001714610312241527)
  ·
    refine ⟨51968056502571915468362291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34645371001714610312241527 51968056502571915468362291)
    ·
      refine ⟨77952084753857873202543437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51968056502571915468362291 77952084753857873202543437)
      ·
        refine ⟨29232031782696702450953789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77952084753857873202543437 29232031782696702450953789)
        ·
          refine ⟨10962011918511263419107671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29232031782696702450953789 10962011918511263419107671)
          ·
            refine ⟨16443017877766895128661507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10962011918511263419107671 16443017877766895128661507)
            ·
              refine ⟨24664526816650342692992261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16443017877766895128661507 24664526816650342692992261)
              ·
                refine ⟨4624598778121939254936049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24664526816650342692992261 4624598778121939254936049)
                ·
                  refine ⟨3468449083591454441202037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4624598778121939254936049 3468449083591454441202037)
                  ·
                    refine ⟨325167101586698853862691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3468449083591454441202037 325167101586698853862691)
                    ·
                      rfl

theorem cell22_949891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_949891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949891 prefixEnd_949891 := by exact prefixLift 949891
  have htrace : WordTrace (prefixWord ++ tailWord_949891) baseStart_949891 baseEnd_949891 := by
    simpa [prefixWord, tailWord_949891, baseEnd_949891] using wordTrace_append hprefix tailTrace_949891
  have hstable : (prefixWord ++ tailWord_949891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949891).length < 2 ^ (prefixWord ++ tailWord_949891).sum := by decide
  have hdescent : baseEnd_949891 < baseStart_949891 := by decide
  rcases family_descends (prefixWord ++ tailWord_949891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949893 : List Nat := [1, 3, 1, 1, 4, 1, 4, 2, 5]
def baseStart_949893 : Nat := 118140960795 + 949893 * 2 ^ 59
def prefixEnd_949893 : Nat := 4983230072969 + 3 ^ 40 * 949893 * 2
def baseEnd_949893 : Nat := 108389262075857171770895

theorem tailTrace_949893 : CollatzResearch.WordTrace tailWord_949893 prefixEnd_949893 108389262075857171770895 := by
  unfold tailWord_949893
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645443947707364653814333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23096962631804909769209555 34645443947707364653814333)
  ·
    refine ⟨12992041480390261745180375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34645443947707364653814333 12992041480390261745180375)
    ·
      refine ⟨19488062220585392617770563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12992041480390261745180375 19488062220585392617770563)
      ·
        refine ⟨29232093330878088926655845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19488062220585392617770563 29232093330878088926655845)
        ·
          refine ⟨5481017499539641673747971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29232093330878088926655845 5481017499539641673747971)
          ·
            refine ⟨8221526249309462510621957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5481017499539641673747971 8221526249309462510621957)
            ·
              refine ⟨1541536171745524220741617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8221526249309462510621957 1541536171745524220741617)
              ·
                refine ⟨1156152128809143165556213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1541536171745524220741617 1156152128809143165556213)
                ·
                  refine ⟨108389262075857171770895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1156152128809143165556213 108389262075857171770895)
                  ·
                    rfl

theorem cell22_949893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_949893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949893 prefixEnd_949893 := by exact prefixLift 949893
  have htrace : WordTrace (prefixWord ++ tailWord_949893) baseStart_949893 baseEnd_949893 := by
    simpa [prefixWord, tailWord_949893, baseEnd_949893] using wordTrace_append hprefix tailTrace_949893
  have hstable : (prefixWord ++ tailWord_949893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949893).length < 2 ^ (prefixWord ++ tailWord_949893).sum := by decide
  have hdescent : baseEnd_949893 < baseStart_949893 := by decide
  rcases family_descends (prefixWord ++ tailWord_949893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949897 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 1, 3]
def baseStart_949897 : Nat := 118140960795 + 949897 * 2 ^ 59
def prefixEnd_949897 : Nat := 4983230072969 + 3 ^ 40 * 949897 * 2
def baseEnd_949897 : Nat := 325169155509316838212673

theorem tailTrace_949897 : CollatzResearch.WordTrace tailWord_949897 prefixEnd_949897 325169155509316838212673 := by
  unfold tailWord_949897
  simp only [CollatzResearch.WordTrace]
  refine ⟨34645589839692873336959945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23097059893128582224639963 34645589839692873336959945)
  ·
    refine ⟨25984192379769655002719959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34645589839692873336959945 25984192379769655002719959)
    ·
      refine ⟨38976288569654482504079939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25984192379769655002719959 38976288569654482504079939)
      ·
        refine ⟨58464432854481723756119909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38976288569654482504079939 58464432854481723756119909)
        ·
          refine ⟨10962081160215323204272483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58464432854481723756119909 10962081160215323204272483)
          ·
            refine ⟨16443121740322984806408725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10962081160215323204272483 16443121740322984806408725)
            ·
              refine ⟨770771331577639912800409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16443121740322984806408725 770771331577639912800409)
              ·
                refine ⟨578078498683229934600307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770771331577639912800409 578078498683229934600307)
                ·
                  refine ⟨867117748024844901900461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578078498683229934600307 867117748024844901900461)
                  ·
                    refine ⟨325169155509316838212673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867117748024844901900461 325169155509316838212673)
                    ·
                      rfl

theorem cell22_949897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_949897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949897 prefixEnd_949897 := by exact prefixLift 949897
  have htrace : WordTrace (prefixWord ++ tailWord_949897) baseStart_949897 baseEnd_949897 := by
    simpa [prefixWord, tailWord_949897, baseEnd_949897] using wordTrace_append hprefix tailTrace_949897
  have hstable : (prefixWord ++ tailWord_949897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949897).length < 2 ^ (prefixWord ++ tailWord_949897).sum := by decide
  have hdescent : baseEnd_949897 < baseStart_949897 := by decide
  rcases family_descends (prefixWord ++ tailWord_949897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949923 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 1, 4]
def baseStart_949923 : Nat := 118140960795 + 949923 * 2 ^ 59
def prefixEnd_949923 : Nat := 4983230072969 + 3 ^ 40 * 949923 * 2
def baseEnd_949923 : Nat := 325178055840661437062593

theorem tailTrace_949923 : CollatzResearch.WordTrace tailWord_949923 prefixEnd_949923 325178055840661437062593 := by
  unfold tailWord_949923
  simp only [CollatzResearch.WordTrace]
  refine ⟨34646538137598679777406423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23097692091732453184937615 34646538137598679777406423)
  ·
    refine ⟨51969807206398019666109635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34646538137598679777406423 51969807206398019666109635)
    ·
      refine ⟨77954710809597029499164453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51969807206398019666109635 77954710809597029499164453)
      ·
        refine ⟨14616508276799443031093335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77954710809597029499164453 14616508276799443031093335)
        ·
          refine ⟨21924762415199164546640003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14616508276799443031093335 21924762415199164546640003)
          ·
            refine ⟨32887143622798746819960005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21924762415199164546640003 32887143622798746819960005)
            ·
              refine ⟨6166339429274765028742501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32887143622798746819960005 6166339429274765028742501)
              ·
                refine ⟨1156188642989018442889219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6166339429274765028742501 1156188642989018442889219)
                ·
                  refine ⟨1734282964483527664333829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156188642989018442889219 1734282964483527664333829)
                  ·
                    refine ⟨325178055840661437062593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1734282964483527664333829 325178055840661437062593)
                    ·
                      rfl

theorem cell22_949923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 4].length) (baseStart_949923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949923 prefixEnd_949923 := by exact prefixLift 949923
  have htrace : WordTrace (prefixWord ++ tailWord_949923) baseStart_949923 baseEnd_949923 := by
    simpa [prefixWord, tailWord_949923, baseEnd_949923] using wordTrace_append hprefix tailTrace_949923
  have hstable : (prefixWord ++ tailWord_949923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949923).length < 2 ^ (prefixWord ++ tailWord_949923).sum := by decide
  have hdescent : baseEnd_949923 < baseStart_949923 := by decide
  rcases family_descends (prefixWord ++ tailWord_949923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_949970 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_949970 : Nat := 118140960795 + 949970 * 2 ^ 59
def prefixEnd_949970 : Nat := 4983230072969 + 3 ^ 40 * 949970 * 2
def baseEnd_949970 : Nat := 325194144901168981137449

theorem tailTrace_949970 : CollatzResearch.WordTrace tailWord_949970 prefixEnd_949970 325194144901168981137449 := by
  unfold tailWord_949970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662063092107101701091841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23098834912285604536244909 8662063092107101701091841)
  ·
    refine ⟨6496547319080326275818881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8662063092107101701091841 6496547319080326275818881)
    ·
      refine ⟨4872410489310244706864161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6496547319080326275818881 4872410489310244706864161)
      ·
        refine ⟨3654307866982683530148121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4872410489310244706864161 3654307866982683530148121)
        ·
          refine ⟨2740730900237012647611091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3654307866982683530148121 2740730900237012647611091)
          ·
            refine ⟨4111096350355518971416637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740730900237012647611091 4111096350355518971416637)
            ·
              refine ⟨1541661131383319614281239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4111096350355518971416637 1541661131383319614281239)
              ·
                refine ⟨2312491697074979421421859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541661131383319614281239 2312491697074979421421859)
                ·
                  refine ⟨3468737545612469132132789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2312491697074979421421859 3468737545612469132132789)
                  ·
                    refine ⟨325194144901168981137449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3468737545612469132132789 325194144901168981137449)
                    ·
                      rfl

theorem cell22_949970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_949970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_949970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_949970 prefixEnd_949970 := by exact prefixLift 949970
  have htrace : WordTrace (prefixWord ++ tailWord_949970) baseStart_949970 baseEnd_949970 := by
    simpa [prefixWord, tailWord_949970, baseEnd_949970] using wordTrace_append hprefix tailTrace_949970
  have hstable : (prefixWord ++ tailWord_949970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_949970).length < 2 ^ (prefixWord ++ tailWord_949970).sum := by decide
  have hdescent : baseEnd_949970 < baseStart_949970 := by decide
  rcases family_descends (prefixWord ++ tailWord_949970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950004 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_950004 : Nat := 118140960795 + 950004 * 2 ^ 59
def prefixEnd_950004 : Nat := 4983230072969 + 3 ^ 40 * 950004 * 2
def baseEnd_950004 : Nat := 325205783796004225787345

theorem tailTrace_950004 : CollatzResearch.WordTrace tailWord_950004 prefixEnd_950004 325205783796004225787345 := by
  unfold tailWord_950004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17324746225152615305552533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23099661633536820407403377 17324746225152615305552533)
  ·
    refine ⟨812097479304028842447775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17324746225152615305552533 812097479304028842447775)
    ·
      refine ⟨1218146218956043263671663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812097479304028842447775 1218146218956043263671663)
      ·
        refine ⟨1827219328434064895507495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1218146218956043263671663 1827219328434064895507495)
        ·
          refine ⟨2740828992651097343261243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1827219328434064895507495 2740828992651097343261243)
          ·
            refine ⟨4111243488976646014891865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2740828992651097343261243 4111243488976646014891865)
            ·
              refine ⟨3083432616732484511168899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4111243488976646014891865 3083432616732484511168899)
              ·
                refine ⟨4625148925098726766753349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3083432616732484511168899 4625148925098726766753349)
                ·
                  refine ⟨867215423456011268766253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4625148925098726766753349 867215423456011268766253)
                  ·
                    refine ⟨325205783796004225787345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867215423456011268766253 325205783796004225787345)
                    ·
                      rfl

theorem cell22_950004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_950004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950004 prefixEnd_950004 := by exact prefixLift 950004
  have htrace : WordTrace (prefixWord ++ tailWord_950004) baseStart_950004 baseEnd_950004 := by
    simpa [prefixWord, tailWord_950004, baseEnd_950004] using wordTrace_append hprefix tailTrace_950004
  have hstable : (prefixWord ++ tailWord_950004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950004).length < 2 ^ (prefixWord ++ tailWord_950004).sum := by decide
  have hdescent : baseEnd_950004 < baseStart_950004 := by decide
  rcases family_descends (prefixWord ++ tailWord_950004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950015 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 3, 3]
def baseStart_950015 : Nat := 118140960795 + 950015 * 2 ^ 59
def prefixEnd_950015 : Nat := 4983230072969 + 3 ^ 40 * 950015 * 2
def baseEnd_950015 : Nat := 325209549320803863762311

theorem tailTrace_950015 : CollatzResearch.WordTrace tailWord_950015 prefixEnd_950015 325209549320803863762311 := by
  unfold tailWord_950015
  simp only [CollatzResearch.WordTrace]
  refine ⟨34649893653265379489755499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23099929102176919659836999 34649893653265379489755499)
  ·
    refine ⟨51974840479898069234633249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34649893653265379489755499 51974840479898069234633249)
    ·
      refine ⟨38981130359923551925974937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51974840479898069234633249 38981130359923551925974937)
      ·
        refine ⟨29235847769942663944481203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38981130359923551925974937 29235847769942663944481203)
        ·
          refine ⟨43853771654913995916721805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29235847769942663944481203 43853771654913995916721805)
          ·
            refine ⟨16445164370592748468770677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43853771654913995916721805 16445164370592748468770677)
            ·
              refine ⟨1541734159743070168947251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16445164370592748468770677 1541734159743070168947251)
              ·
                refine ⟨2312601239614605253420877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541734159743070168947251 2312601239614605253420877)
                ·
                  refine ⟨867225464855476970032829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2312601239614605253420877 867225464855476970032829)
                  ·
                    refine ⟨325209549320803863762311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867225464855476970032829 325209549320803863762311)
                    ·
                      rfl

theorem cell22_950015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_950015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950015 prefixEnd_950015 := by exact prefixLift 950015
  have htrace : WordTrace (prefixWord ++ tailWord_950015) baseStart_950015 baseEnd_950015 := by
    simpa [prefixWord, tailWord_950015, baseEnd_950015] using wordTrace_append hprefix tailTrace_950015
  have hstable : (prefixWord ++ tailWord_950015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950015).length < 2 ^ (prefixWord ++ tailWord_950015).sum := by decide
  have hdescent : baseEnd_950015 < baseStart_950015 := by decide
  rcases family_descends (prefixWord ++ tailWord_950015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950036 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_950036 : Nat := 118140960795 + 950036 * 2 ^ 59
def prefixEnd_950036 : Nat := 4983230072969 + 3 ^ 40 * 950036 * 2
def baseEnd_950036 : Nat := 325216738049966808987247

theorem tailTrace_950036 : CollatzResearch.WordTrace tailWord_950036 prefixEnd_950036 325216738049966808987247 := by
  unfold tailWord_950036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17325329793094650038134981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23100439724126200050846641 17325329793094650038134981)
  ·
    refine ⟨3248499336205246882150309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17325329793094650038134981 3248499336205246882150309)
    ·
      refine ⟨609093625538483790403183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3248499336205246882150309 609093625538483790403183)
      ·
        refine ⟨913640438307725685604775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609093625538483790403183 913640438307725685604775)
        ·
          refine ⟨1370460657461588528407163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913640438307725685604775 1370460657461588528407163)
          ·
            refine ⟨2055690986192382792610745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370460657461588528407163 2055690986192382792610745)
            ·
              refine ⟨1541768239644287094458059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2055690986192382792610745 1541768239644287094458059)
              ·
                refine ⟨2312652359466430641687089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1541768239644287094458059 2312652359466430641687089)
                ·
                  refine ⟨1734489269599822981265317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2312652359466430641687089 1734489269599822981265317)
                  ·
                    refine ⟨325216738049966808987247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1734489269599822981265317 325216738049966808987247)
                    ·
                      rfl

theorem cell22_950036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_950036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950036 prefixEnd_950036 := by exact prefixLift 950036
  have htrace : WordTrace (prefixWord ++ tailWord_950036) baseStart_950036 baseEnd_950036 := by
    simpa [prefixWord, tailWord_950036, baseEnd_950036] using wordTrace_append hprefix tailTrace_950036
  have hstable : (prefixWord ++ tailWord_950036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950036).length < 2 ^ (prefixWord ++ tailWord_950036).sum := by decide
  have hdescent : baseEnd_950036 < baseStart_950036 := by decide
  rcases family_descends (prefixWord ++ tailWord_950036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950066 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_950066 : Nat := 118140960795 + 950066 * 2 ^ 59
def prefixEnd_950066 : Nat := 4983230072969 + 3 ^ 40 * 950066 * 2
def baseEnd_950066 : Nat := 325227007663056730737155

theorem tailTrace_950066 : CollatzResearch.WordTrace tailWord_950066 prefixEnd_950066 325227007663056730737155 := by
  unfold tailWord_950066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8662938444020153799965513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23101169184053743466574701 8662938444020153799965513)
  ·
    refine ⟨6497203833015115349974135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8662938444020153799965513 6497203833015115349974135)
    ·
      refine ⟨9745805749522673024961203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497203833015115349974135 9745805749522673024961203)
      ·
        refine ⟨14618708624284009537441805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9745805749522673024961203 14618708624284009537441805)
        ·
          refine ⟨5482015734106503576540677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14618708624284009537441805 5482015734106503576540677)
          ·
            refine ⟨1027877950144969420601377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5482015734106503576540677 1027877950144969420601377)
            ·
              refine ⟨770908462608727065451033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027877950144969420601377 770908462608727065451033)
              ·
                refine ⟨578181346956545299088275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 770908462608727065451033 578181346956545299088275)
                ·
                  refine ⟨867272020434817948632413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578181346956545299088275 867272020434817948632413)
                  ·
                    refine ⟨325227007663056730737155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867272020434817948632413 325227007663056730737155)
                    ·
                      rfl

theorem cell22_950066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_950066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950066 prefixEnd_950066 := by exact prefixLift 950066
  have htrace : WordTrace (prefixWord ++ tailWord_950066) baseStart_950066 baseEnd_950066 := by
    simpa [prefixWord, tailWord_950066, baseEnd_950066] using wordTrace_append hprefix tailTrace_950066
  have hstable : (prefixWord ++ tailWord_950066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950066).length < 2 ^ (prefixWord ++ tailWord_950066).sum := by decide
  have hdescent : baseEnd_950066 < baseStart_950066 := by decide
  rcases family_descends (prefixWord ++ tailWord_950066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950105 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_950105 : Nat := 118140960795 + 950105 * 2 ^ 59
def prefixEnd_950105 : Nat := 4983230072969 + 3 ^ 40 * 950105 * 2
def baseEnd_950105 : Nat := 325240358160073629012035

theorem tailTrace_950105 : CollatzResearch.WordTrace tailWord_950105 prefixEnd_950105 325240358160073629012035 := by
  unfold tailWord_950105
  simp only [CollatzResearch.WordTrace]
  refine ⟨34653176222939324860531769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23102117481959549907021179 34653176222939324860531769)
  ·
    refine ⟨25989882167204493645398827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34653176222939324860531769 25989882167204493645398827)
    ·
      refine ⟨38984823250806740468098241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25989882167204493645398827 38984823250806740468098241)
      ·
        refine ⟨29238617438105055351073681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38984823250806740468098241 29238617438105055351073681)
        ·
          refine ⟨21928963078578791513305261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29238617438105055351073681 21928963078578791513305261)
          ·
            refine ⟨8223361154467046817489473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21928963078578791513305261 8223361154467046817489473)
            ·
              refine ⟨6167520865850285113117105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223361154467046817489473 6167520865850285113117105)
              ·
                refine ⟨4625640649387713834837829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6167520865850285113117105 4625640649387713834837829)
                ·
                  refine ⟨867307621760196344032093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4625640649387713834837829 867307621760196344032093)
                  ·
                    refine ⟨325240358160073629012035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867307621760196344032093 325240358160073629012035)
                    ·
                      rfl

theorem cell22_950105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_950105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950105 prefixEnd_950105 := by exact prefixLift 950105
  have htrace : WordTrace (prefixWord ++ tailWord_950105) baseStart_950105 baseEnd_950105 := by
    simpa [prefixWord, tailWord_950105, baseEnd_950105] using wordTrace_append hprefix tailTrace_950105
  have hstable : (prefixWord ++ tailWord_950105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950105).length < 2 ^ (prefixWord ++ tailWord_950105).sum := by decide
  have hdescent : baseEnd_950105 < baseStart_950105 := by decide
  rcases family_descends (prefixWord ++ tailWord_950105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950120 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_950120 : Nat := 118140960795 + 950120 * 2 ^ 59
def prefixEnd_950120 : Nat := 4983230072969 + 3 ^ 40 * 950120 * 2
def baseEnd_950120 : Nat := 325245492966618589886989

theorem tailTrace_950120 : CollatzResearch.WordTrace tailWord_950120 prefixEnd_950120 325245492966618589886989 := by
  unfold tailWord_950120
  simp only [CollatzResearch.WordTrace]
  refine ⟨17326861658942491211163907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23102482211923321614885209 17326861658942491211163907)
  ·
    refine ⟨25990292488413736816745861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17326861658942491211163907 25990292488413736816745861)
    ·
      refine ⟨4873179841577575653139849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25990292488413736816745861 4873179841577575653139849)
      ·
        refine ⟨3654884881183181739854887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4873179841577575653139849 3654884881183181739854887)
        ·
          refine ⟨5482327321774772609782331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3654884881183181739854887 5482327321774772609782331)
          ·
            refine ⟨8223490982662158914673497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5482327321774772609782331 8223490982662158914673497)
            ·
              refine ⟨6167618236996619186005123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8223490982662158914673497 6167618236996619186005123)
              ·
                refine ⟨9251427355494928779007685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6167618236996619186005123 9251427355494928779007685)
                ·
                  refine ⟨1734642629155299146063941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9251427355494928779007685 1734642629155299146063941)
                  ·
                    refine ⟨325245492966618589886989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1734642629155299146063941 325245492966618589886989)
                    ·
                      rfl

theorem cell22_950120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_950120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950120 prefixEnd_950120 := by exact prefixLift 950120
  have htrace : WordTrace (prefixWord ++ tailWord_950120) baseStart_950120 baseEnd_950120 := by
    simpa [prefixWord, tailWord_950120, baseEnd_950120] using wordTrace_append hprefix tailTrace_950120
  have hstable : (prefixWord ++ tailWord_950120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950120).length < 2 ^ (prefixWord ++ tailWord_950120).sum := by decide
  have hdescent : baseEnd_950120 < baseStart_950120 := by decide
  rcases family_descends (prefixWord ++ tailWord_950120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950158 : List Nat := [4, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_950158 : Nat := 118140960795 + 950158 * 2 ^ 59
def prefixEnd_950158 : Nat := 4983230072969 + 3 ^ 40 * 950158 * 2
def baseEnd_950158 : Nat := 108419500381066385812291

theorem tailTrace_950158 : CollatzResearch.WordTrace tailWord_950158 prefixEnd_950158 108419500381066385812291 := by
  unfold tailWord_950158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4331888661468414364026391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 23103406194498209941474085 4331888661468414364026391)
  ·
    refine ⟨6497832992202621546039587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4331888661468414364026391 6497832992202621546039587)
    ·
      refine ⟨9746749488303932319059381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497832992202621546039587 9746749488303932319059381)
      ·
        refine ⟨913757764528493654911817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9746749488303932319059381 913757764528493654911817)
        ·
          refine ⟨685318323396370241183863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913757764528493654911817 685318323396370241183863)
          ·
            refine ⟨1027977485094555361775795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685318323396370241183863 1027977485094555361775795)
            ·
              refine ⟨1541966227641833042663693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1027977485094555361775795 1541966227641833042663693)
              ·
                refine ⟨578237335365687390998885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1541966227641833042663693 578237335365687390998885)
                ·
                  refine ⟨108419500381066385812291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578237335365687390998885 108419500381066385812291)
                  ·
                    rfl

theorem cell22_950158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_950158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950158 prefixEnd_950158 := by exact prefixLift 950158
  have htrace : WordTrace (prefixWord ++ tailWord_950158) baseStart_950158 baseEnd_950158 := by
    simpa [prefixWord, tailWord_950158, baseEnd_950158] using wordTrace_append hprefix tailTrace_950158
  have hstable : (prefixWord ++ tailWord_950158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950158).length < 2 ^ (prefixWord ++ tailWord_950158).sum := by decide
  have hdescent : baseEnd_950158 < baseStart_950158 := by decide
  rcases family_descends (prefixWord ++ tailWord_950158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950180 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_950180 : Nat := 118140960795 + 950180 * 2 ^ 59
def prefixEnd_950180 : Nat := 4983230072969 + 3 ^ 40 * 950180 * 2
def baseEnd_950180 : Nat := 108422010730932811128935

theorem tailTrace_950180 : CollatzResearch.WordTrace tailWord_950180 prefixEnd_950180 108422010730932811128935 := by
  unfold tailWord_950180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17327955848833806334755997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23103941131778408446341329 17327955848833806334755997)
  ·
    refine ⟨6497983443312677375533499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17327955848833806334755997 6497983443312677375533499)
    ·
      refine ⟨9746975164969016063300249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6497983443312677375533499 9746975164969016063300249)
      ·
        refine ⟨7310231373726762047475187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9746975164969016063300249 7310231373726762047475187)
        ·
          refine ⟨10965347060590143071212781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7310231373726762047475187 10965347060590143071212781)
          ·
            refine ⟨4112005147721303651704793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10965347060590143071212781 4112005147721303651704793)
            ·
              refine ⟨3084003860790977738778595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4112005147721303651704793 3084003860790977738778595)
              ·
                refine ⟨4626005791186466608167893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3084003860790977738778595 4626005791186466608167893)
                ·
                  refine ⟨108422010730932811128935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4626005791186466608167893 108422010730932811128935)
                  ·
                    rfl

theorem cell22_950180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_950180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950180 prefixEnd_950180 := by exact prefixLift 950180
  have htrace : WordTrace (prefixWord ++ tailWord_950180) baseStart_950180 baseEnd_950180 := by
    simpa [prefixWord, tailWord_950180, baseEnd_950180] using wordTrace_append hprefix tailTrace_950180
  have hstable : (prefixWord ++ tailWord_950180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950180).length < 2 ^ (prefixWord ++ tailWord_950180).sum := by decide
  have hdescent : baseEnd_950180 < baseStart_950180 := by decide
  rcases family_descends (prefixWord ++ tailWord_950180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950197 : List Nat := [1, 3, 3, 2, 1, 3, 1, 3, 5]
def baseStart_950197 : Nat := 118140960795 + 950197 * 2 ^ 59
def prefixEnd_950197 : Nat := 4983230072969 + 3 ^ 40 * 950197 * 2
def baseEnd_950197 : Nat := 108423950546738685237251

theorem tailTrace_950197 : CollatzResearch.WordTrace tailWord_950197 prefixEnd_950197 108423950546738685237251 := by
  unfold tailWord_950197
  simp only [CollatzResearch.WordTrace]
  refine ⟨34656531738606024572880845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23104354492404016381920563 34656531738606024572880845)
  ·
    refine ⟨12996199401977259214830317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34656531738606024572880845 12996199401977259214830317)
    ·
      refine ⟨4873574775741472205561369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12996199401977259214830317 4873574775741472205561369)
      ·
        refine ⟨3655181081806104154171027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4873574775741472205561369 3655181081806104154171027)
        ·
          refine ⟨5482771622709156231256541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655181081806104154171027 5482771622709156231256541)
          ·
            refine ⟨2056039358515933586721203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5482771622709156231256541 2056039358515933586721203)
            ·
              refine ⟨3084059037773900380081805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056039358515933586721203 3084059037773900380081805)
              ·
                refine ⟨1156522139165212642530677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3084059037773900380081805 1156522139165212642530677)
                ·
                  refine ⟨108423950546738685237251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1156522139165212642530677 108423950546738685237251)
                  ·
                    rfl

theorem cell22_950197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_950197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950197 prefixEnd_950197 := by exact prefixLift 950197
  have htrace : WordTrace (prefixWord ++ tailWord_950197) baseStart_950197 baseEnd_950197 := by
    simpa [prefixWord, tailWord_950197, baseEnd_950197] using wordTrace_append hprefix tailTrace_950197
  have hstable : (prefixWord ++ tailWord_950197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950197).length < 2 ^ (prefixWord ++ tailWord_950197).sum := by decide
  have hdescent : baseEnd_950197 < baseStart_950197 := by decide
  rcases family_descends (prefixWord ++ tailWord_950197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950255 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 6]
def baseStart_950255 : Nat := 118140960795 + 950255 * 2 ^ 59
def prefixEnd_950255 : Nat := 4983230072969 + 3 ^ 40 * 950255 * 2
def baseEnd_950255 : Nat := 325291706225523237761575

theorem tailTrace_950255 : CollatzResearch.WordTrace tailWord_950255 prefixEnd_950255 325291706225523237761575 := by
  unfold tailWord_950255
  simp only [CollatzResearch.WordTrace]
  refine ⟨34658647172395900478492219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23105764781597266985661479 34658647172395900478492219)
  ·
    refine ⟨51987970758593850717738329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34658647172395900478492219 51987970758593850717738329)
    ·
      refine ⟨38990978068945388038303747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51987970758593850717738329 38990978068945388038303747)
      ·
        refine ⟨58486467103418082057455621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38990978068945388038303747 58486467103418082057455621)
        ·
          refine ⟨10966212581890890385772929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58486467103418082057455621 10966212581890890385772929)
          ·
            refine ⟨8224659436418167789329697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10966212581890890385772929 8224659436418167789329697)
            ·
              refine ⟨6168494577313625841997273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8224659436418167789329697 6168494577313625841997273)
              ·
                refine ⟨4626370932985219381497955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6168494577313625841997273 4626370932985219381497955)
                ·
                  refine ⟨6939556399477829072246933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4626370932985219381497955 6939556399477829072246933)
                  ·
                    refine ⟨325291706225523237761575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6939556399477829072246933 325291706225523237761575)
                    ·
                      rfl

theorem cell22_950255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_950255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950255 prefixEnd_950255 := by exact prefixLift 950255
  have htrace : WordTrace (prefixWord ++ tailWord_950255) baseStart_950255 baseEnd_950255 := by
    simpa [prefixWord, tailWord_950255, baseEnd_950255] using wordTrace_append hprefix tailTrace_950255
  have hstable : (prefixWord ++ tailWord_950255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950255).length < 2 ^ (prefixWord ++ tailWord_950255).sum := by decide
  have hdescent : baseEnd_950255 < baseStart_950255 := by decide
  rcases family_descends (prefixWord ++ tailWord_950255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950308 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_950308 : Nat := 118140960795 + 950308 * 2 ^ 59
def prefixEnd_950308 : Nat := 4983230072969 + 3 ^ 40 * 950308 * 2
def baseEnd_950308 : Nat := 325309849208648766186413

theorem tailTrace_950308 : CollatzResearch.WordTrace tailWord_950308 prefixEnd_950308 325309849208648766186413 := by
  unfold tailWord_950308
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330290120601945265085789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23107053494135927020114385 17330290120601945265085789)
  ·
    refine ⟨6498858795225729474407171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17330290120601945265085789 6498858795225729474407171)
    ·
      refine ⟨9748288192838594211610757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6498858795225729474407171 9748288192838594211610757)
      ·
        refine ⟨1827804036157236414677017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9748288192838594211610757 1827804036157236414677017)
        ·
          refine ⟨1370853027117927311007763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1827804036157236414677017 1370853027117927311007763)
          ·
            refine ⟨2056279540676890966511645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1370853027117927311007763 2056279540676890966511645)
            ·
              refine ⟨771104827753834112441867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2056279540676890966511645 771104827753834112441867)
              ·
                refine ⟨1156657241630751168662801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771104827753834112441867 1156657241630751168662801)
                ·
                  refine ⟨867492931223063376497101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156657241630751168662801 867492931223063376497101)
                  ·
                    refine ⟨325309849208648766186413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867492931223063376497101 325309849208648766186413)
                    ·
                      rfl

theorem cell22_950308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_950308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950308 prefixEnd_950308 := by exact prefixLift 950308
  have htrace : WordTrace (prefixWord ++ tailWord_950308) baseStart_950308 baseEnd_950308 := by
    simpa [prefixWord, tailWord_950308, baseEnd_950308] using wordTrace_append hprefix tailTrace_950308
  have hstable : (prefixWord ++ tailWord_950308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950308).length < 2 ^ (prefixWord ++ tailWord_950308).sum := by decide
  have hdescent : baseEnd_950308 < baseStart_950308 := by decide
  rcases family_descends (prefixWord ++ tailWord_950308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950336 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 1, 3]
def baseStart_950336 : Nat := 118140960795 + 950336 * 2 ^ 59
def prefixEnd_950336 : Nat := 4983230072969 + 3 ^ 40 * 950336 * 2
def baseEnd_950336 : Nat := 325319434180866026486327

theorem tailTrace_950336 : CollatzResearch.WordTrace tailWord_950336 prefixEnd_950336 325319434180866026486327 := by
  unfold tailWord_950336
  simp only [CollatzResearch.WordTrace]
  refine ⟨17330800742551225656095431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23107734323401634208127241 17330800742551225656095431)
  ·
    refine ⟨25996201113826838484143147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17330800742551225656095431 25996201113826838484143147)
    ·
      refine ⟨38994301670740257726214721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25996201113826838484143147 38994301670740257726214721)
      ·
        refine ⟨29245726253055193294661041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38994301670740257726214721 29245726253055193294661041)
        ·
          refine ⟨21934294689791394970995781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29245726253055193294661041 21934294689791394970995781)
          ·
            refine ⟨4112680254335886557061709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21934294689791394970995781 4112680254335886557061709)
            ·
              refine ⟨1542255095375957458898141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4112680254335886557061709 1542255095375957458898141)
              ·
                refine ⟨578345660765984047086803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1542255095375957458898141 578345660765984047086803)
                ·
                  refine ⟨867518491148976070630205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578345660765984047086803 867518491148976070630205)
                  ·
                    refine ⟨325319434180866026486327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867518491148976070630205 325319434180866026486327)
                    ·
                      rfl

theorem cell22_950336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_950336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950336 prefixEnd_950336 := by exact prefixLift 950336
  have htrace : WordTrace (prefixWord ++ tailWord_950336) baseStart_950336 baseEnd_950336 := by
    simpa [prefixWord, tailWord_950336, baseEnd_950336] using wordTrace_append hprefix tailTrace_950336
  have hstable : (prefixWord ++ tailWord_950336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950336).length < 2 ^ (prefixWord ++ tailWord_950336).sum := by decide
  have hdescent : baseEnd_950336 < baseStart_950336 := by decide
  rcases family_descends (prefixWord ++ tailWord_950336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950349 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 5]
def baseStart_950349 : Nat := 118140960795 + 950349 * 2 ^ 59
def prefixEnd_950349 : Nat := 4983230072969 + 3 ^ 40 * 950349 * 2
def baseEnd_950349 : Nat := 108441294782179441970429

theorem tailTrace_950349 : CollatzResearch.WordTrace tailWord_950349 prefixEnd_950349 108441294782179441970429 := by
  unfold tailWord_950349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34662075634055354532414101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23108050422703569688276067 34662075634055354532414101)
  ·
    refine ⟨1624784795346344743706911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34662075634055354532414101 1624784795346344743706911)
    ·
      refine ⟨2437177193019517115560367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624784795346344743706911 2437177193019517115560367)
      ·
        refine ⟨3655765789529275673340551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437177193019517115560367 3655765789529275673340551)
        ·
          refine ⟨5483648684293913510010827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3655765789529275673340551 5483648684293913510010827)
          ·
            refine ⟨8225473026440870265016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5483648684293913510010827 8225473026440870265016241)
            ·
              refine ⟨6169104769830652698762181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8225473026440870265016241 6169104769830652698762181)
              ·
                refine ⟨1156707144343247381017909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6169104769830652698762181 1156707144343247381017909)
                ·
                  refine ⟨108441294782179441970429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1156707144343247381017909 108441294782179441970429)
                  ·
                    rfl

theorem cell22_950349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_950349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950349 prefixEnd_950349 := by exact prefixLift 950349
  have htrace : WordTrace (prefixWord ++ tailWord_950349) baseStart_950349 baseEnd_950349 := by
    simpa [prefixWord, tailWord_950349, baseEnd_950349] using wordTrace_append hprefix tailTrace_950349
  have hstable : (prefixWord ++ tailWord_950349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950349).length < 2 ^ (prefixWord ++ tailWord_950349).sum := by decide
  have hdescent : baseEnd_950349 < baseStart_950349 := by decide
  rcases family_descends (prefixWord ++ tailWord_950349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950362 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 3, 4]
def baseStart_950362 : Nat := 118140960795 + 950362 * 2 ^ 59
def prefixEnd_950362 : Nat := 4983230072969 + 3 ^ 40 * 950362 * 2
def baseEnd_950362 : Nat := 325328334512210625336247

theorem tailTrace_950362 : CollatzResearch.WordTrace tailWord_950362 prefixEnd_950362 325328334512210625336247 := by
  unfold tailWord_950362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8665637445752064438159335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23108366522005505168424893 8665637445752064438159335)
  ·
    refine ⟨12998456168628096657239003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8665637445752064438159335 12998456168628096657239003)
    ·
      refine ⟨19497684252942144985858505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12998456168628096657239003 19497684252942144985858505)
      ·
        refine ⟨14623263189706608739393879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19497684252942144985858505 14623263189706608739393879)
        ·
          refine ⟨21934894784559913109090819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14623263189706608739393879 21934894784559913109090819)
          ·
            refine ⟨32902342176839869663636229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21934894784559913109090819 32902342176839869663636229)
            ·
              refine ⟨6169189158157475561931793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32902342176839869663636229 6169189158157475561931793)
              ·
                refine ⟨4626891868618106671448845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6169189158157475561931793 4626891868618106671448845)
                ·
                  refine ⟨1735084450731790001793317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4626891868618106671448845 1735084450731790001793317)
                  ·
                    refine ⟨325328334512210625336247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735084450731790001793317 325328334512210625336247)
                    ·
                      rfl

theorem cell22_950362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_950362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950362 prefixEnd_950362 := by exact prefixLift 950362
  have htrace : WordTrace (prefixWord ++ tailWord_950362) baseStart_950362 baseEnd_950362 := by
    simpa [prefixWord, tailWord_950362, baseEnd_950362] using wordTrace_append hprefix tailTrace_950362
  have hstable : (prefixWord ++ tailWord_950362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950362).length < 2 ^ (prefixWord ++ tailWord_950362).sum := by decide
  have hdescent : baseEnd_950362 < baseStart_950362 := by decide
  rcases family_descends (prefixWord ++ tailWord_950362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950396 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_950396 : Nat := 118140960795 + 950396 * 2 ^ 59
def prefixEnd_950396 : Nat := 4983230072969 + 3 ^ 40 * 950396 * 2
def baseEnd_950396 : Nat := 325339973407045869986143

theorem tailTrace_950396 : CollatzResearch.WordTrace tailWord_950396 prefixEnd_950396 325339973407045869986143 := by
  unfold tailWord_950396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17331894932442540779687521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23109193243256721039583361 17331894932442540779687521)
  ·
    refine ⟨12998921199331905584765641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17331894932442540779687521 12998921199331905584765641)
    ·
      refine ⟨9749190899498929188574231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12998921199331905584765641 9749190899498929188574231)
      ·
        refine ⟨14623786349248393782861347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9749190899498929188574231 14623786349248393782861347)
        ·
          refine ⟨21935679523872590674292021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14623786349248393782861347 21935679523872590674292021)
          ·
            refine ⟨2056469955363055375714877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21935679523872590674292021 2056469955363055375714877)
            ·
              refine ⟨771176233261145765893079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2056469955363055375714877 771176233261145765893079)
              ·
                refine ⟨1156764349891718648839619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771176233261145765893079 1156764349891718648839619)
                ·
                  refine ⟨1735146524837577973259429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1156764349891718648839619 1735146524837577973259429)
                  ·
                    refine ⟨325339973407045869986143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735146524837577973259429 325339973407045869986143)
                    ·
                      rfl

theorem cell22_950396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_950396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950396 prefixEnd_950396 := by exact prefixLift 950396
  have htrace : WordTrace (prefixWord ++ tailWord_950396) baseStart_950396 baseEnd_950396 := by
    simpa [prefixWord, tailWord_950396, baseEnd_950396] using wordTrace_append hprefix tailTrace_950396
  have hstable : (prefixWord ++ tailWord_950396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950396).length < 2 ^ (prefixWord ++ tailWord_950396).sum := by decide
  have hdescent : baseEnd_950396 < baseStart_950396 := by decide
  rcases family_descends (prefixWord ++ tailWord_950396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950426 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_950426 : Nat := 118140960795 + 950426 * 2 ^ 59
def prefixEnd_950426 : Nat := 4983230072969 + 3 ^ 40 * 950426 * 2
def baseEnd_950426 : Nat := 325350243020135791736051

theorem tailTrace_950426 : CollatzResearch.WordTrace tailWord_950426 prefixEnd_950426 325350243020135791736051 := by
  unfold tailWord_950426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8666221013694099170741783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23109922703184264455311421 8666221013694099170741783)
  ·
    refine ⟨12999331520541148756112675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8666221013694099170741783 12999331520541148756112675)
    ·
      refine ⟨19498997280811723134169013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12999331520541148756112675 19498997280811723134169013)
      ·
        refine ⟨1828030995076099043828345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19498997280811723134169013 1828030995076099043828345)
        ·
          refine ⟨1371023246307074282871259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1828030995076099043828345 1371023246307074282871259)
          ·
            refine ⟨2056534869460611424306889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371023246307074282871259 2056534869460611424306889)
            ·
              refine ⟨1542401152095458568230167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2056534869460611424306889 1542401152095458568230167)
              ·
                refine ⟨2313601728143187852345251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542401152095458568230167 2313601728143187852345251)
                ·
                  refine ⟨3470402592214781778517877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2313601728143187852345251 3470402592214781778517877)
                  ·
                    refine ⟨325350243020135791736051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3470402592214781778517877 325350243020135791736051)
                    ·
                      rfl

theorem cell22_950426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_950426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950426 prefixEnd_950426 := by exact prefixLift 950426
  have htrace : WordTrace (prefixWord ++ tailWord_950426) baseStart_950426 baseEnd_950426 := by
    simpa [prefixWord, tailWord_950426, baseEnd_950426] using wordTrace_append hprefix tailTrace_950426
  have hstable : (prefixWord ++ tailWord_950426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950426).length < 2 ^ (prefixWord ++ tailWord_950426).sum := by decide
  have hdescent : baseEnd_950426 < baseStart_950426 := by decide
  rcases family_descends (prefixWord ++ tailWord_950426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950460 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_950460 : Nat := 118140960795 + 950460 * 2 ^ 59
def prefixEnd_950460 : Nat := 4983230072969 + 3 ^ 40 * 950460 * 2
def baseEnd_950460 : Nat := 325361881914971036385947

theorem tailTrace_950460 : CollatzResearch.WordTrace tailWord_950460 prefixEnd_950460 325361881914971036385947 := by
  unfold tailWord_950460
  simp only [CollatzResearch.WordTrace]
  refine ⟨17333062068326610244852417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23110749424435480326469889 17333062068326610244852417)
  ·
    refine ⟨12999796551244957683639313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17333062068326610244852417 12999796551244957683639313)
    ·
      refine ⟨9749847413433718262729485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12999796551244957683639313 9749847413433718262729485)
      ·
        refine ⟨3656192780037644348523557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9749847413433718262729485 3656192780037644348523557)
        ·
          refine ⟨685536146257058315348167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3656192780037644348523557 685536146257058315348167)
          ·
            refine ⟨1028304219385587473022251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685536146257058315348167 1028304219385587473022251)
            ·
              refine ⟨1542456329078381209533377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028304219385587473022251 1542456329078381209533377)
              ·
                refine ⟨1156842246808785907150033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1542456329078381209533377 1156842246808785907150033)
                ·
                  refine ⟨867631685106589430362525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1156842246808785907150033 867631685106589430362525)
                  ·
                    refine ⟨325361881914971036385947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867631685106589430362525 325361881914971036385947)
                    ·
                      rfl

theorem cell22_950460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_950460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950460 prefixEnd_950460 := by exact prefixLift 950460
  have htrace : WordTrace (prefixWord ++ tailWord_950460) baseStart_950460 baseEnd_950460 := by
    simpa [prefixWord, tailWord_950460, baseEnd_950460] using wordTrace_append hprefix tailTrace_950460
  have hstable : (prefixWord ++ tailWord_950460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950460).length < 2 ^ (prefixWord ++ tailWord_950460).sum := by decide
  have hdescent : baseEnd_950460 < baseStart_950460 := by decide
  rcases family_descends (prefixWord ++ tailWord_950460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950512 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 8]
def baseStart_950512 : Nat := 118140960795 + 950512 * 2 ^ 59
def prefixEnd_950512 : Nat := 4983230072969 + 3 ^ 40 * 950512 * 2
def baseEnd_950512 : Nat := 108459894192553411361929

theorem tailTrace_950512 : CollatzResearch.WordTrace tailWord_950512 prefixEnd_950512 108459894192553411361929 := by
  unfold tailWord_950512
  simp only [CollatzResearch.WordTrace]
  refine ⟨17334010366232416685298895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23112013821643222247065193 17334010366232416685298895)
  ·
    refine ⟨26001015549348625027948343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17334010366232416685298895 26001015549348625027948343)
    ·
      refine ⟨39001523324022937541922515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26001015549348625027948343 39001523324022937541922515)
      ·
        refine ⟨58502284986034406312883773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39001523324022937541922515 58502284986034406312883773)
        ·
          refine ⟨21938356869762902367331415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58502284986034406312883773 21938356869762902367331415)
          ·
            refine ⟨32907535304644353550997123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21938356869762902367331415 32907535304644353550997123)
            ·
              refine ⟨49361302956966530326495685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32907535304644353550997123 49361302956966530326495685)
              ·
                refine ⟨9255244304431224436217941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49361302956966530326495685 9255244304431224436217941)
                ·
                  refine ⟨108459894192553411361929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9255244304431224436217941 108459894192553411361929)
                  ·
                    rfl

theorem cell22_950512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_950512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950512 prefixEnd_950512 := by exact prefixLift 950512
  have htrace : WordTrace (prefixWord ++ tailWord_950512) baseStart_950512 baseEnd_950512 := by
    simpa [prefixWord, tailWord_950512, baseEnd_950512] using wordTrace_append hprefix tailTrace_950512
  have hstable : (prefixWord ++ tailWord_950512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950512).length < 2 ^ (prefixWord ++ tailWord_950512).sum := by decide
  have hdescent : baseEnd_950512 < baseStart_950512 := by decide
  rcases family_descends (prefixWord ++ tailWord_950512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950535 : List Nat := [1, 1, 4, 5, 1, 2, 2, 1, 5]
def baseStart_950535 : Nat := 118140960795 + 950535 * 2 ^ 59
def prefixEnd_950535 : Nat := 4983230072969 + 3 ^ 40 * 950535 * 2
def baseEnd_950535 : Nat := 108462518649231946920239

theorem tailTrace_950535 : CollatzResearch.WordTrace tailWord_950535 prefixEnd_950535 108462518649231946920239 := by
  unfold tailWord_950535
  simp only [CollatzResearch.WordTrace]
  refine ⟨34668859611381508298685059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23112573074254338865790039 34668859611381508298685059)
  ·
    refine ⟨52003289417072262448027589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34668859611381508298685059 52003289417072262448027589)
    ·
      refine ⟨9750616765701049209005173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52003289417072262448027589 9750616765701049209005173)
      ·
        refine ⟨914120321784473363344235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9750616765701049209005173 914120321784473363344235)
        ·
          refine ⟨1371180482676710045016353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914120321784473363344235 1371180482676710045016353)
          ·
            refine ⟨1028385362007532533762265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1371180482676710045016353 1028385362007532533762265)
            ·
              refine ⟨771289021505649400321699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028385362007532533762265 771289021505649400321699)
              ·
                refine ⟨1156933532258474100482549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771289021505649400321699 1156933532258474100482549)
                ·
                  refine ⟨108462518649231946920239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1156933532258474100482549 108462518649231946920239)
                  ·
                    rfl

theorem cell22_950535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 1, 5].length) (baseStart_950535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950535 prefixEnd_950535 := by exact prefixLift 950535
  have htrace : WordTrace (prefixWord ++ tailWord_950535) baseStart_950535 baseEnd_950535 := by
    simpa [prefixWord, tailWord_950535, baseEnd_950535] using wordTrace_append hprefix tailTrace_950535
  have hstable : (prefixWord ++ tailWord_950535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950535).length < 2 ^ (prefixWord ++ tailWord_950535).sum := by decide
  have hdescent : baseEnd_950535 < baseStart_950535 := by decide
  rcases family_descends (prefixWord ++ tailWord_950535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950580 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_950580 : Nat := 118140960795 + 950580 * 2 ^ 59
def prefixEnd_950580 : Nat := 4983230072969 + 3 ^ 40 * 950580 * 2
def baseEnd_950580 : Nat := 108467653455776907795193

theorem tailTrace_950580 : CollatzResearch.WordTrace tailWord_950580 prefixEnd_950580 108467653455776907795193 := by
  unfold tailWord_950580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335250448109240492036597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23113667264145653989382129 17335250448109240492036597)
  ·
    refine ⟨1625179729510241296128431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17335250448109240492036597 1625179729510241296128431)
    ·
      refine ⟨2437769594265361944192647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625179729510241296128431 2437769594265361944192647)
      ·
        refine ⟨3656654391398042916288971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2437769594265361944192647 3656654391398042916288971)
        ·
          refine ⟨5484981587097064374433457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3656654391398042916288971 5484981587097064374433457)
          ·
            refine ⟨4113736190322798280825093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5484981587097064374433457 4113736190322798280825093)
            ·
              refine ⟨771325535685524677654705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4113736190322798280825093 771325535685524677654705)
              ·
                refine ⟨578494151764143508241029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 771325535685524677654705 578494151764143508241029)
                ·
                  refine ⟨108467653455776907795193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578494151764143508241029 108467653455776907795193)
                  ·
                    rfl

theorem cell22_950580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_950580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950580 prefixEnd_950580 := by exact prefixLift 950580
  have htrace : WordTrace (prefixWord ++ tailWord_950580) baseStart_950580 baseEnd_950580 := by
    simpa [prefixWord, tailWord_950580, baseEnd_950580] using wordTrace_append hprefix tailTrace_950580
  have hstable : (prefixWord ++ tailWord_950580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950580).length < 2 ^ (prefixWord ++ tailWord_950580).sum := by decide
  have hdescent : baseEnd_950580 < baseStart_950580 := by decide
  rcases family_descends (prefixWord ++ tailWord_950580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950604 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_950604 : Nat := 118140960795 + 950604 * 2 ^ 59
def prefixEnd_950604 : Nat := 4983230072969 + 3 ^ 40 * 950604 * 2
def baseEnd_950604 : Nat := 325411176057802660785505

theorem tailTrace_950604 : CollatzResearch.WordTrace tailWord_950604 prefixEnd_950604 325411176057802660785505 := by
  unfold tailWord_950604
  simp only [CollatzResearch.WordTrace]
  refine ⟨17335688124065766541473433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23114250832087688721964577 17335688124065766541473433)
  ·
    refine ⟨13001766093049324906105075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17335688124065766541473433 13001766093049324906105075)
    ·
      refine ⟨19502649139573987359157613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13001766093049324906105075 19502649139573987359157613)
      ·
        refine ⟨7313493427340245259684105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19502649139573987359157613 7313493427340245259684105)
        ·
          refine ⟨5485120070505183944763079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7313493427340245259684105 5485120070505183944763079)
          ·
            refine ⟨8227680105757775917144619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5485120070505183944763079 8227680105757775917144619)
            ·
              refine ⟨12341520158636663875716929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8227680105757775917144619 12341520158636663875716929)
              ·
                refine ⟨9256140118977497906787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12341520158636663875716929 9256140118977497906787697)
                ·
                  refine ⟨6942105089233123430090773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9256140118977497906787697 6942105089233123430090773)
                  ·
                    refine ⟨325411176057802660785505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6942105089233123430090773 325411176057802660785505)
                    ·
                      rfl

theorem cell22_950604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_950604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950604 prefixEnd_950604 := by exact prefixLift 950604
  have htrace : WordTrace (prefixWord ++ tailWord_950604) baseStart_950604 baseEnd_950604 := by
    simpa [prefixWord, tailWord_950604, baseEnd_950604] using wordTrace_append hprefix tailTrace_950604
  have hstable : (prefixWord ++ tailWord_950604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950604).length < 2 ^ (prefixWord ++ tailWord_950604).sum := by decide
  have hdescent : baseEnd_950604 < baseStart_950604 := by decide
  rcases family_descends (prefixWord ++ tailWord_950604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950623 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 1, 3]
def baseStart_950623 : Nat := 118140960795 + 950623 * 2 ^ 59
def prefixEnd_950623 : Nat := 4983230072969 + 3 ^ 40 * 950623 * 2
def baseEnd_950623 : Nat := 325417680146092944560447

theorem tailTrace_950623 : CollatzResearch.WordTrace tailWord_950623 prefixEnd_950623 325417680146092944560447 := by
  unfold tailWord_950623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34672069235062699327888523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23114712823375132885259015 34672069235062699327888523)
  ·
    refine ⟨52008103852594048991832785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34672069235062699327888523 52008103852594048991832785)
    ·
      refine ⟨39006077889445536743874589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52008103852594048991832785 39006077889445536743874589)
      ·
        refine ⟨14627279208542076278952971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39006077889445536743874589 14627279208542076278952971)
        ·
          refine ⟨21940918812813114418429457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14627279208542076278952971 21940918812813114418429457)
          ·
            refine ⟨16455689109609835813822093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21940918812813114418429457 16455689109609835813822093)
            ·
              refine ⟨6170883416103688430183285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16455689109609835813822093 6170883416103688430183285)
              ·
                refine ⟨578520320259720790329683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6170883416103688430183285 578520320259720790329683)
                ·
                  refine ⟨867780480389581185494525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578520320259720790329683 867780480389581185494525)
                  ·
                    refine ⟨325417680146092944560447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867780480389581185494525 325417680146092944560447)
                    ·
                      rfl

theorem cell22_950623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 3].length) (baseStart_950623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950623 prefixEnd_950623 := by exact prefixLift 950623
  have htrace : WordTrace (prefixWord ++ tailWord_950623) baseStart_950623 baseEnd_950623 := by
    simpa [prefixWord, tailWord_950623, baseEnd_950623] using wordTrace_append hprefix tailTrace_950623
  have hstable : (prefixWord ++ tailWord_950623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950623).length < 2 ^ (prefixWord ++ tailWord_950623).sum := by decide
  have hdescent : baseEnd_950623 < baseStart_950623 := by decide
  rcases family_descends (prefixWord ++ tailWord_950623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950636 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_950636 : Nat := 118140960795 + 950636 * 2 ^ 59
def prefixEnd_950636 : Nat := 4983230072969 + 3 ^ 40 * 950636 * 2
def baseEnd_950636 : Nat := 108474043437255081328469

theorem tailTrace_950636 : CollatzResearch.WordTrace tailWord_950636 prefixEnd_950636 108474043437255081328469 := by
  unfold tailWord_950636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17336271692007801274055881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23115028922677068365407841 17336271692007801274055881)
  ·
    refine ⟨13002203769005850955541911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17336271692007801274055881 13002203769005850955541911)
    ·
      refine ⟨19503305653508776433312867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13002203769005850955541911 19503305653508776433312867)
      ·
        refine ⟨29254958480263164649969301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19503305653508776433312867 29254958480263164649969301)
        ·
          refine ⟨1371326178762335842967311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29254958480263164649969301 1371326178762335842967311)
          ·
            refine ⟨2056989268143503764450967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371326178762335842967311 2056989268143503764450967)
            ·
              refine ⟨3085483902215255646676451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2056989268143503764450967 3085483902215255646676451)
              ·
                refine ⟨4628225853322883470014677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3085483902215255646676451 4628225853322883470014677)
                ·
                  refine ⟨108474043437255081328469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4628225853322883470014677 108474043437255081328469)
                  ·
                    rfl

theorem cell22_950636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_950636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950636 prefixEnd_950636 := by exact prefixLift 950636
  have htrace : WordTrace (prefixWord ++ tailWord_950636) baseStart_950636 baseEnd_950636 := by
    simpa [prefixWord, tailWord_950636, baseEnd_950636] using wordTrace_append hprefix tailTrace_950636
  have hstable : (prefixWord ++ tailWord_950636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950636).length < 2 ^ (prefixWord ++ tailWord_950636).sum := by decide
  have hdescent : baseEnd_950636 < baseStart_950636 := by decide
  rcases family_descends (prefixWord ++ tailWord_950636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950653 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 5]
def baseStart_950653 : Nat := 118140960795 + 950653 * 2 ^ 59
def prefixEnd_950653 : Nat := 4983230072969 + 3 ^ 40 * 950653 * 2
def baseEnd_950653 : Nat := 108475983253060955436785

theorem tailTrace_950653 : CollatzResearch.WordTrace tailWord_950653 prefixEnd_950653 108475983253060955436785 := by
  unfold tailWord_950653
  simp only [CollatzResearch.WordTrace]
  refine ⟨34673163424954014451480613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23115442283302676300987075 34673163424954014451480613)
  ·
    refine ⟨6501218142178877709652615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34673163424954014451480613 6501218142178877709652615)
    ·
      refine ⟨9751827213268316564478923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6501218142178877709652615 9751827213268316564478923)
      ·
        refine ⟨14627740819902474846718385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9751827213268316564478923 14627740819902474846718385)
        ·
          refine ⟨10970805614926856135038789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14627740819902474846718385 10970805614926856135038789)
          ·
            refine ⟨2057026052798785525319773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10970805614926856135038789 2057026052798785525319773)
            ·
              refine ⟨771384769799544571994915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2057026052798785525319773 771384769799544571994915)
              ·
                refine ⟨1157077154699316857992373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771384769799544571994915 1157077154699316857992373)
                ·
                  refine ⟨108475983253060955436785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157077154699316857992373 108475983253060955436785)
                  ·
                    rfl

theorem cell22_950653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_950653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950653 prefixEnd_950653 := by exact prefixLift 950653
  have htrace : WordTrace (prefixWord ++ tailWord_950653) baseStart_950653 baseEnd_950653 := by
    simpa [prefixWord, tailWord_950653, baseEnd_950653] using wordTrace_append hprefix tailTrace_950653
  have hstable : (prefixWord ++ tailWord_950653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950653).length < 2 ^ (prefixWord ++ tailWord_950653).sum := by decide
  have hdescent : baseEnd_950653 < baseStart_950653 := by decide
  rcases family_descends (prefixWord ++ tailWord_950653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950728 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_950728 : Nat := 118140960795 + 950728 * 2 ^ 59
def prefixEnd_950728 : Nat := 4983230072969 + 3 ^ 40 * 950728 * 2
def baseEnd_950728 : Nat := 325453623791907670685125

theorem tailTrace_950728 : CollatzResearch.WordTrace tailWord_950728 prefixEnd_950728 325453623791907670685125 := by
  unfold tailWord_950728
  simp only [CollatzResearch.WordTrace]
  refine ⟨17337949449841151130230419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23117265933121534840307225 17337949449841151130230419)
  ·
    refine ⟨26006924174761726695345629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17337949449841151130230419 26006924174761726695345629)
    ·
      refine ⟨9752596565535647510754611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26006924174761726695345629 9752596565535647510754611)
      ·
        refine ⟨14628894848303471266131917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9752596565535647510754611 14628894848303471266131917)
        ·
          refine ⟨5485835568113801724799469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14628894848303471266131917 5485835568113801724799469)
          ·
            refine ⟨2057188338042675646799801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5485835568113801724799469 2057188338042675646799801)
            ·
              refine ⟨1542891253532006735099851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057188338042675646799801 1542891253532006735099851)
              ·
                refine ⟨2314336880298010102649777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1542891253532006735099851 2314336880298010102649777)
                ·
                  refine ⟨1735752660223507576987333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2314336880298010102649777 1735752660223507576987333)
                  ·
                    refine ⟨325453623791907670685125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735752660223507576987333 325453623791907670685125)
                    ·
                      rfl

theorem cell22_950728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_950728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950728 prefixEnd_950728 := by exact prefixLift 950728
  have htrace : WordTrace (prefixWord ++ tailWord_950728) baseStart_950728 baseEnd_950728 := by
    simpa [prefixWord, tailWord_950728, baseEnd_950728] using wordTrace_append hprefix tailTrace_950728
  have hstable : (prefixWord ++ tailWord_950728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950728).length < 2 ^ (prefixWord ++ tailWord_950728).sum := by decide
  have hdescent : baseEnd_950728 < baseStart_950728 := by decide
  rcases family_descends (prefixWord ++ tailWord_950728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950771 : List Nat := [1, 1, 1, 2, 2, 2, 3, 5, 5]
def baseStart_950771 : Nat := 118140960795 + 950771 * 2 ^ 59
def prefixEnd_950771 : Nat := 4983230072969 + 3 ^ 40 * 950771 * 2
def baseEnd_950771 : Nat := 108489447856889963953331

theorem tailTrace_950771 : CollatzResearch.WordTrace tailWord_950771 prefixEnd_950771 108489447856889963953331 := by
  unfold tailWord_950771
  simp only [CollatzResearch.WordTrace]
  refine ⟨34677467238526520604276167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23118311492351013736184111 34677467238526520604276167)
  ·
    refine ⟨52016200857789780906414251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34677467238526520604276167 52016200857789780906414251)
    ·
      refine ⟨78024301286684671359621377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52016200857789780906414251 78024301286684671359621377)
      ·
        refine ⟨58518225965013503519716033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78024301286684671359621377 58518225965013503519716033)
        ·
          refine ⟨43888669473760127639787025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58518225965013503519716033 43888669473760127639787025)
          ·
            refine ⟨32916502105320095729840269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43888669473760127639787025 32916502105320095729840269)
            ·
              refine ⟨12343688289495035898690101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32916502105320095729840269 12343688289495035898690101)
              ·
                refine ⟨1157220777140159615502197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12343688289495035898690101 1157220777140159615502197)
                ·
                  refine ⟨108489447856889963953331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157220777140159615502197 108489447856889963953331)
                  ·
                    rfl

theorem cell22_950771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 5, 5].length) (baseStart_950771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950771 prefixEnd_950771 := by exact prefixLift 950771
  have htrace : WordTrace (prefixWord ++ tailWord_950771) baseStart_950771 baseEnd_950771 := by
    simpa [prefixWord, tailWord_950771, baseEnd_950771] using wordTrace_append hprefix tailTrace_950771
  have hstable : (prefixWord ++ tailWord_950771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950771).length < 2 ^ (prefixWord ++ tailWord_950771).sum := by decide
  have hdescent : baseEnd_950771 < baseStart_950771 := by decide
  rcases family_descends (prefixWord ++ tailWord_950771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950801 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_950801 : Nat := 118140960795 + 950801 * 2 ^ 59
def prefixEnd_950801 : Nat := 4983230072969 + 3 ^ 40 * 950801 * 2
def baseEnd_950801 : Nat := 325478613183759813609901

theorem tailTrace_950801 : CollatzResearch.WordTrace tailWord_950801 prefixEnd_950801 325478613183759813609901 := by
  unfold tailWord_950801
  simp only [CollatzResearch.WordTrace]
  refine ⟨34678561428417835727868257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23119040952278557151912171 34678561428417835727868257)
  ·
    refine ⟨26008921071313376795901193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34678561428417835727868257 26008921071313376795901193)
    ·
      refine ⟨19506690803485032596925895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26008921071313376795901193 19506690803485032596925895)
      ·
        refine ⟨29260036205227548895388843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19506690803485032596925895 29260036205227548895388843)
        ·
          refine ⟨43890054307841323343083265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29260036205227548895388843 43890054307841323343083265)
          ·
            refine ⟨32917540730880992507312449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43890054307841323343083265 32917540730880992507312449)
            ·
              refine ⟨24688155548160744380484337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32917540730880992507312449 24688155548160744380484337)
              ·
                refine ⟨18516116661120558285363253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24688155548160744380484337 18516116661120558285363253)
                ·
                  refine ⟨1735885936980052339252805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18516116661120558285363253 1735885936980052339252805)
                  ·
                    refine ⟨325478613183759813609901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1735885936980052339252805 325478613183759813609901)
                    ·
                      rfl

theorem cell22_950801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_950801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950801 prefixEnd_950801 := by exact prefixLift 950801
  have htrace : WordTrace (prefixWord ++ tailWord_950801) baseStart_950801 baseEnd_950801 := by
    simpa [prefixWord, tailWord_950801, baseEnd_950801] using wordTrace_append hprefix tailTrace_950801
  have hstable : (prefixWord ++ tailWord_950801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950801).length < 2 ^ (prefixWord ++ tailWord_950801).sum := by decide
  have hdescent : baseEnd_950801 < baseStart_950801 := by decide
  rcases family_descends (prefixWord ++ tailWord_950801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950848 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_950848 : Nat := 118140960795 + 950848 * 2 ^ 59
def prefixEnd_950848 : Nat := 4983230072969 + 3 ^ 40 * 950848 * 2
def baseEnd_950848 : Nat := 325494702244267357684757

theorem tailTrace_950848 : CollatzResearch.WordTrace tailWord_950848 prefixEnd_950848 325494702244267357684757 := by
  unfold tailWord_950848
  simp only [CollatzResearch.WordTrace]
  refine ⟨17340137829623781377414599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23120183772831708503219465 17340137829623781377414599)
  ·
    refine ⟨26010206744435672066121899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17340137829623781377414599 26010206744435672066121899)
    ·
      refine ⟨39015310116653508099182849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26010206744435672066121899 39015310116653508099182849)
      ·
        refine ⟨29261482587490131074387137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39015310116653508099182849 29261482587490131074387137)
        ·
          refine ⟨21946111940617598305790353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29261482587490131074387137 21946111940617598305790353)
          ·
            refine ⟨16459583955463198729342765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21946111940617598305790353 16459583955463198729342765)
            ·
              refine ⟨6172343983298699523503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16459583955463198729342765 6172343983298699523503537)
              ·
                refine ⟨4629257987474024642627653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6172343983298699523503537 4629257987474024642627653)
                ·
                  refine ⟨867985872651379620492685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4629257987474024642627653 867985872651379620492685)
                  ·
                    refine ⟨325494702244267357684757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 867985872651379620492685 325494702244267357684757)
                    ·
                      rfl

theorem cell22_950848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_950848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950848 prefixEnd_950848 := by exact prefixLift 950848
  have htrace : WordTrace (prefixWord ++ tailWord_950848) baseStart_950848 baseEnd_950848 := by
    simpa [prefixWord, tailWord_950848, baseEnd_950848] using wordTrace_append hprefix tailTrace_950848
  have hstable : (prefixWord ++ tailWord_950848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950848).length < 2 ^ (prefixWord ++ tailWord_950848).sum := by decide
  have hdescent : baseEnd_950848 < baseStart_950848 := by decide
  rcases family_descends (prefixWord ++ tailWord_950848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950891 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 6]
def baseStart_950891 : Nat := 118140960795 + 950891 * 2 ^ 59
def prefixEnd_950891 : Nat := 4983230072969 + 3 ^ 40 * 950891 * 2
def baseEnd_950891 : Nat := 325509422023029578859625

theorem tailTrace_950891 : CollatzResearch.WordTrace tailWord_950891 prefixEnd_950891 325509422023029578859625 := by
  unfold tailWord_950891
  simp only [CollatzResearch.WordTrace]
  refine ⟨34681843998091781098644527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23121229332061187399096351 34681843998091781098644527)
  ·
    refine ⟨52022765997137671647966791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34681843998091781098644527 52022765997137671647966791)
    ·
      refine ⟨78034148995706507471950187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52022765997137671647966791 78034148995706507471950187)
      ·
        refine ⟨117051223493559761207925281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78034148995706507471950187 117051223493559761207925281)
        ·
          refine ⟨87788417620169820905943961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117051223493559761207925281 87788417620169820905943961)
          ·
            refine ⟨65841313215127365679457971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87788417620169820905943961 65841313215127365679457971)
            ·
              refine ⟨98761969822691048519186957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65841313215127365679457971 98761969822691048519186957)
              ·
                refine ⟨37035738683509143194695109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98761969822691048519186957 37035738683509143194695109)
                ·
                  refine ⟨6944201003157964349005333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37035738683509143194695109 6944201003157964349005333)
                  ·
                    refine ⟨325509422023029578859625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6944201003157964349005333 325509422023029578859625)
                    ·
                      rfl

theorem cell22_950891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_950891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950891 prefixEnd_950891 := by exact prefixLift 950891
  have htrace : WordTrace (prefixWord ++ tailWord_950891) baseStart_950891 baseEnd_950891 := by
    simpa [prefixWord, tailWord_950891, baseEnd_950891] using wordTrace_append hprefix tailTrace_950891
  have hstable : (prefixWord ++ tailWord_950891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950891).length < 2 ^ (prefixWord ++ tailWord_950891).sum := by decide
  have hdescent : baseEnd_950891 < baseStart_950891 := by decide
  rcases family_descends (prefixWord ++ tailWord_950891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950940 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_950940 : Nat := 118140960795 + 950940 * 2 ^ 59
def prefixEnd_950940 : Nat := 4983230072969 + 3 ^ 40 * 950940 * 2
def baseEnd_950940 : Nat := 108508731908136594794825

theorem tailTrace_950940 : CollatzResearch.WordTrace tailWord_950940 prefixEnd_950940 108508731908136594794825 := by
  unfold tailWord_950940
  simp only [CollatzResearch.WordTrace]
  refine ⟨17341815587457131233589137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23122420783276174978118849 17341815587457131233589137)
  ·
    refine ⟨13006361690592848425191853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17341815587457131233589137 13006361690592848425191853)
    ·
      refine ⟨4877385633972318159446945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13006361690592848425191853 4877385633972318159446945)
      ·
        refine ⟨3658039225479238619585209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4877385633972318159446945 3658039225479238619585209)
        ·
          refine ⟨2743529419109428964688907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3658039225479238619585209 2743529419109428964688907)
          ·
            refine ⟨4115294128664143447033361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2743529419109428964688907 4115294128664143447033361)
            ·
              refine ⟨3086470596498107585275021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4115294128664143447033361 3086470596498107585275021)
              ·
                refine ⟨1157426473686790344478133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3086470596498107585275021 1157426473686790344478133)
                ·
                  refine ⟨108508731908136594794825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1157426473686790344478133 108508731908136594794825)
                  ·
                    rfl

theorem cell22_950940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_950940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950940 prefixEnd_950940 := by exact prefixLift 950940
  have htrace : WordTrace (prefixWord ++ tailWord_950940) baseStart_950940 baseEnd_950940 := by
    simpa [prefixWord, tailWord_950940, baseEnd_950940] using wordTrace_append hprefix tailTrace_950940
  have hstable : (prefixWord ++ tailWord_950940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950940).length < 2 ^ (prefixWord ++ tailWord_950940).sum := by decide
  have hdescent : baseEnd_950940 < baseStart_950940 := by decide
  rcases family_descends (prefixWord ++ tailWord_950940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950961 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 1, 3]
def baseStart_950961 : Nat := 118140960795 + 950961 * 2 ^ 59
def prefixEnd_950961 : Nat := 4983230072969 + 3 ^ 40 * 950961 * 2
def baseEnd_950961 : Nat := 325533384453572729609411

theorem tailTrace_950961 : CollatzResearch.WordTrace tailWord_950961 prefixEnd_950961 325533384453572729609411 := by
  unfold tailWord_950961
  simp only [CollatzResearch.WordTrace]
  refine ⟨34684397107838183053692737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23122931405225455369128491 34684397107838183053692737)
  ·
    refine ⟨26013297830878637290269553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34684397107838183053692737 26013297830878637290269553)
    ·
      refine ⟨19509973373158977967702165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26013297830878637290269553 19509973373158977967702165)
      ·
        refine ⟨914530001866827092236039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19509973373158977967702165 914530001866827092236039)
        ·
          refine ⟨1371795002800240638354059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914530001866827092236039 1371795002800240638354059)
          ·
            refine ⟨2057692504200360957531089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1371795002800240638354059 2057692504200360957531089)
            ·
              refine ⟨1543269378150270718148317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057692504200360957531089 1543269378150270718148317)
              ·
                refine ⟨578726016806351519305619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1543269378150270718148317 578726016806351519305619)
                ·
                  refine ⟨868089025209527278958429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578726016806351519305619 868089025209527278958429)
                  ·
                    refine ⟨325533384453572729609411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 868089025209527278958429 325533384453572729609411)
                    ·
                      rfl

theorem cell22_950961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_950961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950961 prefixEnd_950961 := by exact prefixLift 950961
  have htrace : WordTrace (prefixWord ++ tailWord_950961) baseStart_950961 baseEnd_950961 := by
    simpa [prefixWord, tailWord_950961, baseEnd_950961] using wordTrace_append hprefix tailTrace_950961
  have hstable : (prefixWord ++ tailWord_950961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950961).length < 2 ^ (prefixWord ++ tailWord_950961).sum := by decide
  have hdescent : baseEnd_950961 < baseStart_950961 := by decide
  rcases family_descends (prefixWord ++ tailWord_950961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_950970 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_950970 : Nat := 118140960795 + 950970 * 2 ^ 59
def prefixEnd_950970 : Nat := 4983230072969 + 3 ^ 40 * 950970 * 2
def baseEnd_950970 : Nat := 325536465337499706134383

theorem tailTrace_950970 : CollatzResearch.WordTrace tailWord_950970 prefixEnd_950970 325536465337499706134383 := by
  unfold tailWord_950970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8671181341201394397692591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23123150243203718393846909 8671181341201394397692591)
  ·
    refine ⟨13006772011802091596538887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8671181341201394397692591 13006772011802091596538887)
    ·
      refine ⟨19510158017703137394808331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13006772011802091596538887 19510158017703137394808331)
      ·
        refine ⟨29265237026554706092212497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19510158017703137394808331 29265237026554706092212497)
        ·
          refine ⟨21948927769916029569159373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29265237026554706092212497 21948927769916029569159373)
          ·
            refine ⟨8230847913718511088434765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21948927769916029569159373 8230847913718511088434765)
            ·
              refine ⟨3086567967644441658163037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8230847913718511088434765 3086567967644441658163037)
              ·
                refine ⟨1157462987866665621811139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3086567967644441658163037 1157462987866665621811139)
                ·
                  refine ⟨1736194481799998432716709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157462987866665621811139 1736194481799998432716709)
                  ·
                    refine ⟨325536465337499706134383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736194481799998432716709 325536465337499706134383)
                    ·
                      rfl

theorem cell22_950970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_950970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_950970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_950970 prefixEnd_950970 := by exact prefixLift 950970
  have htrace : WordTrace (prefixWord ++ tailWord_950970) baseStart_950970 baseEnd_950970 := by
    simpa [prefixWord, tailWord_950970, baseEnd_950970] using wordTrace_append hprefix tailTrace_950970
  have hstable : (prefixWord ++ tailWord_950970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_950970).length < 2 ^ (prefixWord ++ tailWord_950970).sum := by decide
  have hdescent : baseEnd_950970 < baseStart_950970 := by decide
  rcases family_descends (prefixWord ++ tailWord_950970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951000 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_951000 : Nat := 118140960795 + 951000 * 2 ^ 59
def prefixEnd_951000 : Nat := 4983230072969 + 3 ^ 40 * 951000 * 2
def baseEnd_951000 : Nat := 325546734950589627884291

theorem tailTrace_951000 : CollatzResearch.WordTrace tailWord_951000 prefixEnd_951000 325546734950589627884291 := by
  unfold tailWord_951000
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342909777348446357181227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23123879703131261809574969 17342909777348446357181227)
  ·
    refine ⟨26014364666022669535771841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17342909777348446357181227 26014364666022669535771841)
    ·
      refine ⟨19510773499517002151828881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26014364666022669535771841 19510773499517002151828881)
      ·
        refine ⟨14633080124637751613871661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19510773499517002151828881 14633080124637751613871661)
        ·
          refine ⟨5487405046739156855201873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14633080124637751613871661 5487405046739156855201873)
          ·
            refine ⟨4115553785054367641401405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5487405046739156855201873 4115553785054367641401405)
            ·
              refine ⟨1543332669395387865525527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4115553785054367641401405 1543332669395387865525527)
              ·
                refine ⟨2314999004093081798288291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1543332669395387865525527 2314999004093081798288291)
                ·
                  refine ⟨3472498506139622697432437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2314999004093081798288291 3472498506139622697432437)
                  ·
                    refine ⟨325546734950589627884291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3472498506139622697432437 325546734950589627884291)
                    ·
                      rfl

theorem cell22_951000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_951000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951000 prefixEnd_951000 := by exact prefixLift 951000
  have htrace : WordTrace (prefixWord ++ tailWord_951000) baseStart_951000 baseEnd_951000 := by
    simpa [prefixWord, tailWord_951000, baseEnd_951000] using wordTrace_append hprefix tailTrace_951000
  have hstable : (prefixWord ++ tailWord_951000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951000).length < 2 ^ (prefixWord ++ tailWord_951000).sum := by decide
  have hdescent : baseEnd_951000 < baseStart_951000 := by decide
  rcases family_descends (prefixWord ++ tailWord_951000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951004 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_951004 : Nat := 118140960795 + 951004 * 2 ^ 59
def prefixEnd_951004 : Nat := 4983230072969 + 3 ^ 40 * 951004 * 2
def baseEnd_951004 : Nat := 325548104232334950784279

theorem tailTrace_951004 : CollatzResearch.WordTrace tailWord_951004 prefixEnd_951004 325548104232334950784279 := by
  unfold tailWord_951004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17342982723341200698754033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 23123976964454934265005377 17342982723341200698754033)
  ·
    refine ⟨13007237042505900524065525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17342982723341200698754033 13007237042505900524065525)
    ·
      refine ⟨1219428472734928174131143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13007237042505900524065525 1219428472734928174131143)
      ·
        refine ⟨1829142709102392261196715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219428472734928174131143 1829142709102392261196715)
        ·
          refine ⟨2743714063653588391795073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1829142709102392261196715 2743714063653588391795073)
          ·
            refine ⟨2057785547740191293846305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2743714063653588391795073 2057785547740191293846305)
            ·
              refine ⟨1543339160805143470384729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2057785547740191293846305 1543339160805143470384729)
              ·
                refine ⟨1157504370603857602788547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543339160805143470384729 1157504370603857602788547)
                ·
                  refine ⟨1736256555905786404182821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157504370603857602788547 1736256555905786404182821)
                  ·
                    refine ⟨325548104232334950784279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736256555905786404182821 325548104232334950784279)
                    ·
                      rfl

theorem cell22_951004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_951004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951004 prefixEnd_951004 := by exact prefixLift 951004
  have htrace : WordTrace (prefixWord ++ tailWord_951004) baseStart_951004 baseEnd_951004 := by
    simpa [prefixWord, tailWord_951004, baseEnd_951004] using wordTrace_append hprefix tailTrace_951004
  have hstable : (prefixWord ++ tailWord_951004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951004).length < 2 ^ (prefixWord ++ tailWord_951004).sum := by decide
  have hdescent : baseEnd_951004 < baseStart_951004 := by decide
  rcases family_descends (prefixWord ++ tailWord_951004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951043 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 6]
def baseStart_951043 : Nat := 118140960795 + 951043 * 2 ^ 59
def prefixEnd_951043 : Nat := 4983230072969 + 3 ^ 40 * 951043 * 2
def baseEnd_951043 : Nat := 325561454729351849059159

theorem tailTrace_951043 : CollatzResearch.WordTrace tailWord_951043 prefixEnd_951043 325561454729351849059159 := by
  unfold tailWord_951043
  simp only [CollatzResearch.WordTrace]
  refine ⟨34687387893541111058177783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23124925262360740705451855 34687387893541111058177783)
  ·
    refine ⟨52031081840311666587266675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34687387893541111058177783 52031081840311666587266675)
    ·
      refine ⟨78046622760467499880900013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52031081840311666587266675 78046622760467499880900013)
      ·
        refine ⟨29267483535175312455337505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78046622760467499880900013 29267483535175312455337505)
        ·
          refine ⟨21950612651381484341503129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29267483535175312455337505 21950612651381484341503129)
          ·
            refine ⟨16462959488536113256127347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21950612651381484341503129 16462959488536113256127347)
            ·
              refine ⟨24694439232804169884191021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16462959488536113256127347 24694439232804169884191021)
              ·
                refine ⟨9260414712301563706571633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24694439232804169884191021 9260414712301563706571633)
                ·
                  refine ⟨6945311034226172779928725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9260414712301563706571633 6945311034226172779928725)
                  ·
                    refine ⟨325561454729351849059159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6945311034226172779928725 325561454729351849059159)
                    ·
                      rfl

theorem cell22_951043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_951043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951043 prefixEnd_951043 := by exact prefixLift 951043
  have htrace : WordTrace (prefixWord ++ tailWord_951043) baseStart_951043 baseEnd_951043 := by
    simpa [prefixWord, tailWord_951043, baseEnd_951043] using wordTrace_append hprefix tailTrace_951043
  have hstable : (prefixWord ++ tailWord_951043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951043).length < 2 ^ (prefixWord ++ tailWord_951043).sum := by decide
  have hdescent : baseEnd_951043 < baseStart_951043 := by decide
  rcases family_descends (prefixWord ++ tailWord_951043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951090 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_951090 : Nat := 118140960795 + 951090 * 2 ^ 59
def prefixEnd_951090 : Nat := 4983230072969 + 3 ^ 40 * 951090 * 2
def baseEnd_951090 : Nat := 325577543789859393134015

theorem tailTrace_951090 : CollatzResearch.WordTrace tailWord_951090 prefixEnd_951090 325577543789859393134015 := by
  unfold tailWord_951090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8672275531092709521284681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23126068082913892056759149 8672275531092709521284681)
  ·
    refine ⟨6504206648319532140963511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8672275531092709521284681 6504206648319532140963511)
    ·
      refine ⟨9756309972479298211445267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6504206648319532140963511 9756309972479298211445267)
      ·
        refine ⟨14634464958718947317167901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9756309972479298211445267 14634464958718947317167901)
        ·
          refine ⟨5487924359519605243937963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14634464958718947317167901 5487924359519605243937963)
          ·
            refine ⟨8231886539279407865906945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5487924359519605243937963 8231886539279407865906945)
            ·
              refine ⟨6173914904459555899430209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8231886539279407865906945 6173914904459555899430209)
              ·
                refine ⟨4630436178344666924572657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6173914904459555899430209 4630436178344666924572657)
                ·
                  refine ⟨3472827133758500193429493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4630436178344666924572657 3472827133758500193429493)
                  ·
                    refine ⟨325577543789859393134015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3472827133758500193429493 325577543789859393134015)
                    ·
                      rfl

theorem cell22_951090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_951090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951090 prefixEnd_951090 := by exact prefixLift 951090
  have htrace : WordTrace (prefixWord ++ tailWord_951090) baseStart_951090 baseEnd_951090 := by
    simpa [prefixWord, tailWord_951090, baseEnd_951090] using wordTrace_append hprefix tailTrace_951090
  have hstable : (prefixWord ++ tailWord_951090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951090).length < 2 ^ (prefixWord ++ tailWord_951090).sum := by decide
  have hdescent : baseEnd_951090 < baseStart_951090 := by decide
  rcases family_descends (prefixWord ++ tailWord_951090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951122 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_951122 : Nat := 118140960795 + 951122 * 2 ^ 59
def prefixEnd_951122 : Nat := 4983230072969 + 3 ^ 40 * 951122 * 2
def baseEnd_951122 : Nat := 325588498043821976333917

theorem tailTrace_951122 : CollatzResearch.WordTrace tailWord_951122 prefixEnd_951122 325588498043821976333917 := by
  unfold tailWord_951122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8672567315063726887575905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 23126846173503271700202413 8672567315063726887575905)
  ·
    refine ⟨6504425486297795165681929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8672567315063726887575905 6504425486297795165681929)
    ·
      refine ⟨4878319114723346374261447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6504425486297795165681929 4878319114723346374261447)
      ·
        refine ⟨7317478672085019561392171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4878319114723346374261447 7317478672085019561392171)
        ·
          refine ⟨10976218008127529342088257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7317478672085019561392171 10976218008127529342088257)
          ·
            refine ⟨8232163506095647006566193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10976218008127529342088257 8232163506095647006566193)
            ·
              refine ⟨6174122629571735254924645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8232163506095647006566193 6174122629571735254924645)
              ·
                refine ⟨1157647993044700360298371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6174122629571735254924645 1157647993044700360298371)
                ·
                  refine ⟨1736471989567050540447557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157647993044700360298371 1736471989567050540447557)
                  ·
                    refine ⟨325588498043821976333917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736471989567050540447557 325588498043821976333917)
                    ·
                      rfl

theorem cell22_951122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_951122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951122 prefixEnd_951122 := by exact prefixLift 951122
  have htrace : WordTrace (prefixWord ++ tailWord_951122) baseStart_951122 baseEnd_951122 := by
    simpa [prefixWord, tailWord_951122, baseEnd_951122] using wordTrace_append hprefix tailTrace_951122
  have hstable : (prefixWord ++ tailWord_951122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951122).length < 2 ^ (prefixWord ++ tailWord_951122).sum := by decide
  have hdescent : baseEnd_951122 < baseStart_951122 := by decide
  rcases family_descends (prefixWord ++ tailWord_951122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951135 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 1, 5]
def baseStart_951135 : Nat := 118140960795 + 951135 * 2 ^ 59
def prefixEnd_951135 : Nat := 4983230072969 + 3 ^ 40 * 951135 * 2
def baseEnd_951135 : Nat := 325592948209494275758877

theorem tailTrace_951135 : CollatzResearch.WordTrace tailWord_951135 prefixEnd_951135 325592948209494275758877 := by
  unfold tailWord_951135
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690743409207810770526859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23127162272805207180351239 34690743409207810770526859)
  ·
    refine ⟨52036115113811716155790289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34690743409207810770526859 52036115113811716155790289)
    ·
      refine ⟨39027086335358787116842717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52036115113811716155790289 39027086335358787116842717)
      ·
        refine ⟨14635157375759545168816019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39027086335358787116842717 14635157375759545168816019)
        ·
          refine ⟨21952736063639317753224029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14635157375759545168816019 21952736063639317753224029)
          ·
            refine ⟨8232276023864744157459011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21952736063639317753224029 8232276023864744157459011)
            ·
              refine ⟨12348414035797116236188517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8232276023864744157459011 12348414035797116236188517)
              ·
                refine ⟨2315327631711959294285347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12348414035797116236188517 2315327631711959294285347)
                ·
                  refine ⟨3472991447567938941428021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2315327631711959294285347 3472991447567938941428021)
                  ·
                    refine ⟨325592948209494275758877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3472991447567938941428021 325592948209494275758877)
                    ·
                      rfl

theorem cell22_951135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_951135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951135 prefixEnd_951135 := by exact prefixLift 951135
  have htrace : WordTrace (prefixWord ++ tailWord_951135) baseStart_951135 baseEnd_951135 := by
    simpa [prefixWord, tailWord_951135, baseEnd_951135] using wordTrace_append hprefix tailTrace_951135
  have hstable : (prefixWord ++ tailWord_951135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951135).length < 2 ^ (prefixWord ++ tailWord_951135).sum := by decide
  have hdescent : baseEnd_951135 < baseStart_951135 := by decide
  rcases family_descends (prefixWord ++ tailWord_951135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_951139 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 1, 4]
def baseStart_951139 : Nat := 118140960795 + 951139 * 2 ^ 59
def prefixEnd_951139 : Nat := 4983230072969 + 3 ^ 40 * 951139 * 2
def baseEnd_951139 : Nat := 325594317491239598658865

theorem tailTrace_951139 : CollatzResearch.WordTrace tailWord_951139 prefixEnd_951139 325594317491239598658865 := by
  unfold tailWord_951139
  simp only [CollatzResearch.WordTrace]
  refine ⟨34690889301193319453672471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 23127259534128879635781647 34690889301193319453672471)
  ·
    refine ⟨52036333951789979180508707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34690889301193319453672471 52036333951789979180508707)
    ·
      refine ⟨78054500927684968770763061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52036333951789979180508707 78054500927684968770763061)
      ·
        refine ⟨7317609461970465822259037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78054500927684968770763061 7317609461970465822259037)
        ·
          refine ⟨2744103548238924683347139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7317609461970465822259037 2744103548238924683347139)
          ·
            refine ⟨4116155322358387025020709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2744103548238924683347139 4116155322358387025020709)
            ·
              refine ⟨771779122942197567191383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4116155322358387025020709 771779122942197567191383)
              ·
                refine ⟨1157668684413296350787075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771779122942197567191383 1157668684413296350787075)
                ·
                  refine ⟨1736503026619944526180613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1157668684413296350787075 1736503026619944526180613)
                  ·
                    refine ⟨325594317491239598658865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1736503026619944526180613 325594317491239598658865)
                    ·
                      rfl

theorem cell22_951139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 4].length) (baseStart_951139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_951139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_951139 prefixEnd_951139 := by exact prefixLift 951139
  have htrace : WordTrace (prefixWord ++ tailWord_951139) baseStart_951139 baseEnd_951139 := by
    simpa [prefixWord, tailWord_951139, baseEnd_951139] using wordTrace_append hprefix tailTrace_951139
  have hstable : (prefixWord ++ tailWord_951139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_951139).length < 2 ^ (prefixWord ++ tailWord_951139).sum := by decide
  have hdescent : baseEnd_951139 < baseStart_951139 := by decide
  rcases family_descends (prefixWord ++ tailWord_951139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
