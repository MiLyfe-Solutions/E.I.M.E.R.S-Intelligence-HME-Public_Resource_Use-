import V185TrunkScan22Chunk180

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1615228 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 4, 3]
def baseStart_1615228 : Nat := 118140960795 + 1615228 * 2 ^ 59
def prefixEnd_1615228 : Nat := 4983230072969 + 3 ^ 40 * 1615228 * 2
def baseEnd_1615228 : Nat := 552925553733674431147805

theorem tailTrace_1615228 : CollatzResearch.WordTrace tailWord_1615228 prefixEnd_1615228 552925553733674431147805 := by
  unfold tailWord_1615228
  simp only [CollatzResearch.WordTrace]
  refine ⟨29456102496156144912627169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39274803328208193216836225 29456102496156144912627169)
  ·
    refine ⟨22092076872117108684470377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29456102496156144912627169 22092076872117108684470377)
    ·
      refine ⟨16569057654087831513352783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22092076872117108684470377 16569057654087831513352783)
      ·
        refine ⟨24853586481131747270029175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16569057654087831513352783 24853586481131747270029175)
        ·
          refine ⟨37280379721697620905043763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24853586481131747270029175 37280379721697620905043763)
          ·
            refine ⟨55920569582546431357565645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37280379721697620905043763 55920569582546431357565645)
            ·
              refine ⟨20970213593454911759087117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55920569582546431357565645 20970213593454911759087117)
              ·
                refine ⟨7863830097545591909657669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20970213593454911759087117 7863830097545591909657669)
                ·
                  refine ⟨1474468143289798483060813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7863830097545591909657669 1474468143289798483060813)
                  ·
                    refine ⟨552925553733674431147805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474468143289798483060813 552925553733674431147805)
                    ·
                      rfl

theorem cell22_1615228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_1615228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615228 prefixEnd_1615228 := by exact prefixLift 1615228
  have htrace : WordTrace (prefixWord ++ tailWord_1615228) baseStart_1615228 baseEnd_1615228 := by
    simpa [prefixWord, tailWord_1615228, baseEnd_1615228] using wordTrace_append hprefix tailTrace_1615228
  have hstable : (prefixWord ++ tailWord_1615228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615228).length < 2 ^ (prefixWord ++ tailWord_1615228).sum := by decide
  have hdescent : baseEnd_1615228 < baseStart_1615228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615262 : List Nat := [4, 3, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1615262 : Nat := 118140960795 + 1615262 * 2 ^ 59
def prefixEnd_1615262 : Nat := 4983230072969 + 3 ^ 40 * 1615262 * 2
def baseEnd_1615262 : Nat := 552937192628509675797701

theorem tailTrace_1615262 : CollatzResearch.WordTrace tailWord_1615262 prefixEnd_1615262 552937192628509675797701 := by
  unfold tailWord_1615262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364180634273639203999005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39275630049459409087994693 7364180634273639203999005)
  ·
    refine ⟨2761567737852614701499627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7364180634273639203999005 2761567737852614701499627)
    ·
      refine ⟨4142351606778922052249441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761567737852614701499627 4142351606778922052249441)
      ·
        refine ⟨3106763705084191539187081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4142351606778922052249441 3106763705084191539187081)
        ·
          refine ⟨2330072778813143654390311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3106763705084191539187081 2330072778813143654390311)
          ·
            refine ⟨3495109168219715481585467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330072778813143654390311 3495109168219715481585467)
            ·
              refine ⟨5242663752329573222378201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495109168219715481585467 5242663752329573222378201)
              ·
                refine ⟨3931997814247179916783651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5242663752329573222378201 3931997814247179916783651)
                ·
                  refine ⟨5897996721370769875175477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3931997814247179916783651 5897996721370769875175477)
                  ·
                    refine ⟨552937192628509675797701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5897996721370769875175477 552937192628509675797701)
                    ·
                      rfl

theorem cell22_1615262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1615262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615262 prefixEnd_1615262 := by exact prefixLift 1615262
  have htrace : WordTrace (prefixWord ++ tailWord_1615262) baseStart_1615262 baseEnd_1615262 := by
    simpa [prefixWord, tailWord_1615262, baseEnd_1615262] using wordTrace_append hprefix tailTrace_1615262
  have hstable : (prefixWord ++ tailWord_1615262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615262).length < 2 ^ (prefixWord ++ tailWord_1615262).sum := by decide
  have hdescent : baseEnd_1615262 < baseStart_1615262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615292 : List Nat := [2, 2, 2, 4, 3, 1, 1, 7]
def baseStart_1615292 : Nat := 118140960795 + 1615292 * 2 ^ 59
def prefixEnd_1615292 : Nat := 4983230072969 + 3 ^ 40 * 1615292 * 2
def baseEnd_1615292 : Nat := 61438606915733288616401

theorem tailTrace_1615292 : CollatzResearch.WordTrace tailWord_1615292 prefixEnd_1615292 61438606915733288616401 := by
  unfold tailWord_1615292
  simp only [CollatzResearch.WordTrace]
  refine ⟨29457269632040214377792065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39276359509386952503722753 29457269632040214377792065)
  ·
    refine ⟨22092952224030160783344049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29457269632040214377792065 22092952224030160783344049)
    ·
      refine ⟨16569714168022620587508037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22092952224030160783344049 16569714168022620587508037)
      ·
        refine ⟨3106821406504241360157757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16569714168022620587508037 3106821406504241360157757)
        ·
          refine ⟨1165058027439090510059159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3106821406504241360157757 1165058027439090510059159)
          ·
            refine ⟨1747587041158635765088739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165058027439090510059159 1747587041158635765088739)
            ·
              refine ⟨2621380561737953647633109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747587041158635765088739 2621380561737953647633109)
              ·
                refine ⟨61438606915733288616401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2621380561737953647633109 61438606915733288616401)
                ·
                  rfl

theorem cell22_1615292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 7].length) (baseStart_1615292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615292 prefixEnd_1615292 := by exact prefixLift 1615292
  have htrace : WordTrace (prefixWord ++ tailWord_1615292) baseStart_1615292 baseEnd_1615292 := by
    simpa [prefixWord, tailWord_1615292, baseEnd_1615292] using wordTrace_append hprefix tailTrace_1615292
  have hstable : (prefixWord ++ tailWord_1615292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615292).length < 2 ^ (prefixWord ++ tailWord_1615292).sum := by decide
  have hdescent : baseEnd_1615292 < baseStart_1615292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615303 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 5]
def baseStart_1615303 : Nat := 118140960795 + 1615303 * 2 ^ 59
def prefixEnd_1615303 : Nat := 4983230072969 + 3 ^ 40 * 1615303 * 2
def baseEnd_1615303 : Nat := 184317075922133078507525

theorem tailTrace_1615303 : CollatzResearch.WordTrace tailWord_1615303 prefixEnd_1615303 184317075922133078507525 := by
  unfold tailWord_1615303
  simp only [CollatzResearch.WordTrace]
  refine ⟨58914940467040577634234563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39276626978027051756156375 58914940467040577634234563)
  ·
    refine ⟨88372410700560866451351845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58914940467040577634234563 88372410700560866451351845)
    ·
      refine ⟨16569827006355162459628471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88372410700560866451351845 16569827006355162459628471)
      ·
        refine ⟨24854740509532743689442707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16569827006355162459628471 24854740509532743689442707)
        ·
          refine ⟨37282110764299115534164061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24854740509532743689442707 37282110764299115534164061)
          ·
            refine ⟨13980791536612168325311523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37282110764299115534164061 13980791536612168325311523)
            ·
              refine ⟨20971187304918252487967285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13980791536612168325311523 20971187304918252487967285)
              ·
                refine ⟨1966048809836086170746933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20971187304918252487967285 1966048809836086170746933)
                ·
                  refine ⟨184317075922133078507525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966048809836086170746933 184317075922133078507525)
                  ·
                    rfl

theorem cell22_1615303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 5].length) (baseStart_1615303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615303 prefixEnd_1615303 := by exact prefixLift 1615303
  have htrace : WordTrace (prefixWord ++ tailWord_1615303) baseStart_1615303 baseEnd_1615303 := by
    simpa [prefixWord, tailWord_1615303, baseEnd_1615303] using wordTrace_append hprefix tailTrace_1615303
  have hstable : (prefixWord ++ tailWord_1615303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615303).length < 2 ^ (prefixWord ++ tailWord_1615303).sum := by decide
  have hdescent : baseEnd_1615303 < baseStart_1615303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615363 : List Nat := [1, 1, 1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_1615363 : Nat := 118140960795 + 1615363 * 2 ^ 59
def prefixEnd_1615363 : Nat := 4983230072969 + 3 ^ 40 * 1615363 * 2
def baseEnd_1615363 : Nat := 552971766992579079022391

theorem tailTrace_1615363 : CollatzResearch.WordTrace tailWord_1615363 prefixEnd_1615363 552971766992579079022391 := by
  unfold tailWord_1615363
  simp only [CollatzResearch.WordTrace]
  refine ⟨58917128846823207881418743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39278085897882138587612495 58917128846823207881418743)
  ·
    refine ⟨88375693270234811822128115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58917128846823207881418743 88375693270234811822128115)
    ·
      refine ⟨132563539905352217733192173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88375693270234811822128115 132563539905352217733192173)
      ·
        refine ⟨49711327464507081649947065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132563539905352217733192173 49711327464507081649947065)
        ·
          refine ⟨37283495598380311237460299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49711327464507081649947065 37283495598380311237460299)
          ·
            refine ⟨55925243397570466856190449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37283495598380311237460299 55925243397570466856190449)
            ·
              refine ⟨41943932548177850142142837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55925243397570466856190449 41943932548177850142142837)
              ·
                refine ⟨3932243676391673450825891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41943932548177850142142837 3932243676391673450825891)
                ·
                  refine ⟨5898365514587510176238837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3932243676391673450825891 5898365514587510176238837)
                  ·
                    refine ⟨552971766992579079022391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5898365514587510176238837 552971766992579079022391)
                    ·
                      rfl

theorem cell22_1615363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_1615363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615363 prefixEnd_1615363 := by exact prefixLift 1615363
  have htrace : WordTrace (prefixWord ++ tailWord_1615363) baseStart_1615363 baseEnd_1615363 := by
    simpa [prefixWord, tailWord_1615363, baseEnd_1615363] using wordTrace_append hprefix tailTrace_1615363
  have hstable : (prefixWord ++ tailWord_1615363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615363).length < 2 ^ (prefixWord ++ tailWord_1615363).sum := by decide
  have hdescent : baseEnd_1615363 < baseStart_1615363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615367 : List Nat := [1, 1, 4, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1615367 : Nat := 118140960795 + 1615367 * 2 ^ 59
def prefixEnd_1615367 : Nat := 4983230072969 + 3 ^ 40 * 1615367 * 2
def baseEnd_1615367 : Nat := 552973136274324401922379

theorem tailTrace_1615367 : CollatzResearch.WordTrace tailWord_1615367 prefixEnd_1615367 552973136274324401922379 := by
  unfold tailWord_1615367
  simp only [CollatzResearch.WordTrace]
  refine ⟨58917274738808716564564355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39278183159205811043042903 58917274738808716564564355)
  ·
    refine ⟨88375912108213074846846533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58917274738808716564564355 88375912108213074846846533)
    ·
      refine ⟨16570483520289951533783725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88375912108213074846846533 16570483520289951533783725)
      ·
        refine ⟨6213931320108731825168897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16570483520289951533783725 6213931320108731825168897)
        ·
          refine ⟨4660448490081548868876673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6213931320108731825168897 4660448490081548868876673)
          ·
            refine ⟨3495336367561161651657505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4660448490081548868876673 3495336367561161651657505)
            ·
              refine ⟨2621502275670871238743129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3495336367561161651657505 2621502275670871238743129)
              ·
                refine ⟨1966126706753153429057347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621502275670871238743129 1966126706753153429057347)
                ·
                  refine ⟨2949190060129730143586021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966126706753153429057347 2949190060129730143586021)
                  ·
                    refine ⟨552973136274324401922379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949190060129730143586021 552973136274324401922379)
                    ·
                      rfl

theorem cell22_1615367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1615367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615367 prefixEnd_1615367 := by exact prefixLift 1615367
  have htrace : WordTrace (prefixWord ++ tailWord_1615367) baseStart_1615367 baseEnd_1615367 := by
    simpa [prefixWord, tailWord_1615367, baseEnd_1615367] using wordTrace_append hprefix tailTrace_1615367
  have hstable : (prefixWord ++ tailWord_1615367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615367).length < 2 ^ (prefixWord ++ tailWord_1615367).sum := by decide
  have hdescent : baseEnd_1615367 < baseStart_1615367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615393 : List Nat := [1, 2, 3, 2, 2, 2, 10]
def baseStart_1615393 : Nat := 118140960795 + 1615393 * 2 ^ 59
def prefixEnd_1615393 : Nat := 4983230072969 + 3 ^ 40 * 1615393 * 2
def baseEnd_1615393 : Nat := 20480816170580333361937

theorem tailTrace_1615393 : CollatzResearch.WordTrace tailWord_1615393 prefixEnd_1615393 20480816170580333361937 := by
  unfold tailWord_1615393
  simp only [CollatzResearch.WordTrace]
  refine ⟨58918223036714523005010833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39278815357809682003340555 58918223036714523005010833)
  ·
    refine ⟨44188667277535892253758125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58918223036714523005010833 44188667277535892253758125)
    ·
      refine ⟨16570750229075959595159297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44188667277535892253758125 16570750229075959595159297)
      ·
        refine ⟨12428062671806969696369473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16570750229075959595159297 12428062671806969696369473)
        ·
          refine ⟨9321047003855227272277105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12428062671806969696369473 9321047003855227272277105)
          ·
            refine ⟨6990785252891420454207829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9321047003855227272277105 6990785252891420454207829)
            ·
              refine ⟨20480816170580333361937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6990785252891420454207829 20480816170580333361937)
              ·
                rfl

theorem cell22_1615393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 10].length) (baseStart_1615393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615393 prefixEnd_1615393 := by exact prefixLift 1615393
  have htrace : WordTrace (prefixWord ++ tailWord_1615393) baseStart_1615393 baseEnd_1615393 := by
    simpa [prefixWord, tailWord_1615393, baseEnd_1615393] using wordTrace_append hprefix tailTrace_1615393
  have hstable : (prefixWord ++ tailWord_1615393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615393).length < 2 ^ (prefixWord ++ tailWord_1615393).sum := by decide
  have hdescent : baseEnd_1615393 < baseStart_1615393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615459 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 1, 3]
def baseStart_1615459 : Nat := 118140960795 + 1615459 * 2 ^ 59
def prefixEnd_1615459 : Nat := 4983230072969 + 3 ^ 40 * 1615459 * 2
def baseEnd_1615459 : Nat := 553004629754466828622097

theorem tailTrace_1615459 : CollatzResearch.WordTrace tailWord_1615459 prefixEnd_1615459 553004629754466828622097 := by
  unfold tailWord_1615459
  simp only [CollatzResearch.WordTrace]
  refine ⟨58920630254475416276913431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39280420169650277517942287 58920630254475416276913431)
  ·
    refine ⟨88380945381713124415370147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58920630254475416276913431 88380945381713124415370147)
    ·
      refine ⟨132571418072569686623055221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88380945381713124415370147 132571418072569686623055221)
      ·
        refine ⟨12428570444303408120911427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132571418072569686623055221 12428570444303408120911427)
        ·
          refine ⟨18642855666455112181367141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12428570444303408120911427 18642855666455112181367141)
          ·
            refine ⟨3495535437460333534006339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18642855666455112181367141 3495535437460333534006339)
            ·
              refine ⟨5243303156190500301009509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495535437460333534006339 5243303156190500301009509)
              ·
                refine ⟨983119341785718806439283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5243303156190500301009509 983119341785718806439283)
                ·
                  refine ⟨1474679012678578209658925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983119341785718806439283 1474679012678578209658925)
                  ·
                    refine ⟨553004629754466828622097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1474679012678578209658925 553004629754466828622097)
                    ·
                      rfl

theorem cell22_1615459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 1, 3].length) (baseStart_1615459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615459 prefixEnd_1615459 := by exact prefixLift 1615459
  have htrace : WordTrace (prefixWord ++ tailWord_1615459) baseStart_1615459 baseEnd_1615459 := by
    simpa [prefixWord, tailWord_1615459, baseEnd_1615459] using wordTrace_append hprefix tailTrace_1615459
  have hstable : (prefixWord ++ tailWord_1615459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615459).length < 2 ^ (prefixWord ++ tailWord_1615459).sum := by decide
  have hdescent : baseEnd_1615459 < baseStart_1615459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615506 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_1615506 : Nat := 118140960795 + 1615506 * 2 ^ 59
def prefixEnd_1615506 : Nat := 4983230072969 + 3 ^ 40 * 1615506 * 2
def baseEnd_1615506 : Nat := 184340239604991457565651

theorem tailTrace_1615506 : CollatzResearch.WordTrace tailWord_1615506 prefixEnd_1615506 184340239604991457565651 := by
  unfold tailWord_1615506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730586121326285825968593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39281562990203428869249581 14730586121326285825968593)
  ·
    refine ⟨11047939590994714369476445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14730586121326285825968593 11047939590994714369476445)
    ·
      refine ⟨4142977346623017888553667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11047939590994714369476445 4142977346623017888553667)
      ·
        refine ⟨6214466019934526832830501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4142977346623017888553667 6214466019934526832830501)
        ·
          refine ⟨1165212378737723781155719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6214466019934526832830501 1165212378737723781155719)
          ·
            refine ⟨1747818568106585671733579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165212378737723781155719 1747818568106585671733579)
            ·
              refine ⟨2621727852159878507600369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747818568106585671733579 2621727852159878507600369)
              ·
                refine ⟨1966295889119908880700277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621727852159878507600369 1966295889119908880700277)
                ·
                  refine ⟨184340239604991457565651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1966295889119908880700277 184340239604991457565651)
                  ·
                    rfl

theorem cell22_1615506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_1615506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615506 prefixEnd_1615506 := by exact prefixLift 1615506
  have htrace : WordTrace (prefixWord ++ tailWord_1615506) baseStart_1615506 baseEnd_1615506 := by
    simpa [prefixWord, tailWord_1615506, baseEnd_1615506] using wordTrace_append hprefix tailTrace_1615506
  have hstable : (prefixWord ++ tailWord_1615506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615506).length < 2 ^ (prefixWord ++ tailWord_1615506).sum := by decide
  have hdescent : baseEnd_1615506 < baseStart_1615506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615562 : List Nat := [3, 1, 2, 1, 5, 2, 8]
def baseStart_1615562 : Nat := 118140960795 + 1615562 * 2 ^ 59
def prefixEnd_1615562 : Nat := 4983230072969 + 3 ^ 40 * 1615562 * 2
def baseEnd_1615562 : Nat := 20482958842941070122103

theorem tailTrace_1615562 : CollatzResearch.WordTrace tailWord_1615562 prefixEnd_1615562 20482958842941070122103 := by
  unfold tailWord_1615562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14731096743275566216978235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39282924648734843245275293 14731096743275566216978235)
  ·
    refine ⟨22096645114913349325467353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14731096743275566216978235 22096645114913349325467353)
    ·
      refine ⟨16572483836185011994100515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22096645114913349325467353 16572483836185011994100515)
      ·
        refine ⟨24858725754277517991150773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16572483836185011994100515 24858725754277517991150773)
        ·
          refine ⟨2330505539463517311670385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24858725754277517991150773 2330505539463517311670385)
          ·
            refine ⟨1747879154597637983752789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2330505539463517311670385 1747879154597637983752789)
            ·
              refine ⟨20482958842941070122103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1747879154597637983752789 20482958842941070122103)
              ·
                rfl

theorem cell22_1615562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 8].length) (baseStart_1615562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615562 prefixEnd_1615562 := by exact prefixLift 1615562
  have htrace : WordTrace (prefixWord ++ tailWord_1615562) baseStart_1615562 baseEnd_1615562 := by
    simpa [prefixWord, tailWord_1615562, baseEnd_1615562] using wordTrace_append hprefix tailTrace_1615562
  have hstable : (prefixWord ++ tailWord_1615562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615562).length < 2 ^ (prefixWord ++ tailWord_1615562).sum := by decide
  have hdescent : baseEnd_1615562 < baseStart_1615562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615564 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_1615564 : Nat := 118140960795 + 1615564 * 2 ^ 59
def prefixEnd_1615564 : Nat := 4983230072969 + 3 ^ 40 * 1615564 * 2
def baseEnd_1615564 : Nat := 553040573400281554746775

theorem tailTrace_1615564 : CollatzResearch.WordTrace tailWord_1615564 prefixEnd_1615564 553040573400281554746775 := by
  unfold tailWord_1615564
  simp only [CollatzResearch.WordTrace]
  refine ⟨29462229959547509604742873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39282973279396679472990497 29462229959547509604742873)
  ·
    refine ⟨22096672469660632203557155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29462229959547509604742873 22096672469660632203557155)
    ·
      refine ⟨33145008704490948305335733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22096672469660632203557155 33145008704490948305335733)
      ·
        refine ⟨3107344566046026403625225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33145008704490948305335733 3107344566046026403625225)
        ·
          refine ⟨2330508424534519802718919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3107344566046026403625225 2330508424534519802718919)
          ·
            refine ⟨3495762636801779704078379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330508424534519802718919 3495762636801779704078379)
            ·
              refine ⟨5243643955202669556117569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3495762636801779704078379 5243643955202669556117569)
              ·
                refine ⟨3932732966402002167088177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5243643955202669556117569 3932732966402002167088177)
                ·
                  refine ⟨2949549724801501625316133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3932732966402002167088177 2949549724801501625316133)
                  ·
                    refine ⟨553040573400281554746775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949549724801501625316133 553040573400281554746775)
                    ·
                      rfl

theorem cell22_1615564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_1615564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615564 prefixEnd_1615564 := by exact prefixLift 1615564
  have htrace : WordTrace (prefixWord ++ tailWord_1615564) baseStart_1615564 baseEnd_1615564 := by
    simpa [prefixWord, tailWord_1615564, baseEnd_1615564] using wordTrace_append hprefix tailTrace_1615564
  have hstable : (prefixWord ++ tailWord_1615564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615564).length < 2 ^ (prefixWord ++ tailWord_1615564).sum := by decide
  have hdescent : baseEnd_1615564 < baseStart_1615564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615575 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1615575 : Nat := 118140960795 + 1615575 * 2 ^ 59
def prefixEnd_1615575 : Nat := 4983230072969 + 3 ^ 40 * 1615575 * 2
def baseEnd_1615575 : Nat := 553044338925081192721741

theorem tailTrace_1615575 : CollatzResearch.WordTrace tailWord_1615575 prefixEnd_1615575 553044338925081192721741 := by
  unfold tailWord_1615575
  simp only [CollatzResearch.WordTrace]
  refine ⟨58924861122055168088136179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39283240748036778725424119 58924861122055168088136179)
  ·
    refine ⟨88387291683082752132204269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58924861122055168088136179 88387291683082752132204269)
    ·
      refine ⟨33145234381156032049576601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88387291683082752132204269 33145234381156032049576601)
      ·
        refine ⟨24858925785867024037182451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33145234381156032049576601 24858925785867024037182451)
        ·
          refine ⟨37288388678800536055773677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24858925785867024037182451 37288388678800536055773677)
          ·
            refine ⟨13983145754550201020915129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37288388678800536055773677 13983145754550201020915129)
            ·
              refine ⟨10487359315912650765686347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13983145754550201020915129 10487359315912650765686347)
              ·
                refine ⟨15731038973868976148529521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487359315912650765686347 15731038973868976148529521)
                ·
                  refine ⟨11798279230401732111397141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15731038973868976148529521 11798279230401732111397141)
                  ·
                    refine ⟨553044338925081192721741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11798279230401732111397141 553044338925081192721741)
                    ·
                      rfl

theorem cell22_1615575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1615575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615575 prefixEnd_1615575 := by exact prefixLift 1615575
  have htrace : WordTrace (prefixWord ++ tailWord_1615575) baseStart_1615575 baseEnd_1615575 := by
    simpa [prefixWord, tailWord_1615575, baseEnd_1615575] using wordTrace_append hprefix tailTrace_1615575
  have hstable : (prefixWord ++ tailWord_1615575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615575).length < 2 ^ (prefixWord ++ tailWord_1615575).sum := by decide
  have hdescent : baseEnd_1615575 < baseStart_1615575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615637 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_1615637 : Nat := 118140960795 + 1615637 * 2 ^ 59
def prefixEnd_1615637 : Nat := 4983230072969 + 3 ^ 40 * 1615637 * 2
def baseEnd_1615637 : Nat := 553065562792133697671551

theorem tailTrace_1615637 : CollatzResearch.WordTrace tailWord_1615637 prefixEnd_1615637 553065562792133697671551 := by
  unfold tailWord_1615637
  simp only [CollatzResearch.WordTrace]
  refine ⟨58927122447830552676893165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39284748298553701784595443 58927122447830552676893165)
  ·
    refine ⟨22097670917936457253834937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58927122447830552676893165 22097670917936457253834937)
    ·
      refine ⟨16573253188452342940376203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22097670917936457253834937 16573253188452342940376203)
      ·
        refine ⟨24859879782678514410564305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16573253188452342940376203 24859879782678514410564305)
        ·
          refine ⟨18644909837008885807923229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24859879782678514410564305 18644909837008885807923229)
          ·
            refine ⟨6991841188878332177971211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18644909837008885807923229 6991841188878332177971211)
            ·
              refine ⟨10487761783317498266956817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991841188878332177971211 10487761783317498266956817)
              ·
                refine ⟨7865821337488123700217613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10487761783317498266956817 7865821337488123700217613)
                ·
                  refine ⟨2949683001558046387581605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7865821337488123700217613 2949683001558046387581605)
                  ·
                    refine ⟨553065562792133697671551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2949683001558046387581605 553065562792133697671551)
                    ·
                      rfl

theorem cell22_1615637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_1615637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615637 prefixEnd_1615637 := by exact prefixLift 1615637
  have htrace : WordTrace (prefixWord ++ tailWord_1615637) baseStart_1615637 baseEnd_1615637 := by
    simpa [prefixWord, tailWord_1615637, baseEnd_1615637] using wordTrace_append hprefix tailTrace_1615637
  have hstable : (prefixWord ++ tailWord_1615637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615637).length < 2 ^ (prefixWord ++ tailWord_1615637).sum := by decide
  have hdescent : baseEnd_1615637 < baseStart_1615637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615652 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_1615652 : Nat := 118140960795 + 1615652 * 2 ^ 59
def prefixEnd_1615652 : Nat := 4983230072969 + 3 ^ 40 * 1615652 * 2
def baseEnd_1615652 : Nat := 184356899199559552848835

theorem tailTrace_1615652 : CollatzResearch.WordTrace tailWord_1615652 prefixEnd_1615652 184356899199559552848835 := by
  unfold tailWord_1615652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29463834771388105119344605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39285113028517473492459473 29463834771388105119344605)
  ·
    refine ⟨11048938039270539419754227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29463834771388105119344605 11048938039270539419754227)
    ·
      refine ⟨16573407058905809129631341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11048938039270539419754227 16573407058905809129631341)
      ·
        refine ⟨6215027647089678423611753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16573407058905809129631341 6215027647089678423611753)
        ·
          refine ⟨4661270735317258817708815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215027647089678423611753 4661270735317258817708815)
          ·
            refine ⟨6991906102975888226563223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661270735317258817708815 6991906102975888226563223)
            ·
              refine ⟨10487859154463832339844835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991906102975888226563223 10487859154463832339844835)
              ·
                refine ⟨15731788731695748509767253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10487859154463832339844835 15731788731695748509767253)
                ·
                  refine ⟨184356899199559552848835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15731788731695748509767253 184356899199559552848835)
                  ·
                    rfl

theorem cell22_1615652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_1615652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615652 prefixEnd_1615652 := by exact prefixLift 1615652
  have htrace : WordTrace (prefixWord ++ tailWord_1615652) baseStart_1615652 baseEnd_1615652 := by
    simpa [prefixWord, tailWord_1615652, baseEnd_1615652] using wordTrace_append hprefix tailTrace_1615652
  have hstable : (prefixWord ++ tailWord_1615652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615652).length < 2 ^ (prefixWord ++ tailWord_1615652).sum := by decide
  have hdescent : baseEnd_1615652 < baseStart_1615652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615686 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1615686 : Nat := 118140960795 + 1615686 * 2 ^ 59
def prefixEnd_1615686 : Nat := 4983230072969 + 3 ^ 40 * 1615686 * 2
def baseEnd_1615686 : Nat := 184360778831171301065467

theorem tailTrace_1615686 : CollatzResearch.WordTrace tailWord_1615686 prefixEnd_1615686 184360778831171301065467 := by
  unfold tailWord_1615686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1841528425770407313919591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39285939749768689363617941 1841528425770407313919591)
  ·
    refine ⟨2762292638655610970879387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1841528425770407313919591 2762292638655610970879387)
    ·
      refine ⟨4143438957983416456319081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2762292638655610970879387 4143438957983416456319081)
      ·
        refine ⟨3107579218487562342239311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4143438957983416456319081 3107579218487562342239311)
        ·
          refine ⟨4661368827731343513358967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3107579218487562342239311 4661368827731343513358967)
          ·
            refine ⟨6992053241597015270038451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661368827731343513358967 6992053241597015270038451)
            ·
              refine ⟨10488079862395522905057677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6992053241597015270038451 10488079862395522905057677)
              ·
                refine ⟨3933029948398321089396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10488079862395522905057677 3933029948398321089396629)
                ·
                  refine ⟨184360778831171301065467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3933029948398321089396629 184360778831171301065467)
                  ·
                    rfl

theorem cell22_1615686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1615686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615686 prefixEnd_1615686 := by exact prefixLift 1615686
  have htrace : WordTrace (prefixWord ++ tailWord_1615686) baseStart_1615686 baseEnd_1615686 := by
    simpa [prefixWord, tailWord_1615686, baseEnd_1615686] using wordTrace_append hprefix tailTrace_1615686
  have hstable : (prefixWord ++ tailWord_1615686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615686).length < 2 ^ (prefixWord ++ tailWord_1615686).sum := by decide
  have hdescent : baseEnd_1615686 < baseStart_1615686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615714 : List Nat := [3, 3, 2, 1, 2, 2, 1, 8]
def baseStart_1615714 : Nat := 118140960795 + 1615714 * 2 ^ 59
def prefixEnd_1615714 : Nat := 4983230072969 + 3 ^ 40 * 1615714 * 2
def baseEnd_1615714 : Nat := 61454657940636795944035

theorem tailTrace_1615714 : CollatzResearch.WordTrace tailWord_1615714 prefixEnd_1615714 61454657940636795944035 := by
  unfold tailWord_1615714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14732482717137898706861549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39286620579034396551630797 14732482717137898706861549)
  ·
    refine ⟨5524681018926712015073081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14732482717137898706861549 5524681018926712015073081)
    ·
      refine ⟨4143510764195034011304811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5524681018926712015073081 4143510764195034011304811)
      ·
        refine ⟨6215266146292551016957217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4143510764195034011304811 6215266146292551016957217)
        ·
          refine ⟨4661449609719413262717913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6215266146292551016957217 4661449609719413262717913)
          ·
            refine ⟨3496087207289559947038435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4661449609719413262717913 3496087207289559947038435)
            ·
              refine ⟨5244130810934339920557653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496087207289559947038435 5244130810934339920557653)
              ·
                refine ⟨61454657940636795944035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5244130810934339920557653 61454657940636795944035)
                ·
                  rfl

theorem cell22_1615714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_1615714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615714 prefixEnd_1615714 := by exact prefixLift 1615714
  have htrace : WordTrace (prefixWord ++ tailWord_1615714) baseStart_1615714 baseEnd_1615714 := by
    simpa [prefixWord, tailWord_1615714, baseEnd_1615714] using wordTrace_append hprefix tailTrace_1615714
  have hstable : (prefixWord ++ tailWord_1615714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615714).length < 2 ^ (prefixWord ++ tailWord_1615714).sum := by decide
  have hdescent : baseEnd_1615714 < baseStart_1615714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615817 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_1615817 : Nat := 118140960795 + 1615817 * 2 ^ 59
def prefixEnd_1615817 : Nat := 4983230072969 + 3 ^ 40 * 1615817 * 2
def baseEnd_1615817 : Nat := 553127180470673228170999

theorem tailTrace_1615817 : CollatzResearch.WordTrace tailWord_1615817 prefixEnd_1615817 553127180470673228170999 := by
  unfold tailWord_1615817
  simp only [CollatzResearch.WordTrace]
  refine ⟨58933687587178443418445705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39289125058118962278963803 58933687587178443418445705)
  ·
    refine ⟨44200265690383832563834279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58933687587178443418445705 44200265690383832563834279)
    ·
      refine ⟨66300398535575748845751419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44200265690383832563834279 66300398535575748845751419)
      ·
        refine ⟨99450597803363623268627129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66300398535575748845751419 99450597803363623268627129)
        ·
          refine ⟨74587948352522717451470347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99450597803363623268627129 74587948352522717451470347)
          ·
            refine ⟨111881922528784076177205521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74587948352522717451470347 111881922528784076177205521)
            ·
              refine ⟨83911441896588057132904141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111881922528784076177205521 83911441896588057132904141)
              ·
                refine ⟨31466790711220521424839053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83911441896588057132904141 31466790711220521424839053)
                ·
                  refine ⟨11800046516707695534314645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31466790711220521424839053 11800046516707695534314645)
                  ·
                    refine ⟨553127180470673228170999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11800046516707695534314645 553127180470673228170999)
                    ·
                      rfl

theorem cell22_1615817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_1615817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615817 prefixEnd_1615817 := by exact prefixLift 1615817
  have htrace : WordTrace (prefixWord ++ tailWord_1615817) baseStart_1615817 baseEnd_1615817 := by
    simpa [prefixWord, tailWord_1615817, baseEnd_1615817] using wordTrace_append hprefix tailTrace_1615817
  have hstable : (prefixWord ++ tailWord_1615817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615817).length < 2 ^ (prefixWord ++ tailWord_1615817).sum := by decide
  have hdescent : baseEnd_1615817 < baseStart_1615817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615819 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 1, 5]
def baseStart_1615819 : Nat := 118140960795 + 1615819 * 2 ^ 59
def prefixEnd_1615819 : Nat := 4983230072969 + 3 ^ 40 * 1615819 * 2
def baseEnd_1615819 : Nat := 553127865111545889620993

theorem tailTrace_1615819 : CollatzResearch.WordTrace tailWord_1615819 prefixEnd_1615819 553127865111545889620993 := by
  unfold tailWord_1615819
  simp only [CollatzResearch.WordTrace]
  refine ⟨58933760533171197760018511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39289173688780798506679007 58933760533171197760018511)
  ·
    refine ⟨88400640799756796640027767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58933760533171197760018511 88400640799756796640027767)
    ·
      refine ⟨132600961199635194960041651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88400640799756796640027767 132600961199635194960041651)
      ·
        refine ⟨198901441799452792440062477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132600961199635194960041651 198901441799452792440062477)
        ·
          refine ⟨74588040674794797165023429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198901441799452792440062477 74588040674794797165023429)
          ·
            refine ⟨13985257626524024468441893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74588040674794797165023429 13985257626524024468441893)
            ·
              refine ⟨2622235804973254587832855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13985257626524024468441893 2622235804973254587832855)
              ·
                refine ⟨3933353707459881881749283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622235804973254587832855 3933353707459881881749283)
                ·
                  refine ⟨5900030561189822822623925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3933353707459881881749283 5900030561189822822623925)
                  ·
                    refine ⟨553127865111545889620993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5900030561189822822623925 553127865111545889620993)
                    ·
                      rfl

theorem cell22_1615819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_1615819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615819 prefixEnd_1615819 := by exact prefixLift 1615819
  have htrace : WordTrace (prefixWord ++ tailWord_1615819) baseStart_1615819 baseEnd_1615819 := by
    simpa [prefixWord, tailWord_1615819, baseEnd_1615819] using wordTrace_append hprefix tailTrace_1615819
  have hstable : (prefixWord ++ tailWord_1615819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615819).length < 2 ^ (prefixWord ++ tailWord_1615819).sum := by decide
  have hdescent : baseEnd_1615819 < baseStart_1615819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615926 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1615926 : Nat := 118140960795 + 1615926 * 2 ^ 59
def prefixEnd_1615926 : Nat := 4983230072969 + 3 ^ 40 * 1615926 * 2
def baseEnd_1615926 : Nat := 553164493398233277195665

theorem tailTrace_1615926 : CollatzResearch.WordTrace tailWord_1615926 prefixEnd_1615926 553164493398233277195665 := by
  unfold tailWord_1615926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3683603946486472189635227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39291775429189036689442421 3683603946486472189635227)
  ·
    refine ⟨5525405919729708284452841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3683603946486472189635227 5525405919729708284452841)
    ·
      refine ⟨4144054439797281213339631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5525405919729708284452841 4144054439797281213339631)
      ·
        refine ⟨6216081659695921820009447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4144054439797281213339631 6216081659695921820009447)
        ·
          refine ⟨9324122489543882730014171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216081659695921820009447 9324122489543882730014171)
          ·
            refine ⟨13986183734315824095021257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9324122489543882730014171 13986183734315824095021257)
            ·
              refine ⟨10489637800736868071265943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13986183734315824095021257 10489637800736868071265943)
              ·
                refine ⟨15734456701105302106898915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10489637800736868071265943 15734456701105302106898915)
                ·
                  refine ⟨23601685051657953160348373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15734456701105302106898915 23601685051657953160348373)
                  ·
                    refine ⟨553164493398233277195665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23601685051657953160348373 553164493398233277195665)
                    ·
                      rfl

theorem cell22_1615926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1615926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615926 prefixEnd_1615926 := by exact prefixLift 1615926
  have htrace : WordTrace (prefixWord ++ tailWord_1615926) baseStart_1615926 baseEnd_1615926 := by
    simpa [prefixWord, tailWord_1615926, baseEnd_1615926] using wordTrace_append hprefix tailTrace_1615926
  have hstable : (prefixWord ++ tailWord_1615926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615926).length < 2 ^ (prefixWord ++ tailWord_1615926).sum := by decide
  have hdescent : baseEnd_1615926 < baseStart_1615926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615969 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_1615969 : Nat := 118140960795 + 1615969 * 2 ^ 59
def prefixEnd_1615969 : Nat := 4983230072969 + 3 ^ 40 * 1615969 * 2
def baseEnd_1615969 : Nat := 553179213176995498370533

theorem tailTrace_1615969 : CollatzResearch.WordTrace tailWord_1615969 prefixEnd_1615969 553179213176995498370533 := by
  unfold tailWord_1615969
  simp only [CollatzResearch.WordTrace]
  refine ⟨58939231482627773377978961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39292820988418515585319307 58939231482627773377978961)
  ·
    refine ⟨44204423611970830033484221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58939231482627773377978961 44204423611970830033484221)
    ·
      refine ⟨16576658854489061262556583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44204423611970830033484221 16576658854489061262556583)
      ·
        refine ⟨24864988281733591893834875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576658854489061262556583 24864988281733591893834875)
        ·
          refine ⟨37297482422600387840752313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24864988281733591893834875 37297482422600387840752313)
          ·
            refine ⟨27973111816950290880564235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37297482422600387840752313 27973111816950290880564235)
            ·
              refine ⟨41959667725425436320846353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27973111816950290880564235 41959667725425436320846353)
              ·
                refine ⟨31469750794069077240634765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41959667725425436320846353 31469750794069077240634765)
                ·
                  refine ⟨11801156547775903965238037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31469750794069077240634765 11801156547775903965238037)
                  ·
                    refine ⟨553179213176995498370533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11801156547775903965238037 553179213176995498370533)
                    ·
                      rfl

theorem cell22_1615969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_1615969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615969 prefixEnd_1615969 := by exact prefixLift 1615969
  have htrace : WordTrace (prefixWord ++ tailWord_1615969) baseStart_1615969 baseEnd_1615969 := by
    simpa [prefixWord, tailWord_1615969, baseEnd_1615969] using wordTrace_append hprefix tailTrace_1615969
  have hstable : (prefixWord ++ tailWord_1615969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615969).length < 2 ^ (prefixWord ++ tailWord_1615969).sum := by decide
  have hdescent : baseEnd_1615969 < baseStart_1615969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615971 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 4, 3]
def baseStart_1615971 : Nat := 118140960795 + 1615971 * 2 ^ 59
def prefixEnd_1615971 : Nat := 4983230072969 + 3 ^ 40 * 1615971 * 2
def baseEnd_1615971 : Nat := 553179897817868159820527

theorem tailTrace_1615971 : CollatzResearch.WordTrace tailWord_1615971 prefixEnd_1615971 553179897817868159820527 := by
  unfold tailWord_1615971
  simp only [CollatzResearch.WordTrace]
  refine ⟨58939304428620527719551767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39292869619080351813034511 58939304428620527719551767)
  ·
    refine ⟨88408956642930791579327651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58939304428620527719551767 88408956642930791579327651)
    ·
      refine ⟨132613434964396187368991477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88408956642930791579327651 132613434964396187368991477)
      ·
        refine ⟨12432509527912142565842951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 132613434964396187368991477 12432509527912142565842951)
        ·
          refine ⟨18648764291868213848764427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12432509527912142565842951 18648764291868213848764427)
          ·
            refine ⟨27973146437802320773146641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18648764291868213848764427 27973146437802320773146641)
            ·
              refine ⟨20979859828351740579859981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27973146437802320773146641 20979859828351740579859981)
              ·
                refine ⟨7867447435631902717447493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20979859828351740579859981 7867447435631902717447493)
                ·
                  refine ⟨1475146394180981759521405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7867447435631902717447493 1475146394180981759521405)
                  ·
                    refine ⟨553179897817868159820527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475146394180981759521405 553179897817868159820527)
                    ·
                      rfl

theorem cell22_1615971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 3].length) (baseStart_1615971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615971 prefixEnd_1615971 := by exact prefixLift 1615971
  have htrace : WordTrace (prefixWord ++ tailWord_1615971) baseStart_1615971 baseEnd_1615971 := by
    simpa [prefixWord, tailWord_1615971, baseEnd_1615971] using wordTrace_append hprefix tailTrace_1615971
  have hstable : (prefixWord ++ tailWord_1615971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615971).length < 2 ^ (prefixWord ++ tailWord_1615971).sum := by decide
  have hdescent : baseEnd_1615971 < baseStart_1615971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1615973 : List Nat := [1, 3, 1, 3, 2, 3, 1, 4, 4]
def baseStart_1615973 : Nat := 118140960795 + 1615973 * 2 ^ 59
def prefixEnd_1615973 : Nat := 4983230072969 + 3 ^ 40 * 1615973 * 2
def baseEnd_1615973 : Nat := 184393527486246940423507

theorem tailTrace_1615973 : CollatzResearch.WordTrace tailWord_1615973 prefixEnd_1615973 184393527486246940423507 := by
  unfold tailWord_1615973
  simp only [CollatzResearch.WordTrace]
  refine ⟨58939377374613282061124573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39292918249742188040749715 58939377374613282061124573)
  ·
    refine ⟨22102266515479980772921715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58939377374613282061124573 22102266515479980772921715)
    ·
      refine ⟨33153399773219971159382573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22102266515479980772921715 33153399773219971159382573)
      ·
        refine ⟨12432524914957489184768465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33153399773219971159382573 12432524914957489184768465)
        ·
          refine ⟨9324393686218116888576349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12432524914957489184768465 9324393686218116888576349)
          ·
            refine ⟨3496647632331793833216131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9324393686218116888576349 3496647632331793833216131)
            ·
              refine ⟨5244971448497690749824197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496647632331793833216131 5244971448497690749824197)
              ·
                refine ⟨983432146593317015592037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5244971448497690749824197 983432146593317015592037)
                ·
                  refine ⟨184393527486246940423507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983432146593317015592037 184393527486246940423507)
                  ·
                    rfl

theorem cell22_1615973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_1615973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1615973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1615973 prefixEnd_1615973 := by exact prefixLift 1615973
  have htrace : WordTrace (prefixWord ++ tailWord_1615973) baseStart_1615973 baseEnd_1615973 := by
    simpa [prefixWord, tailWord_1615973, baseEnd_1615973] using wordTrace_append hprefix tailTrace_1615973
  have hstable : (prefixWord ++ tailWord_1615973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1615973).length < 2 ^ (prefixWord ++ tailWord_1615973).sum := by decide
  have hdescent : baseEnd_1615973 < baseStart_1615973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1615973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616003 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 2, 4]
def baseStart_1616003 : Nat := 118140960795 + 1616003 * 2 ^ 59
def prefixEnd_1616003 : Nat := 4983230072969 + 3 ^ 40 * 1616003 * 2
def baseEnd_1616003 : Nat := 553190852071830743020429

theorem tailTrace_1616003 : CollatzResearch.WordTrace tailWord_1616003 prefixEnd_1616003 553190852071830743020429 := by
  unfold tailWord_1616003
  simp only [CollatzResearch.WordTrace]
  refine ⟨58940471564504597184716663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39293647709669731456477775 58940471564504597184716663)
  ·
    refine ⟨88410707346756895777074995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58940471564504597184716663 88410707346756895777074995)
    ·
      refine ⟨132616061020135343665612493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88410707346756895777074995 132616061020135343665612493)
      ·
        refine ⟨49731022882550753874604685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132616061020135343665612493 49731022882550753874604685)
        ·
          refine ⟨18649133580956532702976757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49731022882550753874604685 18649133580956532702976757)
          ·
            refine ⟨1748356273214674940904071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18649133580956532702976757 1748356273214674940904071)
            ·
              refine ⟨2622534409822012411356107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748356273214674940904071 2622534409822012411356107)
              ·
                refine ⟨3933801614733018617034161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2622534409822012411356107 3933801614733018617034161)
                ·
                  refine ⟨2950351211049763962775621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3933801614733018617034161 2950351211049763962775621)
                  ·
                    refine ⟨553190852071830743020429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950351211049763962775621 553190852071830743020429)
                    ·
                      rfl

theorem cell22_1616003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 4].length) (baseStart_1616003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616003 prefixEnd_1616003 := by exact prefixLift 1616003
  have htrace : WordTrace (prefixWord ++ tailWord_1616003) baseStart_1616003 baseEnd_1616003 := by
    simpa [prefixWord, tailWord_1616003, baseEnd_1616003] using wordTrace_append hprefix tailTrace_1616003
  have hstable : (prefixWord ++ tailWord_1616003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616003).length < 2 ^ (prefixWord ++ tailWord_1616003).sum := by decide
  have hdescent : baseEnd_1616003 < baseStart_1616003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616016 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 5, 3]
def baseStart_1616016 : Nat := 118140960795 + 1616016 * 2 ^ 59
def prefixEnd_1616016 : Nat := 4983230072969 + 3 ^ 40 * 1616016 * 2
def baseEnd_1616016 : Nat := 553195302237503042445389

theorem tailTrace_1616016 : CollatzResearch.WordTrace tailWord_1616016 prefixEnd_1616016 553195302237503042445389 := by
  unfold tailWord_1616016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29470472856728750202469951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39293963808971666936626601 29470472856728750202469951)
  ·
    refine ⟨44205709285093125303704927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29470472856728750202469951 44205709285093125303704927)
    ·
      refine ⟨66308563927639687955557391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44205709285093125303704927 66308563927639687955557391)
      ·
        refine ⟨99462845891459531933336087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66308563927639687955557391 99462845891459531933336087)
        ·
          refine ⟨149194268837189297900004131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99462845891459531933336087 149194268837189297900004131)
          ·
            refine ⟨223791403255783946850006197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149194268837189297900004131 223791403255783946850006197)
            ·
              refine ⟨20980444055229745017188081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 223791403255783946850006197 20980444055229745017188081)
              ·
                refine ⟨15735333041422308762891061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20980444055229745017188081 15735333041422308762891061)
                ·
                  refine ⟨1475187472633341446521037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15735333041422308762891061 1475187472633341446521037)
                  ·
                    refine ⟨553195302237503042445389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475187472633341446521037 553195302237503042445389)
                    ·
                      rfl

theorem cell22_1616016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 5, 3].length) (baseStart_1616016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616016 prefixEnd_1616016 := by exact prefixLift 1616016
  have htrace : WordTrace (prefixWord ++ tailWord_1616016) baseStart_1616016 baseEnd_1616016 := by
    simpa [prefixWord, tailWord_1616016, baseEnd_1616016] using wordTrace_append hprefix tailTrace_1616016
  have hstable : (prefixWord ++ tailWord_1616016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616016).length < 2 ^ (prefixWord ++ tailWord_1616016).sum := by decide
  have hdescent : baseEnd_1616016 < baseStart_1616016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616033 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1616033 : Nat := 118140960795 + 1616033 * 2 ^ 59
def prefixEnd_1616033 : Nat := 4983230072969 + 3 ^ 40 * 1616033 * 2
def baseEnd_1616033 : Nat := 553201121684920664770337

theorem tailTrace_1616033 : CollatzResearch.WordTrace tailWord_1616033 prefixEnd_1616033 553201121684920664770337 := by
  unfold tailWord_1616033
  simp only [CollatzResearch.WordTrace]
  refine ⟨58941565754395912308308753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39294377169597274872205835 58941565754395912308308753)
  ·
    refine ⟨44206174315796934231231565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58941565754395912308308753 44206174315796934231231565)
    ·
      refine ⟨16577315368423850336711837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44206174315796934231231565 16577315368423850336711837)
      ·
        refine ⟨6216493263158943876266939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16577315368423850336711837 6216493263158943876266939)
        ·
          refine ⟨9324739894738415814400409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6216493263158943876266939 9324739894738415814400409)
          ·
            refine ⟨6993554921053811860800307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9324739894738415814400409 6993554921053811860800307)
            ·
              refine ⟨10490332381580717791200461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6993554921053811860800307 10490332381580717791200461)
              ·
                refine ⟨3933874643092769171700173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10490332381580717791200461 3933874643092769171700173)
                ·
                  refine ⟨1475202991159788439387565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3933874643092769171700173 1475202991159788439387565)
                  ·
                    refine ⟨553201121684920664770337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475202991159788439387565 553201121684920664770337)
                    ·
                      rfl

theorem cell22_1616033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1616033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616033 prefixEnd_1616033 := by exact prefixLift 1616033
  have htrace : WordTrace (prefixWord ++ tailWord_1616033) baseStart_1616033 baseEnd_1616033 := by
    simpa [prefixWord, tailWord_1616033, baseEnd_1616033] using wordTrace_append hprefix tailTrace_1616033
  have hstable : (prefixWord ++ tailWord_1616033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616033).length < 2 ^ (prefixWord ++ tailWord_1616033).sum := by decide
  have hdescent : baseEnd_1616033 < baseStart_1616033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616052 : List Nat := [2, 5, 3, 1, 1, 1, 1, 8]
def baseStart_1616052 : Nat := 118140960795 + 1616052 * 2 ^ 59
def prefixEnd_1616052 : Nat := 4983230072969 + 3 ^ 40 * 1616052 * 2
def baseEnd_1616052 : Nat := 61467513974801216505031

theorem tailTrace_1616052 : CollatzResearch.WordTrace tailWord_1616052 prefixEnd_1616052 61467513974801216505031 := by
  unfold tailWord_1616052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29471129370663539276625205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39294839160884719035500273 29471129370663539276625205)
  ·
    refine ⟨2762918378499706807183613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29471129370663539276625205 2762918378499706807183613)
    ·
      refine ⟨1036094391937390052693855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2762918378499706807183613 1036094391937390052693855)
      ·
        refine ⟨1554141587906085079040783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036094391937390052693855 1554141587906085079040783)
        ·
          refine ⟨2331212381859127618561175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554141587906085079040783 2331212381859127618561175)
          ·
            refine ⟨3496818572788691427841763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331212381859127618561175 3496818572788691427841763)
            ·
              refine ⟨5245227859183037141762645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3496818572788691427841763 5245227859183037141762645)
              ·
                refine ⟨61467513974801216505031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5245227859183037141762645 61467513974801216505031)
                ·
                  rfl

theorem cell22_1616052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_1616052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616052 prefixEnd_1616052 := by exact prefixLift 1616052
  have htrace : WordTrace (prefixWord ++ tailWord_1616052) baseStart_1616052 baseEnd_1616052 := by
    simpa [prefixWord, tailWord_1616052, baseEnd_1616052] using wordTrace_append hprefix tailTrace_1616052
  have hstable : (prefixWord ++ tailWord_1616052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616052).length < 2 ^ (prefixWord ++ tailWord_1616052).sum := by decide
  have hdescent : baseEnd_1616052 < baseStart_1616052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616136 : List Nat := [2, 1, 3, 2, 3, 11]
def baseStart_1616136 : Nat := 118140960795 + 1616136 * 2 ^ 59
def prefixEnd_1616136 : Nat := 4983230072969 + 3 ^ 40 * 1616136 * 2
def baseEnd_1616136 : Nat := 6830078773948922585741

theorem tailTrace_1616136 : CollatzResearch.WordTrace tailWord_1616136 prefixEnd_1616136 6830078773948922585741 := by
  unfold tailWord_1616136
  simp only [CollatzResearch.WordTrace]
  refine ⟨29472661236511380449654131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39296881648681840599538841 29472661236511380449654131)
  ·
    refine ⟨44208991854767070674481197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29472661236511380449654131 44208991854767070674481197)
    ·
      refine ⟨16578371945537651502930449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44208991854767070674481197 16578371945537651502930449)
      ·
        refine ⟨12433778959153238627197837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16578371945537651502930449 12433778959153238627197837)
        ·
          refine ⟨4662667109682464485199189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12433778959153238627197837 4662667109682464485199189)
          ·
            refine ⟨6830078773948922585741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4662667109682464485199189 6830078773948922585741)
            ·
              rfl

theorem cell22_1616136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 11].length) (baseStart_1616136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616136 prefixEnd_1616136 := by exact prefixLift 1616136
  have htrace : WordTrace (prefixWord ++ tailWord_1616136) baseStart_1616136 baseEnd_1616136 := by
    simpa [prefixWord, tailWord_1616136, baseEnd_1616136] using wordTrace_append hprefix tailTrace_1616136
  have hstable : (prefixWord ++ tailWord_1616136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616136).length < 2 ^ (prefixWord ++ tailWord_1616136).sum := by decide
  have hdescent : baseEnd_1616136 < baseStart_1616136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616138 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_1616138 : Nat := 118140960795 + 1616138 * 2 ^ 59
def prefixEnd_1616138 : Nat := 4983230072969 + 3 ^ 40 * 1616138 * 2
def baseEnd_1616138 : Nat := 553237065330735390895015

theorem tailTrace_1616138 : CollatzResearch.WordTrace tailWord_1616138 prefixEnd_1616138 553237065330735390895015 := by
  unfold tailWord_1616138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736348854753878810220267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39296930279343676827254045 14736348854753878810220267)
  ·
    refine ⟨22104523282130818215330401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14736348854753878810220267 22104523282130818215330401)
    ·
      refine ⟨16578392461598113661497801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22104523282130818215330401 16578392461598113661497801)
      ·
        refine ⟨12433794346198585246123351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16578392461598113661497801 12433794346198585246123351)
        ·
          refine ⟨18650691519297877869185027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12433794346198585246123351 18650691519297877869185027)
          ·
            refine ⟨27976037278946816803777541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18650691519297877869185027 27976037278946816803777541)
            ·
              refine ⟨5245506989802528150708289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27976037278946816803777541 5245506989802528150708289)
              ·
                refine ⟨3934130242351896113031217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5245506989802528150708289 3934130242351896113031217)
                ·
                  refine ⟨2950597681763922084773413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3934130242351896113031217 2950597681763922084773413)
                  ·
                    refine ⟨553237065330735390895015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2950597681763922084773413 553237065330735390895015)
                    ·
                      rfl

theorem cell22_1616138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_1616138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616138 prefixEnd_1616138 := by exact prefixLift 1616138
  have htrace : WordTrace (prefixWord ++ tailWord_1616138) baseStart_1616138 baseEnd_1616138 := by
    simpa [prefixWord, tailWord_1616138, baseEnd_1616138] using wordTrace_append hprefix tailTrace_1616138
  have hstable : (prefixWord ++ tailWord_1616138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616138).length < 2 ^ (prefixWord ++ tailWord_1616138).sum := by decide
  have hdescent : baseEnd_1616138 < baseStart_1616138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616140 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 2, 3]
def baseStart_1616140 : Nat := 118140960795 + 1616140 * 2 ^ 59
def prefixEnd_1616140 : Nat := 4983230072969 + 3 ^ 40 * 1616140 * 2
def baseEnd_1616140 : Nat := 553237749971608052345009

theorem tailTrace_1616140 : CollatzResearch.WordTrace tailWord_1616140 prefixEnd_1616140 553237749971608052345009 := by
  unfold tailWord_1616140
  simp only [CollatzResearch.WordTrace]
  refine ⟨29472734182504134791226937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39296978910005513054969249 29472734182504134791226937)
  ·
    refine ⟨22104550636878101093420203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29472734182504134791226937 22104550636878101093420203)
    ·
      refine ⟨33156825955317151640130305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22104550636878101093420203 33156825955317151640130305)
      ·
        refine ⟨24867619466487863730097729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33156825955317151640130305 24867619466487863730097729)
        ·
          refine ⟨18650714599865897797573297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24867619466487863730097729 18650714599865897797573297)
          ·
            refine ⟨13988035949899423348179973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18650714599865897797573297 13988035949899423348179973)
            ·
              refine ⟨2622756740606141877783745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13988035949899423348179973 2622756740606141877783745)
              ·
                refine ⟨1967067555454606408337809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622756740606141877783745 1967067555454606408337809)
                ·
                  refine ⟨1475300666590954806253357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967067555454606408337809 1475300666590954806253357)
                  ·
                    refine ⟨553237749971608052345009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475300666590954806253357 553237749971608052345009)
                    ·
                      rfl

theorem cell22_1616140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_1616140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616140 prefixEnd_1616140 := by exact prefixLift 1616140
  have htrace : WordTrace (prefixWord ++ tailWord_1616140) baseStart_1616140 baseEnd_1616140 := by
    simpa [prefixWord, tailWord_1616140, baseEnd_1616140] using wordTrace_append hprefix tailTrace_1616140
  have hstable : (prefixWord ++ tailWord_1616140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616140).length < 2 ^ (prefixWord ++ tailWord_1616140).sum := by decide
  have hdescent : baseEnd_1616140 < baseStart_1616140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616211 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_1616211 : Nat := 118140960795 + 1616211 * 2 ^ 59
def prefixEnd_1616211 : Nat := 4983230072969 + 3 ^ 40 * 1616211 * 2
def baseEnd_1616211 : Nat := 553262054722587533819791

theorem tailTrace_1616211 : CollatzResearch.WordTrace tailWord_1616211 prefixEnd_1616211 553262054722587533819791 := by
  unfold tailWord_1616211
  simp only [CollatzResearch.WordTrace]
  refine ⟨58948057947751048708288487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39298705298500699138858991 58948057947751048708288487)
  ·
    refine ⟨88422086921626573062432731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58948057947751048708288487 88422086921626573062432731)
    ·
      refine ⟨132633130382439859593649097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88422086921626573062432731 132633130382439859593649097)
      ·
        refine ⟨99474847786829894695236823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132633130382439859593649097 99474847786829894695236823)
        ·
          refine ⟨149212271680244842042855235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99474847786829894695236823 149212271680244842042855235)
          ·
            refine ⟨223818407520367263064282853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149212271680244842042855235 223818407520367263064282853)
            ·
              refine ⟨41965951410068861824553035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 223818407520367263064282853 41965951410068861824553035)
              ·
                refine ⟨62948927115103292736829553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41965951410068861824553035 62948927115103292736829553)
                ·
                  refine ⟨47211695336327469552622165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62948927115103292736829553 47211695336327469552622165)
                  ·
                    refine ⟨553262054722587533819791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47211695336327469552622165 553262054722587533819791)
                    ·
                      rfl

theorem cell22_1616211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_1616211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616211 prefixEnd_1616211 := by exact prefixLift 1616211
  have htrace : WordTrace (prefixWord ++ tailWord_1616211) baseStart_1616211 baseEnd_1616211 := by
    simpa [prefixWord, tailWord_1616211, baseEnd_1616211] using wordTrace_append hprefix tailTrace_1616211
  have hstable : (prefixWord ++ tailWord_1616211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616211).length < 2 ^ (prefixWord ++ tailWord_1616211).sum := by decide
  have hdescent : baseEnd_1616211 < baseStart_1616211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616215 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 5]
def baseStart_1616215 : Nat := 118140960795 + 1616215 * 2 ^ 59
def prefixEnd_1616215 : Nat := 4983230072969 + 3 ^ 40 * 1616215 * 2
def baseEnd_1616215 : Nat := 184421141334777618906593

theorem tailTrace_1616215 : CollatzResearch.WordTrace tailWord_1616215 prefixEnd_1616215 184421141334777618906593 := by
  unfold tailWord_1616215
  simp only [CollatzResearch.WordTrace]
  refine ⟨58948203839736557391434099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39298802559824371594289399 58948203839736557391434099)
  ·
    refine ⟨88422305759604836087151149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58948203839736557391434099 88422305759604836087151149)
    ·
      refine ⟨33158364659851813532681681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88422305759604836087151149 33158364659851813532681681)
      ·
        refine ⟨24868773494888860149511261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33158364659851813532681681 24868773494888860149511261)
        ·
          refine ⟨9325790060583322556066723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24868773494888860149511261 9325790060583322556066723)
          ·
            refine ⟨13988685090874983834100085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9325790060583322556066723 13988685090874983834100085)
            ·
              refine ⟨1311439227269529734446883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13988685090874983834100085 1311439227269529734446883)
              ·
                refine ⟨1967158840904294601670325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311439227269529734446883 1967158840904294601670325)
                ·
                  refine ⟨184421141334777618906593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1967158840904294601670325 184421141334777618906593)
                  ·
                    rfl

theorem cell22_1616215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 5].length) (baseStart_1616215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616215 prefixEnd_1616215 := by exact prefixLift 1616215
  have htrace : WordTrace (prefixWord ++ tailWord_1616215) baseStart_1616215 baseEnd_1616215 := by
    simpa [prefixWord, tailWord_1616215, baseEnd_1616215] using wordTrace_append hprefix tailTrace_1616215
  have hstable : (prefixWord ++ tailWord_1616215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616215).length < 2 ^ (prefixWord ++ tailWord_1616215).sum := by decide
  have hdescent : baseEnd_1616215 < baseStart_1616215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616236 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 1, 3]
def baseStart_1616236 : Nat := 118140960795 + 1616236 * 2 ^ 59
def prefixEnd_1616236 : Nat := 4983230072969 + 3 ^ 40 * 1616236 * 2
def baseEnd_1616236 : Nat := 553270612733495801944715

theorem tailTrace_1616236 : CollatzResearch.WordTrace tailWord_1616236 prefixEnd_1616236 553270612733495801944715 := by
  unfold tailWord_1616236
  simp only [CollatzResearch.WordTrace]
  refine ⟨29474484886330238988974281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39299313181773651985299041 29474484886330238988974281)
  ·
    refine ⟨22105863664747679241730711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29474484886330238988974281 22105863664747679241730711)
    ·
      refine ⟨33158795497121518862596067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22105863664747679241730711 33158795497121518862596067)
      ·
        refine ⟨49738193245682278293894101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33158795497121518862596067 49738193245682278293894101)
        ·
          refine ⟨1165738904195678397513143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49738193245682278293894101 1165738904195678397513143)
          ·
            refine ⟨1748608356293517596269715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165738904195678397513143 1748608356293517596269715)
            ·
              refine ⟨2622912534440276394404573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1748608356293517596269715 2622912534440276394404573)
              ·
                refine ⟨983592200415103647901715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2622912534440276394404573 983592200415103647901715)
                ·
                  refine ⟨1475388300622655471852573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983592200415103647901715 1475388300622655471852573)
                  ·
                    refine ⟨553270612733495801944715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475388300622655471852573 553270612733495801944715)
                    ·
                      rfl

theorem cell22_1616236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_1616236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616236 prefixEnd_1616236 := by exact prefixLift 1616236
  have htrace : WordTrace (prefixWord ++ tailWord_1616236) baseStart_1616236 baseEnd_1616236 := by
    simpa [prefixWord, tailWord_1616236, baseEnd_1616236] using wordTrace_append hprefix tailTrace_1616236
  have hstable : (prefixWord ++ tailWord_1616236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616236).length < 2 ^ (prefixWord ++ tailWord_1616236).sum := by decide
  have hdescent : baseEnd_1616236 < baseStart_1616236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616266 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 5]
def baseStart_1616266 : Nat := 118140960795 + 1616266 * 2 ^ 59
def prefixEnd_1616266 : Nat := 4983230072969 + 3 ^ 40 * 1616266 * 2
def baseEnd_1616266 : Nat := 184426960782195241231541

theorem tailTrace_1616266 : CollatzResearch.WordTrace tailWord_1616266 prefixEnd_1616266 184426960782195241231541 := by
  unfold tailWord_1616266
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737515990637948275385163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39300042641701195401027101 14737515990637948275385163)
  ·
    refine ⟨22106273985956922413077745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14737515990637948275385163 22106273985956922413077745)
    ·
      refine ⟨16579705489467691809808309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22106273985956922413077745 16579705489467691809808309)
      ·
        refine ⟨1554347389637596107169529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16579705489467691809808309 1554347389637596107169529)
        ·
          refine ⟨1165760542228197080377147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554347389637596107169529 1165760542228197080377147)
          ·
            refine ⟨1748640813342295620565721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165760542228197080377147 1748640813342295620565721)
            ·
              refine ⟨1311480610006721715424291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748640813342295620565721 1311480610006721715424291)
              ·
                refine ⟨1967220915010082573136437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311480610006721715424291 1967220915010082573136437)
                ·
                  refine ⟨184426960782195241231541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1967220915010082573136437 184426960782195241231541)
                  ·
                    rfl

theorem cell22_1616266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_1616266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616266 prefixEnd_1616266 := by exact prefixLift 1616266
  have htrace : WordTrace (prefixWord ++ tailWord_1616266) baseStart_1616266 baseEnd_1616266 := by
    simpa [prefixWord, tailWord_1616266, baseEnd_1616266] using wordTrace_append hprefix tailTrace_1616266
  have hstable : (prefixWord ++ tailWord_1616266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616266).length < 2 ^ (prefixWord ++ tailWord_1616266).sum := by decide
  have hdescent : baseEnd_1616266 < baseStart_1616266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616288 : List Nat := [2, 1, 1, 4, 1, 3, 2, 8]
def baseStart_1616288 : Nat := 118140960795 + 1616288 * 2 ^ 59
def prefixEnd_1616288 : Nat := 4983230072969 + 3 ^ 40 * 1616288 * 2
def baseEnd_1616288 : Nat := 61476490377353888849395

theorem tailTrace_1616288 : CollatzResearch.WordTrace tailWord_1616288 prefixEnd_1616288 61476490377353888849395 := by
  unfold tailWord_1616288
  simp only [CollatzResearch.WordTrace]
  refine ⟨29475433184236045429420759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39300577578981393905894345 29475433184236045429420759)
  ·
    refine ⟨44213149776354068144131139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29475433184236045429420759 44213149776354068144131139)
    ·
      refine ⟨66319724664531102216196709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44213149776354068144131139 66319724664531102216196709)
      ·
        refine ⟨12434948374599581665536883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66319724664531102216196709 12434948374599581665536883)
        ·
          refine ⟨18652422561899372498305325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12434948374599581665536883 18652422561899372498305325)
          ·
            refine ⟨6994658460712264686864497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18652422561899372498305325 6994658460712264686864497)
            ·
              refine ⟨5245993845534198515148373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6994658460712264686864497 5245993845534198515148373)
              ·
                refine ⟨61476490377353888849395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5245993845534198515148373 61476490377353888849395)
                ·
                  rfl

theorem cell22_1616288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_1616288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616288 prefixEnd_1616288 := by exact prefixLift 1616288
  have htrace : WordTrace (prefixWord ++ tailWord_1616288) baseStart_1616288 baseEnd_1616288 := by
    simpa [prefixWord, tailWord_1616288, baseEnd_1616288] using wordTrace_append hprefix tailTrace_1616288
  have hstable : (prefixWord ++ tailWord_1616288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616288).length < 2 ^ (prefixWord ++ tailWord_1616288).sum := by decide
  have hdescent : baseEnd_1616288 < baseStart_1616288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616309 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_1616309 : Nat := 118140960795 + 1616309 * 2 ^ 59
def prefixEnd_1616309 : Nat := 4983230072969 + 3 ^ 40 * 1616309 * 2
def baseEnd_1616309 : Nat := 553295602125347944869491

theorem tailTrace_1616309 : CollatzResearch.WordTrace tailWord_1616309 prefixEnd_1616309 553295602125347944869491 := by
  unfold tailWord_1616309
  simp only [CollatzResearch.WordTrace]
  refine ⟨58951632301396011445355981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39301088200930674296903987 58951632301396011445355981)
  ·
    refine ⟨22106862113023504292008493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58951632301396011445355981 22106862113023504292008493)
    ·
      refine ⟨8290073292383814109503185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22106862113023504292008493 8290073292383814109503185)
      ·
        refine ⟨6217554969287860582127389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8290073292383814109503185 6217554969287860582127389)
        ·
          refine ⟨2331583113482947718297771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6217554969287860582127389 2331583113482947718297771)
          ·
            refine ⟨3497374670224421577446657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2331583113482947718297771 3497374670224421577446657)
            ·
              refine ⟨2623031002668316183084993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3497374670224421577446657 2623031002668316183084993)
              ·
                refine ⟨1967273252001237137313745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623031002668316183084993 1967273252001237137313745)
                ·
                  refine ⟨1475454939000927852985309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967273252001237137313745 1475454939000927852985309)
                  ·
                    refine ⟨553295602125347944869491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475454939000927852985309 553295602125347944869491)
                    ·
                      rfl

theorem cell22_1616309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_1616309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616309 prefixEnd_1616309 := by exact prefixLift 1616309
  have htrace : WordTrace (prefixWord ++ tailWord_1616309) baseStart_1616309 baseEnd_1616309 := by
    simpa [prefixWord, tailWord_1616309, baseEnd_1616309] using wordTrace_append hprefix tailTrace_1616309
  have hstable : (prefixWord ++ tailWord_1616309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616309).length < 2 ^ (prefixWord ++ tailWord_1616309).sum := by decide
  have hdescent : baseEnd_1616309 < baseStart_1616309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616320 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 3, 3]
def baseStart_1616320 : Nat := 118140960795 + 1616320 * 2 ^ 59
def prefixEnd_1616320 : Nat := 4983230072969 + 3 ^ 40 * 1616320 * 2
def baseEnd_1616320 : Nat := 553299367650147582844457

theorem tailTrace_1616320 : CollatzResearch.WordTrace tailWord_1616320 prefixEnd_1616320 553299367650147582844457 := by
  unfold tailWord_1616320
  simp only [CollatzResearch.WordTrace]
  refine ⟨29476016752178080162003207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39301355669570773549337609 29476016752178080162003207)
  ·
    refine ⟨44214025128267120243004811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29476016752178080162003207 44214025128267120243004811)
    ·
      refine ⟨66321037692400680364507217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44214025128267120243004811 66321037692400680364507217)
      ·
        refine ⟨49740778269300510273380413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66321037692400680364507217 49740778269300510273380413)
        ·
          refine ⟨18652791850987691352517655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49740778269300510273380413 18652791850987691352517655)
          ·
            refine ⟨27979187776481537028776483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18652791850987691352517655 27979187776481537028776483)
            ·
              refine ⟨41968781664722305543164725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27979187776481537028776483 41968781664722305543164725)
              ·
                refine ⟨3934573281067716144671693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41968781664722305543164725 3934573281067716144671693)
                ·
                  refine ⟨1475464980400393554251885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3934573281067716144671693 1475464980400393554251885)
                  ·
                    refine ⟨553299367650147582844457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475464980400393554251885 553299367650147582844457)
                    ·
                      rfl

theorem cell22_1616320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 3, 3].length) (baseStart_1616320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616320 prefixEnd_1616320 := by exact prefixLift 1616320
  have htrace : WordTrace (prefixWord ++ tailWord_1616320) baseStart_1616320 baseEnd_1616320 := by
    simpa [prefixWord, tailWord_1616320, baseEnd_1616320] using wordTrace_append hprefix tailTrace_1616320
  have hstable : (prefixWord ++ tailWord_1616320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616320).length < 2 ^ (prefixWord ++ tailWord_1616320).sum := by decide
  have hdescent : baseEnd_1616320 < baseStart_1616320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616395 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 6]
def baseStart_1616395 : Nat := 118140960795 + 1616395 * 2 ^ 59
def prefixEnd_1616395 : Nat := 4983230072969 + 3 ^ 40 * 1616395 * 2
def baseEnd_1616395 : Nat := 184441680560957462406409

theorem tailTrace_1616395 : CollatzResearch.WordTrace tailWord_1616395 prefixEnd_1616395 184441680560957462406409 := by
  unfold tailWord_1616395
  simp only [CollatzResearch.WordTrace]
  refine ⟨58954768979084448132986639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39303179319389632088657759 58954768979084448132986639)
  ·
    refine ⟨88432153468626672199479959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58954768979084448132986639 88432153468626672199479959)
    ·
      refine ⟨132648230202940008299219939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88432153468626672199479959 132648230202940008299219939)
      ·
        refine ⟨198972345304410012448829909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132648230202940008299219939 198972345304410012448829909)
        ·
          refine ⟨4663414343072109666769451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 198972345304410012448829909 4663414343072109666769451)
          ·
            refine ⟨6995121514608164500154177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663414343072109666769451 6995121514608164500154177)
            ·
              refine ⟨5246341135956123375115633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6995121514608164500154177 5246341135956123375115633)
              ·
                refine ⟨3934755851967092531336725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5246341135956123375115633 3934755851967092531336725)
                ·
                  refine ⟨184441680560957462406409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3934755851967092531336725 184441680560957462406409)
                  ·
                    rfl

theorem cell22_1616395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_1616395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616395 prefixEnd_1616395 := by exact prefixLift 1616395
  have htrace : WordTrace (prefixWord ++ tailWord_1616395) baseStart_1616395 baseEnd_1616395 := by
    simpa [prefixWord, tailWord_1616395, baseEnd_1616395] using wordTrace_append hprefix tailTrace_1616395
  have hstable : (prefixWord ++ tailWord_1616395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616395).length < 2 ^ (prefixWord ++ tailWord_1616395).sum := by decide
  have hdescent : baseEnd_1616395 < baseStart_1616395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616410 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_1616410 : Nat := 118140960795 + 1616410 * 2 ^ 59
def prefixEnd_1616410 : Nat := 4983230072969 + 3 ^ 40 * 1616410 * 2
def baseEnd_1616410 : Nat := 553330176489417348094181

theorem tailTrace_1616410 : CollatzResearch.WordTrace tailWord_1616410 prefixEnd_1616410 553330176489417348094181 := by
  unfold tailWord_1616410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14738829018507526423695671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39303544049353403796521789 14738829018507526423695671)
  ·
    refine ⟨22108243527761289635543507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14738829018507526423695671 22108243527761289635543507)
    ·
      refine ⟨33162365291641934453315261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22108243527761289635543507 33162365291641934453315261)
      ·
        refine ⟨12435886984365725419993223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33162365291641934453315261 12435886984365725419993223)
        ·
          refine ⟨18653830476548588129989835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12435886984365725419993223 18653830476548588129989835)
          ·
            refine ⟨27980745714822882194984753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18653830476548588129989835 27980745714822882194984753)
            ·
              refine ⟨20985559286117161646238565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27980745714822882194984753 20985559286117161646238565)
              ·
                refine ⟨3934792366146967808669731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20985559286117161646238565 3934792366146967808669731)
                ·
                  refine ⟨5902188549220451713004597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3934792366146967808669731 5902188549220451713004597)
                  ·
                    refine ⟨553330176489417348094181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5902188549220451713004597 553330176489417348094181)
                    ·
                      rfl

theorem cell22_1616410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_1616410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616410 prefixEnd_1616410 := by exact prefixLift 1616410
  have htrace : WordTrace (prefixWord ++ tailWord_1616410) baseStart_1616410 baseEnd_1616410 := by
    simpa [prefixWord, tailWord_1616410, baseEnd_1616410] using wordTrace_append hprefix tailTrace_1616410
  have hstable : (prefixWord ++ tailWord_1616410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616410).length < 2 ^ (prefixWord ++ tailWord_1616410).sum := by decide
  have hdescent : baseEnd_1616410 < baseStart_1616410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616440 : List Nat := [2, 1, 2, 1, 4, 1, 4, 7]
def baseStart_1616440 : Nat := 118140960795 + 1616440 * 2 ^ 59
def prefixEnd_1616440 : Nat := 4983230072969 + 3 ^ 40 * 1616440 * 2
def baseEnd_1616440 : Nat := 61482271789167474427121

theorem tailTrace_1616440 : CollatzResearch.WordTrace tailWord_1616440 prefixEnd_1616440 61482271789167474427121 := by
  unfold tailWord_1616440
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478205131960710409187387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39304273509280947212249849 29478205131960710409187387)
  ·
    refine ⟨44217307697941065613781081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29478205131960710409187387 44217307697941065613781081)
    ·
      refine ⟨33162980773455799210335811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44217307697941065613781081 33162980773455799210335811)
      ·
        refine ⟨49744471160183698815503717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33162980773455799210335811 49744471160183698815503717)
        ·
          refine ⟨9327088342534443527906947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49744471160183698815503717 9327088342534443527906947)
          ·
            refine ⟨13990632513801665291860421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9327088342534443527906947 13990632513801665291860421)
            ·
              refine ⟨2623243596337812242223829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13990632513801665291860421 2623243596337812242223829)
              ·
                refine ⟨61482271789167474427121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2623243596337812242223829 61482271789167474427121)
                ·
                  rfl

theorem cell22_1616440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_1616440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616440 prefixEnd_1616440 := by exact prefixLift 1616440
  have htrace : WordTrace (prefixWord ++ tailWord_1616440) baseStart_1616440 baseEnd_1616440 := by
    simpa [prefixWord, tailWord_1616440, baseEnd_1616440] using wordTrace_append hprefix tailTrace_1616440
  have hstable : (prefixWord ++ tailWord_1616440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616440).length < 2 ^ (prefixWord ++ tailWord_1616440).sum := by decide
  have hdescent : baseEnd_1616440 < baseStart_1616440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616444 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 2, 3]
def baseStart_1616444 : Nat := 118140960795 + 1616444 * 2 ^ 59
def prefixEnd_1616444 : Nat := 4983230072969 + 3 ^ 40 * 1616444 * 2
def baseEnd_1616444 : Nat := 553341815384252592744077

theorem tailTrace_1616444 : CollatzResearch.WordTrace tailWord_1616444 prefixEnd_1616444 553341815384252592744077 := by
  unfold tailWord_1616444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29478278077953464750760193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39304370770604619667680257 29478278077953464750760193)
  ·
    refine ⟨22108708558465098563070145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29478278077953464750760193 22108708558465098563070145)
    ·
      refine ⟨16581531418848823922302609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22108708558465098563070145 16581531418848823922302609)
      ·
        refine ⟨12436148564136617941726957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16581531418848823922302609 12436148564136617941726957)
        ·
          refine ⟨4663555711551231728147609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12436148564136617941726957 4663555711551231728147609)
          ·
            refine ⟨3497666783663423796110707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4663555711551231728147609 3497666783663423796110707)
            ·
              refine ⟨5246500175495135694166061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3497666783663423796110707 5246500175495135694166061)
              ·
                refine ⟨1967437565810675885312273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5246500175495135694166061 1967437565810675885312273)
                ·
                  refine ⟨1475578174358006913984205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967437565810675885312273 1475578174358006913984205)
                  ·
                    refine ⟨553341815384252592744077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475578174358006913984205 553341815384252592744077)
                    ·
                      rfl

theorem cell22_1616444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_1616444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616444 prefixEnd_1616444 := by exact prefixLift 1616444
  have htrace : WordTrace (prefixWord ++ tailWord_1616444) baseStart_1616444 baseEnd_1616444 := by
    simpa [prefixWord, tailWord_1616444, baseEnd_1616444] using wordTrace_append hprefix tailTrace_1616444
  have hstable : (prefixWord ++ tailWord_1616444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616444).length < 2 ^ (prefixWord ++ tailWord_1616444).sum := by decide
  have hdescent : baseEnd_1616444 < baseStart_1616444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616613 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_1616613 : Nat := 118140960795 + 1616613 * 2 ^ 59
def prefixEnd_1616613 : Nat := 4983230072969 + 3 ^ 40 * 1616613 * 2
def baseEnd_1616613 : Nat := 553399667537992485268559

theorem tailTrace_1616613 : CollatzResearch.WordTrace tailWord_1616613 prefixEnd_1616613 553399667537992485268559 := by
  unfold tailWord_1616613
  simp only [CollatzResearch.WordTrace]
  refine ⟨58962720092294671364422493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39308480061529780909614995 58962720092294671364422493)
  ·
    refine ⟨22111020034610501761658435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58962720092294671364422493 22111020034610501761658435)
    ·
      refine ⟨33166530051915752642487653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22111020034610501761658435 33166530051915752642487653)
      ·
        refine ⟨6218724384734203620466435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33166530051915752642487653 6218724384734203620466435)
        ·
          refine ⟨9328086577101305430699653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6218724384734203620466435 9328086577101305430699653)
          ·
            refine ⟨1749016233206494768256185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9328086577101305430699653 1749016233206494768256185)
            ·
              refine ⟨1311762174904871076192139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1749016233206494768256185 1311762174904871076192139)
              ·
                refine ⟨1967643262357306614288209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1311762174904871076192139 1967643262357306614288209)
                ·
                  refine ⟨1475732446767979960716157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1967643262357306614288209 1475732446767979960716157)
                  ·
                    refine ⟨553399667537992485268559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475732446767979960716157 553399667537992485268559)
                    ·
                      rfl

theorem cell22_1616613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_1616613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616613 prefixEnd_1616613 := by exact prefixLift 1616613
  have htrace : WordTrace (prefixWord ++ tailWord_1616613) baseStart_1616613 baseEnd_1616613 := by
    simpa [prefixWord, tailWord_1616613, baseEnd_1616613] using wordTrace_append hprefix tailTrace_1616613
  have hstable : (prefixWord ++ tailWord_1616613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616613).length < 2 ^ (prefixWord ++ tailWord_1616613).sum := by decide
  have hdescent : baseEnd_1616613 < baseStart_1616613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616641 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1616641 : Nat := 118140960795 + 1616641 * 2 ^ 59
def prefixEnd_1616641 : Nat := 4983230072969 + 3 ^ 40 * 1616641 * 2
def baseEnd_1616641 : Nat := 553409252510209745568473

theorem tailTrace_1616641 : CollatzResearch.WordTrace tailWord_1616641 prefixEnd_1616641 553409252510209745568473 := by
  unfold tailWord_1616641
  simp only [CollatzResearch.WordTrace]
  refine ⟨58963741336193232146441777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39309160890795488097627851 58963741336193232146441777)
  ·
    refine ⟨44222806002144924109831333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58963741336193232146441777 44222806002144924109831333)
    ·
      refine ⟨8291776125402173270593375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44222806002144924109831333 8291776125402173270593375)
      ·
        refine ⟨12437664188103259905890063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8291776125402173270593375 12437664188103259905890063)
        ·
          refine ⟨18656496282154889858835095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12437664188103259905890063 18656496282154889858835095)
          ·
            refine ⟨27984744423232334788252643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18656496282154889858835095 27984744423232334788252643)
            ·
              refine ⟨41977116634848502182378965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27984744423232334788252643 41977116634848502182378965)
              ·
                refine ⟨983838671129261769899507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41977116634848502182378965 983838671129261769899507)
                ·
                  refine ⟨1475758006693892654849261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983838671129261769899507 1475758006693892654849261)
                  ·
                    refine ⟨553409252510209745568473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475758006693892654849261 553409252510209745568473)
                    ·
                      rfl

theorem cell22_1616641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1616641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616641 prefixEnd_1616641 := by exact prefixLift 1616641
  have htrace : WordTrace (prefixWord ++ tailWord_1616641) baseStart_1616641 baseEnd_1616641 := by
    simpa [prefixWord, tailWord_1616641, baseEnd_1616641] using wordTrace_append hprefix tailTrace_1616641
  have hstable : (prefixWord ++ tailWord_1616641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616641).length < 2 ^ (prefixWord ++ tailWord_1616641).sum := by decide
  have hdescent : baseEnd_1616641 < baseStart_1616641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616652 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_1616652 : Nat := 118140960795 + 1616652 * 2 ^ 59
def prefixEnd_1616652 : Nat := 4983230072969 + 3 ^ 40 * 1616652 * 2
def baseEnd_1616652 : Nat := 553413018035009383543439

theorem tailTrace_1616652 : CollatzResearch.WordTrace tailWord_1616652 prefixEnd_1616652 553413018035009383543439 := by
  unfold tailWord_1616652
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482071269576690512546105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39309428359435587350061473 29482071269576690512546105)
  ·
    refine ⟨22111553452182517884409579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29482071269576690512546105 22111553452182517884409579)
    ·
      refine ⟨33167330178273776826614369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22111553452182517884409579 33167330178273776826614369)
      ·
        refine ⟨24875497633705332619960777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33167330178273776826614369 24875497633705332619960777)
        ·
          refine ⟨18656623225278999464970583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24875497633705332619960777 18656623225278999464970583)
          ·
            refine ⟨27984934837918499197455875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18656623225278999464970583 27984934837918499197455875)
            ·
              refine ⟨41977402256877748796183813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27984934837918499197455875 41977402256877748796183813)
              ·
                refine ⟨7870762923164577899284465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41977402256877748796183813 7870762923164577899284465)
                ·
                  refine ⟨5903072192373433424463349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7870762923164577899284465 5903072192373433424463349)
                  ·
                    refine ⟨553413018035009383543439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5903072192373433424463349 553413018035009383543439)
                    ·
                      rfl

theorem cell22_1616652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_1616652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616652 prefixEnd_1616652 := by exact prefixLift 1616652
  have htrace : WordTrace (prefixWord ++ tailWord_1616652) baseStart_1616652 baseEnd_1616652 := by
    simpa [prefixWord, tailWord_1616652, baseEnd_1616652] using wordTrace_append hprefix tailTrace_1616652
  have hstable : (prefixWord ++ tailWord_1616652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616652).length < 2 ^ (prefixWord ++ tailWord_1616652).sum := by decide
  have hdescent : baseEnd_1616652 < baseStart_1616652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616684 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_1616684 : Nat := 118140960795 + 1616684 * 2 ^ 59
def prefixEnd_1616684 : Nat := 4983230072969 + 3 ^ 40 * 1616684 * 2
def baseEnd_1616684 : Nat := 553423972288971966743341

theorem tailTrace_1616684 : CollatzResearch.WordTrace tailWord_1616684 prefixEnd_1616684 553423972288971966743341 := by
  unfold tailWord_1616684
  simp only [CollatzResearch.WordTrace]
  refine ⟨29482654837518725245128553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39310206450024966993504737 29482654837518725245128553)
  ·
    refine ⟨22111991128139043933846415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29482654837518725245128553 22111991128139043933846415)
    ·
      refine ⟨33167986692208565900769623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22111991128139043933846415 33167986692208565900769623)
      ·
        refine ⟨49751980038312848851154435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33167986692208565900769623 49751980038312848851154435)
        ·
          refine ⟨74627970057469273276731653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49751980038312848851154435 74627970057469273276731653)
          ·
            refine ⟨13992744385775488739387185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74627970057469273276731653 13992744385775488739387185)
            ·
              refine ⟨10494558289331616554540389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13992744385775488739387185 10494558289331616554540389)
              ·
                refine ⟨1967729679249678103976323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10494558289331616554540389 1967729679249678103976323)
                ·
                  refine ⟨2951594518874517155964485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1967729679249678103976323 2951594518874517155964485)
                  ·
                    refine ⟨553423972288971966743341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2951594518874517155964485 553423972288971966743341)
                    ·
                      rfl

theorem cell22_1616684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_1616684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616684 prefixEnd_1616684 := by exact prefixLift 1616684
  have htrace : WordTrace (prefixWord ++ tailWord_1616684) baseStart_1616684 baseEnd_1616684 := by
    simpa [prefixWord, tailWord_1616684, baseEnd_1616684] using wordTrace_append hprefix tailTrace_1616684
  have hstable : (prefixWord ++ tailWord_1616684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616684).length < 2 ^ (prefixWord ++ tailWord_1616684).sum := by decide
  have hdescent : baseEnd_1616684 < baseStart_1616684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616705 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 5]
def baseStart_1616705 : Nat := 118140960795 + 1616705 * 2 ^ 59
def prefixEnd_1616705 : Nat := 4983230072969 + 3 ^ 40 * 1616705 * 2
def baseEnd_1616705 : Nat := 184477053672711637322759

theorem tailTrace_1616705 : CollatzResearch.WordTrace tailWord_1616705 prefixEnd_1616705 184477053672711637322759 := by
  unfold tailWord_1616705
  simp only [CollatzResearch.WordTrace]
  refine ⟨58966075607961371076771569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39310717071974247384514379 58966075607961371076771569)
  ·
    refine ⟨44224556705971028307578677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58966075607961371076771569 44224556705971028307578677)
    ·
      refine ⟨4146052191184783903835501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44224556705971028307578677 4146052191184783903835501)
      ·
        refine ⟨1554769571694293963938313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4146052191184783903835501 1554769571694293963938313)
        ·
          refine ⟨1166077178770720472953735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1554769571694293963938313 1166077178770720472953735)
          ·
            refine ⟨1749115768156080709430603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166077178770720472953735 1749115768156080709430603)
            ·
              refine ⟨2623673652234121064145905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749115768156080709430603 2623673652234121064145905)
              ·
                refine ⟨1967755239175590798109429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2623673652234121064145905 1967755239175590798109429)
                ·
                  refine ⟨184477053672711637322759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1967755239175590798109429 184477053672711637322759)
                  ·
                    rfl

theorem cell22_1616705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_1616705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616705 prefixEnd_1616705 := by exact prefixLift 1616705
  have htrace : WordTrace (prefixWord ++ tailWord_1616705) baseStart_1616705 baseEnd_1616705 := by
    simpa [prefixWord, tailWord_1616705, baseEnd_1616705] using wordTrace_append hprefix tailTrace_1616705
  have hstable : (prefixWord ++ tailWord_1616705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616705).length < 2 ^ (prefixWord ++ tailWord_1616705).sum := by decide
  have hdescent : baseEnd_1616705 < baseStart_1616705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616716 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 4]
def baseStart_1616716 : Nat := 118140960795 + 1616716 * 2 ^ 59
def prefixEnd_1616716 : Nat := 4983230072969 + 3 ^ 40 * 1616716 * 2
def baseEnd_1616716 : Nat := 184478308847644849981081

theorem tailTrace_1616716 : CollatzResearch.WordTrace tailWord_1616716 prefixEnd_1616716 184478308847644849981081 := by
  unfold tailWord_1616716
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483238405460759977711001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39310984540614346636948001 29483238405460759977711001)
  ·
    refine ⟨22112428804095569983283251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29483238405460759977711001 22112428804095569983283251)
    ·
      refine ⟨33168643206143354974924877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22112428804095569983283251 33168643206143354974924877)
      ·
        refine ⟨12438241202303758115596829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33168643206143354974924877 12438241202303758115596829)
        ·
          refine ⟨4664340450863909293348811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12438241202303758115596829 4664340450863909293348811)
          ·
            refine ⟨6996510676295863940023217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4664340450863909293348811 6996510676295863940023217)
            ·
              refine ⟨5247383007221897955017413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6996510676295863940023217 5247383007221897955017413)
              ·
                refine ⟨983884313854105866565765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5247383007221897955017413 983884313854105866565765)
                ·
                  refine ⟨184478308847644849981081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983884313854105866565765 184478308847644849981081)
                  ·
                    rfl

theorem cell22_1616716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 4].length) (baseStart_1616716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616716 prefixEnd_1616716 := by exact prefixLift 1616716
  have htrace : WordTrace (prefixWord ++ tailWord_1616716) baseStart_1616716 baseEnd_1616716 := by
    simpa [prefixWord, tailWord_1616716, baseEnd_1616716] using wordTrace_append hprefix tailTrace_1616716
  have hstable : (prefixWord ++ tailWord_1616716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616716).length < 2 ^ (prefixWord ++ tailWord_1616716).sum := by decide
  have hdescent : baseEnd_1616716 < baseStart_1616716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616744 : List Nat := [2, 1, 4, 2, 1, 3, 1, 8]
def baseStart_1616744 : Nat := 118140960795 + 1616744 * 2 ^ 59
def prefixEnd_1616744 : Nat := 4983230072969 + 3 ^ 40 * 1616744 * 2
def baseEnd_1616744 : Nat := 61493834612794645582573

theorem tailTrace_1616744 : CollatzResearch.WordTrace tailWord_1616744 prefixEnd_1616744 61493834612794645582573 := by
  unfold tailWord_1616744
  simp only [CollatzResearch.WordTrace]
  refine ⟨29483749027410040368720643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39311665369880053824960857 29483749027410040368720643)
  ·
    refine ⟨44225623541115060553080965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29483749027410040368720643 44225623541115060553080965)
    ·
      refine ⟨8292304413959073853702681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44225623541115060553080965 8292304413959073853702681)
      ·
        refine ⟨6219228310469305390277011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8292304413959073853702681 6219228310469305390277011)
        ·
          refine ⟨9328842465703958085415517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6219228310469305390277011 9328842465703958085415517)
          ·
            refine ⟨3498315924638984282030819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9328842465703958085415517 3498315924638984282030819)
            ·
              refine ⟨5247473886958476423046229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3498315924638984282030819 5247473886958476423046229)
              ·
                refine ⟨61493834612794645582573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5247473886958476423046229 61493834612794645582573)
                ·
                  rfl

theorem cell22_1616744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_1616744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616744 prefixEnd_1616744 := by exact prefixLift 1616744
  have htrace : WordTrace (prefixWord ++ tailWord_1616744) baseStart_1616744 baseEnd_1616744 := by
    simpa [prefixWord, tailWord_1616744, baseEnd_1616744] using wordTrace_append hprefix tailTrace_1616744
  have hstable : (prefixWord ++ tailWord_1616744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616744).length < 2 ^ (prefixWord ++ tailWord_1616744).sum := by decide
  have hdescent : baseEnd_1616744 < baseStart_1616744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616750 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_1616750 : Nat := 118140960795 + 1616750 * 2 ^ 59
def prefixEnd_1616750 : Nat := 4983230072969 + 3 ^ 40 * 1616750 * 2
def baseEnd_1616750 : Nat := 184482188479256598197713

theorem tailTrace_1616750 : CollatzResearch.WordTrace tailWord_1616750 prefixEnd_1616750 184482188479256598197713 := by
  unfold tailWord_1616750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7370964611599792970269963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39311811261865562508106469 7370964611599792970269963)
  ·
    refine ⟨11056446917399689455404945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7370964611599792970269963 11056446917399689455404945)
    ·
      refine ⟨8292335188049767091553709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11056446917399689455404945 8292335188049767091553709)
      ·
        refine ⟨3109625695518662659332641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8292335188049767091553709 3109625695518662659332641)
        ·
          refine ⟨2332219271638996994499481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109625695518662659332641 2332219271638996994499481)
          ·
            refine ⟨1749164453729247745874611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332219271638996994499481 1749164453729247745874611)
            ·
              refine ⟨2623746680593871618811917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749164453729247745874611 2623746680593871618811917)
              ·
                refine ⟨983905005222701857054469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2623746680593871618811917 983905005222701857054469)
                ·
                  refine ⟨184482188479256598197713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 983905005222701857054469 184482188479256598197713)
                  ·
                    rfl

theorem cell22_1616750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_1616750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616750 prefixEnd_1616750 := by exact prefixLift 1616750
  have htrace : WordTrace (prefixWord ++ tailWord_1616750) baseStart_1616750 baseEnd_1616750 := by
    simpa [prefixWord, tailWord_1616750, baseEnd_1616750] using wordTrace_append hprefix tailTrace_1616750
  have hstable : (prefixWord ++ tailWord_1616750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616750).length < 2 ^ (prefixWord ++ tailWord_1616750).sum := by decide
  have hdescent : baseEnd_1616750 < baseStart_1616750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616759 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 5, 3]
def baseStart_1616759 : Nat := 118140960795 + 1616759 * 2 ^ 59
def prefixEnd_1616759 : Nat := 4983230072969 + 3 ^ 40 * 1616759 * 2
def baseEnd_1616759 : Nat := 553449646321696771118111

theorem tailTrace_1616759 : CollatzResearch.WordTrace tailWord_1616759 prefixEnd_1616759 553449646321696771118111 := by
  unfold tailWord_1616759
  simp only [CollatzResearch.WordTrace]
  refine ⟨58968045149765738299237331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39312030099843825532824887 58968045149765738299237331)
  ·
    refine ⟨88452067724648607448855997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58968045149765738299237331 88452067724648607448855997)
    ·
      refine ⟨33169525396743227793320999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88452067724648607448855997 33169525396743227793320999)
      ·
        refine ⟨49754288095114841689981499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33169525396743227793320999 49754288095114841689981499)
        ·
          refine ⟨74631432142672262534972249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49754288095114841689981499 74631432142672262534972249)
          ·
            refine ⟨55973574107004196901229187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74631432142672262534972249 55973574107004196901229187)
            ·
              refine ⟨83960361160506295351843781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55973574107004196901229187 83960361160506295351843781)
              ·
                refine ⟨15742567717594930378470709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83960361160506295351843781 15742567717594930378470709)
                ·
                  refine ⟨1475865723524524722981629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15742567717594930378470709 1475865723524524722981629)
                  ·
                    refine ⟨553449646321696771118111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1475865723524524722981629 553449646321696771118111)
                    ·
                      rfl

theorem cell22_1616759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_1616759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616759 prefixEnd_1616759 := by exact prefixLift 1616759
  have htrace : WordTrace (prefixWord ++ tailWord_1616759) baseStart_1616759 baseEnd_1616759 := by
    simpa [prefixWord, tailWord_1616759, baseEnd_1616759] using wordTrace_append hprefix tailTrace_1616759
  have hstable : (prefixWord ++ tailWord_1616759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616759).length < 2 ^ (prefixWord ++ tailWord_1616759).sum := by decide
  have hdescent : baseEnd_1616759 < baseStart_1616759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616879 : List Nat := [1, 1, 2, 1, 4, 4, 9]
def baseStart_1616879 : Nat := 118140960795 + 1616879 * 2 ^ 59
def prefixEnd_1616879 : Nat := 4983230072969 + 3 ^ 40 * 1616879 * 2
def baseEnd_1616879 : Nat := 20499656473113202152509

theorem tailTrace_1616879 : CollatzResearch.WordTrace tailWord_1616879 prefixEnd_1616879 20499656473113202152509 := by
  unfold tailWord_1616879
  simp only [CollatzResearch.WordTrace]
  refine ⟨58972421909330998793605691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39314947939553999195737127 58972421909330998793605691)
  ·
    refine ⟨88458632863996498190408537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58972421909330998793605691 88458632863996498190408537)
    ·
      refine ⟨66343974647997373642806403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88458632863996498190408537 66343974647997373642806403)
      ·
        refine ⟨99515961971996060464209605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66343974647997373642806403 99515961971996060464209605)
        ·
          refine ⟨18659242869749261337039301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99515961971996060464209605 18659242869749261337039301)
          ·
            refine ⟨3498608038077986500694869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18659242869749261337039301 3498608038077986500694869)
            ·
              refine ⟨20499656473113202152509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3498608038077986500694869 20499656473113202152509)
              ·
                rfl

theorem cell22_1616879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 9].length) (baseStart_1616879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616879 prefixEnd_1616879 := by exact prefixLift 1616879
  have htrace : WordTrace (prefixWord ++ tailWord_1616879) baseStart_1616879 baseEnd_1616879 := by
    simpa [prefixWord, tailWord_1616879, baseEnd_1616879] using wordTrace_append hprefix tailTrace_1616879
  have hstable : (prefixWord ++ tailWord_1616879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616879).length < 2 ^ (prefixWord ++ tailWord_1616879).sum := by decide
  have hdescent : baseEnd_1616879 < baseStart_1616879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1616885 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 6]
def baseStart_1616885 : Nat := 118140960795 + 1616885 * 2 ^ 59
def prefixEnd_1616885 : Nat := 4983230072969 + 3 ^ 40 * 1616885 * 2
def baseEnd_1616885 : Nat := 184497592898891480822575

theorem tailTrace_1616885 : CollatzResearch.WordTrace tailWord_1616885 prefixEnd_1616885 184497592898891480822575 := by
  unfold tailWord_1616885
  simp only [CollatzResearch.WordTrace]
  refine ⟨58972640747309261818324109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39315093831539507878882739 58972640747309261818324109)
  ·
    refine ⟨22114740280240973181871541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58972640747309261818324109 22114740280240973181871541)
    ·
      refine ⟨2073256901272591235800457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22114740280240973181871541 2073256901272591235800457)
      ·
        refine ⟨1554942675954443426850343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2073256901272591235800457 1554942675954443426850343)
        ·
          refine ⟨2332414013931665140275515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554942675954443426850343 2332414013931665140275515)
          ·
            refine ⟨3498621020897497710413273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332414013931665140275515 3498621020897497710413273)
            ·
              refine ⟨2623965765673123282809955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3498621020897497710413273 2623965765673123282809955)
              ·
                refine ⟨3935948648509684924214933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2623965765673123282809955 3935948648509684924214933)
                ·
                  refine ⟨184497592898891480822575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3935948648509684924214933 184497592898891480822575)
                  ·
                    rfl

theorem cell22_1616885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_1616885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1616885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1616885 prefixEnd_1616885 := by exact prefixLift 1616885
  have htrace : WordTrace (prefixWord ++ tailWord_1616885) baseStart_1616885 baseEnd_1616885 := by
    simpa [prefixWord, tailWord_1616885, baseEnd_1616885] using wordTrace_append hprefix tailTrace_1616885
  have hstable : (prefixWord ++ tailWord_1616885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1616885).length < 2 ^ (prefixWord ++ tailWord_1616885).sum := by decide
  have hdescent : baseEnd_1616885 < baseStart_1616885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1616885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617016 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_1617016 : Nat := 118140960795 + 1617016 * 2 ^ 59
def prefixEnd_1617016 : Nat := 4983230072969 + 3 ^ 40 * 1617016 * 2
def baseEnd_1617016 : Nat := 553537622673833767442323

theorem tailTrace_1617016 : CollatzResearch.WordTrace tailWord_1617016 prefixEnd_1617016 553537622673833767442323 := by
  unfold tailWord_1617016
  simp only [CollatzResearch.WordTrace]
  refine ⟨29488709354917335595671451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39318279139889780794228601 29488709354917335595671451)
  ·
    refine ⟨44233064032376003393507177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29488709354917335595671451 44233064032376003393507177)
    ·
      refine ⟨33174798024282002545130383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44233064032376003393507177 33174798024282002545130383)
      ·
        refine ⟨49762197036423003817695575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33174798024282002545130383 49762197036423003817695575)
        ·
          refine ⟨74643295554634505726543363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49762197036423003817695575 74643295554634505726543363)
          ·
            refine ⟨111964943331951758589815045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74643295554634505726543363 111964943331951758589815045)
            ·
              refine ⟨20993426874740954735590321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111964943331951758589815045 20993426874740954735590321)
              ·
                refine ⟨15745070156055716051692741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20993426874740954735590321 15745070156055716051692741)
                ·
                  refine ⟨2952200654260446759692389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15745070156055716051692741 2952200654260446759692389)
                  ·
                    refine ⟨553537622673833767442323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952200654260446759692389 553537622673833767442323)
                    ·
                      rfl

theorem cell22_1617016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_1617016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617016 prefixEnd_1617016 := by exact prefixLift 1617016
  have htrace : WordTrace (prefixWord ++ tailWord_1617016) baseStart_1617016 baseEnd_1617016 := by
    simpa [prefixWord, tailWord_1617016, baseEnd_1617016] using wordTrace_append hprefix tailTrace_1617016
  have hstable : (prefixWord ++ tailWord_1617016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617016).length < 2 ^ (prefixWord ++ tailWord_1617016).sum := by decide
  have hdescent : baseEnd_1617016 < baseStart_1617016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617033 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_1617033 : Nat := 118140960795 + 1617033 * 2 ^ 59
def prefixEnd_1617033 : Nat := 4983230072969 + 3 ^ 40 * 1617033 * 2
def baseEnd_1617033 : Nat := 553543442121251389767271

theorem tailTrace_1617033 : CollatzResearch.WordTrace tailWord_1617033 prefixEnd_1617033 553543442121251389767271 := by
  unfold tailWord_1617033
  simp only [CollatzResearch.WordTrace]
  refine ⟨58978038750773083094711753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39318692500515388729807835 58978038750773083094711753)
  ·
    refine ⟨44233529063079812321033815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58978038750773083094711753 44233529063079812321033815)
    ·
      refine ⟨66350293594619718481550723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44233529063079812321033815 66350293594619718481550723)
      ·
        refine ⟨99525440391929577722326085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66350293594619718481550723 99525440391929577722326085)
        ·
          refine ⟨18661020073486795822936141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99525440391929577722326085 18661020073486795822936141)
          ·
            refine ⟨6997882527557548433601053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18661020073486795822936141 6997882527557548433601053)
            ·
              refine ⟨2624205947834080662600395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6997882527557548433601053 2624205947834080662600395)
              ·
                refine ⟨3936308921751120993900593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624205947834080662600395 3936308921751120993900593)
                ·
                  refine ⟨2952231691313340745425445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936308921751120993900593 2952231691313340745425445)
                  ·
                    refine ⟨553543442121251389767271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952231691313340745425445 553543442121251389767271)
                    ·
                      rfl

theorem cell22_1617033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_1617033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617033 prefixEnd_1617033 := by exact prefixLift 1617033
  have htrace : WordTrace (prefixWord ++ tailWord_1617033) baseStart_1617033 baseEnd_1617033 := by
    simpa [prefixWord, tailWord_1617033, baseEnd_1617033] using wordTrace_append hprefix tailTrace_1617033
  have hstable : (prefixWord ++ tailWord_1617033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617033).length < 2 ^ (prefixWord ++ tailWord_1617033).sum := by decide
  have hdescent : baseEnd_1617033 < baseStart_1617033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617052 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 2, 3]
def baseStart_1617052 : Nat := 118140960795 + 1617052 * 2 ^ 59
def prefixEnd_1617052 : Nat := 4983230072969 + 3 ^ 40 * 1617052 * 2
def baseEnd_1617052 : Nat := 553549946209541673542213

theorem tailTrace_1617052 : CollatzResearch.WordTrace tailWord_1617052 prefixEnd_1617052 553549946209541673542213 := by
  unfold tailWord_1617052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29489365868852124669826705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39319154491802832893102273 29489365868852124669826705)
  ·
    refine ⟨22117024401639093502370029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29489365868852124669826705 22117024401639093502370029)
    ·
      refine ⟨8293884150614660063388761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22117024401639093502370029 8293884150614660063388761)
      ·
        refine ⟨6220413112960995047541571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8293884150614660063388761 6220413112960995047541571)
        ·
          refine ⟨9330619669441492571312357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220413112960995047541571 9330619669441492571312357)
          ·
            refine ⟨1749491188020279857121067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9330619669441492571312357 1749491188020279857121067)
            ·
              refine ⟨2624236782030419785681601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749491188020279857121067 2624236782030419785681601)
              ·
                refine ⟨1968177586522814839261201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624236782030419785681601 1968177586522814839261201)
                ·
                  refine ⟨1476133189892111129445901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1968177586522814839261201 1476133189892111129445901)
                  ·
                    refine ⟨553549946209541673542213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476133189892111129445901 553549946209541673542213)
                    ·
                      rfl

theorem cell22_1617052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_1617052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617052 prefixEnd_1617052 := by exact prefixLift 1617052
  have htrace : WordTrace (prefixWord ++ tailWord_1617052) baseStart_1617052 baseEnd_1617052 := by
    simpa [prefixWord, tailWord_1617052, baseEnd_1617052] using wordTrace_append hprefix tailTrace_1617052
  have hstable : (prefixWord ++ tailWord_1617052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617052).length < 2 ^ (prefixWord ++ tailWord_1617052).sum := by decide
  have hdescent : baseEnd_1617052 < baseStart_1617052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617069 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1617069 : Nat := 118140960795 + 1617069 * 2 ^ 59
def prefixEnd_1617069 : Nat := 4983230072969 + 3 ^ 40 * 1617069 * 2
def baseEnd_1617069 : Nat := 553555765656959295867161

theorem tailTrace_1617069 : CollatzResearch.WordTrace tailWord_1617069 prefixEnd_1617069 553555765656959295867161 := by
  unfold tailWord_1617069
  simp only [CollatzResearch.WordTrace]
  refine ⟨58979351778642661243022261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39319567852428440828681507 58979351778642661243022261)
  ·
    refine ⟨5529314229247749491533337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58979351778642661243022261 5529314229247749491533337)
    ·
      refine ⟨4146985671935812118650003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5529314229247749491533337 4146985671935812118650003)
      ·
        refine ⟨6220478507903718177975005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4146985671935812118650003 6220478507903718177975005)
        ·
          refine ⟨2332679440463894316740627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6220478507903718177975005 2332679440463894316740627)
          ·
            refine ⟨3499019160695841475110941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332679440463894316740627 3499019160695841475110941)
            ·
              refine ⟨1312132185260940553166603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3499019160695841475110941 1312132185260940553166603)
              ·
                refine ⟨1968198277891410829749905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312132185260940553166603 1968198277891410829749905)
                ·
                  refine ⟨1476148708418558122312429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1968198277891410829749905 1476148708418558122312429)
                  ·
                    refine ⟨553555765656959295867161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476148708418558122312429 553555765656959295867161)
                    ·
                      rfl

theorem cell22_1617069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1617069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617069 prefixEnd_1617069 := by exact prefixLift 1617069
  have htrace : WordTrace (prefixWord ++ tailWord_1617069) baseStart_1617069 baseEnd_1617069 := by
    simpa [prefixWord, tailWord_1617069, baseEnd_1617069] using wordTrace_append hprefix tailTrace_1617069
  have hstable : (prefixWord ++ tailWord_1617069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617069).length < 2 ^ (prefixWord ++ tailWord_1617069).sum := by decide
  have hdescent : baseEnd_1617069 < baseStart_1617069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617091 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_1617091 : Nat := 118140960795 + 1617091 * 2 ^ 59
def prefixEnd_1617091 : Nat := 4983230072969 + 3 ^ 40 * 1617091 * 2
def baseEnd_1617091 : Nat := 553563296706558571817093

theorem tailTrace_1617091 : CollatzResearch.WordTrace tailWord_1617091 prefixEnd_1617091 553563296706558571817093 := by
  unfold tailWord_1617091
  simp only [CollatzResearch.WordTrace]
  refine ⟨58980154184562959000323127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39320102789708639333548751 58980154184562959000323127)
  ·
    refine ⟨88470231276844438500484691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58980154184562959000323127 88470231276844438500484691)
    ·
      refine ⟨132705346915266657750727037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88470231276844438500484691 132705346915266657750727037)
      ·
        refine ⟨49764505093224996656522639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132705346915266657750727037 49764505093224996656522639)
        ·
          refine ⟨74646757639837494984783959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49764505093224996656522639 74646757639837494984783959)
          ·
            refine ⟨111970136459756242477175939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74646757639837494984783959 111970136459756242477175939)
            ·
              refine ⟨167955204689634363715763909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111970136459756242477175939 167955204689634363715763909)
              ·
                refine ⟨31491600879306443196705733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167955204689634363715763909 31491600879306443196705733)
                ·
                  refine ⟨5904675164869958099382325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31491600879306443196705733 5904675164869958099382325)
                  ·
                    refine ⟨553563296706558571817093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5904675164869958099382325 553563296706558571817093)
                    ·
                      rfl

theorem cell22_1617091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_1617091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617091 prefixEnd_1617091 := by exact prefixLift 1617091
  have htrace : WordTrace (prefixWord ++ tailWord_1617091) baseStart_1617091 baseEnd_1617091 := by
    simpa [prefixWord, tailWord_1617091, baseEnd_1617091] using wordTrace_append hprefix tailTrace_1617091
  have hstable : (prefixWord ++ tailWord_1617091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617091).length < 2 ^ (prefixWord ++ tailWord_1617091).sum := by decide
  have hdescent : baseEnd_1617091 < baseStart_1617091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617153 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1617153 : Nat := 118140960795 + 1617153 * 2 ^ 59
def prefixEnd_1617153 : Nat := 4983230072969 + 3 ^ 40 * 1617153 * 2
def baseEnd_1617153 : Nat := 553584520573611076766903

theorem tailTrace_1617153 : CollatzResearch.WordTrace tailWord_1617153 prefixEnd_1617153 553584520573611076766903 := by
  unfold tailWord_1617153
  simp only [CollatzResearch.WordTrace]
  refine ⟨58982415510338343589080113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39321610340225562392720075 58982415510338343589080113)
  ·
    refine ⟨44236811632753757691810085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58982415510338343589080113 44236811632753757691810085)
    ·
      refine ⟨8294402181141329567214391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44236811632753757691810085 8294402181141329567214391)
      ·
        refine ⟨12441603271711994350821587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294402181141329567214391 12441603271711994350821587)
        ·
          refine ⟨18662404907567991526232381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12441603271711994350821587 18662404907567991526232381)
          ·
            refine ⟨6998401840337996822337143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18662404907567991526232381 6998401840337996822337143)
            ·
              refine ⟨10497602760506995233505715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6998401840337996822337143 10497602760506995233505715)
              ·
                refine ⟨15746404140760492850258573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497602760506995233505715 15746404140760492850258573)
                ·
                  refine ⟨5904901552785184818846965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15746404140760492850258573 5904901552785184818846965)
                  ·
                    refine ⟨553584520573611076766903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5904901552785184818846965 553584520573611076766903)
                    ·
                      rfl

theorem cell22_1617153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1617153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617153 prefixEnd_1617153 := by exact prefixLift 1617153
  have htrace : WordTrace (prefixWord ++ tailWord_1617153) baseStart_1617153 baseEnd_1617153 := by
    simpa [prefixWord, tailWord_1617153, baseEnd_1617153] using wordTrace_append hprefix tailTrace_1617153
  have hstable : (prefixWord ++ tailWord_1617153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617153).length < 2 ^ (prefixWord ++ tailWord_1617153).sum := by decide
  have hdescent : baseEnd_1617153 < baseStart_1617153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617202 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_1617202 : Nat := 118140960795 + 1617202 * 2 ^ 59
def prefixEnd_1617202 : Nat := 4983230072969 + 3 ^ 40 * 1617202 * 2
def baseEnd_1617202 : Nat := 553601294274991282291753

theorem tailTrace_1617202 : CollatzResearch.WordTrace tailWord_1617202 prefixEnd_1617202 553601294274991282291753 := by
  unfold tailWord_1617202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746050671790206239403465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39322801791440549971742573 14746050671790206239403465)
  ·
    refine ⟨11059538003842654679552599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14746050671790206239403465 11059538003842654679552599)
    ·
      refine ⟨16589307005763982019328899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11059538003842654679552599 16589307005763982019328899)
      ·
        refine ⟨24883960508645973028993349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16589307005763982019328899 24883960508645973028993349)
        ·
          refine ⟨4665742595371119942936253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24883960508645973028993349 4665742595371119942936253)
          ·
            refine ⟨1749653473264169978601095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4665742595371119942936253 1749653473264169978601095)
            ·
              refine ⟨2624480209896254967901643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749653473264169978601095 2624480209896254967901643)
              ·
                refine ⟨3936720314844382451852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624480209896254967901643 3936720314844382451852465)
                ·
                  refine ⟨2952540236133286838889349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3936720314844382451852465 2952540236133286838889349)
                  ·
                    refine ⟨553601294274991282291753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952540236133286838889349 553601294274991282291753)
                    ·
                      rfl

theorem cell22_1617202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_1617202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617202 prefixEnd_1617202 := by exact prefixLift 1617202
  have htrace : WordTrace (prefixWord ++ tailWord_1617202) baseStart_1617202 baseEnd_1617202 := by
    simpa [prefixWord, tailWord_1617202, baseEnd_1617202] using wordTrace_append hprefix tailTrace_1617202
  have hstable : (prefixWord ++ tailWord_1617202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617202).length < 2 ^ (prefixWord ++ tailWord_1617202).sum := by decide
  have hdescent : baseEnd_1617202 < baseStart_1617202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617206 : List Nat := [5, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_1617206 : Nat := 118140960795 + 1617206 * 2 ^ 59
def prefixEnd_1617206 : Nat := 4983230072969 + 3 ^ 40 * 1617206 * 2
def baseEnd_1617206 : Nat := 184534221185578868397247

theorem tailTrace_1617206 : CollatzResearch.WordTrace tailWord_1617206 prefixEnd_1617206 184534221185578868397247 := by
  unfold tailWord_1617206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686521786196645852547467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39322899052764222427172981 3686521786196645852547467)
  ·
    refine ⟨5529782679294968778821201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686521786196645852547467 5529782679294968778821201)
    ·
      refine ⟨4147337009471226584115901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5529782679294968778821201 4147337009471226584115901)
      ·
        refine ⟨1555251378551709969043463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4147337009471226584115901 1555251378551709969043463)
        ·
          refine ⟨2332877067827564953565195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555251378551709969043463 2332877067827564953565195)
          ·
            refine ⟨3499315601741347430347793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332877067827564953565195 3499315601741347430347793)
            ·
              refine ⟨2624486701306010572760845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3499315601741347430347793 2624486701306010572760845)
              ·
                refine ⟨984182512989753964785317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624486701306010572760845 984182512989753964785317)
                ·
                  refine ⟨184534221185578868397247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 984182512989753964785317 184534221185578868397247)
                  ·
                    rfl

theorem cell22_1617206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_1617206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617206 prefixEnd_1617206 := by exact prefixLift 1617206
  have htrace : WordTrace (prefixWord ++ tailWord_1617206) baseStart_1617206 baseEnd_1617206 := by
    simpa [prefixWord, tailWord_1617206, baseEnd_1617206] using wordTrace_append hprefix tailTrace_1617206
  have hstable : (prefixWord ++ tailWord_1617206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617206).length < 2 ^ (prefixWord ++ tailWord_1617206).sum := by decide
  have hdescent : baseEnd_1617206 < baseStart_1617206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617232 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 1, 3]
def baseStart_1617232 : Nat := 118140960795 + 1617232 * 2 ^ 59
def prefixEnd_1617232 : Nat := 4983230072969 + 3 ^ 40 * 1617232 * 2
def baseEnd_1617232 : Nat := 553611563888081204041661

theorem tailTrace_1617232 : CollatzResearch.WordTrace tailWord_1617232 prefixEnd_1617232 553611563888081204041661 := by
  unfold tailWord_1617232
  simp only [CollatzResearch.WordTrace]
  refine ⟨29492648438526070040602975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39323531251368093387470633 29492648438526070040602975)
  ·
    refine ⟨44238972657789105060904463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29492648438526070040602975 44238972657789105060904463)
    ·
      refine ⟨66358458986683657591356695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44238972657789105060904463 66358458986683657591356695)
      ·
        refine ⟨99537688480025486387035043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66358458986683657591356695 99537688480025486387035043)
        ·
          refine ⟨149306532720038229580552565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99537688480025486387035043 149306532720038229580552565)
          ·
            refine ⟨13997487442503584023176803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149306532720038229580552565 13997487442503584023176803)
            ·
              refine ⟨20996231163755376034765205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997487442503584023176803 20996231163755376034765205)
              ·
                refine ⟨984198335801033251629619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20996231163755376034765205 984198335801033251629619)
                ·
                  refine ⟨1476297503701549877444429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984198335801033251629619 1476297503701549877444429)
                  ·
                    refine ⟨553611563888081204041661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476297503701549877444429 553611563888081204041661)
                    ·
                      rfl

theorem cell22_1617232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 1, 3].length) (baseStart_1617232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617232 prefixEnd_1617232 := by exact prefixLift 1617232
  have htrace : WordTrace (prefixWord ++ tailWord_1617232) baseStart_1617232 baseEnd_1617232 := by
    simpa [prefixWord, tailWord_1617232, baseEnd_1617232] using wordTrace_append hprefix tailTrace_1617232
  have hstable : (prefixWord ++ tailWord_1617232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617232).length < 2 ^ (prefixWord ++ tailWord_1617232).sum := by decide
  have hdescent : baseEnd_1617232 < baseStart_1617232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617238 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_1617238 : Nat := 118140960795 + 1617238 * 2 ^ 59
def prefixEnd_1617238 : Nat := 4983230072969 + 3 ^ 40 * 1617238 * 2
def baseEnd_1617238 : Nat := 553613617810699188391643

theorem tailTrace_1617238 : CollatzResearch.WordTrace tailWord_1617238 prefixEnd_1617238 553613617810699188391643 := by
  unfold tailWord_1617238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686594732189400194120273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39323677143353602070616245 3686594732189400194120273)
  ·
    refine ⟨2764946049142050145590205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3686594732189400194120273 2764946049142050145590205)
    ·
      refine ⟨1036854768428268804596327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2764946049142050145590205 1036854768428268804596327)
      ·
        refine ⟨1555282152642403206894491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036854768428268804596327 1555282152642403206894491)
        ·
          refine ⟨2332923228963604810341737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555282152642403206894491 2332923228963604810341737)
          ·
            refine ⟨1749692421722703607756303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2332923228963604810341737 1749692421722703607756303)
            ·
              refine ⟨2624538632584055411634455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749692421722703607756303 2624538632584055411634455)
              ·
                refine ⟨3936807948876083117451683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2624538632584055411634455 3936807948876083117451683)
                ·
                  refine ⟨5905211923314124676177525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3936807948876083117451683 5905211923314124676177525)
                  ·
                    refine ⟨553613617810699188391643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5905211923314124676177525 553613617810699188391643)
                    ·
                      rfl

theorem cell22_1617238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_1617238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617238 prefixEnd_1617238 := by exact prefixLift 1617238
  have htrace : WordTrace (prefixWord ++ tailWord_1617238) baseStart_1617238 baseEnd_1617238 := by
    simpa [prefixWord, tailWord_1617238, baseEnd_1617238] using wordTrace_append hprefix tailTrace_1617238
  have hstable : (prefixWord ++ tailWord_1617238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617238).length < 2 ^ (prefixWord ++ tailWord_1617238).sum := by decide
  have hdescent : baseEnd_1617238 < baseStart_1617238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617273 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 8]
def baseStart_1617273 : Nat := 118140960795 + 1617273 * 2 ^ 59
def prefixEnd_1617273 : Nat := 4983230072969 + 3 ^ 40 * 1617273 * 2
def baseEnd_1617273 : Nat := 184541866341990254588845

theorem tailTrace_1617273 : CollatzResearch.WordTrace tailWord_1617273 prefixEnd_1617273 184541866341990254588845 := by
  unfold tailWord_1617273
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986792269903604083448473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39324528179935736055632315 58986792269903604083448473)
  ·
    refine ⟨44240094202427703062586355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58986792269903604083448473 44240094202427703062586355)
    ·
      refine ⟨66360141303641554593879533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44240094202427703062586355 66360141303641554593879533)
      ·
        refine ⟨24885052988865582972704825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66360141303641554593879533 24885052988865582972704825)
        ·
          refine ⟨18663789741649187229528619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24885052988865582972704825 18663789741649187229528619)
          ·
            refine ⟨27995684612473780844292929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18663789741649187229528619 27995684612473780844292929)
            ·
              refine ⟨20996763459355335633219697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27995684612473780844292929 20996763459355335633219697)
              ·
                refine ⟨15747572594516501724914773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20996763459355335633219697 15747572594516501724914773)
                ·
                  refine ⟨184541866341990254588845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15747572594516501724914773 184541866341990254588845)
                  ·
                    rfl

theorem cell22_1617273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_1617273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617273 prefixEnd_1617273 := by exact prefixLift 1617273
  have htrace : WordTrace (prefixWord ++ tailWord_1617273) baseStart_1617273 baseEnd_1617273 := by
    simpa [prefixWord, tailWord_1617273, baseEnd_1617273] using wordTrace_append hprefix tailTrace_1617273
  have hstable : (prefixWord ++ tailWord_1617273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617273).length < 2 ^ (prefixWord ++ tailWord_1617273).sum := by decide
  have hdescent : baseEnd_1617273 < baseStart_1617273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617275 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 1, 4]
def baseStart_1617275 : Nat := 118140960795 + 1617275 * 2 ^ 59
def prefixEnd_1617275 : Nat := 4983230072969 + 3 ^ 40 * 1617275 * 2
def baseEnd_1617275 : Nat := 553626283666843425216529

theorem tailTrace_1617275 : CollatzResearch.WordTrace tailWord_1617275 prefixEnd_1617275 553626283666843425216529 := by
  unfold tailWord_1617275
  simp only [CollatzResearch.WordTrace]
  refine ⟨58986865215896358425021279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39324576810597572283347519 58986865215896358425021279)
  ·
    refine ⟨88480297823844537637531919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58986865215896358425021279 88480297823844537637531919)
    ·
      refine ⟨132720446735766806456297879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88480297823844537637531919 132720446735766806456297879)
      ·
        refine ⟨199080670103650209684446819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132720446735766806456297879 199080670103650209684446819)
        ·
          refine ⟨298621005155475314526670229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199080670103650209684446819 298621005155475314526670229)
          ·
            refine ⟨13997859616662905368437667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 298621005155475314526670229 13997859616662905368437667)
            ·
              refine ⟨20996789424994358052656501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13997859616662905368437667 20996789424994358052656501)
              ·
                refine ⟨1968449008593221067436547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20996789424994358052656501 1968449008593221067436547)
                ·
                  refine ⟨2952673512889831601154821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968449008593221067436547 2952673512889831601154821)
                  ·
                    refine ⟨553626283666843425216529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952673512889831601154821 553626283666843425216529)
                    ·
                      rfl

theorem cell22_1617275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 4].length) (baseStart_1617275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617275 prefixEnd_1617275 := by exact prefixLift 1617275
  have htrace : WordTrace (prefixWord ++ tailWord_1617275) baseStart_1617275 baseEnd_1617275 := by
    simpa [prefixWord, tailWord_1617275, baseEnd_1617275] using wordTrace_append hprefix tailTrace_1617275
  have hstable : (prefixWord ++ tailWord_1617275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617275).length < 2 ^ (prefixWord ++ tailWord_1617275).sum := by decide
  have hdescent : baseEnd_1617275 < baseStart_1617275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617309 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1617309 : Nat := 118140960795 + 1617309 * 2 ^ 59
def prefixEnd_1617309 : Nat := 4983230072969 + 3 ^ 40 * 1617309 * 2
def baseEnd_1617309 : Nat := 553637922561678669866425

theorem tailTrace_1617309 : CollatzResearch.WordTrace tailWord_1617309 prefixEnd_1617309 553637922561678669866425 := by
  unfold tailWord_1617309
  simp only [CollatzResearch.WordTrace]
  refine ⟨58988105297773182231758981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39325403531848788154505987 58988105297773182231758981)
  ·
    refine ⟨11060269743332471668454809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58988105297773182231758981 11060269743332471668454809)
    ·
      refine ⟨8295202307499353751341107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11060269743332471668454809 8295202307499353751341107)
      ·
        refine ⟨12442803461249030627011661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8295202307499353751341107 12442803461249030627011661)
        ·
          refine ⟨4666051297968386485129373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12442803461249030627011661 4666051297968386485129373)
          ·
            refine ⟨1749769236738144931923515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4666051297968386485129373 1749769236738144931923515)
            ·
              refine ⟨2624653855107217397885273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749769236738144931923515 2624653855107217397885273)
              ·
                refine ⟨1968490391330413048413955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2624653855107217397885273 1968490391330413048413955)
                ·
                  refine ⟨2952735586995619572620933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968490391330413048413955 2952735586995619572620933)
                  ·
                    refine ⟨553637922561678669866425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952735586995619572620933 553637922561678669866425)
                    ·
                      rfl

theorem cell22_1617309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1617309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617309 prefixEnd_1617309 := by exact prefixLift 1617309
  have htrace : WordTrace (prefixWord ++ tailWord_1617309) baseStart_1617309 baseEnd_1617309 := by
    simpa [prefixWord, tailWord_1617309, baseEnd_1617309] using wordTrace_append hprefix tailTrace_1617309
  have hstable : (prefixWord ++ tailWord_1617309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617309).length < 2 ^ (prefixWord ++ tailWord_1617309).sum := by decide
  have hdescent : baseEnd_1617309 < baseStart_1617309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617365 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1617365 : Nat := 118140960795 + 1617365 * 2 ^ 59
def prefixEnd_1617365 : Nat := 4983230072969 + 3 ^ 40 * 1617365 * 2
def baseEnd_1617365 : Nat := 553657092506113190466253

theorem tailTrace_1617365 : CollatzResearch.WordTrace tailWord_1617365 prefixEnd_1617365 553657092506113190466253 := by
  unfold tailWord_1617365
  simp only [CollatzResearch.WordTrace]
  refine ⟨58990147785570303795797549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39326765190380202530531699 58990147785570303795797549)
  ·
    refine ⟨22121305419588863923424081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58990147785570303795797549 22121305419588863923424081)
    ·
      refine ⟨16590979064691647942568061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22121305419588863923424081 16590979064691647942568061)
      ·
        refine ⟨6221617149259367978463023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16590979064691647942568061 6221617149259367978463023)
        ·
          refine ⟨9332425723889051967694535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6221617149259367978463023 9332425723889051967694535)
          ·
            refine ⟨13998638585833577951541803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9332425723889051967694535 13998638585833577951541803)
            ·
              refine ⟨20997957878750366927312705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13998638585833577951541803 20997957878750366927312705)
              ·
                refine ⟨15748468409062775195484529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20997957878750366927312705 15748468409062775195484529)
                ·
                  refine ⟨11811351306797081396613397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15748468409062775195484529 11811351306797081396613397)
                  ·
                    refine ⟨553657092506113190466253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11811351306797081396613397 553657092506113190466253)
                    ·
                      rfl

theorem cell22_1617365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1617365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617365 prefixEnd_1617365 := by exact prefixLift 1617365
  have htrace : WordTrace (prefixWord ++ tailWord_1617365) baseStart_1617365 baseEnd_1617365 := by
    simpa [prefixWord, tailWord_1617365, baseEnd_1617365] using wordTrace_append hprefix tailTrace_1617365
  have hstable : (prefixWord ++ tailWord_1617365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617365).length < 2 ^ (prefixWord ++ tailWord_1617365).sum := by decide
  have hdescent : baseEnd_1617365 < baseStart_1617365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617425 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 6]
def baseStart_1617425 : Nat := 118140960795 + 1617425 * 2 ^ 59
def prefixEnd_1617425 : Nat := 4983230072969 + 3 ^ 40 * 1617425 * 2
def baseEnd_1617425 : Nat := 184559210577431011322023

theorem tailTrace_1617425 : CollatzResearch.WordTrace tailWord_1617425 prefixEnd_1617425 184559210577431011322023 := by
  unfold tailWord_1617425
  simp only [CollatzResearch.WordTrace]
  refine ⟨58992336165352934042981729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39328224110235289361987819 58992336165352934042981729)
  ·
    refine ⟨44244252124014700532236297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58992336165352934042981729 44244252124014700532236297)
    ·
      refine ⟨33183189093011025399177223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44244252124014700532236297 33183189093011025399177223)
      ·
        refine ⟨49774783639516538098765835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33183189093011025399177223 49774783639516538098765835)
        ·
          refine ⟨74662175459274807148148753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49774783639516538098765835 74662175459274807148148753)
          ·
            refine ⟨55996631594456105361111565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74662175459274807148148753 55996631594456105361111565)
            ·
              refine ⟨20998736847921039510416837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55996631594456105361111565 20998736847921039510416837)
              ·
                refine ⟨3937263158985194908203157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20998736847921039510416837 3937263158985194908203157)
                ·
                  refine ⟨184559210577431011322023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3937263158985194908203157 184559210577431011322023)
                  ·
                    rfl

theorem cell22_1617425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_1617425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617425 prefixEnd_1617425 := by exact prefixLift 1617425
  have htrace : WordTrace (prefixWord ++ tailWord_1617425) baseStart_1617425 baseEnd_1617425 := by
    simpa [prefixWord, tailWord_1617425, baseEnd_1617425] using wordTrace_append hprefix tailTrace_1617425
  have hstable : (prefixWord ++ tailWord_1617425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617425).length < 2 ^ (prefixWord ++ tailWord_1617425).sum := by decide
  have hdescent : baseEnd_1617425 < baseStart_1617425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617427 : List Nat := [1, 1, 1, 2, 1, 6, 1, 4, 1, 4]
def baseStart_1617427 : Nat := 118140960795 + 1617427 * 2 ^ 59
def prefixEnd_1617427 : Nat := 4983230072969 + 3 ^ 40 * 1617427 * 2
def baseEnd_1617427 : Nat := 553678316373165695416063

theorem tailTrace_1617427 : CollatzResearch.WordTrace tailWord_1617427 prefixEnd_1617427 553678316373165695416063 := by
  unfold tailWord_1617427
  simp only [CollatzResearch.WordTrace]
  refine ⟨58992409111345688384554535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39328272740897125589703023 58992409111345688384554535)
  ·
    refine ⟨88488613667018532576831803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58992409111345688384554535 88488613667018532576831803)
    ·
      refine ⟨132732920500527798865247705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88488613667018532576831803 132732920500527798865247705)
      ·
        refine ⟨99549690375395849148935779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132732920500527798865247705 99549690375395849148935779)
        ·
          refine ⟨149324535563093773723403669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99549690375395849148935779 149324535563093773723403669)
          ·
            refine ⟨6999587604520020643284547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149324535563093773723403669 6999587604520020643284547)
            ·
              refine ⟨10499381406780030964926821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6999587604520020643284547 10499381406780030964926821)
              ·
                refine ⟨1968634013771255805923779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10499381406780030964926821 1968634013771255805923779)
                ·
                  refine ⟨2952951020656883708885669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968634013771255805923779 2952951020656883708885669)
                  ·
                    refine ⟨553678316373165695416063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2952951020656883708885669 553678316373165695416063)
                    ·
                      rfl

theorem cell22_1617427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 4].length) (baseStart_1617427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617427 prefixEnd_1617427 := by exact prefixLift 1617427
  have htrace : WordTrace (prefixWord ++ tailWord_1617427) baseStart_1617427 baseEnd_1617427 := by
    simpa [prefixWord, tailWord_1617427, baseEnd_1617427] using wordTrace_append hprefix tailTrace_1617427
  have hstable : (prefixWord ++ tailWord_1617427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617427).length < 2 ^ (prefixWord ++ tailWord_1617427).sum := by decide
  have hdescent : baseEnd_1617427 < baseStart_1617427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617515 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 11]
def baseStart_1617515 : Nat := 118140960795 + 1617515 * 2 ^ 59
def prefixEnd_1617515 : Nat := 4983230072969 + 3 ^ 40 * 1617515 * 2
def baseEnd_1617515 : Nat := 184569480190520933071931

theorem tailTrace_1617515 : CollatzResearch.WordTrace tailWord_1617515 prefixEnd_1617515 184569480190520933071931 := by
  unfold tailWord_1617515
  simp only [CollatzResearch.WordTrace]
  refine ⟨58995618735026879413757999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39330412490017919609171999 58995618735026879413757999)
  ·
    refine ⟨88493428102540319120636999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58995618735026879413757999 88493428102540319120636999)
    ·
      refine ⟨132740142153810478680955499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88493428102540319120636999 132740142153810478680955499)
      ·
        refine ⟨199110213230715718021433249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132740142153810478680955499 199110213230715718021433249)
        ·
          refine ⟨149332659923036788516074937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199110213230715718021433249 149332659923036788516074937)
          ·
            refine ⟨111999494942277591387056203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149332659923036788516074937 111999494942277591387056203)
            ·
              refine ⟨167999242413416387080584305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111999494942277591387056203 167999242413416387080584305)
              ·
                refine ⟨125999431810062290310438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167999242413416387080584305 125999431810062290310438229)
                ·
                  refine ⟨184569480190520933071931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 125999431810062290310438229 184569480190520933071931)
                  ·
                    rfl

theorem cell22_1617515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_1617515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617515 prefixEnd_1617515 := by exact prefixLift 1617515
  have htrace : WordTrace (prefixWord ++ tailWord_1617515) baseStart_1617515 baseEnd_1617515 := by
    simpa [prefixWord, tailWord_1617515, baseEnd_1617515] using wordTrace_append hprefix tailTrace_1617515
  have hstable : (prefixWord ++ tailWord_1617515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617515).length < 2 ^ (prefixWord ++ tailWord_1617515).sum := by decide
  have hdescent : baseEnd_1617515 < baseStart_1617515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617566 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1617566 : Nat := 118140960795 + 1617566 * 2 ^ 59
def prefixEnd_1617566 : Nat := 4983230072969 + 3 ^ 40 * 1617566 * 2
def baseEnd_1617566 : Nat := 184575299637938555396879

theorem tailTrace_1617566 : CollatzResearch.WordTrace tailWord_1617566 prefixEnd_1617566 184575299637938555396879 := by
  unfold tailWord_1617566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7374684857230264390483069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39331652571894743415909701 7374684857230264390483069)
  ·
    refine ⟨2765506821461349146431151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7374684857230264390483069 2765506821461349146431151)
    ·
      refine ⟨4148260232192023719646727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765506821461349146431151 4148260232192023719646727)
      ·
        refine ⟨6222390348288035579470091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148260232192023719646727 6222390348288035579470091)
        ·
          refine ⟨9333585522432053369205137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222390348288035579470091 9333585522432053369205137)
          ·
            refine ⟨7000189141824040026903853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9333585522432053369205137 7000189141824040026903853)
            ·
              refine ⟨2625070928184015010088945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7000189141824040026903853 2625070928184015010088945)
              ·
                refine ⟨1968803196138011257566709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625070928184015010088945 1968803196138011257566709)
                ·
                  refine ⟨184575299637938555396879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1968803196138011257566709 184575299637938555396879)
                  ·
                    rfl

theorem cell22_1617566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1617566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617566 prefixEnd_1617566 := by exact prefixLift 1617566
  have htrace : WordTrace (prefixWord ++ tailWord_1617566) baseStart_1617566 baseEnd_1617566 := by
    simpa [prefixWord, tailWord_1617566, baseEnd_1617566] using wordTrace_append hprefix tailTrace_1617566
  have hstable : (prefixWord ++ tailWord_1617566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617566).length < 2 ^ (prefixWord ++ tailWord_1617566).sum := by decide
  have hdescent : baseEnd_1617566 < baseStart_1617566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617596 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 1, 4]
def baseStart_1617596 : Nat := 118140960795 + 1617596 * 2 ^ 59
def prefixEnd_1617596 : Nat := 4983230072969 + 3 ^ 40 * 1617596 * 2
def baseEnd_1617596 : Nat := 553736168526905587940545

theorem tailTrace_1617596 : CollatzResearch.WordTrace tailWord_1617596 prefixEnd_1617596 553736168526905587940545 := by
  unfold tailWord_1617596
  simp only [CollatzResearch.WordTrace]
  refine ⟨29499286523866715123728321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39332382031822286831637761 29499286523866715123728321)
  ·
    refine ⟨22124464892900036342796241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29499286523866715123728321 22124464892900036342796241)
    ·
      refine ⟨16593348669675027257097181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22124464892900036342796241 16593348669675027257097181)
      ·
        refine ⟨6222505751128135221411443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16593348669675027257097181 6222505751128135221411443)
        ·
          refine ⟨9333758626692202832117165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6222505751128135221411443 9333758626692202832117165)
          ·
            refine ⟨3500159485009576062043937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9333758626692202832117165 3500159485009576062043937)
            ·
              refine ⟨2625119613757182046532953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500159485009576062043937 2625119613757182046532953)
              ·
                refine ⟨1968839710317886534899715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625119613757182046532953 1968839710317886534899715)
                ·
                  refine ⟨2953259565476829802349573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968839710317886534899715 2953259565476829802349573)
                  ·
                    refine ⟨553736168526905587940545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953259565476829802349573 553736168526905587940545)
                    ·
                      rfl

theorem cell22_1617596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_1617596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617596 prefixEnd_1617596 := by exact prefixLift 1617596
  have htrace : WordTrace (prefixWord ++ tailWord_1617596) baseStart_1617596 baseEnd_1617596 := by
    simpa [prefixWord, tailWord_1617596, baseEnd_1617596] using wordTrace_append hprefix tailTrace_1617596
  have hstable : (prefixWord ++ tailWord_1617596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617596).length < 2 ^ (prefixWord ++ tailWord_1617596).sum := by decide
  have hdescent : baseEnd_1617596 < baseStart_1617596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617607 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1617607 : Nat := 118140960795 + 1617607 * 2 ^ 59
def prefixEnd_1617607 : Nat := 4983230072969 + 3 ^ 40 * 1617607 * 2
def baseEnd_1617607 : Nat := 553739934051705225915511

theorem tailTrace_1617607 : CollatzResearch.WordTrace tailWord_1617607 prefixEnd_1617607 553739934051705225915511 := by
  unfold tailWord_1617607
  simp only [CollatzResearch.WordTrace]
  refine ⟨58998974250693579126107075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39332649500462386084071383 58998974250693579126107075)
  ·
    refine ⟨88498461376040368689160613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58998974250693579126107075 88498461376040368689160613)
    ·
      refine ⟨16593461508007569129217615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88498461376040368689160613 16593461508007569129217615)
      ·
        refine ⟨24890192262011353693826423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16593461508007569129217615 24890192262011353693826423)
        ·
          refine ⟨37335288393017030540739635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24890192262011353693826423 37335288393017030540739635)
          ·
            refine ⟨56002932589525545811109453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37335288393017030540739635 56002932589525545811109453)
            ·
              refine ⟨21001099721072079679166045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56002932589525545811109453 21001099721072079679166045)
              ·
                refine ⟨7875412395402029879687267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21001099721072079679166045 7875412395402029879687267)
                ·
                  refine ⟨11813118593103044819530901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875412395402029879687267 11813118593103044819530901)
                  ·
                    refine ⟨553739934051705225915511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11813118593103044819530901 553739934051705225915511)
                    ·
                      rfl

theorem cell22_1617607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1617607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617607 prefixEnd_1617607 := by exact prefixLift 1617607
  have htrace : WordTrace (prefixWord ++ tailWord_1617607) baseStart_1617607 baseEnd_1617607 := by
    simpa [prefixWord, tailWord_1617607, baseEnd_1617607] using wordTrace_append hprefix tailTrace_1617607
  have hstable : (prefixWord ++ tailWord_1617607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617607).length < 2 ^ (prefixWord ++ tailWord_1617607).sum := by decide
  have hdescent : baseEnd_1617607 < baseStart_1617607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617613 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1617613 : Nat := 118140960795 + 1617613 * 2 ^ 59
def prefixEnd_1617613 : Nat := 4983230072969 + 3 ^ 40 * 1617613 * 2
def baseEnd_1617613 : Nat := 553741987974323210265493

theorem tailTrace_1617613 : CollatzResearch.WordTrace tailWord_1617613 prefixEnd_1617613 553741987974323210265493 := by
  unfold tailWord_1617613
  simp only [CollatzResearch.WordTrace]
  refine ⟨58999193088671842150825493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39332795392447894767216995 58999193088671842150825493)
  ·
    refine ⟨2765587176031492600819945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58999193088671842150825493 2765587176031492600819945)
    ·
      refine ⟨2074190382023619450614959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765587176031492600819945 2074190382023619450614959)
      ·
        refine ⟨3111285573035429175922439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074190382023619450614959 3111285573035429175922439)
        ·
          refine ⟨4666928359553143763883659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3111285573035429175922439 4666928359553143763883659)
          ·
            refine ⟨7000392539329715645825489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666928359553143763883659 7000392539329715645825489)
            ·
              refine ⟨5250294404497286734369117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7000392539329715645825489 5250294404497286734369117)
              ·
                refine ⟨1968860401686482525388419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5250294404497286734369117 1968860401686482525388419)
                ·
                  refine ⟨2953290602529723788082629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1968860401686482525388419 2953290602529723788082629)
                  ·
                    refine ⟨553741987974323210265493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953290602529723788082629 553741987974323210265493)
                    ·
                      rfl

theorem cell22_1617613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1617613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617613 prefixEnd_1617613 := by exact prefixLift 1617613
  have htrace : WordTrace (prefixWord ++ tailWord_1617613) baseStart_1617613 baseEnd_1617613 := by
    simpa [prefixWord, tailWord_1617613, baseEnd_1617613] using wordTrace_append hprefix tailTrace_1617613
  have hstable : (prefixWord ++ tailWord_1617613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617613).length < 2 ^ (prefixWord ++ tailWord_1617613).sum := by decide
  have hdescent : baseEnd_1617613 < baseStart_1617613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617624 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_1617624 : Nat := 118140960795 + 1617624 * 2 ^ 59
def prefixEnd_1617624 : Nat := 4983230072969 + 3 ^ 40 * 1617624 * 2
def baseEnd_1617624 : Nat := 553745753499122848240459

theorem tailTrace_1617624 : CollatzResearch.WordTrace tailWord_1617624 prefixEnd_1617624 553745753499122848240459 := by
  unfold tailWord_1617624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29499797145815995514737963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39333062861087994019650617 29499797145815995514737963)
  ·
    refine ⟨44249695718723993272106945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29499797145815995514737963 44249695718723993272106945)
    ·
      refine ⟨33187271789042994954080209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44249695718723993272106945 33187271789042994954080209)
      ·
        refine ⟨24890453841782246215560157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33187271789042994954080209 24890453841782246215560157)
        ·
          refine ⟨9333920190668342330835059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24890453841782246215560157 9333920190668342330835059)
          ·
            refine ⟨14000880286002513496252589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9333920190668342330835059 14000880286002513496252589)
            ·
              refine ⟨5250330107250942561094721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14000880286002513496252589 5250330107250942561094721)
              ·
                refine ⟨3937747580438206920821041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5250330107250942561094721 3937747580438206920821041)
                ·
                  refine ⟨2953310685328655190615781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3937747580438206920821041 2953310685328655190615781)
                  ·
                    refine ⟨553745753499122848240459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953310685328655190615781 553745753499122848240459)
                    ·
                      rfl

theorem cell22_1617624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_1617624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617624 prefixEnd_1617624 := by exact prefixLift 1617624
  have htrace : WordTrace (prefixWord ++ tailWord_1617624) baseStart_1617624 baseEnd_1617624 := by
    simpa [prefixWord, tailWord_1617624, baseEnd_1617624] using wordTrace_append hprefix tailTrace_1617624
  have hstable : (prefixWord ++ tailWord_1617624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617624).length < 2 ^ (prefixWord ++ tailWord_1617624).sum := by decide
  have hdescent : baseEnd_1617624 < baseStart_1617624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617628 : List Nat := [2, 2, 5, 1, 2, 2, 1, 1, 6]
def baseStart_1617628 : Nat := 118140960795 + 1617628 * 2 ^ 59
def prefixEnd_1617628 : Nat := 4983230072969 + 3 ^ 40 * 1617628 * 2
def baseEnd_1617628 : Nat := 184582374260289390380149

theorem tailTrace_1617628 : CollatzResearch.WordTrace tailWord_1617628 prefixEnd_1617628 184582374260289390380149 := by
  unfold tailWord_1617628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29499870091808749856310769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39333160122411666475081025 29499870091808749856310769)
  ·
    refine ⟨22124902568856562392233077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29499870091808749856310769 22124902568856562392233077)
    ·
      refine ⟨2074209615830302724271851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22124902568856562392233077 2074209615830302724271851)
      ·
        refine ⟨3111314423745454086407777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2074209615830302724271851 3111314423745454086407777)
        ·
          refine ⟨2333485817809090564805833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111314423745454086407777 2333485817809090564805833)
          ·
            refine ⟨1750114363356817923604375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333485817809090564805833 1750114363356817923604375)
            ·
              refine ⟨2625171545035226885406563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750114363356817923604375 2625171545035226885406563)
              ·
                refine ⟨3937757317552840328109845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625171545035226885406563 3937757317552840328109845)
                ·
                  refine ⟨184582374260289390380149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3937757317552840328109845 184582374260289390380149)
                  ·
                    rfl

theorem cell22_1617628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 1, 6].length) (baseStart_1617628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617628 prefixEnd_1617628 := by exact prefixLift 1617628
  have htrace : WordTrace (prefixWord ++ tailWord_1617628) baseStart_1617628 baseEnd_1617628 := by
    simpa [prefixWord, tailWord_1617628, baseEnd_1617628] using wordTrace_append hprefix tailTrace_1617628
  have hstable : (prefixWord ++ tailWord_1617628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617628).length < 2 ^ (prefixWord ++ tailWord_1617628).sum := by decide
  have hdescent : baseEnd_1617628 < baseStart_1617628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617667 : List Nat := [1, 1, 1, 3, 2, 2, 2, 1, 9]
def baseStart_1617667 : Nat := 118140960795 + 1617667 * 2 ^ 59
def prefixEnd_1617667 : Nat := 4983230072969 + 3 ^ 40 * 1617667 * 2
def baseEnd_1617667 : Nat := 184586824425961689805109

theorem tailTrace_1617667 : CollatzResearch.WordTrace tailWord_1617667 prefixEnd_1617667 184586824425961689805109 := by
  unfold tailWord_1617667
  simp only [CollatzResearch.WordTrace]
  refine ⟨59001162630476209373291255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39334108420317472915527503 59001162630476209373291255)
  ·
    refine ⟨88501743945714314059936883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59001162630476209373291255 88501743945714314059936883)
    ·
      refine ⟨132752615918571471089905325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88501743945714314059936883 132752615918571471089905325)
      ·
        refine ⟨49782230969464301658714497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132752615918571471089905325 49782230969464301658714497)
        ·
          refine ⟨37336673227098226244035873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49782230969464301658714497 37336673227098226244035873)
          ·
            refine ⟨28002504920323669683026905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37336673227098226244035873 28002504920323669683026905)
            ·
              refine ⟨21001878690242752262270179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28002504920323669683026905 21001878690242752262270179)
              ·
                refine ⟨31502818035364128393405269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21001878690242752262270179 31502818035364128393405269)
                ·
                  refine ⟨184586824425961689805109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31502818035364128393405269 184586824425961689805109)
                  ·
                    rfl

theorem cell22_1617667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_1617667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617667 prefixEnd_1617667 := by exact prefixLift 1617667
  have htrace : WordTrace (prefixWord ++ tailWord_1617667) baseStart_1617667 baseEnd_1617667 := by
    simpa [prefixWord, tailWord_1617667, baseEnd_1617667] using wordTrace_append hprefix tailTrace_1617667
  have hstable : (prefixWord ++ tailWord_1617667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617667).length < 2 ^ (prefixWord ++ tailWord_1617667).sum := by decide
  have hdescent : baseEnd_1617667 < baseStart_1617667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617731 : List Nat := [1, 1, 1, 3, 1, 6, 1, 3, 1, 4]
def baseStart_1617731 : Nat := 118140960795 + 1617731 * 2 ^ 59
def prefixEnd_1617731 : Nat := 4983230072969 + 3 ^ 40 * 1617731 * 2
def baseEnd_1617731 : Nat := 553782381785810235815131

theorem tailTrace_1617731 : CollatzResearch.WordTrace tailWord_1617731 prefixEnd_1617731 553782381785810235815131 := by
  unfold tailWord_1617731
  simp only [CollatzResearch.WordTrace]
  refine ⟨59003496902244348303621047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39335664601496232202414031 59003496902244348303621047)
  ·
    refine ⟨88505245353366522455431571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59003496902244348303621047 88505245353366522455431571)
    ·
      refine ⟨132757868030049783683147357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88505245353366522455431571 132757868030049783683147357)
      ·
        refine ⟨49784200511268668881180259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132757868030049783683147357 49784200511268668881180259)
        ·
          refine ⟨74676300766903003321770389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49784200511268668881180259 74676300766903003321770389)
          ·
            refine ⟨3500451598448578280707987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74676300766903003321770389 3500451598448578280707987)
            ·
              refine ⟨5250677397672867421061981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500451598448578280707987 5250677397672867421061981)
              ·
                refine ⟨1969004024127325282898243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5250677397672867421061981 1969004024127325282898243)
                ·
                  refine ⟨2953506036190987924347365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969004024127325282898243 2953506036190987924347365)
                  ·
                    refine ⟨553782381785810235815131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953506036190987924347365 553782381785810235815131)
                    ·
                      rfl

theorem cell22_1617731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 1, 4].length) (baseStart_1617731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617731 prefixEnd_1617731 := by exact prefixLift 1617731
  have htrace : WordTrace (prefixWord ++ tailWord_1617731) baseStart_1617731 baseEnd_1617731 := by
    simpa [prefixWord, tailWord_1617731, baseEnd_1617731] using wordTrace_append hprefix tailTrace_1617731
  have hstable : (prefixWord ++ tailWord_1617731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617731).length < 2 ^ (prefixWord ++ tailWord_1617731).sum := by decide
  have hdescent : baseEnd_1617731 < baseStart_1617731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617746 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1617746 : Nat := 118140960795 + 1617746 * 2 ^ 59
def prefixEnd_1617746 : Nat := 4983230072969 + 3 ^ 40 * 1617746 * 2
def baseEnd_1617746 : Nat := 184595838864118398896695

theorem tailTrace_1617746 : CollatzResearch.WordTrace tailWord_1617746 prefixEnd_1617746 184595838864118398896695 := by
  unfold tailWord_1617746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751010999297501466354273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39336029331460003910278061 14751010999297501466354273)
  ·
    refine ⟨11063258249473126099765705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14751010999297501466354273 11063258249473126099765705)
    ·
      refine ⟨8297443687104844574824279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11063258249473126099765705 8297443687104844574824279)
      ·
        refine ⟨12446165530657266862236419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8297443687104844574824279 12446165530657266862236419)
        ·
          refine ⟨18669248295985900293354629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12446165530657266862236419 18669248295985900293354629)
          ·
            refine ⟨3500484055497356305003993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18669248295985900293354629 3500484055497356305003993)
            ·
              refine ⟨2625363041623017228752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500484055497356305003993 2625363041623017228752995)
              ·
                refine ⟨3938044562434525843129493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625363041623017228752995 3938044562434525843129493)
                ·
                  refine ⟨184595838864118398896695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3938044562434525843129493 184595838864118398896695)
                  ·
                    rfl

theorem cell22_1617746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1617746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617746 prefixEnd_1617746 := by exact prefixLift 1617746
  have htrace : WordTrace (prefixWord ++ tailWord_1617746) baseStart_1617746 baseEnd_1617746 := by
    simpa [prefixWord, tailWord_1617746, baseEnd_1617746] using wordTrace_append hprefix tailTrace_1617746
  have hstable : (prefixWord ++ tailWord_1617746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617746).length < 2 ^ (prefixWord ++ tailWord_1617746).sum := by decide
  have hdescent : baseEnd_1617746 < baseStart_1617746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617759 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_1617759 : Nat := 118140960795 + 1617759 * 2 ^ 59
def prefixEnd_1617759 : Nat := 4983230072969 + 3 ^ 40 * 1617759 * 2
def baseEnd_1617759 : Nat := 553791966758027496115045

theorem tailTrace_1617759 : CollatzResearch.WordTrace tailWord_1617759 prefixEnd_1617759 553791966758027496115045 := by
  unfold tailWord_1617759
  simp only [CollatzResearch.WordTrace]
  refine ⟨59004518146142909085640331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39336345430761939390426887 59004518146142909085640331)
  ·
    refine ⟨88506777219214363628460497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59004518146142909085640331 88506777219214363628460497)
    ·
      refine ⟨66380082914410772721345373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88506777219214363628460497 66380082914410772721345373)
      ·
        refine ⟨24892531092904039770504515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66380082914410772721345373 24892531092904039770504515)
        ·
          refine ⟨37338796639356059655756773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24892531092904039770504515 37338796639356059655756773)
          ·
            refine ⟨7001024369879261185454395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37338796639356059655756773 7001024369879261185454395)
            ·
              refine ⟨10501536554818891778181593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001024369879261185454395 10501536554818891778181593)
              ·
                refine ⟨7876152416114168833636195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10501536554818891778181593 7876152416114168833636195)
                ·
                  refine ⟨11814228624171253250454293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7876152416114168833636195 11814228624171253250454293)
                  ·
                    refine ⟨553791966758027496115045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11814228624171253250454293 553791966758027496115045)
                    ·
                      rfl

theorem cell22_1617759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_1617759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617759 prefixEnd_1617759 := by exact prefixLift 1617759
  have htrace : WordTrace (prefixWord ++ tailWord_1617759) baseStart_1617759 baseEnd_1617759 := by
    simpa [prefixWord, tailWord_1617759, baseEnd_1617759] using wordTrace_append hprefix tailTrace_1617759
  have hstable : (prefixWord ++ tailWord_1617759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617759).length < 2 ^ (prefixWord ++ tailWord_1617759).sum := by decide
  have hdescent : baseEnd_1617759 < baseStart_1617759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617804 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_1617804 : Nat := 118140960795 + 1617804 * 2 ^ 59
def prefixEnd_1617804 : Nat := 4983230072969 + 3 ^ 40 * 1617804 * 2
def baseEnd_1617804 : Nat := 553807371177662378739907

theorem tailTrace_1617804 : CollatzResearch.WordTrace tailWord_1617804 prefixEnd_1617804 553807371177662378739907 := by
  unfold tailWord_1617804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29503079715489940885514233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39337439620653254514018977 29503079715489940885514233)
  ·
    refine ⟨22127309786617455664135675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29503079715489940885514233 22127309786617455664135675)
    ·
      refine ⟨33190964679926183496203513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22127309786617455664135675 33190964679926183496203513)
      ·
        refine ⟨24893223509944637622152635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33190964679926183496203513 24893223509944637622152635)
        ·
          refine ⟨37339835264916956433228953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24893223509944637622152635 37339835264916956433228953)
          ·
            refine ⟨28004876448687717324921715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37339835264916956433228953 28004876448687717324921715)
            ·
              refine ⟨42007314673031575987382573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28004876448687717324921715 42007314673031575987382573)
              ·
                refine ⟨15752743002386840995268465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42007314673031575987382573 15752743002386840995268465)
                ·
                  refine ⟨11814557251790130746451349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15752743002386840995268465 11814557251790130746451349)
                  ·
                    refine ⟨553807371177662378739907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11814557251790130746451349 553807371177662378739907)
                    ·
                      rfl

theorem cell22_1617804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_1617804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617804 prefixEnd_1617804 := by exact prefixLift 1617804
  have htrace : WordTrace (prefixWord ++ tailWord_1617804) baseStart_1617804 baseEnd_1617804 := by
    simpa [prefixWord, tailWord_1617804, baseEnd_1617804] using wordTrace_append hprefix tailTrace_1617804
  have hstable : (prefixWord ++ tailWord_1617804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617804).length < 2 ^ (prefixWord ++ tailWord_1617804).sum := by decide
  have hdescent : baseEnd_1617804 < baseStart_1617804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617812 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 2, 3]
def baseStart_1617812 : Nat := 118140960795 + 1617812 * 2 ^ 59
def prefixEnd_1617812 : Nat := 4983230072969 + 3 ^ 40 * 1617812 * 2
def baseEnd_1617812 : Nat := 553810109741153024539883

theorem tailTrace_1617812 : CollatzResearch.WordTrace tailWord_1617812 prefixEnd_1617812 553810109741153024539883 := by
  unfold tailWord_1617812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29503225607475449568659845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39337634143300599424879793 29503225607475449568659845)
  ·
    refine ⟨5531854801401646794123721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29503225607475449568659845 5531854801401646794123721)
    ·
      refine ⟨4148891101051235095592791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5531854801401646794123721 4148891101051235095592791)
      ·
        refine ⟨6223336651576852643389187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4148891101051235095592791 6223336651576852643389187)
        ·
          refine ⟨9335004977365278965083781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6223336651576852643389187 9335004977365278965083781)
          ·
            refine ⟨1750313433255989805953209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9335004977365278965083781 1750313433255989805953209)
            ·
              refine ⟨1312735074941992354464907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750313433255989805953209 1312735074941992354464907)
              ·
                refine ⟨1969102612412988531697361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312735074941992354464907 1969102612412988531697361)
                ·
                  refine ⟨1476826959309741398773021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1969102612412988531697361 1476826959309741398773021)
                  ·
                    refine ⟨553810109741153024539883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476826959309741398773021 553810109741153024539883)
                    ·
                      rfl

theorem cell22_1617812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_1617812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617812 prefixEnd_1617812 := by exact prefixLift 1617812
  have htrace : WordTrace (prefixWord ++ tailWord_1617812) baseStart_1617812 baseEnd_1617812 := by
    simpa [prefixWord, tailWord_1617812, baseEnd_1617812] using wordTrace_append hprefix tailTrace_1617812
  have hstable : (prefixWord ++ tailWord_1617812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617812).length < 2 ^ (prefixWord ++ tailWord_1617812).sum := by decide
  have hdescent : baseEnd_1617812 < baseStart_1617812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617853 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 5]
def baseStart_1617853 : Nat := 118140960795 + 1617853 * 2 ^ 59
def prefixEnd_1617853 : Nat := 4983230072969 + 3 ^ 40 * 1617853 * 2
def baseEnd_1617853 : Nat := 184608048293014194754919

theorem tailTrace_1617853 : CollatzResearch.WordTrace tailWord_1617853 prefixEnd_1617853 184608048293014194754919 := by
  unfold tailWord_1617853
  simp only [CollatzResearch.WordTrace]
  refine ⟨59007946607802363139562213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39338631071868242093041475 59007946607802363139562213)
  ·
    refine ⟨11063989988962943088667915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59007946607802363139562213 11063989988962943088667915)
    ·
      refine ⟨16595984983444414633001873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11063989988962943088667915 16595984983444414633001873)
      ·
        refine ⟨12446988737583310974751405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16595984983444414633001873 12446988737583310974751405)
        ·
          refine ⟨4667620776593741615531777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12446988737583310974751405 4667620776593741615531777)
          ·
            refine ⟨3500715582445306211648833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4667620776593741615531777 3500715582445306211648833)
            ·
              refine ⟨2625536686833979658736625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3500715582445306211648833 2625536686833979658736625)
              ·
                refine ⟨1969152515125484744052469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2625536686833979658736625 1969152515125484744052469)
                ·
                  refine ⟨184608048293014194754919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969152515125484744052469 184608048293014194754919)
                  ·
                    rfl

theorem cell22_1617853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_1617853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617853 prefixEnd_1617853 := by exact prefixLift 1617853
  have htrace : WordTrace (prefixWord ++ tailWord_1617853) baseStart_1617853 baseEnd_1617853 := by
    simpa [prefixWord, tailWord_1617853, baseEnd_1617853] using wordTrace_append hprefix tailTrace_1617853
  have hstable : (prefixWord ++ tailWord_1617853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617853).length < 2 ^ (prefixWord ++ tailWord_1617853).sum := by decide
  have hdescent : baseEnd_1617853 < baseStart_1617853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617866 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 3, 4]
def baseStart_1617866 : Nat := 118140960795 + 1617866 * 2 ^ 59
def prefixEnd_1617866 : Nat := 4983230072969 + 3 ^ 40 * 1617866 * 2
def baseEnd_1617866 : Nat := 553828595044714883689717

theorem tailTrace_1617866 : CollatzResearch.WordTrace tailWord_1617866 prefixEnd_1617866 553828595044714883689717 := by
  unfold tailWord_1617866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752105189188816589946363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39338947171170177573190301 14752105189188816589946363)
  ·
    refine ⟨22128157783783224884919545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14752105189188816589946363 22128157783783224884919545)
    ·
      refine ⟨16596118337837418663689659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22128157783783224884919545 16596118337837418663689659)
      ·
        refine ⟨24894177506756127995534489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16596118337837418663689659 24894177506756127995534489)
        ·
          refine ⟨18670633130067095996650867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24894177506756127995534489 18670633130067095996650867)
          ·
            refine ⟨28005949695100643994976301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18670633130067095996650867 28005949695100643994976301)
            ·
              refine ⟨10502231135662741498116113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28005949695100643994976301 10502231135662741498116113)
              ·
                refine ⟨7876673351747056123587085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10502231135662741498116113 7876673351747056123587085)
                ·
                  refine ⟨2953752506905146046345157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7876673351747056123587085 2953752506905146046345157)
                  ·
                    refine ⟨553828595044714883689717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2953752506905146046345157 553828595044714883689717)
                    ·
                      rfl

theorem cell22_1617866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_1617866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617866 prefixEnd_1617866 := by exact prefixLift 1617866
  have htrace : WordTrace (prefixWord ++ tailWord_1617866) baseStart_1617866 baseEnd_1617866 := by
    simpa [prefixWord, tailWord_1617866, baseEnd_1617866] using wordTrace_append hprefix tailTrace_1617866
  have hstable : (prefixWord ++ tailWord_1617866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617866).length < 2 ^ (prefixWord ++ tailWord_1617866).sum := by decide
  have hdescent : baseEnd_1617866 < baseStart_1617866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617913 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_1617913 : Nat := 118140960795 + 1617913 * 2 ^ 59
def prefixEnd_1617913 : Nat := 4983230072969 + 3 ^ 40 * 1617913 * 2
def baseEnd_1617913 : Nat := 553844684105222427764573

theorem tailTrace_1617913 : CollatzResearch.WordTrace tailWord_1617913 prefixEnd_1617913 553844684105222427764573 := by
  unfold tailWord_1617913
  simp only [CollatzResearch.WordTrace]
  refine ⟨59010134987584993386746393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39340089991723328924497595 59010134987584993386746393)
  ·
    refine ⟨44257601240688745040059795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59010134987584993386746393 44257601240688745040059795)
    ·
      refine ⟨66386401861033117560089693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44257601240688745040059795 66386401861033117560089693)
      ·
        refine ⟨24894900697887419085033635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66386401861033117560089693 24894900697887419085033635)
        ·
          refine ⟨37342351046831128627550453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24894900697887419085033635 37342351046831128627550453)
          ·
            refine ⟨3500845410640418308832855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37342351046831128627550453 3500845410640418308832855)
            ·
              refine ⟨5251268115960627463249283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500845410640418308832855 5251268115960627463249283)
              ·
                refine ⟨7876902173940941194873925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251268115960627463249283 7876902173940941194873925)
                ·
                  refine ⟨1476919157613926474038861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7876902173940941194873925 1476919157613926474038861)
                  ·
                    refine ⟨553844684105222427764573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476919157613926474038861 553844684105222427764573)
                    ·
                      rfl

theorem cell22_1617913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_1617913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617913 prefixEnd_1617913 := by exact prefixLift 1617913
  have htrace : WordTrace (prefixWord ++ tailWord_1617913) baseStart_1617913 baseEnd_1617913 := by
    simpa [prefixWord, tailWord_1617913, baseEnd_1617913] using wordTrace_append hprefix tailTrace_1617913
  have hstable : (prefixWord ++ tailWord_1617913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617913).length < 2 ^ (prefixWord ++ tailWord_1617913).sum := by decide
  have hdescent : baseEnd_1617913 < baseStart_1617913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617930 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_1617930 : Nat := 118140960795 + 1617930 * 2 ^ 59
def prefixEnd_1617930 : Nat := 4983230072969 + 3 ^ 40 * 1617930 * 2
def baseEnd_1617930 : Nat := 553850503552640050089521

theorem tailTrace_1617930 : CollatzResearch.WordTrace tailWord_1617930 prefixEnd_1617930 553850503552640050089521 := by
  unfold tailWord_1617930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14752688757130851322528811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39340503352348936860076829 14752688757130851322528811)
  ·
    refine ⟨22129033135696276983793217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14752688757130851322528811 22129033135696276983793217)
    ·
      refine ⟨16596774851772207737844913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22129033135696276983793217 16596774851772207737844913)
      ·
        refine ⟨12447581138829155803383685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16596774851772207737844913 12447581138829155803383685)
        ·
          refine ⟨2333921463530466713134441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12447581138829155803383685 2333921463530466713134441)
          ·
            refine ⟨1750441097647850034850831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333921463530466713134441 1750441097647850034850831)
            ·
              refine ⟨2625661646471775052276247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750441097647850034850831 2625661646471775052276247)
              ·
                refine ⟨3938492469707662578414371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2625661646471775052276247 3938492469707662578414371)
                ·
                  refine ⟨5907738704561493867621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3938492469707662578414371 5907738704561493867621557)
                  ·
                    refine ⟨553850503552640050089521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5907738704561493867621557 553850503552640050089521)
                    ·
                      rfl

theorem cell22_1617930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_1617930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617930 prefixEnd_1617930 := by exact prefixLift 1617930
  have htrace : WordTrace (prefixWord ++ tailWord_1617930) baseStart_1617930 baseEnd_1617930 := by
    simpa [prefixWord, tailWord_1617930, baseEnd_1617930] using wordTrace_append hprefix tailTrace_1617930
  have hstable : (prefixWord ++ tailWord_1617930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617930).length < 2 ^ (prefixWord ++ tailWord_1617930).sum := by decide
  have hdescent : baseEnd_1617930 < baseStart_1617930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617943 : List Nat := [1, 1, 3, 5, 2, 1, 1, 8]
def baseStart_1617943 : Nat := 118140960795 + 1617943 * 2 ^ 59
def prefixEnd_1617943 : Nat := 4983230072969 + 3 ^ 40 * 1617943 * 2
def baseEnd_1617943 : Nat := 61539439302034705501609

theorem tailTrace_1617943 : CollatzResearch.WordTrace tailWord_1617943 prefixEnd_1617943 61539439302034705501609 := by
  unfold tailWord_1617943
  simp only [CollatzResearch.WordTrace]
  refine ⟨59011229177476308510338483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39340819451650872340225655 59011229177476308510338483)
  ·
    refine ⟨88516843766214462765507725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59011229177476308510338483 88516843766214462765507725)
    ·
      refine ⟨33193816412330423537065397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88516843766214462765507725 33193816412330423537065397)
      ·
        refine ⟨3111920288655977206599881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33193816412330423537065397 3111920288655977206599881)
        ·
          refine ⟨2333940216491982904949911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3111920288655977206599881 2333940216491982904949911)
          ·
            refine ⟨3500910324737974357424867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333940216491982904949911 3500910324737974357424867)
            ·
              refine ⟨5251365487106961536137301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500910324737974357424867 5251365487106961536137301)
              ·
                refine ⟨61539439302034705501609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5251365487106961536137301 61539439302034705501609)
                ·
                  rfl

theorem cell22_1617943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 8].length) (baseStart_1617943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617943 prefixEnd_1617943 := by exact prefixLift 1617943
  have htrace : WordTrace (prefixWord ++ tailWord_1617943) baseStart_1617943 baseEnd_1617943 := by
    simpa [prefixWord, tailWord_1617943, baseEnd_1617943] using wordTrace_append hprefix tailTrace_1617943
  have hstable : (prefixWord ++ tailWord_1617943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617943).length < 2 ^ (prefixWord ++ tailWord_1617943).sum := by decide
  have hdescent : baseEnd_1617943 < baseStart_1617943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617960 : List Nat := [2, 1, 5, 3, 1, 2, 8]
def baseStart_1617960 : Nat := 118140960795 + 1617960 * 2 ^ 59
def prefixEnd_1617960 : Nat := 4983230072969 + 3 ^ 40 * 1617960 * 2
def baseEnd_1617960 : Nat := 20513361969101110068127

theorem tailTrace_1617960 : CollatzResearch.WordTrace tailWord_1617960 prefixEnd_1617960 20513361969101110068127 := by
  unfold tailWord_1617960
  simp only [CollatzResearch.WordTrace]
  refine ⟨29505924609207360206853667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39341232812276480275804889 29505924609207360206853667)
  ·
    refine ⟨44258886913811040310280501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29505924609207360206853667 44258886913811040310280501)
    ·
      refine ⟨4149270648169785029088797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44258886913811040310280501 4149270648169785029088797)
      ·
        refine ⟨1555976493063669385908299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4149270648169785029088797 1555976493063669385908299)
        ·
          refine ⟨2333964739595504078862449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555976493063669385908299 2333964739595504078862449)
          ·
            refine ⟨1750473554696628059146837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2333964739595504078862449 1750473554696628059146837)
            ·
              refine ⟨20513361969101110068127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1750473554696628059146837 20513361969101110068127)
              ·
                rfl

theorem cell22_1617960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 8].length) (baseStart_1617960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617960 prefixEnd_1617960 := by exact prefixLift 1617960
  have htrace : WordTrace (prefixWord ++ tailWord_1617960) baseStart_1617960 baseEnd_1617960 := by
    simpa [prefixWord, tailWord_1617960, baseEnd_1617960] using wordTrace_append hprefix tailTrace_1617960
  have hstable : (prefixWord ++ tailWord_1617960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617960).length < 2 ^ (prefixWord ++ tailWord_1617960).sum := by decide
  have hdescent : baseEnd_1617960 < baseStart_1617960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617971 : List Nat := [1, 1, 1, 2, 4, 1, 4, 1, 7]
def baseStart_1617971 : Nat := 118140960795 + 1617971 * 2 ^ 59
def prefixEnd_1617971 : Nat := 4983230072969 + 3 ^ 40 * 1617971 * 2
def baseEnd_1617971 : Nat := 184621512896843203271465

theorem tailTrace_1617971 : CollatzResearch.WordTrace tailWord_1617971 prefixEnd_1617971 184621512896843203271465 := by
  unfold tailWord_1617971
  simp only [CollatzResearch.WordTrace]
  refine ⟨59012250421374869292357767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39341500280916579528238511 59012250421374869292357767)
  ·
    refine ⟨88518375632062303938536651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59012250421374869292357767 88518375632062303938536651)
    ·
      refine ⟨132777563448093455907804977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88518375632062303938536651 132777563448093455907804977)
      ·
        refine ⟨99583172586070091930853733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132777563448093455907804977 99583172586070091930853733)
        ·
          refine ⟨18671844859888142237035075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99583172586070091930853733 18671844859888142237035075)
          ·
            refine ⟨28007767289832213355552613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18671844859888142237035075 28007767289832213355552613)
            ·
              refine ⟨5251456366843540004166115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28007767289832213355552613 5251456366843540004166115)
              ·
                refine ⟨7877184550265310006249173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251456366843540004166115 7877184550265310006249173)
                ·
                  refine ⟨184621512896843203271465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7877184550265310006249173 184621512896843203271465)
                  ·
                    rfl

theorem cell22_1617971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_1617971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617971 prefixEnd_1617971 := by exact prefixLift 1617971
  have htrace : WordTrace (prefixWord ++ tailWord_1617971) baseStart_1617971 baseEnd_1617971 := by
    simpa [prefixWord, tailWord_1617971, baseEnd_1617971] using wordTrace_append hprefix tailTrace_1617971
  have hstable : (prefixWord ++ tailWord_1617971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617971).length < 2 ^ (prefixWord ++ tailWord_1617971).sum := by decide
  have hdescent : baseEnd_1617971 < baseStart_1617971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1617975 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 1, 3]
def baseStart_1617975 : Nat := 118140960795 + 1617975 * 2 ^ 59
def prefixEnd_1617975 : Nat := 4983230072969 + 3 ^ 40 * 1617975 * 2
def baseEnd_1617975 : Nat := 553865907972274932714383

theorem tailTrace_1617975 : CollatzResearch.WordTrace tailWord_1617975 prefixEnd_1617975 553865907972274932714383 := by
  unfold tailWord_1617975
  simp only [CollatzResearch.WordTrace]
  refine ⟨59012396313360377975503379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39341597542240251983668919 59012396313360377975503379)
  ·
    refine ⟨88518594470040566963255069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59012396313360377975503379 88518594470040566963255069)
    ·
      refine ⟨33194472926265212611220651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88518594470040566963255069 33194472926265212611220651)
      ·
        refine ⟨49791709389397818916830977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33194472926265212611220651 49791709389397818916830977)
        ·
          refine ⟨37343782042048364187623233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49791709389397818916830977 37343782042048364187623233)
          ·
            refine ⟨28007836531536273140717425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37343782042048364187623233 28007836531536273140717425)
            ·
              refine ⟨21005877398652204855538069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28007836531536273140717425 21005877398652204855538069)
              ·
                refine ⟨984650503061822102603347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21005877398652204855538069 984650503061822102603347)
                ·
                  refine ⟨1476975754592733153905021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984650503061822102603347 1476975754592733153905021)
                  ·
                    refine ⟨553865907972274932714383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1476975754592733153905021 553865907972274932714383)
                    ·
                      rfl

theorem cell22_1617975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_1617975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1617975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1617975 prefixEnd_1617975 := by exact prefixLift 1617975
  have htrace : WordTrace (prefixWord ++ tailWord_1617975) baseStart_1617975 baseEnd_1617975 := by
    simpa [prefixWord, tailWord_1617975, baseEnd_1617975] using wordTrace_append hprefix tailTrace_1617975
  have hstable : (prefixWord ++ tailWord_1617975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1617975).length < 2 ^ (prefixWord ++ tailWord_1617975).sum := by decide
  have hdescent : baseEnd_1617975 < baseStart_1617975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1617975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618026 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1618026 : Nat := 118140960795 + 1618026 * 2 ^ 59
def prefixEnd_1618026 : Nat := 4983230072969 + 3 ^ 40 * 1618026 * 2
def baseEnd_1618026 : Nat := 553883366314527799689227

theorem tailTrace_1618026 : CollatzResearch.WordTrace tailWord_1618026 prefixEnd_1618026 553883366314527799689227 := by
  unfold tailWord_1618026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14753564109043903421402483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39342837624117075790406621 14753564109043903421402483)
  ·
    refine ⟨22130346163565855132103725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14753564109043903421402483 22130346163565855132103725)
    ·
      refine ⟨8298879811337195674538897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22130346163565855132103725 8298879811337195674538897)
      ·
        refine ⟨6224159858502896755904173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8298879811337195674538897 6224159858502896755904173)
        ·
          refine ⟨2334059946938586283464065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6224159858502896755904173 2334059946938586283464065)
          ·
            refine ⟨1750544960203939712598049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334059946938586283464065 1750544960203939712598049)
            ·
              refine ⟨1312908720152954784448537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750544960203939712598049 1312908720152954784448537)
              ·
                refine ⟨984681540114716088336403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1312908720152954784448537 984681540114716088336403)
                ·
                  refine ⟨1477022310172074132504605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984681540114716088336403 1477022310172074132504605)
                  ·
                    refine ⟨553883366314527799689227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477022310172074132504605 553883366314527799689227)
                    ·
                      rfl

theorem cell22_1618026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1618026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618026 prefixEnd_1618026 := by exact prefixLift 1618026
  have htrace : WordTrace (prefixWord ++ tailWord_1618026) baseStart_1618026 baseEnd_1618026 := by
    simpa [prefixWord, tailWord_1618026, baseEnd_1618026] using wordTrace_append hprefix tailTrace_1618026
  have hstable : (prefixWord ++ tailWord_1618026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618026).length < 2 ^ (prefixWord ++ tailWord_1618026).sum := by decide
  have hdescent : baseEnd_1618026 < baseStart_1618026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618048 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_1618048 : Nat := 118140960795 + 1618048 * 2 ^ 59
def prefixEnd_1618048 : Nat := 4983230072969 + 3 ^ 40 * 1618048 * 2
def baseEnd_1618048 : Nat := 553890897364127075639159

theorem tailTrace_1618048 : CollatzResearch.WordTrace tailWord_1618048 prefixEnd_1618048 553890897364127075639159 := by
  unfold tailWord_1618048
  simp only [CollatzResearch.WordTrace]
  refine ⟨29507529421047955721455399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39343372561397274295273865 29507529421047955721455399)
  ·
    refine ⟨44261294131571933582183099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29507529421047955721455399 44261294131571933582183099)
    ·
      refine ⟨66391941197357900373274649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44261294131571933582183099 66391941197357900373274649)
      ·
        refine ⟨49793955898018425279955987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66391941197357900373274649 49793955898018425279955987)
        ·
          refine ⟨74690933847027637919933981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49793955898018425279955987 74690933847027637919933981)
          ·
            refine ⟨28009100192635364219975243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74690933847027637919933981 28009100192635364219975243)
            ·
              refine ⟨42013650288953046329962865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28009100192635364219975243 42013650288953046329962865)
              ·
                refine ⟨31510237716714784747472149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42013650288953046329962865 31510237716714784747472149)
                ·
                  refine ⟨1477042392971005535037757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31510237716714784747472149 1477042392971005535037757)
                  ·
                    refine ⟨553890897364127075639159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477042392971005535037757 553890897364127075639159)
                    ·
                      rfl

theorem cell22_1618048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_1618048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618048 prefixEnd_1618048 := by exact prefixLift 1618048
  have htrace : WordTrace (prefixWord ++ tailWord_1618048) baseStart_1618048 baseEnd_1618048 := by
    simpa [prefixWord, tailWord_1618048, baseEnd_1618048] using wordTrace_append hprefix tailTrace_1618048
  have hstable : (prefixWord ++ tailWord_1618048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618048).length < 2 ^ (prefixWord ++ tailWord_1618048).sum := by decide
  have hdescent : baseEnd_1618048 < baseStart_1618048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618082 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1618082 : Nat := 118140960795 + 1618082 * 2 ^ 59
def prefixEnd_1618082 : Nat := 4983230072969 + 3 ^ 40 * 1618082 * 2
def baseEnd_1618082 : Nat := 553902536258962320289055

theorem tailTrace_1618082 : CollatzResearch.WordTrace tailWord_1618082 prefixEnd_1618082 553902536258962320289055 := by
  unfold tailWord_1618082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754074730993183812412125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39344199282648490166432333 14754074730993183812412125)
  ·
    refine ⟨5532778024122443929654547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14754074730993183812412125 5532778024122443929654547)
    ·
      refine ⟨8299167036183665894481821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532778024122443929654547 8299167036183665894481821)
      ·
        refine ⟨3112187638568874710430683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8299167036183665894481821 3112187638568874710430683)
        ·
          refine ⟨4668281457853312065646025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112187638568874710430683 4668281457853312065646025)
          ·
            refine ⟨3501211093389984049234519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668281457853312065646025 3501211093389984049234519)
            ·
              refine ⟨5251816640084976073851779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501211093389984049234519 5251816640084976073851779)
              ·
                refine ⟨7877724960127464110777669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251816640084976073851779 7877724960127464110777669)
                ·
                  refine ⟨1477073430023899520770813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7877724960127464110777669 1477073430023899520770813)
                  ·
                    refine ⟨553902536258962320289055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477073430023899520770813 553902536258962320289055)
                    ·
                      rfl

theorem cell22_1618082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1618082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618082 prefixEnd_1618082 := by exact prefixLift 1618082
  have htrace : WordTrace (prefixWord ++ tailWord_1618082) baseStart_1618082 baseEnd_1618082 := by
    simpa [prefixWord, tailWord_1618082, baseEnd_1618082] using wordTrace_append hprefix tailTrace_1618082
  have hstable : (prefixWord ++ tailWord_1618082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618082).length < 2 ^ (prefixWord ++ tailWord_1618082).sum := by decide
  have hdescent : baseEnd_1618082 < baseStart_1618082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618138 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1618138 : Nat := 118140960795 + 1618138 * 2 ^ 59
def prefixEnd_1618138 : Nat := 4983230072969 + 3 ^ 40 * 1618138 * 2
def baseEnd_1618138 : Nat := 553921706203396840888883

theorem tailTrace_1618138 : CollatzResearch.WordTrace tailWord_1618138 prefixEnd_1618138 553921706203396840888883 := by
  unfold tailWord_1618138
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754585352942464203421767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39345560941179904542458045 14754585352942464203421767)
  ·
    refine ⟨22131878029413696305132651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754585352942464203421767 22131878029413696305132651)
    ·
      refine ⟨33197817044120544457698977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22131878029413696305132651 33197817044120544457698977)
      ·
        refine ⟨24898362783090408343274233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33197817044120544457698977 24898362783090408343274233)
        ·
          refine ⟨18673772087317806257455675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24898362783090408343274233 18673772087317806257455675)
          ·
            refine ⟨28010658130976709386183513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18673772087317806257455675 28010658130976709386183513)
            ·
              refine ⟨21007993598232532039637635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28010658130976709386183513 21007993598232532039637635)
              ·
                refine ⟨31511990397348798059456453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21007993598232532039637635 31511990397348798059456453)
                ·
                  refine ⟨5908498199502899636148085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31511990397348798059456453 5908498199502899636148085)
                  ·
                    refine ⟨553921706203396840888883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5908498199502899636148085 553921706203396840888883)
                    ·
                      rfl

theorem cell22_1618138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1618138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618138 prefixEnd_1618138 := by exact prefixLift 1618138
  have htrace : WordTrace (prefixWord ++ tailWord_1618138) baseStart_1618138 baseEnd_1618138 := by
    simpa [prefixWord, tailWord_1618138, baseEnd_1618138] using wordTrace_append hprefix tailTrace_1618138
  have hstable : (prefixWord ++ tailWord_1618138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618138).length < 2 ^ (prefixWord ++ tailWord_1618138).sum := by decide
  have hdescent : baseEnd_1618138 < baseStart_1618138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618144 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 1, 3]
def baseStart_1618144 : Nat := 118140960795 + 1618144 * 2 ^ 59
def prefixEnd_1618144 : Nat := 4983230072969 + 3 ^ 40 * 1618144 * 2
def baseEnd_1618144 : Nat := 553923760126014825238865

theorem tailTrace_1618144 : CollatzResearch.WordTrace tailWord_1618144 prefixEnd_1618144 553923760126014825238865 := by
  unfold tailWord_1618144
  simp only [CollatzResearch.WordTrace]
  refine ⟨29509280124874059919202743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39345706833165413225603657 29509280124874059919202743)
  ·
    refine ⟨44263920187311089878804115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29509280124874059919202743 44263920187311089878804115)
    ·
      refine ⟨66395880280966634818206173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44263920187311089878804115 66395880280966634818206173)
      ·
        refine ⟨24898455105362488056827315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66395880280966634818206173 24898455105362488056827315)
        ·
          refine ⟨37347682658043732085240973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24898455105362488056827315 37347682658043732085240973)
          ·
            refine ⟨14005380996766399531965365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37347682658043732085240973 14005380996766399531965365)
            ·
              refine ⟨1313004468446849956121753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14005380996766399531965365 1313004468446849956121753)
              ·
                refine ⟨984753351335137467091315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313004468446849956121753 984753351335137467091315)
                ·
                  refine ⟨1477130027002706200636973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 984753351335137467091315 1477130027002706200636973)
                  ·
                    refine ⟨553923760126014825238865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477130027002706200636973 553923760126014825238865)
                    ·
                      rfl

theorem cell22_1618144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 1, 3].length) (baseStart_1618144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618144 prefixEnd_1618144 := by exact prefixLift 1618144
  have htrace : WordTrace (prefixWord ++ tailWord_1618144) baseStart_1618144 baseEnd_1618144 := by
    simpa [prefixWord, tailWord_1618144, baseEnd_1618144] using wordTrace_append hprefix tailTrace_1618144
  have hstable : (prefixWord ++ tailWord_1618144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618144).length < 2 ^ (prefixWord ++ tailWord_1618144).sum := by decide
  have hdescent : baseEnd_1618144 < baseStart_1618144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618153 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_1618153 : Nat := 118140960795 + 1618153 * 2 ^ 59
def prefixEnd_1618153 : Nat := 4983230072969 + 3 ^ 40 * 1618153 * 2
def baseEnd_1618153 : Nat := 553926841009941801763837

theorem tailTrace_1618153 : CollatzResearch.WordTrace tailWord_1618153 prefixEnd_1618153 553926841009941801763837 := by
  unfold tailWord_1618153
  simp only [CollatzResearch.WordTrace]
  refine ⟨59018888506715514375483113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39345925671143676250322075 59018888506715514375483113)
  ·
    refine ⟨44264166380036635781612335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59018888506715514375483113 44264166380036635781612335)
    ·
      refine ⟨66396249570054953672418503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44264166380036635781612335 66396249570054953672418503)
      ·
        refine ⟨99594374355082430508627755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66396249570054953672418503 99594374355082430508627755)
        ·
          refine ⟨149391561532623645762941633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99594374355082430508627755 149391561532623645762941633)
          ·
            refine ⟨112043671149467734322206225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149391561532623645762941633 112043671149467734322206225)
            ·
              refine ⟨84032753362100800741654669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112043671149467734322206225 84032753362100800741654669)
              ·
                refine ⟨31512282510787800278120501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84032753362100800741654669 31512282510787800278120501)
                ·
                  refine ⟨2954276485386356276073797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31512282510787800278120501 2954276485386356276073797)
                  ·
                    refine ⟨553926841009941801763837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954276485386356276073797 553926841009941801763837)
                    ·
                      rfl

theorem cell22_1618153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_1618153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618153 prefixEnd_1618153 := by exact prefixLift 1618153
  have htrace : WordTrace (prefixWord ++ tailWord_1618153) baseStart_1618153 baseEnd_1618153 := by
    simpa [prefixWord, tailWord_1618153, baseEnd_1618153] using wordTrace_append hprefix tailTrace_1618153
  have hstable : (prefixWord ++ tailWord_1618153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618153).length < 2 ^ (prefixWord ++ tailWord_1618153).sum := by decide
  have hdescent : baseEnd_1618153 < baseStart_1618153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618157 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 5]
def baseStart_1618157 : Nat := 118140960795 + 1618157 * 2 ^ 59
def prefixEnd_1618157 : Nat := 4983230072969 + 3 ^ 40 * 1618157 * 2
def baseEnd_1618157 : Nat := 184642736763895708221275

theorem tailTrace_1618157 : CollatzResearch.WordTrace tailWord_1618157 prefixEnd_1618157 184642736763895708221275 := by
  unfold tailWord_1618157
  simp only [CollatzResearch.WordTrace]
  refine ⟨59019034398701023058628725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39346022932467348705752483 59019034398701023058628725)
  ·
    refine ⟨5533034474878220911746443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59019034398701023058628725 5533034474878220911746443)
    ·
      refine ⟨8299551712317331367619665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5533034474878220911746443 8299551712317331367619665)
      ·
        refine ⟨6224663784237998525714749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8299551712317331367619665 6224663784237998525714749)
        ·
          refine ⟨2334248919089249447143031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6224663784237998525714749 2334248919089249447143031)
          ·
            refine ⟨3501373378633874170714547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334248919089249447143031 3501373378633874170714547)
            ·
              refine ⟨5252060067950811256071821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501373378633874170714547 5252060067950811256071821)
              ·
                refine ⟨1969522525481554221026933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5252060067950811256071821 1969522525481554221026933)
                ·
                  refine ⟨184642736763895708221275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1969522525481554221026933 184642736763895708221275)
                  ·
                    rfl

theorem cell22_1618157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_1618157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618157 prefixEnd_1618157 := by exact prefixLift 1618157
  have htrace : WordTrace (prefixWord ++ tailWord_1618157) baseStart_1618157 baseEnd_1618157 := by
    simpa [prefixWord, tailWord_1618157, baseEnd_1618157] using wordTrace_append hprefix tailTrace_1618157
  have hstable : (prefixWord ++ tailWord_1618157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618157).length < 2 ^ (prefixWord ++ tailWord_1618157).sum := by decide
  have hdescent : baseEnd_1618157 < baseStart_1618157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618168 : List Nat := [2, 1, 2, 1, 1, 2, 1, 6, 6]
def baseStart_1618168 : Nat := 118140960795 + 1618168 * 2 ^ 59
def prefixEnd_1618168 : Nat := 4983230072969 + 3 ^ 40 * 1618168 * 2
def baseEnd_1618168 : Nat := 184643991938828920879597

theorem tailTrace_1618168 : CollatzResearch.WordTrace tailWord_1618168 prefixEnd_1618168 184643991938828920879597 := by
  unfold tailWord_1618168
  simp only [CollatzResearch.WordTrace]
  refine ⟨29509717800830585968639579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39346290401107447958186105 29509717800830585968639579)
  ·
    refine ⟨44264576701245878952959369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29509717800830585968639579 44264576701245878952959369)
    ·
      refine ⟨33198432525934409214719527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44264576701245878952959369 33198432525934409214719527)
      ·
        refine ⟨49797648788901613822079291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33198432525934409214719527 49797648788901613822079291)
        ·
          refine ⟨74696473183352420733118937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49797648788901613822079291 74696473183352420733118937)
          ·
            refine ⟨56022354887514315549839203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74696473183352420733118937 56022354887514315549839203)
            ·
              refine ⟨84033532331271473324758805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56022354887514315549839203 84033532331271473324758805)
              ·
                refine ⟨3939071828028350312098069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84033532331271473324758805 3939071828028350312098069)
                ·
                  refine ⟨184643991938828920879597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3939071828028350312098069 184643991938828920879597)
                  ·
                    rfl

theorem cell22_1618168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_1618168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618168 prefixEnd_1618168 := by exact prefixLift 1618168
  have htrace : WordTrace (prefixWord ++ tailWord_1618168) baseStart_1618168 baseEnd_1618168 := by
    simpa [prefixWord, tailWord_1618168, baseEnd_1618168] using wordTrace_append hprefix tailTrace_1618168
  have hstable : (prefixWord ++ tailWord_1618168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618168).length < 2 ^ (prefixWord ++ tailWord_1618168).sum := by decide
  have hdescent : baseEnd_1618168 < baseStart_1618168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618170 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_1618170 : Nat := 118140960795 + 1618170 * 2 ^ 59
def prefixEnd_1618170 : Nat := 4983230072969 + 3 ^ 40 * 1618170 * 2
def baseEnd_1618170 : Nat := 553932660457359424088785

theorem tailTrace_1618170 : CollatzResearch.WordTrace tailWord_1618170 prefixEnd_1618170 553932660457359424088785 := by
  unfold tailWord_1618170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754877136913481569712991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39346339031769284185901309 14754877136913481569712991)
  ·
    refine ⟨22132315705370222354569487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14754877136913481569712991 22132315705370222354569487)
    ·
      refine ⟨33198473558055333531854231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22132315705370222354569487 33198473558055333531854231)
      ·
        refine ⟨49797710337083000297781347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33198473558055333531854231 49797710337083000297781347)
        ·
          refine ⟨74696565505624500446672021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49797710337083000297781347 74696565505624500446672021)
          ·
            refine ⟨3501401508076148458437751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74696565505624500446672021 3501401508076148458437751)
            ·
              refine ⟨5252102262114222687656627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501401508076148458437751 5252102262114222687656627)
              ·
                refine ⟨7878153393171334031484941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5252102262114222687656627 7878153393171334031484941)
                ·
                  refine ⟨2954307522439250261806853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7878153393171334031484941 2954307522439250261806853)
                  ·
                    refine ⟨553932660457359424088785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954307522439250261806853 553932660457359424088785)
                    ·
                      rfl

theorem cell22_1618170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_1618170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618170 prefixEnd_1618170 := by exact prefixLift 1618170
  have htrace : WordTrace (prefixWord ++ tailWord_1618170) baseStart_1618170 baseEnd_1618170 := by
    simpa [prefixWord, tailWord_1618170, baseEnd_1618170] using wordTrace_append hprefix tailTrace_1618170
  have hstable : (prefixWord ++ tailWord_1618170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618170).length < 2 ^ (prefixWord ++ tailWord_1618170).sum := by decide
  have hdescent : baseEnd_1618170 < baseStart_1618170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618187 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 1, 4]
def baseStart_1618187 : Nat := 118140960795 + 1618187 * 2 ^ 59
def prefixEnd_1618187 : Nat := 4983230072969 + 3 ^ 40 * 1618187 * 2
def baseEnd_1618187 : Nat := 553938479904777046413733

theorem tailTrace_1618187 : CollatzResearch.WordTrace tailWord_1618187 prefixEnd_1618187 553938479904777046413733 := by
  unfold tailWord_1618187
  simp only [CollatzResearch.WordTrace]
  refine ⟨59020128588592338182220815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39346752392394892121480543 59020128588592338182220815)
  ·
    refine ⟨88530192882888507273331223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59020128588592338182220815 88530192882888507273331223)
    ·
      refine ⟨132795289324332760909996835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88530192882888507273331223 132795289324332760909996835)
      ·
        refine ⟨199192933986499141364995253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132795289324332760909996835 199192933986499141364995253)
        ·
          refine ⟨18674337561234294502968305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199192933986499141364995253 18674337561234294502968305)
          ·
            refine ⟨14005753170925720877226229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18674337561234294502968305 14005753170925720877226229)
            ·
              refine ⟨1313039359774286332239959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14005753170925720877226229 1313039359774286332239959)
              ·
                refine ⟨1969559039661429498359939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313039359774286332239959 1969559039661429498359939)
                ·
                  refine ⟨2954338559492144247539909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969559039661429498359939 2954338559492144247539909)
                  ·
                    refine ⟨553938479904777046413733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954338559492144247539909 553938479904777046413733)
                    ·
                      rfl

theorem cell22_1618187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 1, 4].length) (baseStart_1618187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618187 prefixEnd_1618187 := by exact prefixLift 1618187
  have htrace : WordTrace (prefixWord ++ tailWord_1618187) baseStart_1618187 baseEnd_1618187 := by
    simpa [prefixWord, tailWord_1618187, baseEnd_1618187] using wordTrace_append hprefix tailTrace_1618187
  have hstable : (prefixWord ++ tailWord_1618187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618187).length < 2 ^ (prefixWord ++ tailWord_1618187).sum := by decide
  have hdescent : baseEnd_1618187 < baseStart_1618187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618268 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 2, 3]
def baseStart_1618268 : Nat := 118140960795 + 1618268 * 2 ^ 59
def prefixEnd_1618268 : Nat := 4983230072969 + 3 ^ 40 * 1618268 * 2
def baseEnd_1618268 : Nat := 553966207860119835138485

theorem tailTrace_1618268 : CollatzResearch.WordTrace tailWord_1618268 prefixEnd_1618268 553966207860119835138485 := by
  unfold tailWord_1618268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29511541450649444507959729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39348721934199259343946305 29511541450649444507959729)
  ·
    refine ⟨22133656087987083380969797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29511541450649444507959729 22133656087987083380969797)
    ·
      refine ⟨4150060516497578133931837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22133656087987083380969797 4150060516497578133931837)
      ·
        refine ⟨1556272693686591800224439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4150060516497578133931837 1556272693686591800224439)
        ·
          refine ⟨2334409040529887700336659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556272693686591800224439 2334409040529887700336659)
          ·
            refine ⟨3501613560794831550504989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334409040529887700336659 3501613560794831550504989)
            ·
              refine ⟨1313105085298061831439371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3501613560794831550504989 1313105085298061831439371)
              ·
                refine ⟨1969657627947092747159057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313105085298061831439371 1969657627947092747159057)
                ·
                  refine ⟨1477243220960319560369293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1969657627947092747159057 1477243220960319560369293)
                  ·
                    refine ⟨553966207860119835138485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477243220960319560369293 553966207860119835138485)
                    ·
                      rfl

theorem cell22_1618268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_1618268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618268 prefixEnd_1618268 := by exact prefixLift 1618268
  have htrace : WordTrace (prefixWord ++ tailWord_1618268) baseStart_1618268 baseEnd_1618268 := by
    simpa [prefixWord, tailWord_1618268, baseEnd_1618268] using wordTrace_append hprefix tailTrace_1618268
  have hstable : (prefixWord ++ tailWord_1618268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618268).length < 2 ^ (prefixWord ++ tailWord_1618268).sum := by decide
  have hdescent : baseEnd_1618268 < baseStart_1618268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618339 : List Nat := [1, 1, 1, 4, 1, 6, 1, 2, 1, 4]
def baseStart_1618339 : Nat := 118140960795 + 1618339 * 2 ^ 59
def prefixEnd_1618339 : Nat := 4983230072969 + 3 ^ 40 * 1618339 * 2
def baseEnd_1618339 : Nat := 553990512611099316613267

theorem tailTrace_1618339 : CollatzResearch.WordTrace tailWord_1618339 prefixEnd_1618339 553990512611099316613267 := by
  unfold tailWord_1618339
  simp only [CollatzResearch.WordTrace]
  refine ⟨59025672484041668141754071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39350448322694445427836047 59025672484041668141754071)
  ·
    refine ⟨88538508726062502212631107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59025672484041668141754071 88538508726062502212631107)
    ·
      refine ⟨132807763089093753318946661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88538508726062502212631107 132807763089093753318946661)
      ·
        refine ⟨24901455579205078747302499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132807763089093753318946661 24901455579205078747302499)
        ·
          refine ⟨37352183368807618120953749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24901455579205078747302499 37352183368807618120953749)
          ·
            refine ⟨1750883595412857099419707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37352183368807618120953749 1750883595412857099419707)
            ·
              refine ⟨2626325393119285649129561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1750883595412857099419707 2626325393119285649129561)
              ·
                refine ⟨1969744044839464236847171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2626325393119285649129561 1969744044839464236847171)
                ·
                  refine ⟨2954616067259196355270757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1969744044839464236847171 2954616067259196355270757)
                  ·
                    refine ⟨553990512611099316613267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954616067259196355270757 553990512611099316613267)
                    ·
                      rfl

theorem cell22_1618339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 2, 1, 4].length) (baseStart_1618339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618339 prefixEnd_1618339 := by exact prefixLift 1618339
  have htrace : WordTrace (prefixWord ++ tailWord_1618339) baseStart_1618339 baseEnd_1618339 := by
    simpa [prefixWord, tailWord_1618339, baseEnd_1618339] using wordTrace_append hprefix tailTrace_1618339
  have hstable : (prefixWord ++ tailWord_1618339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618339).length < 2 ^ (prefixWord ++ tailWord_1618339).sum := by decide
  have hdescent : baseEnd_1618339 < baseStart_1618339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618365 : List Nat := [1, 4, 1, 2, 2, 12]
def baseStart_1618365 : Nat := 118140960795 + 1618365 * 2 ^ 59
def prefixEnd_1618365 : Nat := 4983230072969 + 3 ^ 40 * 1618365 * 2
def baseEnd_1618365 : Nat := 6839498925215356981027

theorem tailTrace_1618365 : CollatzResearch.WordTrace tailWord_1618365 prefixEnd_1618365 6839498925215356981027 := by
  unfold tailWord_1618365
  simp only [CollatzResearch.WordTrace]
  refine ⟨59026620781947474582200549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39351080521298316388133699 59026620781947474582200549)
  ·
    refine ⟨11067491396615151484162603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59026620781947474582200549 11067491396615151484162603)
    ·
      refine ⟨16601237094922727226243905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067491396615151484162603 16601237094922727226243905)
      ·
        refine ⟨12450927821192045419682929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16601237094922727226243905 12450927821192045419682929)
        ·
          refine ⟨9338195865894034064762197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12450927821192045419682929 9338195865894034064762197)
          ·
            refine ⟨6839498925215356981027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9338195865894034064762197 6839498925215356981027)
            ·
              rfl

theorem cell22_1618365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 12].length) (baseStart_1618365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618365 prefixEnd_1618365 := by exact prefixLift 1618365
  have htrace : WordTrace (prefixWord ++ tailWord_1618365) baseStart_1618365 baseEnd_1618365 := by
    simpa [prefixWord, tailWord_1618365, baseEnd_1618365] using wordTrace_append hprefix tailTrace_1618365
  have hstable : (prefixWord ++ tailWord_1618365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618365).length < 2 ^ (prefixWord ++ tailWord_1618365).sum := by decide
  have hdescent : baseEnd_1618365 < baseStart_1618365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618386 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_1618386 : Nat := 118140960795 + 1618386 * 2 ^ 59
def prefixEnd_1618386 : Nat := 4983230072969 + 3 ^ 40 * 1618386 * 2
def baseEnd_1618386 : Nat := 554006601671606860688123

theorem tailTrace_1618386 : CollatzResearch.WordTrace tailWord_1618386 prefixEnd_1618386 554006601671606860688123 := by
  unfold tailWord_1618386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14756846678717848792178753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39351591143247596779143341 14756846678717848792178753)
  ·
    refine ⟨11067635009038386594134065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14756846678717848792178753 11067635009038386594134065)
    ·
      refine ⟨8300726256778789945600549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11067635009038386594134065 8300726256778789945600549)
      ·
        refine ⟨1556386173146023114800103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8300726256778789945600549 1556386173146023114800103)
        ·
          refine ⟨2334579259719034672200155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556386173146023114800103 2334579259719034672200155)
          ·
            refine ⟨3501868889578552008300233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2334579259719034672200155 3501868889578552008300233)
            ·
              refine ⟨2626401667183914006225175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3501868889578552008300233 2626401667183914006225175)
              ·
                refine ⟨3939602500775871009337763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626401667183914006225175 3939602500775871009337763)
                ·
                  refine ⟨5909403751163806514006645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3939602500775871009337763 5909403751163806514006645)
                  ·
                    refine ⟨554006601671606860688123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5909403751163806514006645 554006601671606860688123)
                    ·
                      rfl

theorem cell22_1618386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_1618386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618386 prefixEnd_1618386 := by exact prefixLift 1618386
  have htrace : WordTrace (prefixWord ++ tailWord_1618386) baseStart_1618386 baseEnd_1618386 := by
    simpa [prefixWord, tailWord_1618386, baseEnd_1618386] using wordTrace_append hprefix tailTrace_1618386
  have hstable : (prefixWord ++ tailWord_1618386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618386).length < 2 ^ (prefixWord ++ tailWord_1618386).sum := by decide
  have hdescent : baseEnd_1618386 < baseStart_1618386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618442 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1618442 : Nat := 118140960795 + 1618442 * 2 ^ 59
def prefixEnd_1618442 : Nat := 4983230072969 + 3 ^ 40 * 1618442 * 2
def baseEnd_1618442 : Nat := 554025771616041381287951

theorem tailTrace_1618442 : CollatzResearch.WordTrace tailWord_1618442 prefixEnd_1618442 554025771616041381287951 := by
  unfold tailWord_1618442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14757357300667129183188395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39352952801779011155169053 14757357300667129183188395)
  ·
    refine ⟨22136035951000693774782593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14757357300667129183188395 22136035951000693774782593)
    ·
      refine ⟨16602026963250520331086945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22136035951000693774782593 16602026963250520331086945)
      ·
        refine ⟨12451520222437890248315209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16602026963250520331086945 12451520222437890248315209)
        ·
          refine ⟨9338640166828417686236407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12451520222437890248315209 9338640166828417686236407)
          ·
            refine ⟨14007960250242626529354611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9338640166828417686236407 14007960250242626529354611)
            ·
              refine ⟨21011940375363939794031917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14007960250242626529354611 21011940375363939794031917)
              ·
                refine ⟨7879477640761477422761969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21011940375363939794031917 7879477640761477422761969)
                ·
                  refine ⟨5909608230571108067071477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7879477640761477422761969 5909608230571108067071477)
                  ·
                    refine ⟨554025771616041381287951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5909608230571108067071477 554025771616041381287951)
                    ·
                      rfl

theorem cell22_1618442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1618442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618442 prefixEnd_1618442 := by exact prefixLift 1618442
  have htrace : WordTrace (prefixWord ++ tailWord_1618442) baseStart_1618442 baseEnd_1618442 := by
    simpa [prefixWord, tailWord_1618442, baseEnd_1618442] using wordTrace_append hprefix tailTrace_1618442
  have hstable : (prefixWord ++ tailWord_1618442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618442).length < 2 ^ (prefixWord ++ tailWord_1618442).sum := by decide
  have hdescent : baseEnd_1618442 < baseStart_1618442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618517 : List Nat := [1, 3, 2, 2, 1, 1, 4, 8]
def baseStart_1618517 : Nat := 118140960795 + 1618517 * 2 ^ 59
def prefixEnd_1618517 : Nat := 4983230072969 + 3 ^ 40 * 1618517 * 2
def baseEnd_1618517 : Nat := 61561271738751798406969

theorem tailTrace_1618517 : CollatzResearch.WordTrace tailWord_1618517 prefixEnd_1618517 61561271738751798406969 := by
  unfold tailWord_1618517
  simp only [CollatzResearch.WordTrace]
  refine ⟨59032164677396804541733805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39354776451597869694489203 59032164677396804541733805)
  ·
    refine ⟨22137061754023801703150177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59032164677396804541733805 22137061754023801703150177)
    ·
      refine ⟨16602796315517851277362633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22137061754023801703150177 16602796315517851277362633)
      ·
        refine ⟨12452097236638388458021975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16602796315517851277362633 12452097236638388458021975)
        ·
          refine ⟨18678145854957582687032963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12452097236638388458021975 18678145854957582687032963)
          ·
            refine ⟨28017218782436374030549445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18678145854957582687032963 28017218782436374030549445)
            ·
              refine ⟨5253228521706820130728021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28017218782436374030549445 5253228521706820130728021)
              ·
                refine ⟨61561271738751798406969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5253228521706820130728021 61561271738751798406969)
                ·
                  rfl

theorem cell22_1618517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 8].length) (baseStart_1618517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618517 prefixEnd_1618517 := by exact prefixLift 1618517
  have htrace : WordTrace (prefixWord ++ tailWord_1618517) baseStart_1618517 baseEnd_1618517 := by
    simpa [prefixWord, tailWord_1618517, baseEnd_1618517] using wordTrace_append hprefix tailTrace_1618517
  have hstable : (prefixWord ++ tailWord_1618517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618517).length < 2 ^ (prefixWord ++ tailWord_1618517).sum := by decide
  have hdescent : baseEnd_1618517 < baseStart_1618517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618519 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1618519 : Nat := 118140960795 + 1618519 * 2 ^ 59
def prefixEnd_1618519 : Nat := 4983230072969 + 3 ^ 40 * 1618519 * 2
def baseEnd_1618519 : Nat := 554052130289638847112715

theorem tailTrace_1618519 : CollatzResearch.WordTrace tailWord_1618519 prefixEnd_1618519 554052130289638847112715 := by
  unfold tailWord_1618519
  simp only [CollatzResearch.WordTrace]
  refine ⟨59032237623389558883306611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39354825082259705922204407 59032237623389558883306611)
  ·
    refine ⟨88548356435084338324959917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59032237623389558883306611 88548356435084338324959917)
    ·
      refine ⟨33205633663156626871859969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88548356435084338324959917 33205633663156626871859969)
      ·
        refine ⟨24904225247367470153894977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33205633663156626871859969 24904225247367470153894977)
        ·
          refine ⟨18678168935525602615421233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24904225247367470153894977 18678168935525602615421233)
          ·
            refine ⟨14008626701644201961565925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18678168935525602615421233 14008626701644201961565925)
            ·
              refine ⟨2626617506558287867793611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14008626701644201961565925 2626617506558287867793611)
              ·
                refine ⟨3939926259837431801690417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626617506558287867793611 3939926259837431801690417)
                ·
                  refine ⟨2954944694878073851267813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3939926259837431801690417 2954944694878073851267813)
                  ·
                    refine ⟨554052130289638847112715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2954944694878073851267813 554052130289638847112715)
                    ·
                      rfl

theorem cell22_1618519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1618519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618519 prefixEnd_1618519 := by exact prefixLift 1618519
  have htrace : WordTrace (prefixWord ++ tailWord_1618519) baseStart_1618519 baseEnd_1618519 := by
    simpa [prefixWord, tailWord_1618519, baseEnd_1618519] using wordTrace_append hprefix tailTrace_1618519
  have hstable : (prefixWord ++ tailWord_1618519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618519).length < 2 ^ (prefixWord ++ tailWord_1618519).sum := by decide
  have hdescent : baseEnd_1618519 < baseStart_1618519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618583 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 1, 3]
def baseStart_1618583 : Nat := 118140960795 + 1618583 * 2 ^ 59
def prefixEnd_1618583 : Nat := 4983230072969 + 3 ^ 40 * 1618583 * 2
def baseEnd_1618583 : Nat := 554074038797564013512519

theorem tailTrace_1618583 : CollatzResearch.WordTrace tailWord_1618583 prefixEnd_1618583 554074038797564013512519 := by
  unfold tailWord_1618583
  simp only [CollatzResearch.WordTrace]
  refine ⟨59034571895157697813636403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39356381263438465209090935 59034571895157697813636403)
  ·
    refine ⟨88551857842736546720454605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59034571895157697813636403 88551857842736546720454605)
    ·
      refine ⟨33206946691026205020170477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88551857842736546720454605 33206946691026205020170477)
      ·
        refine ⟨12452605009134826882563929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33206946691026205020170477 12452605009134826882563929)
        ·
          refine ⟨9339453756851120161922947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12452605009134826882563929 9339453756851120161922947)
          ·
            refine ⟨14009180635276680242884421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339453756851120161922947 14009180635276680242884421)
            ·
              refine ⟨2626721369114377545540829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14009180635276680242884421 2626721369114377545540829)
              ·
                refine ⟨985020513417891579577811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2626721369114377545540829 985020513417891579577811)
                ·
                  refine ⟨1477530770126837369366717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985020513417891579577811 1477530770126837369366717)
                  ·
                    refine ⟨554074038797564013512519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477530770126837369366717 554074038797564013512519)
                    ·
                      rfl

theorem cell22_1618583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_1618583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618583 prefixEnd_1618583 := by exact prefixLift 1618583
  have htrace : WordTrace (prefixWord ++ tailWord_1618583) baseStart_1618583 baseEnd_1618583 := by
    simpa [prefixWord, tailWord_1618583, baseEnd_1618583] using wordTrace_append hprefix tailTrace_1618583
  have hstable : (prefixWord ++ tailWord_1618583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618583).length < 2 ^ (prefixWord ++ tailWord_1618583).sum := by decide
  have hdescent : baseEnd_1618583 < baseStart_1618583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618613 : List Nat := [1, 3, 3, 3, 1, 2, 3, 1, 5]
def baseStart_1618613 : Nat := 118140960795 + 1618613 * 2 ^ 59
def prefixEnd_1618613 : Nat := 4983230072969 + 3 ^ 40 * 1618613 * 2
def baseEnd_1618613 : Nat := 184694769470217978420809

theorem tailTrace_1618613 : CollatzResearch.WordTrace tailWord_1618613 prefixEnd_1618613 184694769470217978420809 := by
  unfold tailWord_1618613
  simp only [CollatzResearch.WordTrace]
  refine ⟨59035666085049012937228493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39357110723366008624818995 59035666085049012937228493)
  ·
    refine ⟨22138374781893379851460685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59035666085049012937228493 22138374781893379851460685)
    ·
      refine ⟨8301890543210017444297757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22138374781893379851460685 8301890543210017444297757)
      ·
        refine ⟨3113208953703756541611659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8301890543210017444297757 3113208953703756541611659)
        ·
          refine ⟨4669813430555634812417489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113208953703756541611659 4669813430555634812417489)
          ·
            refine ⟨3502360072916726109313117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4669813430555634812417489 3502360072916726109313117)
            ·
              refine ⟨1313385027343772290992419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3502360072916726109313117 1313385027343772290992419)
              ·
                refine ⟨1970077541015658436488629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313385027343772290992419 1970077541015658436488629)
                ·
                  refine ⟨184694769470217978420809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1970077541015658436488629 184694769470217978420809)
                  ·
                    rfl

theorem cell22_1618613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_1618613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618613 prefixEnd_1618613 := by exact prefixLift 1618613
  have htrace : WordTrace (prefixWord ++ tailWord_1618613) baseStart_1618613 baseEnd_1618613 := by
    simpa [prefixWord, tailWord_1618613, baseEnd_1618613] using wordTrace_append hprefix tailTrace_1618613
  have hstable : (prefixWord ++ tailWord_1618613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618613).length < 2 ^ (prefixWord ++ tailWord_1618613).sum := by decide
  have hdescent : baseEnd_1618613 < baseStart_1618613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618624 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 6]
def baseStart_1618624 : Nat := 118140960795 + 1618624 * 2 ^ 59
def prefixEnd_1618624 : Nat := 4983230072969 + 3 ^ 40 * 1618624 * 2
def baseEnd_1618624 : Nat := 184696024645151191079131

theorem tailTrace_1618624 : CollatzResearch.WordTrace tailWord_1618624 prefixEnd_1618624 184696024645151191079131 := by
  unfold tailWord_1618624
  simp only [CollatzResearch.WordTrace]
  refine ⟨29518033644004580907939463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39357378192006107877252617 29518033644004580907939463)
  ·
    refine ⟨44277050466006871361909195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29518033644004580907939463 44277050466006871361909195)
    ·
      refine ⟨66415575699010307042863793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44277050466006871361909195 66415575699010307042863793)
      ·
        refine ⟨49811681774257730282147845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66415575699010307042863793 49811681774257730282147845)
        ·
          refine ⟨9339690332673324427902721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49811681774257730282147845 9339690332673324427902721)
          ·
            refine ⟨7004767749504993320927041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339690332673324427902721 7004767749504993320927041)
            ·
              refine ⟨5253575812128744990695281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004767749504993320927041 5253575812128744990695281)
              ·
                refine ⟨3940181859096558743021461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5253575812128744990695281 3940181859096558743021461)
                ·
                  refine ⟨184696024645151191079131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3940181859096558743021461 184696024645151191079131)
                  ·
                    rfl

theorem cell22_1618624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_1618624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618624 prefixEnd_1618624 := by exact prefixLift 1618624
  have htrace : WordTrace (prefixWord ++ tailWord_1618624) baseStart_1618624 baseEnd_1618624 := by
    simpa [prefixWord, tailWord_1618624, baseEnd_1618624] using wordTrace_append hprefix tailTrace_1618624
  have hstable : (prefixWord ++ tailWord_1618624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618624).length < 2 ^ (prefixWord ++ tailWord_1618624).sum := by decide
  have hdescent : baseEnd_1618624 < baseStart_1618624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618656 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_1618656 : Nat := 118140960795 + 1618656 * 2 ^ 59
def prefixEnd_1618656 : Nat := 4983230072969 + 3 ^ 40 * 1618656 * 2
def baseEnd_1618656 : Nat := 554099028189416156437295

theorem tailTrace_1618656 : CollatzResearch.WordTrace tailWord_1618656 prefixEnd_1618656 554099028189416156437295 := by
  unfold tailWord_1618656
  simp only [CollatzResearch.WordTrace]
  refine ⟨29518617211946615640521911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39358156282595487520695881 29518617211946615640521911)
  ·
    refine ⟨44277925817919923460782867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29518617211946615640521911 44277925817919923460782867)
    ·
      refine ⟨66416888726879885191174301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44277925817919923460782867 66416888726879885191174301)
      ·
        refine ⟨24906333272579956946690363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66416888726879885191174301 24906333272579956946690363)
        ·
          refine ⟨37359499908869935420035545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24906333272579956946690363 37359499908869935420035545)
          ·
            refine ⟨28019624931652451565026659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37359499908869935420035545 28019624931652451565026659)
            ·
              refine ⟨42029437397478677347539989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28019624931652451565026659 42029437397478677347539989)
              ·
                refine ⟨1970129878006813000665937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42029437397478677347539989 1970129878006813000665937)
                ·
                  refine ⟨1477597408505109750499453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970129878006813000665937 1477597408505109750499453)
                  ·
                    refine ⟨554099028189416156437295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477597408505109750499453 554099028189416156437295)
                    ·
                      rfl

theorem cell22_1618656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_1618656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618656 prefixEnd_1618656 := by exact prefixLift 1618656
  have htrace : WordTrace (prefixWord ++ tailWord_1618656) baseStart_1618656 baseEnd_1618656 := by
    simpa [prefixWord, tailWord_1618656, baseEnd_1618656] using wordTrace_append hprefix tailTrace_1618656
  have hstable : (prefixWord ++ tailWord_1618656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618656).length < 2 ^ (prefixWord ++ tailWord_1618656).sum := by decide
  have hdescent : baseEnd_1618656 < baseStart_1618656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618686 : List Nat := [4, 2, 2, 1, 2, 1, 2, 8]
def baseStart_1618686 : Nat := 118140960795 + 1618686 * 2 ^ 59
def prefixEnd_1618686 : Nat := 4983230072969 + 3 ^ 40 * 1618686 * 2
def baseEnd_1618686 : Nat := 61567699755834008687467

theorem tailTrace_1618686 : CollatzResearch.WordTrace tailWord_1618686 prefixEnd_1618686 61567699755834008687467 := by
  unfold tailWord_1618686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7379791076723068300579489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39358885742523030936423941 7379791076723068300579489)
  ·
    refine ⟨5534843307542301225434617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7379791076723068300579489 5534843307542301225434617)
    ·
      refine ⟨4151132480656725919075963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5534843307542301225434617 4151132480656725919075963)
      ·
        refine ⟨6226698720985088878613945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4151132480656725919075963 6226698720985088878613945)
        ·
          refine ⟨4670024040738816658960459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6226698720985088878613945 4670024040738816658960459)
          ·
            refine ⟨7005036061108224988440689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670024040738816658960459 7005036061108224988440689)
            ·
              refine ⟨5253777045831168741330517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7005036061108224988440689 5253777045831168741330517)
              ·
                refine ⟨61567699755834008687467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5253777045831168741330517 61567699755834008687467)
                ·
                  rfl

theorem cell22_1618686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_1618686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618686 prefixEnd_1618686 := by exact prefixLift 1618686
  have htrace : WordTrace (prefixWord ++ tailWord_1618686) baseStart_1618686 baseEnd_1618686 := by
    simpa [prefixWord, tailWord_1618686, baseEnd_1618686] using wordTrace_append hprefix tailTrace_1618686
  have hstable : (prefixWord ++ tailWord_1618686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618686).length < 2 ^ (prefixWord ++ tailWord_1618686).sum := by decide
  have hdescent : baseEnd_1618686 < baseStart_1618686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618729 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_1618729 : Nat := 118140960795 + 1618729 * 2 ^ 59
def prefixEnd_1618729 : Nat := 4983230072969 + 3 ^ 40 * 1618729 * 2
def baseEnd_1618729 : Nat := 554124017581268299362071

theorem tailTrace_1618729 : CollatzResearch.WordTrace tailWord_1618729 prefixEnd_1618729 554124017581268299362071 := by
  unfold tailWord_1618729
  simp only [CollatzResearch.WordTrace]
  refine ⟨59039896952628764748451241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39359931301752509832300827 59039896952628764748451241)
  ·
    refine ⟨44279922714471573561338431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59039896952628764748451241 44279922714471573561338431)
    ·
      refine ⟨66419884071707360342007647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44279922714471573561338431 66419884071707360342007647)
      ·
        refine ⟨99629826107561040513011471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66419884071707360342007647 99629826107561040513011471)
        ·
          refine ⟨149444739161341560769517207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99629826107561040513011471 149444739161341560769517207)
          ·
            refine ⟨224167108742012341154275811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149444739161341560769517207 224167108742012341154275811)
            ·
              refine ⟨336250663113018511731413717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224167108742012341154275811 336250663113018511731413717)
              ·
                refine ⟨7880874916711371368705009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 336250663113018511731413717 7880874916711371368705009)
                ·
                  refine ⟨5910656187533528526528757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7880874916711371368705009 5910656187533528526528757)
                  ·
                    refine ⟨554124017581268299362071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5910656187533528526528757 554124017581268299362071)
                    ·
                      rfl

theorem cell22_1618729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_1618729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618729 prefixEnd_1618729 := by exact prefixLift 1618729
  have htrace : WordTrace (prefixWord ++ tailWord_1618729) baseStart_1618729 baseEnd_1618729 := by
    simpa [prefixWord, tailWord_1618729, baseEnd_1618729] using wordTrace_append hprefix tailTrace_1618729
  have hstable : (prefixWord ++ tailWord_1618729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618729).length < 2 ^ (prefixWord ++ tailWord_1618729).sum := by decide
  have hdescent : baseEnd_1618729 < baseStart_1618729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618759 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 10]
def baseStart_1618759 : Nat := 118140960795 + 1618759 * 2 ^ 59
def prefixEnd_1618759 : Nat := 4983230072969 + 3 ^ 40 * 1618759 * 2
def baseEnd_1618759 : Nat := 184711429064786073703993

theorem tailTrace_1618759 : CollatzResearch.WordTrace tailWord_1618759 prefixEnd_1618759 184711429064786073703993 := by
  unfold tailWord_1618759
  simp only [CollatzResearch.WordTrace]
  refine ⟨59040991142520079872043331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39360660761680053248028887 59040991142520079872043331)
  ·
    refine ⟨88561486713780119808064997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59040991142520079872043331 88561486713780119808064997)
    ·
      refine ⟨16605278758833772464012187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88561486713780119808064997 16605278758833772464012187)
      ·
        refine ⟨24907918138250658696018281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16605278758833772464012187 24907918138250658696018281)
        ·
          refine ⟨18680938603687994022013711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24907918138250658696018281 18680938603687994022013711)
          ·
            refine ⟨28021407905531991033020567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18680938603687994022013711 28021407905531991033020567)
            ·
              refine ⟨42032111858297986549530851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28021407905531991033020567 42032111858297986549530851)
              ·
                refine ⟨63048167787446979824296277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42032111858297986549530851 63048167787446979824296277)
                ·
                  refine ⟨184711429064786073703993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 63048167787446979824296277 184711429064786073703993)
                  ·
                    rfl

theorem cell22_1618759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_1618759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618759 prefixEnd_1618759 := by exact prefixLift 1618759
  have htrace : WordTrace (prefixWord ++ tailWord_1618759) baseStart_1618759 baseEnd_1618759 := by
    simpa [prefixWord, tailWord_1618759, baseEnd_1618759] using wordTrace_append hprefix tailTrace_1618759
  have hstable : (prefixWord ++ tailWord_1618759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618759).length < 2 ^ (prefixWord ++ tailWord_1618759).sum := by decide
  have hdescent : baseEnd_1618759 < baseStart_1618759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618821 : List Nat := [1, 3, 1, 1, 3, 5, 8]
def baseStart_1618821 : Nat := 118140960795 + 1618821 * 2 ^ 59
def prefixEnd_1618821 : Nat := 4983230072969 + 3 ^ 40 * 1618821 * 2
def baseEnd_1618821 : Nat := 20524278187459656520807

theorem tailTrace_1618821 : CollatzResearch.WordTrace tailWord_1618821 prefixEnd_1618821 20524278187459656520807 := by
  unfold tailWord_1618821
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043252468295464460800317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39362168312196976307200211 59043252468295464460800317)
  ·
    refine ⟨22141219675610799172800119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59043252468295464460800317 22141219675610799172800119)
    ·
      refine ⟨33211829513416198759200179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22141219675610799172800119 33211829513416198759200179)
      ·
        refine ⟨49817744270124298138800269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33211829513416198759200179 49817744270124298138800269)
        ·
          refine ⟨18681654101296611802050101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49817744270124298138800269 18681654101296611802050101)
          ·
            refine ⟨1751405071996557356442197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18681654101296611802050101 1751405071996557356442197)
            ·
              refine ⟨20524278187459656520807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1751405071996557356442197 20524278187459656520807)
              ·
                rfl

theorem cell22_1618821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 8].length) (baseStart_1618821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618821 prefixEnd_1618821 := by exact prefixLift 1618821
  have htrace : WordTrace (prefixWord ++ tailWord_1618821) baseStart_1618821 baseEnd_1618821 := by
    simpa [prefixWord, tailWord_1618821, baseEnd_1618821] using wordTrace_append hprefix tailTrace_1618821
  have hstable : (prefixWord ++ tailWord_1618821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618821).length < 2 ^ (prefixWord ++ tailWord_1618821).sum := by decide
  have hdescent : baseEnd_1618821 < baseStart_1618821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618823 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1618823 : Nat := 118140960795 + 1618823 * 2 ^ 59
def prefixEnd_1618823 : Nat := 4983230072969 + 3 ^ 40 * 1618823 * 2
def baseEnd_1618823 : Nat := 554156195702283387511783

theorem tailTrace_1618823 : CollatzResearch.WordTrace tailWord_1618823 prefixEnd_1618823 554156195702283387511783 := by
  unfold tailWord_1618823
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043325414288218802373123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39362216942858812534915415 59043325414288218802373123)
  ·
    refine ⟨88564988121432328203559685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59043325414288218802373123 88564988121432328203559685)
    ·
      refine ⟨16605935272768561538167441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88564988121432328203559685 16605935272768561538167441)
      ·
        refine ⟨12454451454576421153625581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605935272768561538167441 12454451454576421153625581)
        ·
          refine ⟨4670419295466157932609593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12454451454576421153625581 4670419295466157932609593)
          ·
            refine ⟨3502814471599618449457195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670419295466157932609593 3502814471599618449457195)
            ·
              refine ⟨5254221707399427674185793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3502814471599618449457195 5254221707399427674185793)
              ·
                refine ⟨3940666280549570755639345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254221707399427674185793 3940666280549570755639345)
                ·
                  refine ⟨2955499710412178066729509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940666280549570755639345 2955499710412178066729509)
                  ·
                    refine ⟨554156195702283387511783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2955499710412178066729509 554156195702283387511783)
                    ·
                      rfl

theorem cell22_1618823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1618823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618823 prefixEnd_1618823 := by exact prefixLift 1618823
  have htrace : WordTrace (prefixWord ++ tailWord_1618823) baseStart_1618823 baseEnd_1618823 := by
    simpa [prefixWord, tailWord_1618823, baseEnd_1618823] using wordTrace_append hprefix tailTrace_1618823
  have hstable : (prefixWord ++ tailWord_1618823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618823).length < 2 ^ (prefixWord ++ tailWord_1618823).sum := by decide
  have hdescent : baseEnd_1618823 < baseStart_1618823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618887 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 1, 3]
def baseStart_1618887 : Nat := 118140960795 + 1618887 * 2 ^ 59
def prefixEnd_1618887 : Nat := 4983230072969 + 3 ^ 40 * 1618887 * 2
def baseEnd_1618887 : Nat := 554178104210208553911587

theorem tailTrace_1618887 : CollatzResearch.WordTrace tailWord_1618887 prefixEnd_1618887 554178104210208553911587 := by
  unfold tailWord_1618887
  simp only [CollatzResearch.WordTrace]
  refine ⟨59045659686056357732702915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39363773124037571821801943 59045659686056357732702915)
  ·
    refine ⟨88568489529084536599054373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59045659686056357732702915 88568489529084536599054373)
    ·
      refine ⟨16606591786703350612322695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88568489529084536599054373 16606591786703350612322695)
      ·
        refine ⟨24909887680055025918484043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16606591786703350612322695 24909887680055025918484043)
        ·
          refine ⟨37364831520082538877726065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24909887680055025918484043 37364831520082538877726065)
          ·
            refine ⟨28023623640061904158294549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37364831520082538877726065 28023623640061904158294549)
            ·
              refine ⟨1313607358127901757420057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28023623640061904158294549 1313607358127901757420057)
              ·
                refine ⟨985205518595926318065043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1313607358127901757420057 985205518595926318065043)
                ·
                  refine ⟨1477808277893889477097565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985205518595926318065043 1477808277893889477097565)
                  ·
                    refine ⟨554178104210208553911587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1477808277893889477097565 554178104210208553911587)
                    ·
                      rfl

theorem cell22_1618887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_1618887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618887 prefixEnd_1618887 := by exact prefixLift 1618887
  have htrace : WordTrace (prefixWord ++ tailWord_1618887) baseStart_1618887 baseEnd_1618887 := by
    simpa [prefixWord, tailWord_1618887, baseEnd_1618887] using wordTrace_append hprefix tailTrace_1618887
  have hstable : (prefixWord ++ tailWord_1618887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618887).length < 2 ^ (prefixWord ++ tailWord_1618887).sum := by decide
  have hdescent : baseEnd_1618887 < baseStart_1618887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618898 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1618898 : Nat := 118140960795 + 1618898 * 2 ^ 59
def prefixEnd_1618898 : Nat := 4983230072969 + 3 ^ 40 * 1618898 * 2
def baseEnd_1618898 : Nat := 554181869735008191886553

theorem tailTrace_1618898 : CollatzResearch.WordTrace tailWord_1618898 prefixEnd_1618898 554181869735008191886553 := by
  unfold tailWord_1618898
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761515222254126652838337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39364040592677671074235565 14761515222254126652838337)
  ·
    refine ⟨11071136416690594989628753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14761515222254126652838337 11071136416690594989628753)
    ·
      refine ⟨8303352312517946242221565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11071136416690594989628753 8303352312517946242221565)
      ·
        refine ⟨3113757117194229840833087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8303352312517946242221565 3113757117194229840833087)
        ·
          refine ⟨4670635675791344761249631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113757117194229840833087 4670635675791344761249631)
          ·
            refine ⟨7005953513687017141874447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670635675791344761249631 7005953513687017141874447)
            ·
              refine ⟨10508930270530525712811671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005953513687017141874447 10508930270530525712811671)
              ·
                refine ⟨15763395405795788569217507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10508930270530525712811671 15763395405795788569217507)
                ·
                  refine ⟨23645093108693682853826261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15763395405795788569217507 23645093108693682853826261)
                  ·
                    refine ⟨554181869735008191886553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23645093108693682853826261 554181869735008191886553)
                    ·
                      rfl

theorem cell22_1618898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1618898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618898 prefixEnd_1618898 := by exact prefixLift 1618898
  have htrace : WordTrace (prefixWord ++ tailWord_1618898) baseStart_1618898 baseEnd_1618898 := by
    simpa [prefixWord, tailWord_1618898, baseEnd_1618898] using wordTrace_append hprefix tailTrace_1618898
  have hstable : (prefixWord ++ tailWord_1618898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618898).length < 2 ^ (prefixWord ++ tailWord_1618898).sum := by decide
  have hdescent : baseEnd_1618898 < baseStart_1618898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618913 : List Nat := [1, 2, 3, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1618913 : Nat := 118140960795 + 1618913 * 2 ^ 59
def prefixEnd_1618913 : Nat := 4983230072969 + 3 ^ 40 * 1618913 * 2
def baseEnd_1618913 : Nat := 554187004541553152761507

theorem tailTrace_1618913 : CollatzResearch.WordTrace tailWord_1618913 prefixEnd_1618913 554187004541553152761507 := by
  unfold tailWord_1618913
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046607983962164173149393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39364405322641442782099595 59046607983962164173149393)
  ·
    refine ⟨44284955987971623129862045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59046607983962164173149393 44284955987971623129862045)
    ·
      refine ⟨16606858495489358673698267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44284955987971623129862045 16606858495489358673698267)
      ·
        refine ⟨24910287743234038010547401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16606858495489358673698267 24910287743234038010547401)
        ·
          refine ⟨18682715807425528507910551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24910287743234038010547401 18682715807425528507910551)
          ·
            refine ⟨28024073711138292761865827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682715807425528507910551 28024073711138292761865827)
            ·
              refine ⟨42036110566707439142798741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28024073711138292761865827 42036110566707439142798741)
              ·
                refine ⟨1970442682814411209818691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42036110566707439142798741 1970442682814411209818691)
                ·
                  refine ⟨2955664024221616814728037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970442682814411209818691 2955664024221616814728037)
                  ·
                    refine ⟨554187004541553152761507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2955664024221616814728037 554187004541553152761507)
                    ·
                      rfl

theorem cell22_1618913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1618913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618913 prefixEnd_1618913 := by exact prefixLift 1618913
  have htrace : WordTrace (prefixWord ++ tailWord_1618913) baseStart_1618913 baseEnd_1618913 := by
    simpa [prefixWord, tailWord_1618913, baseEnd_1618913] using wordTrace_append hprefix tailTrace_1618913
  have hstable : (prefixWord ++ tailWord_1618913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618913).length < 2 ^ (prefixWord ++ tailWord_1618913).sum := by decide
  have hdescent : baseEnd_1618913 < baseStart_1618913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618945 : List Nat := [1, 2, 4, 1, 2, 2, 2, 4, 4]
def baseStart_1618945 : Nat := 118140960795 + 1618945 * 2 ^ 59
def prefixEnd_1618945 : Nat := 4983230072969 + 3 ^ 40 * 1618945 * 2
def baseEnd_1618945 : Nat := 184732652931838578653803

theorem tailTrace_1618945 : CollatzResearch.WordTrace tailWord_1618945 prefixEnd_1618945 184732652931838578653803 := by
  unfold tailWord_1618945
  simp only [CollatzResearch.WordTrace]
  refine ⟨59047775119846233638314289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39365183413230822425542859 59047775119846233638314289)
  ·
    refine ⟨44285831339884675228735717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59047775119846233638314289 44285831339884675228735717)
    ·
      refine ⟨8303593376228376605387947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44285831339884675228735717 8303593376228376605387947)
      ·
        refine ⟨12455390064342564908081921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303593376228376605387947 12455390064342564908081921)
        ·
          refine ⟨9341542548256923681061441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12455390064342564908081921 9341542548256923681061441)
          ·
            refine ⟨7006156911192692760796081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9341542548256923681061441 7006156911192692760796081)
            ·
              refine ⟨5254617683394519570597061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7006156911192692760796081 5254617683394519570597061)
              ·
                refine ⟨985240815636472419486949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5254617683394519570597061 985240815636472419486949)
                ·
                  refine ⟨184732652931838578653803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985240815636472419486949 184732652931838578653803)
                  ·
                    rfl

theorem cell22_1618945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 4].length) (baseStart_1618945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618945 prefixEnd_1618945 := by exact prefixLift 1618945
  have htrace : WordTrace (prefixWord ++ tailWord_1618945) baseStart_1618945 baseEnd_1618945 := by
    simpa [prefixWord, tailWord_1618945, baseEnd_1618945] using wordTrace_append hprefix tailTrace_1618945
  have hstable : (prefixWord ++ tailWord_1618945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618945).length < 2 ^ (prefixWord ++ tailWord_1618945).sum := by decide
  have hdescent : baseEnd_1618945 < baseStart_1618945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1618958 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1618958 : Nat := 118140960795 + 1618958 * 2 ^ 59
def prefixEnd_1618958 : Nat := 4983230072969 + 3 ^ 40 * 1618958 * 2
def baseEnd_1618958 : Nat := 554202408961188035386369

theorem tailTrace_1618958 : CollatzResearch.WordTrace tailWord_1618958 prefixEnd_1618958 554202408961188035386369 := by
  unfold tailWord_1618958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7381031158599892107317191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39365499512532757905691685 7381031158599892107317191)
  ·
    refine ⟨11071546737899838160975787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7381031158599892107317191 11071546737899838160975787)
    ·
      refine ⟨16607320106849757241463681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11071546737899838160975787 16607320106849757241463681)
      ·
        refine ⟨12455490080137317931097761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16607320106849757241463681 12455490080137317931097761)
        ·
          refine ⟨9341617560102988448323321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12455490080137317931097761 9341617560102988448323321)
          ·
            refine ⟨7006213170077241336242491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9341617560102988448323321 7006213170077241336242491)
            ·
              refine ⟨10509319755115862004363737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006213170077241336242491 10509319755115862004363737)
              ·
                refine ⟨7881989816336896503272803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10509319755115862004363737 7881989816336896503272803)
                ·
                  refine ⟨11822984724505344754909205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881989816336896503272803 11822984724505344754909205)
                  ·
                    refine ⟨554202408961188035386369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11822984724505344754909205 554202408961188035386369)
                    ·
                      rfl

theorem cell22_1618958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1618958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1618958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1618958 prefixEnd_1618958 := by exact prefixLift 1618958
  have htrace : WordTrace (prefixWord ++ tailWord_1618958) baseStart_1618958 baseEnd_1618958 := by
    simpa [prefixWord, tailWord_1618958, baseEnd_1618958] using wordTrace_append hprefix tailTrace_1618958
  have hstable : (prefixWord ++ tailWord_1618958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1618958).length < 2 ^ (prefixWord ++ tailWord_1618958).sum := by decide
  have hdescent : baseEnd_1618958 < baseStart_1618958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1618958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619063 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 6]
def baseStart_1619063 : Nat := 118140960795 + 1619063 * 2 ^ 59
def prefixEnd_1619063 : Nat := 4983230072969 + 3 ^ 40 * 1619063 * 2
def baseEnd_1619063 : Nat := 184746117535667587170349

theorem tailTrace_1619063 : CollatzResearch.WordTrace tailWord_1619063 prefixEnd_1619063 184746117535667587170349 := by
  unfold tailWord_1619063
  simp only [CollatzResearch.WordTrace]
  refine ⟨59052078933418739791109843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39368052622279159860739895 59052078933418739791109843)
  ·
    refine ⟨88578118400128109686664765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59052078933418739791109843 88578118400128109686664765)
    ·
      refine ⟨33216794400048041132499287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88578118400128109686664765 33216794400048041132499287)
      ·
        refine ⟨49825191600072061698748931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33216794400048041132499287 49825191600072061698748931)
        ·
          refine ⟨74737787400108092548123397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49825191600072061698748931 74737787400108092548123397)
          ·
            refine ⟨14013335137520267352773137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74737787400108092548123397 14013335137520267352773137)
            ·
              refine ⟨10510001353140200514579853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14013335137520267352773137 10510001353140200514579853)
              ·
                refine ⟨3941250507427575192967445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10510001353140200514579853 3941250507427575192967445)
                ·
                  refine ⟨184746117535667587170349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3941250507427575192967445 184746117535667587170349)
                  ·
                    rfl

theorem cell22_1619063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_1619063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619063 prefixEnd_1619063 := by exact prefixLift 1619063
  have htrace : WordTrace (prefixWord ++ tailWord_1619063) baseStart_1619063 baseEnd_1619063 := by
    simpa [prefixWord, tailWord_1619063, baseEnd_1619063] using wordTrace_append hprefix tailTrace_1619063
  have hstable : (prefixWord ++ tailWord_1619063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619063).length < 2 ^ (prefixWord ++ tailWord_1619063).sum := by decide
  have hdescent : baseEnd_1619063 < baseStart_1619063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619095 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1619095 : Nat := 118140960795 + 1619095 * 2 ^ 59
def prefixEnd_1619095 : Nat := 4983230072969 + 3 ^ 40 * 1619095 * 2
def baseEnd_1619095 : Nat := 554249306860965344710949

theorem tailTrace_1619095 : CollatzResearch.WordTrace tailWord_1619095 prefixEnd_1619095 554249306860965344710949 := by
  unfold tailWord_1619095
  simp only [CollatzResearch.WordTrace]
  refine ⟨59053246069302809256274739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39368830712868539504183159 59053246069302809256274739)
  ·
    refine ⟨88579869103954213884412109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59053246069302809256274739 88579869103954213884412109)
    ·
      refine ⟨33217450913982830206654541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88579869103954213884412109 33217450913982830206654541)
      ·
        refine ⟨12456544092743561327495453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33217450913982830206654541 12456544092743561327495453)
        ·
          refine ⟨4671204034778835497810795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12456544092743561327495453 4671204034778835497810795)
          ·
            refine ⟨7006806052168253246716193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671204034778835497810795 7006806052168253246716193)
            ·
              refine ⟨5255104539126189935037145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7006806052168253246716193 5255104539126189935037145)
              ·
                refine ⟨3941328404344642451277859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255104539126189935037145 3941328404344642451277859)
                ·
                  refine ⟨5911992606516963676916789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941328404344642451277859 5911992606516963676916789)
                  ·
                    refine ⟨554249306860965344710949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5911992606516963676916789 554249306860965344710949)
                    ·
                      rfl

theorem cell22_1619095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1619095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619095 prefixEnd_1619095 := by exact prefixLift 1619095
  have htrace : WordTrace (prefixWord ++ tailWord_1619095) baseStart_1619095 baseEnd_1619095 := by
    simpa [prefixWord, tailWord_1619095, baseEnd_1619095] using wordTrace_append hprefix tailTrace_1619095
  have hstable : (prefixWord ++ tailWord_1619095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619095).length < 2 ^ (prefixWord ++ tailWord_1619095).sum := by decide
  have hdescent : baseEnd_1619095 < baseStart_1619095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619114 : List Nat := [3, 1, 5, 1, 1, 1, 2, 4, 4]
def baseStart_1619114 : Nat := 118140960795 + 1619114 * 2 ^ 59
def prefixEnd_1619114 : Nat := 4983230072969 + 3 ^ 40 * 1619114 * 2
def baseEnd_1619114 : Nat := 184751936983085209495297

theorem tailTrace_1619114 : CollatzResearch.WordTrace tailWord_1619114 prefixEnd_1619114 184751936983085209495297 := by
  unfold tailWord_1619114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14763484764058493875304099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39369292704155983667477597 14763484764058493875304099)
  ·
    refine ⟨22145227146087740812956149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14763484764058493875304099 22145227146087740812956149)
    ·
      refine ⟨2076115044945725701214639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22145227146087740812956149 2076115044945725701214639)
      ·
        refine ⟨3114172567418588551821959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076115044945725701214639 3114172567418588551821959)
        ·
          refine ⟨4671258851127882827732939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114172567418588551821959 4671258851127882827732939)
          ·
            refine ⟨7006888276691824241599409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671258851127882827732939 7006888276691824241599409)
            ·
              refine ⟨5255166207518868181199557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7006888276691824241599409 5255166207518868181199557)
              ·
                refine ⟨985343663909787783974917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5255166207518868181199557 985343663909787783974917)
                ·
                  refine ⟨184751936983085209495297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985343663909787783974917 184751936983085209495297)
                  ·
                    rfl

theorem cell22_1619114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_1619114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619114 prefixEnd_1619114 := by exact prefixLift 1619114
  have htrace : WordTrace (prefixWord ++ tailWord_1619114) baseStart_1619114 baseEnd_1619114 := by
    simpa [prefixWord, tailWord_1619114, baseEnd_1619114] using wordTrace_append hprefix tailTrace_1619114
  have hstable : (prefixWord ++ tailWord_1619114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619114).length < 2 ^ (prefixWord ++ tailWord_1619114).sum := by decide
  have hdescent : baseEnd_1619114 < baseStart_1619114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619129 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 2, 3]
def baseStart_1619129 : Nat := 118140960795 + 1619129 * 2 ^ 59
def prefixEnd_1619129 : Nat := 4983230072969 + 3 ^ 40 * 1619129 * 2
def baseEnd_1619129 : Nat := 554260945755800589360845

theorem tailTrace_1619129 : CollatzResearch.WordTrace tailWord_1619129 prefixEnd_1619129 554260945755800589360845 := by
  unfold tailWord_1619129
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054486151179633063012441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39369657434119755375341627 59054486151179633063012441)
  ·
    refine ⟨44290864613384724797259331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59054486151179633063012441 44290864613384724797259331)
    ·
      refine ⟨66436296920077087195888997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44290864613384724797259331 66436296920077087195888997)
      ·
        refine ⟨12456805672514453849229187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66436296920077087195888997 12456805672514453849229187)
        ·
          refine ⟨18685208508771680773843781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456805672514453849229187 18685208508771680773843781)
          ·
            refine ⟨3503476595394690145095709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18685208508771680773843781 3503476595394690145095709)
            ·
              refine ⟨1313803723273008804410891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3503476595394690145095709 1313803723273008804410891)
              ·
                refine ⟨1970705584909513206616337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313803723273008804410891 1970705584909513206616337)
                ·
                  refine ⟨1478029188682134904962253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1970705584909513206616337 1478029188682134904962253)
                  ·
                    refine ⟨554260945755800589360845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478029188682134904962253 554260945755800589360845)
                    ·
                      rfl

theorem cell22_1619129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_1619129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619129 prefixEnd_1619129 := by exact prefixLift 1619129
  have htrace : WordTrace (prefixWord ++ tailWord_1619129) baseStart_1619129 baseEnd_1619129 := by
    simpa [prefixWord, tailWord_1619129, baseEnd_1619129] using wordTrace_append hprefix tailTrace_1619129
  have hstable : (prefixWord ++ tailWord_1619129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619129).length < 2 ^ (prefixWord ++ tailWord_1619129).sum := by decide
  have hdescent : baseEnd_1619129 < baseStart_1619129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619187 : List Nat := [1, 1, 1, 2, 2, 5, 4, 1, 5]
def baseStart_1619187 : Nat := 118140960795 + 1619187 * 2 ^ 59
def prefixEnd_1619187 : Nat := 4983230072969 + 3 ^ 40 * 1619187 * 2
def baseEnd_1619187 : Nat := 184760266780369257136889

theorem tailTrace_1619187 : CollatzResearch.WordTrace tailWord_1619187 prefixEnd_1619187 184760266780369257136889 := by
  unfold tailWord_1619187
  simp only [CollatzResearch.WordTrace]
  refine ⟨59056601584969508968623815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39371067723313005979082543 59056601584969508968623815)
  ·
    refine ⟨88584902377454263452935723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59056601584969508968623815 88584902377454263452935723)
    ·
      refine ⟨132877353566181395179403585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88584902377454263452935723 132877353566181395179403585)
      ·
        refine ⟨99658015174636046384552689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132877353566181395179403585 99658015174636046384552689)
        ·
          refine ⟨74743511380977034788414517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99658015174636046384552689 74743511380977034788414517)
          ·
            refine ⟨7007204191966597011413861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74743511380977034788414517 7007204191966597011413861)
            ·
              refine ⟨1313850785993736939640099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7007204191966597011413861 1313850785993736939640099)
              ·
                refine ⟨1970776178990605409460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313850785993736939640099 1970776178990605409460149)
                ·
                  refine ⟨184760266780369257136889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1970776178990605409460149 184760266780369257136889)
                  ·
                    rfl

theorem cell22_1619187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 4, 1, 5].length) (baseStart_1619187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619187 prefixEnd_1619187 := by exact prefixLift 1619187
  have htrace : WordTrace (prefixWord ++ tailWord_1619187) baseStart_1619187 baseEnd_1619187 := by
    simpa [prefixWord, tailWord_1619187, baseEnd_1619187] using wordTrace_append hprefix tailTrace_1619187
  have hstable : (prefixWord ++ tailWord_1619187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619187).length < 2 ^ (prefixWord ++ tailWord_1619187).sum := by decide
  have hdescent : baseEnd_1619187 < baseStart_1619187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619262 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1619262 : Nat := 118140960795 + 1619262 * 2 ^ 59
def prefixEnd_1619262 : Nat := 4983230072969 + 3 ^ 40 * 1619262 * 2
def baseEnd_1619262 : Nat := 554306474373832575785437

theorem tailTrace_1619262 : CollatzResearch.WordTrace tailWord_1619262 prefixEnd_1619262 554306474373832575785437 := by
  unfold tailWord_1619262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7382417132462224597200505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39372891373131864518402693 7382417132462224597200505)
  ·
    refine ⟨5536812849346668447900379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7382417132462224597200505 5536812849346668447900379)
    ·
      refine ⟨8305219274020002671850569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536812849346668447900379 8305219274020002671850569)
      ·
        refine ⟨6228914455515002003887927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8305219274020002671850569 6228914455515002003887927)
        ·
          refine ⟨9343371683272503005831891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228914455515002003887927 9343371683272503005831891)
          ·
            refine ⟨14015057524908754508747837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343371683272503005831891 14015057524908754508747837)
            ·
              refine ⟨5255646571840782940780439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14015057524908754508747837 5255646571840782940780439)
              ·
                refine ⟨7883469857761174411170659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255646571840782940780439 7883469857761174411170659)
                ·
                  refine ⟨11825204786641761616755989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883469857761174411170659 11825204786641761616755989)
                  ·
                    refine ⟨554306474373832575785437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11825204786641761616755989 554306474373832575785437)
                    ·
                      rfl

theorem cell22_1619262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1619262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619262 prefixEnd_1619262 := by exact prefixLift 1619262
  have htrace : WordTrace (prefixWord ++ tailWord_1619262) baseStart_1619262 baseEnd_1619262 := by
    simpa [prefixWord, tailWord_1619262, baseEnd_1619262] using wordTrace_append hprefix tailTrace_1619262
  have hstable : (prefixWord ++ tailWord_1619262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619262).length < 2 ^ (prefixWord ++ tailWord_1619262).sum := by decide
  have hdescent : baseEnd_1619262 < baseStart_1619262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619268 : List Nat := [2, 3, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1619268 : Nat := 118140960795 + 1619268 * 2 ^ 59
def prefixEnd_1619268 : Nat := 4983230072969 + 3 ^ 40 * 1619268 * 2
def baseEnd_1619268 : Nat := 554308528296450560135419

theorem tailTrace_1619268 : CollatzResearch.WordTrace tailWord_1619268 prefixEnd_1619268 554308528296450560135419 := by
  unfold tailWord_1619268
  simp only [CollatzResearch.WordTrace]
  refine ⟨29529777948838029901161229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39373037265117373201548305 29529777948838029901161229)
  ·
    refine ⟨11073666730814261212935461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29529777948838029901161229 11073666730814261212935461)
    ·
      refine ⟨2076312512027673977425399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11073666730814261212935461 2076312512027673977425399)
      ·
        refine ⟨3114468768041510966138099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076312512027673977425399 3114468768041510966138099)
        ·
          refine ⟨4671703152062266449207149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114468768041510966138099 4671703152062266449207149)
          ·
            refine ⟨1751888682023349918452681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4671703152062266449207149 1751888682023349918452681)
            ·
              refine ⟨1313916511517512438839511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751888682023349918452681 1313916511517512438839511)
              ·
                refine ⟨1970874767276268658259267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313916511517512438839511 1970874767276268658259267)
                ·
                  refine ⟨2956312150914402987388901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970874767276268658259267 2956312150914402987388901)
                  ·
                    refine ⟨554308528296450560135419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956312150914402987388901 554308528296450560135419)
                    ·
                      rfl

theorem cell22_1619268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1619268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619268 prefixEnd_1619268 := by exact prefixLift 1619268
  have htrace : WordTrace (prefixWord ++ tailWord_1619268) baseStart_1619268 baseEnd_1619268 := by
    simpa [prefixWord, tailWord_1619268, baseEnd_1619268] using wordTrace_append hprefix tailTrace_1619268
  have hstable : (prefixWord ++ tailWord_1619268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619268).length < 2 ^ (prefixWord ++ tailWord_1619268).sum := by decide
  have hdescent : baseEnd_1619268 < baseStart_1619268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619290 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_1619290 : Nat := 118140960795 + 1619290 * 2 ^ 59
def prefixEnd_1619290 : Nat := 4983230072969 + 3 ^ 40 * 1619290 * 2
def baseEnd_1619290 : Nat := 554316059346049836085351

theorem tailTrace_1619290 : CollatzResearch.WordTrace tailWord_1619290 prefixEnd_1619290 554316059346049836085351 := by
  unfold tailWord_1619290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765089575899089389905831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39373572202397571706415549 14765089575899089389905831)
  ·
    refine ⟨22147634363848634084858747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14765089575899089389905831 22147634363848634084858747)
    ·
      refine ⟨33221451545772951127288121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22147634363848634084858747 33221451545772951127288121)
      ·
        refine ⟨24916088659329713345466091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33221451545772951127288121 24916088659329713345466091)
        ·
          refine ⟨37374132988994570018199137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24916088659329713345466091 37374132988994570018199137)
          ·
            refine ⟨28030599741745927513649353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37374132988994570018199137 28030599741745927513649353)
            ·
              refine ⟨21022949806309445635237015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28030599741745927513649353 21022949806309445635237015)
              ·
                refine ⟨31534424709464168452855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21022949806309445635237015 31534424709464168452855523)
                ·
                  refine ⟨47301637064196252679283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31534424709464168452855523 47301637064196252679283285)
                  ·
                    refine ⟨554316059346049836085351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47301637064196252679283285 554316059346049836085351)
                    ·
                      rfl

theorem cell22_1619290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_1619290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619290 prefixEnd_1619290 := by exact prefixLift 1619290
  have htrace : WordTrace (prefixWord ++ tailWord_1619290) baseStart_1619290 baseEnd_1619290 := by
    simpa [prefixWord, tailWord_1619290, baseEnd_1619290] using wordTrace_append hprefix tailTrace_1619290
  have hstable : (prefixWord ++ tailWord_1619290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619290).length < 2 ^ (prefixWord ++ tailWord_1619290).sum := by decide
  have hdescent : baseEnd_1619290 < baseStart_1619290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619309 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1619309 : Nat := 118140960795 + 1619309 * 2 ^ 59
def prefixEnd_1619309 : Nat := 4983230072969 + 3 ^ 40 * 1619309 * 2
def baseEnd_1619309 : Nat := 554322563434340119860293

theorem tailTrace_1619309 : CollatzResearch.WordTrace tailWord_1619309 prefixEnd_1619309 554322563434340119860293 := by
  unfold tailWord_1619309
  simp only [CollatzResearch.WordTrace]
  refine ⟨59061051290527523804564981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39374034193685015869709987 59061051290527523804564981)
  ·
    refine ⟨5536973558486955356677967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59061051290527523804564981 5536973558486955356677967)
    ·
      refine ⟨8305460337730433035016951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536973558486955356677967 8305460337730433035016951)
      ·
        refine ⟨12458190506595649552525427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8305460337730433035016951 12458190506595649552525427)
        ·
          refine ⟨18687285759893474328788141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12458190506595649552525427 18687285759893474328788141)
          ·
            refine ⟨7007732159960052873295553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18687285759893474328788141 7007732159960052873295553)
            ·
              refine ⟨5255799119970039654971665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7007732159960052873295553 5255799119970039654971665)
              ·
                refine ⟨3941849339977529741228749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5255799119970039654971665 3941849339977529741228749)
                ·
                  refine ⟨1478193502491573652960781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3941849339977529741228749 1478193502491573652960781)
                  ·
                    refine ⟨554322563434340119860293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478193502491573652960781 554322563434340119860293)
                    ·
                      rfl

theorem cell22_1619309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1619309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619309 prefixEnd_1619309 := by exact prefixLift 1619309
  have htrace : WordTrace (prefixWord ++ tailWord_1619309) baseStart_1619309 baseEnd_1619309 := by
    simpa [prefixWord, tailWord_1619309, baseEnd_1619309] using wordTrace_append hprefix tailTrace_1619309
  have hstable : (prefixWord ++ tailWord_1619309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619309).length < 2 ^ (prefixWord ++ tailWord_1619309).sum := by decide
  have hdescent : baseEnd_1619309 < baseStart_1619309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619356 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 5]
def baseStart_1619356 : Nat := 118140960795 + 1619356 * 2 ^ 59
def prefixEnd_1619356 : Nat := 4983230072969 + 3 ^ 40 * 1619356 * 2
def baseEnd_1619356 : Nat := 184779550831615887978383

theorem tailTrace_1619356 : CollatzResearch.WordTrace tailWord_1619356 prefixEnd_1619356 184779550831615887978383 := by
  unfold tailWord_1619356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29531382760678625415762961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39375177014238167221017281 29531382760678625415762961)
  ·
    refine ⟨22148537070508969061822221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29531382760678625415762961 22148537070508969061822221)
    ·
      refine ⟨8305701401440863398183333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22148537070508969061822221 8305701401440863398183333)
      ·
        refine ⟨1557319012770161887159375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8305701401440863398183333 1557319012770161887159375)
        ·
          refine ⟨2335978519155242830739063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557319012770161887159375 2335978519155242830739063)
          ·
            refine ⟨3503967778732864246108595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335978519155242830739063 3503967778732864246108595)
            ·
              refine ⟨5255951668099296369162893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503967778732864246108595 5255951668099296369162893)
              ·
                refine ⟨1970981875537236138436085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5255951668099296369162893 1970981875537236138436085)
                ·
                  refine ⟨184779550831615887978383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1970981875537236138436085 184779550831615887978383)
                  ·
                    rfl

theorem cell22_1619356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 5].length) (baseStart_1619356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619356 prefixEnd_1619356 := by exact prefixLift 1619356
  have htrace : WordTrace (prefixWord ++ tailWord_1619356) baseStart_1619356 baseEnd_1619356 := by
    simpa [prefixWord, tailWord_1619356, baseEnd_1619356] using wordTrace_append hprefix tailTrace_1619356
  have hstable : (prefixWord ++ tailWord_1619356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619356).length < 2 ^ (prefixWord ++ tailWord_1619356).sum := by decide
  have hdescent : baseEnd_1619356 < baseStart_1619356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619367 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 8]
def baseStart_1619367 : Nat := 118140960795 + 1619367 * 2 ^ 59
def prefixEnd_1619367 : Nat := 4983230072969 + 3 ^ 40 * 1619367 * 2
def baseEnd_1619367 : Nat := 184780806006549100636705

theorem tailTrace_1619367 : CollatzResearch.WordTrace tailWord_1619367 prefixEnd_1619367 184780806006549100636705 := by
  unfold tailWord_1619367
  simp only [CollatzResearch.WordTrace]
  refine ⟨59063166724317399710176355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39375444482878266473450903 59063166724317399710176355)
  ·
    refine ⟨88594750086476099565264533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59063166724317399710176355 88594750086476099565264533)
    ·
      refine ⟨4152878910303567167121775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88594750086476099565264533 4152878910303567167121775)
      ·
        refine ⟨6229318365455350750682663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4152878910303567167121775 6229318365455350750682663)
        ·
          refine ⟨9343977548183026126023995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229318365455350750682663 9343977548183026126023995)
          ·
            refine ⟨14015966322274539189035993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9343977548183026126023995 14015966322274539189035993)
            ·
              refine ⟨10511974741705904391776995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14015966322274539189035993 10511974741705904391776995)
              ·
                refine ⟨15767962112558856587665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10511974741705904391776995 15767962112558856587665493)
                ·
                  refine ⟨184780806006549100636705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15767962112558856587665493 184780806006549100636705)
                  ·
                    rfl

theorem cell22_1619367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 8].length) (baseStart_1619367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619367 prefixEnd_1619367 := by exact prefixLift 1619367
  have htrace : WordTrace (prefixWord ++ tailWord_1619367) baseStart_1619367 baseEnd_1619367 := by
    simpa [prefixWord, tailWord_1619367, baseEnd_1619367] using wordTrace_append hprefix tailTrace_1619367
  have hstable : (prefixWord ++ tailWord_1619367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619367).length < 2 ^ (prefixWord ++ tailWord_1619367).sum := by decide
  have hdescent : baseEnd_1619367 < baseStart_1619367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619394 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1619394 : Nat := 118140960795 + 1619394 * 2 ^ 59
def prefixEnd_1619394 : Nat := 4983230072969 + 3 ^ 40 * 1619394 * 2
def baseEnd_1619394 : Nat := 554351660671428231485033

theorem tailTrace_1619394 : CollatzResearch.WordTrace tailWord_1619394 prefixEnd_1619394 554351660671428231485033 := by
  unfold tailWord_1619394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14766037873804895830352309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39376100996813055547606157 14766037873804895830352309)
  ·
    refine ⟨1384316050669208984095529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14766037873804895830352309 1384316050669208984095529)
    ·
      refine ⟨1038237038001906738071647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1384316050669208984095529 1038237038001906738071647)
      ·
        refine ⟨1557355557002860107107471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038237038001906738071647 1557355557002860107107471)
        ·
          refine ⟨2336033335504290160661207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557355557002860107107471 2336033335504290160661207)
          ·
            refine ⟨3504050003256435240991811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336033335504290160661207 3504050003256435240991811)
            ·
              refine ⟨5256075004884652861487717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504050003256435240991811 5256075004884652861487717)
              ·
                refine ⟨985514063415872411528947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5256075004884652861487717 985514063415872411528947)
                ·
                  refine ⟨1478271095123808617293421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985514063415872411528947 1478271095123808617293421)
                  ·
                    refine ⟨554351660671428231485033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478271095123808617293421 554351660671428231485033)
                    ·
                      rfl

theorem cell22_1619394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1619394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619394 prefixEnd_1619394 := by exact prefixLift 1619394
  have htrace : WordTrace (prefixWord ++ tailWord_1619394) baseStart_1619394 baseEnd_1619394 := by
    simpa [prefixWord, tailWord_1619394, baseEnd_1619394] using wordTrace_append hprefix tailTrace_1619394
  have hstable : (prefixWord ++ tailWord_1619394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619394).length < 2 ^ (prefixWord ++ tailWord_1619394).sum := by decide
  have hdescent : baseEnd_1619394 < baseStart_1619394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619431 : List Nat := [1, 1, 5, 2, 1, 4, 1, 1, 2, 4]
def baseStart_1619431 : Nat := 118140960795 + 1619431 * 2 ^ 59
def prefixEnd_1619431 : Nat := 4983230072969 + 3 ^ 40 * 1619431 * 2
def baseEnd_1619431 : Nat := 554364326527572468309919

theorem tailTrace_1619431 : CollatzResearch.WordTrace tailWord_1619431 prefixEnd_1619431 554364326527572468309919 := by
  unfold tailWord_1619431
  simp only [CollatzResearch.WordTrace]
  refine ⟨59065500996085538640506147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39377000664057025760337431 59065500996085538640506147)
  ·
    refine ⟨88598251494128307960759221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59065500996085538640506147 88598251494128307960759221)
    ·
      refine ⟨8306086077574528871321177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88598251494128307960759221 8306086077574528871321177)
      ·
        refine ⟨6229564558180896653490883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8306086077574528871321177 6229564558180896653490883)
        ·
          refine ⟨9344346837271344980236325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229564558180896653490883 9344346837271344980236325)
          ·
            refine ⟨1752065031988377183794311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9344346837271344980236325 1752065031988377183794311)
            ·
              refine ⟨2628097547982565775691467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752065031988377183794311 2628097547982565775691467)
              ·
                refine ⟨3942146321973848663537201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628097547982565775691467 3942146321973848663537201)
                ·
                  refine ⟨2956609741480386497652901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942146321973848663537201 2956609741480386497652901)
                  ·
                    refine ⟨554364326527572468309919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956609741480386497652901 554364326527572468309919)
                    ·
                      rfl

theorem cell22_1619431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_1619431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619431 prefixEnd_1619431 := by exact prefixLift 1619431
  have htrace : WordTrace (prefixWord ++ tailWord_1619431) baseStart_1619431 baseEnd_1619431 := by
    simpa [prefixWord, tailWord_1619431, baseEnd_1619431] using wordTrace_append hprefix tailTrace_1619431
  have hstable : (prefixWord ++ tailWord_1619431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619431).length < 2 ^ (prefixWord ++ tailWord_1619431).sum := by decide
  have hdescent : baseEnd_1619431 < baseStart_1619431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619519 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 6]
def baseStart_1619519 : Nat := 118140960795 + 1619519 * 2 ^ 59
def prefixEnd_1619519 : Nat := 4983230072969 + 3 ^ 40 * 1619519 * 2
def baseEnd_1619519 : Nat := 184798150241989857369883

theorem tailTrace_1619519 : CollatzResearch.WordTrace tailWord_1619519 prefixEnd_1619519 184798150241989857369883 := by
  unfold tailWord_1619519
  simp only [CollatzResearch.WordTrace]
  refine ⟨59068710619766729669709611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39379140413177819779806407 59068710619766729669709611)
  ·
    refine ⟨88603065929650094504564417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59068710619766729669709611 88603065929650094504564417)
    ·
      refine ⟨66452299447237570878423313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88603065929650094504564417 66452299447237570878423313)
      ·
        refine ⟨49839224585428178158817485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66452299447237570878423313 49839224585428178158817485)
        ·
          refine ⟨18689709219535566809556557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49839224585428178158817485 18689709219535566809556557)
          ·
            refine ⟨7008640957325837553583709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18689709219535566809556557 7008640957325837553583709)
            ·
              refine ⟨2628240358997189082593891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7008640957325837553583709 2628240358997189082593891)
              ·
                refine ⟨3942360538495783623890837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628240358997189082593891 3942360538495783623890837)
                ·
                  refine ⟨184798150241989857369883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3942360538495783623890837 184798150241989857369883)
                  ·
                    rfl

theorem cell22_1619519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 6].length) (baseStart_1619519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619519 prefixEnd_1619519 := by exact prefixLift 1619519
  have htrace : WordTrace (prefixWord ++ tailWord_1619519) baseStart_1619519 baseEnd_1619519 := by
    simpa [prefixWord, tailWord_1619519, baseEnd_1619519] using wordTrace_append hprefix tailTrace_1619519
  have hstable : (prefixWord ++ tailWord_1619519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619519).length < 2 ^ (prefixWord ++ tailWord_1619519).sum := by decide
  have hdescent : baseEnd_1619519 < baseStart_1619519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619534 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1619534 : Nat := 118140960795 + 1619534 * 2 ^ 59
def prefixEnd_1619534 : Nat := 4983230072969 + 3 ^ 40 * 1619534 * 2
def baseEnd_1619534 : Nat := 554399585532514532984603

theorem tailTrace_1619534 : CollatzResearch.WordTrace tailWord_1619534 prefixEnd_1619534 554399585532514532984603 := by
  unfold tailWord_1619534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383657214339048403938207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39379505143141591487670437 7383657214339048403938207)
  ·
    refine ⟨11075485821508572605907311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7383657214339048403938207 11075485821508572605907311)
    ·
      refine ⟨16613228732262858908860967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075485821508572605907311 16613228732262858908860967)
      ·
        refine ⟨24919843098394288363291451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16613228732262858908860967 24919843098394288363291451)
        ·
          refine ⟨37379764647591432544937177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24919843098394288363291451 37379764647591432544937177)
          ·
            refine ⟨28034823485693574408702883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37379764647591432544937177 28034823485693574408702883)
            ·
              refine ⟨42052235228540361613054325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28034823485693574408702883 42052235228540361613054325)
              ·
                refine ⟨3942397052675658901223843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42052235228540361613054325 3942397052675658901223843)
                ·
                  refine ⟨5913595579013488351835765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942397052675658901223843 5913595579013488351835765)
                  ·
                    refine ⟨554399585532514532984603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5913595579013488351835765 554399585532514532984603)
                    ·
                      rfl

theorem cell22_1619534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1619534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619534 prefixEnd_1619534 := by exact prefixLift 1619534
  have htrace : WordTrace (prefixWord ++ tailWord_1619534) baseStart_1619534 baseEnd_1619534 := by
    simpa [prefixWord, tailWord_1619534, baseEnd_1619534] using wordTrace_append hprefix tailTrace_1619534
  have hstable : (prefixWord ++ tailWord_1619534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619534).length < 2 ^ (prefixWord ++ tailWord_1619534).sum := by decide
  have hdescent : baseEnd_1619534 < baseStart_1619534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619538 : List Nat := [3, 2, 2, 1, 2, 4, 1, 2, 1, 4]
def baseStart_1619538 : Nat := 118140960795 + 1619538 * 2 ^ 59
def prefixEnd_1619538 : Nat := 4983230072969 + 3 ^ 40 * 1619538 * 2
def baseEnd_1619538 : Nat := 554400954814259855884591

theorem tailTrace_1619538 : CollatzResearch.WordTrace tailWord_1619538 prefixEnd_1619538 554400954814259855884591 := by
  unfold tailWord_1619538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767350901674473978662817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39379602404465263943100845 14767350901674473978662817)
  ·
    refine ⟨11075513176255855483997113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14767350901674473978662817 11075513176255855483997113)
    ·
      refine ⟨8306634882191891612997835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11075513176255855483997113 8306634882191891612997835)
      ·
        refine ⟨12459952323287837419496753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8306634882191891612997835 12459952323287837419496753)
        ·
          refine ⟨9344964242465878064622565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12459952323287837419496753 9344964242465878064622565)
          ·
            refine ⟨1752180795462352137116731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9344964242465878064622565 1752180795462352137116731)
            ·
              refine ⟨2628271193193528205675097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752180795462352137116731 2628271193193528205675097)
              ·
                refine ⟨1971203394895146154256323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628271193193528205675097 1971203394895146154256323)
                ·
                  refine ⟨2956805092342719231384485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971203394895146154256323 2956805092342719231384485)
                  ·
                    refine ⟨554400954814259855884591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2956805092342719231384485 554400954814259855884591)
                    ·
                      rfl

theorem cell22_1619538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_1619538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619538 prefixEnd_1619538 := by exact prefixLift 1619538
  have htrace : WordTrace (prefixWord ++ tailWord_1619538) baseStart_1619538 baseEnd_1619538 := by
    simpa [prefixWord, tailWord_1619538, baseEnd_1619538] using wordTrace_append hprefix tailTrace_1619538
  have hstable : (prefixWord ++ tailWord_1619538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619538).length < 2 ^ (prefixWord ++ tailWord_1619538).sum := by decide
  have hdescent : baseEnd_1619538 < baseStart_1619538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619568 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_1619568 : Nat := 118140960795 + 1619568 * 2 ^ 59
def prefixEnd_1619568 : Nat := 4983230072969 + 3 ^ 40 * 1619568 * 2
def baseEnd_1619568 : Nat := 554411224427349777634499

theorem tailTrace_1619568 : CollatzResearch.WordTrace tailWord_1619568 prefixEnd_1619568 554411224427349777634499 := by
  unfold tailWord_1619568
  simp only [CollatzResearch.WordTrace]
  refine ⟨29535248898294605519121679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39380331864392807358828905 29535248898294605519121679)
  ·
    refine ⟨44302873347441908278682519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29535248898294605519121679 44302873347441908278682519)
    ·
      refine ⟨66454310021162862418023779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44302873347441908278682519 66454310021162862418023779)
      ·
        refine ⟨99681465031744293627035669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66454310021162862418023779 99681465031744293627035669)
        ·
          refine ⟨4672568673363013763767297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99681465031744293627035669 4672568673363013763767297)
          ·
            refine ⟨3504426505022260322825473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672568673363013763767297 3504426505022260322825473)
            ·
              refine ⟨2628319878766695242119105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504426505022260322825473 2628319878766695242119105)
              ·
                refine ⟨1971239909075021431589329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628319878766695242119105 1971239909075021431589329)
                ·
                  refine ⟨1478429931806266073691997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971239909075021431589329 1478429931806266073691997)
                  ·
                    refine ⟨554411224427349777634499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478429931806266073691997 554411224427349777634499)
                    ·
                      rfl

theorem cell22_1619568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_1619568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619568 prefixEnd_1619568 := by exact prefixLift 1619568
  have htrace : WordTrace (prefixWord ++ tailWord_1619568) baseStart_1619568 baseEnd_1619568 := by
    simpa [prefixWord, tailWord_1619568, baseEnd_1619568] using wordTrace_append hprefix tailTrace_1619568
  have hstable : (prefixWord ++ tailWord_1619568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619568).length < 2 ^ (prefixWord ++ tailWord_1619568).sum := by decide
  have hdescent : baseEnd_1619568 < baseStart_1619568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619570 : List Nat := [3, 2, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1619570 : Nat := 118140960795 + 1619570 * 2 ^ 59
def prefixEnd_1619570 : Nat := 4983230072969 + 3 ^ 40 * 1619570 * 2
def baseEnd_1619570 : Nat := 184803969689407479694831

theorem tailTrace_1619570 : CollatzResearch.WordTrace tailWord_1619570 prefixEnd_1619570 184803969689407479694831 := by
  unfold tailWord_1619570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14767642685645491344954041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39380380495054643586544109 14767642685645491344954041)
  ·
    refine ⟨11075732014234118508715531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14767642685645491344954041 11075732014234118508715531)
    ·
      refine ⟨16613598021351177763073297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075732014234118508715531 16613598021351177763073297)
      ·
        refine ⟨12460198516013383322304973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16613598021351177763073297 12460198516013383322304973)
        ·
          refine ⟨4672574443505018745864365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12460198516013383322304973 4672574443505018745864365)
          ·
            refine ⟨1752215416314382029699137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672574443505018745864365 1752215416314382029699137)
            ·
              refine ⟨1314161562235786522274353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752215416314382029699137 1314161562235786522274353)
              ·
                refine ⟨985621171676839891705765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314161562235786522274353 985621171676839891705765)
                ·
                  refine ⟨184803969689407479694831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 985621171676839891705765 184803969689407479694831)
                  ·
                    rfl

theorem cell22_1619570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1619570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619570 prefixEnd_1619570 := by exact prefixLift 1619570
  have htrace : WordTrace (prefixWord ++ tailWord_1619570) baseStart_1619570 baseEnd_1619570 := by
    simpa [prefixWord, tailWord_1619570, baseEnd_1619570] using wordTrace_append hprefix tailTrace_1619570
  have hstable : (prefixWord ++ tailWord_1619570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619570).length < 2 ^ (prefixWord ++ tailWord_1619570).sum := by decide
  have hdescent : baseEnd_1619570 < baseStart_1619570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619581 : List Nat := [1, 4, 1, 1, 4, 3, 1, 7]
def baseStart_1619581 : Nat := 118140960795 + 1619581 * 2 ^ 59
def prefixEnd_1619581 : Nat := 4983230072969 + 3 ^ 40 * 1619581 * 2
def baseEnd_1619581 : Nat := 61601741621446897451051

theorem tailTrace_1619581 : CollatzResearch.WordTrace tailWord_1619581 prefixEnd_1619581 61601741621446897451051 := by
  unfold tailWord_1619581
  simp only [CollatzResearch.WordTrace]
  refine ⟨59070971945542114258466597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39380647963694742838977731 59070971945542114258466597)
  ·
    refine ⟨11075807239789146423462487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59070971945542114258466597 11075807239789146423462487)
    ·
      refine ⟨16613710859683719635193731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075807239789146423462487 16613710859683719635193731)
      ·
        refine ⟨24920566289525579452790597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16613710859683719635193731 24920566289525579452790597)
        ·
          refine ⟨4672606179286046147398237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24920566289525579452790597 4672606179286046147398237)
          ·
            refine ⟨1752227317232267305274339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672606179286046147398237 1752227317232267305274339)
            ·
              refine ⟨2628340975848400957911509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752227317232267305274339 2628340975848400957911509)
              ·
                refine ⟨61601741621446897451051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2628340975848400957911509 61601741621446897451051)
                ·
                  rfl

theorem cell22_1619581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 7].length) (baseStart_1619581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619581 prefixEnd_1619581 := by exact prefixLift 1619581
  have htrace : WordTrace (prefixWord ++ tailWord_1619581) baseStart_1619581 baseEnd_1619581 := by
    simpa [prefixWord, tailWord_1619581, baseEnd_1619581] using wordTrace_append hprefix tailTrace_1619581
  have hstable : (prefixWord ++ tailWord_1619581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619581).length < 2 ^ (prefixWord ++ tailWord_1619581).sum := by decide
  have hdescent : baseEnd_1619581 < baseStart_1619581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619596 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 3, 3]
def baseStart_1619596 : Nat := 118140960795 + 1619596 * 2 ^ 59
def prefixEnd_1619596 : Nat := 4983230072969 + 3 ^ 40 * 1619596 * 2
def baseEnd_1619596 : Nat := 554420809399567037934413

theorem tailTrace_1619596 : CollatzResearch.WordTrace tailWord_1619596 prefixEnd_1619596 554420809399567037934413 := by
  unfold tailWord_1619596
  simp only [CollatzResearch.WordTrace]
  refine ⟨29535759520243885910131321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39381012693658514546841761 29535759520243885910131321)
  ·
    refine ⟨22151819640182914432598491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29535759520243885910131321 22151819640182914432598491)
    ·
      refine ⟨33227729460274371648897737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22151819640182914432598491 33227729460274371648897737)
      ·
        refine ⟨24920797095205778736673303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33227729460274371648897737 24920797095205778736673303)
        ·
          refine ⟨37381195642808668105009955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24920797095205778736673303 37381195642808668105009955)
          ·
            refine ⟨56071793464213002157514933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37381195642808668105009955 56071793464213002157514933)
            ·
              refine ⟨5256730637269968952267025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56071793464213002157514933 5256730637269968952267025)
              ·
                refine ⟨3942547977952476714200269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256730637269968952267025 3942547977952476714200269)
                ·
                  refine ⟨1478455491732178767825101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942547977952476714200269 1478455491732178767825101)
                  ·
                    refine ⟨554420809399567037934413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478455491732178767825101 554420809399567037934413)
                    ·
                      rfl

theorem cell22_1619596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_1619596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619596 prefixEnd_1619596 := by exact prefixLift 1619596
  have htrace : WordTrace (prefixWord ++ tailWord_1619596) baseStart_1619596 baseEnd_1619596 := by
    simpa [prefixWord, tailWord_1619596, baseEnd_1619596] using wordTrace_append hprefix tailTrace_1619596
  have hstable : (prefixWord ++ tailWord_1619596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619596).length < 2 ^ (prefixWord ++ tailWord_1619596).sum := by decide
  have hdescent : baseEnd_1619596 < baseStart_1619596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619688 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_1619688 : Nat := 118140960795 + 1619688 * 2 ^ 59
def prefixEnd_1619688 : Nat := 4983230072969 + 3 ^ 40 * 1619688 * 2
def baseEnd_1619688 : Nat := 184817434293236488211377

theorem tailTrace_1619688 : CollatzResearch.WordTrace tailWord_1619688 prefixEnd_1619688 184817434293236488211377 := by
  unfold tailWord_1619688
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537437278077235766305859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39383249704102981021741145 29537437278077235766305859)
  ·
    refine ⟨44306155917115853649458789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29537437278077235766305859 44306155917115853649458789)
    ·
      refine ⟨8307404234459222559273523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44306155917115853649458789 8307404234459222559273523)
      ·
        refine ⟨12461106351688833838910285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307404234459222559273523 12461106351688833838910285)
        ·
          refine ⟨4672914881883312689591357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12461106351688833838910285 4672914881883312689591357)
          ·
            refine ⟨1752343080706242258596759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4672914881883312689591357 1752343080706242258596759)
            ·
              refine ⟨2628514621059363387895139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752343080706242258596759 2628514621059363387895139)
              ·
                refine ⟨3942771931589045081842709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628514621059363387895139 3942771931589045081842709)
                ·
                  refine ⟨184817434293236488211377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3942771931589045081842709 184817434293236488211377)
                  ·
                    rfl

theorem cell22_1619688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_1619688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619688 prefixEnd_1619688 := by exact prefixLift 1619688
  have htrace : WordTrace (prefixWord ++ tailWord_1619688) baseStart_1619688 baseEnd_1619688 := by
    simpa [prefixWord, tailWord_1619688, baseEnd_1619688] using wordTrace_append hprefix tailTrace_1619688
  have hstable : (prefixWord ++ tailWord_1619688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619688).length < 2 ^ (prefixWord ++ tailWord_1619688).sum := by decide
  have hdescent : baseEnd_1619688 < baseStart_1619688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619699 : List Nat := [1, 1, 1, 2, 2, 3, 3, 9]
def baseStart_1619699 : Nat := 118140960795 + 1619699 * 2 ^ 59
def prefixEnd_1619699 : Nat := 4983230072969 + 3 ^ 40 * 1619699 * 2
def baseEnd_1619699 : Nat := 61606229822723233623233

theorem tailTrace_1619699 : CollatzResearch.WordTrace tailWord_1619699 prefixEnd_1619699 61606229822723233623233 := by
  unfold tailWord_1619699
  simp only [CollatzResearch.WordTrace]
  refine ⟨59075275759114620411262151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39383517172743080274174767 59075275759114620411262151)
  ·
    refine ⟨88612913638671930616893227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59075275759114620411262151 88612913638671930616893227)
    ·
      refine ⟨132919370458007895925339841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88612913638671930616893227 132919370458007895925339841)
      ·
        refine ⟨99689527843505921944004881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132919370458007895925339841 99689527843505921944004881)
        ·
          refine ⟨74767145882629441458003661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99689527843505921944004881 74767145882629441458003661)
          ·
            refine ⟨28037679705986040546751373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74767145882629441458003661 28037679705986040546751373)
            ·
              refine ⟨10514129889744765205031765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28037679705986040546751373 10514129889744765205031765)
              ·
                refine ⟨61606229822723233623233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10514129889744765205031765 61606229822723233623233)
                ·
                  rfl

theorem cell22_1619699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 9].length) (baseStart_1619699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619699 prefixEnd_1619699 := by exact prefixLift 1619699
  have htrace : WordTrace (prefixWord ++ tailWord_1619699) baseStart_1619699 baseEnd_1619699 := by
    simpa [prefixWord, tailWord_1619699, baseEnd_1619699] using wordTrace_append hprefix tailTrace_1619699
  have hstable : (prefixWord ++ tailWord_1619699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619699).length < 2 ^ (prefixWord ++ tailWord_1619699).sum := by decide
  have hdescent : baseEnd_1619699 < baseStart_1619699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619716 : List Nat := [2, 3, 2, 2, 1, 2, 2, 8]
def baseStart_1619716 : Nat := 118140960795 + 1619716 * 2 ^ 59
def prefixEnd_1619716 : Nat := 4983230072969 + 3 ^ 40 * 1619716 * 2
def baseEnd_1619716 : Nat := 61606876427991858326005

theorem tailTrace_1619716 : CollatzResearch.WordTrace tailWord_1619716 prefixEnd_1619716 61606876427991858326005 := by
  unfold tailWord_1619716
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537947900026516157315501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39383930533368688209754001 29537947900026516157315501)
  ·
    refine ⟨11076730462509943558993313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29537947900026516157315501 11076730462509943558993313)
    ·
      refine ⟨8307547846882457669244985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11076730462509943558993313 8307547846882457669244985)
      ·
        refine ⟨6230660885161843251933739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8307547846882457669244985 6230660885161843251933739)
        ·
          refine ⟨9345991327742764877900609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6230660885161843251933739 9345991327742764877900609)
          ·
            refine ⟨7009493495807073658425457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9345991327742764877900609 7009493495807073658425457)
            ·
              refine ⟨5257120121855305243819093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7009493495807073658425457 5257120121855305243819093)
              ·
                refine ⟨61606876427991858326005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5257120121855305243819093 61606876427991858326005)
                ·
                  rfl

theorem cell22_1619716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 8].length) (baseStart_1619716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619716 prefixEnd_1619716 := by exact prefixLift 1619716
  have htrace : WordTrace (prefixWord ++ tailWord_1619716) baseStart_1619716 baseEnd_1619716 := by
    simpa [prefixWord, tailWord_1619716, baseEnd_1619716] using wordTrace_append hprefix tailTrace_1619716
  have hstable : (prefixWord ++ tailWord_1619716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619716).length < 2 ^ (prefixWord ++ tailWord_1619716).sum := by decide
  have hdescent : baseEnd_1619716 < baseStart_1619716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619731 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 7, 3]
def baseStart_1619731 : Nat := 118140960795 + 1619731 * 2 ^ 59
def prefixEnd_1619731 : Nat := 4983230072969 + 3 ^ 40 * 1619731 * 2
def baseEnd_1619731 : Nat := 554467022658471685808999

theorem tailTrace_1619731 : CollatzResearch.WordTrace tailWord_1619731 prefixEnd_1619731 554467022658471685808999 := by
  unfold tailWord_1619731
  simp only [CollatzResearch.WordTrace]
  refine ⟨59076442894998689876427047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39384295263332459917618031 59076442894998689876427047)
  ·
    refine ⟨88614664342498034814640571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59076442894998689876427047 88614664342498034814640571)
    ·
      refine ⟨132921996513747052221960857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88614664342498034814640571 132921996513747052221960857)
      ·
        refine ⟨99691497385310289166470643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132921996513747052221960857 99691497385310289166470643)
        ·
          refine ⟨149537246077965433749705965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99691497385310289166470643 149537246077965433749705965)
          ·
            refine ⟨56076467279237037656139737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149537246077965433749705965 56076467279237037656139737)
            ·
              refine ⟨42057350459427778242104803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56076467279237037656139737 42057350459427778242104803)
              ·
                refine ⟨63086025689141667363157205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42057350459427778242104803 63086025689141667363157205)
                ·
                  refine ⟨1478578727089257828823997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 63086025689141667363157205 1478578727089257828823997)
                  ·
                    refine ⟨554467022658471685808999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478578727089257828823997 554467022658471685808999)
                    ·
                      rfl

theorem cell22_1619731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 3].length) (baseStart_1619731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619731 prefixEnd_1619731 := by exact prefixLift 1619731
  have htrace : WordTrace (prefixWord ++ tailWord_1619731) baseStart_1619731 baseEnd_1619731 := by
    simpa [prefixWord, tailWord_1619731, baseEnd_1619731] using wordTrace_append hprefix tailTrace_1619731
  have hstable : (prefixWord ++ tailWord_1619731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619731).length < 2 ^ (prefixWord ++ tailWord_1619731).sum := by decide
  have hdescent : baseEnd_1619731 < baseStart_1619731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619746 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1619746 : Nat := 118140960795 + 1619746 * 2 ^ 59
def prefixEnd_1619746 : Nat := 4983230072969 + 3 ^ 40 * 1619746 * 2
def baseEnd_1619746 : Nat := 554472157465016646683953

theorem tailTrace_1619746 : CollatzResearch.WordTrace tailWord_1619746 prefixEnd_1619746 554472157465016646683953 := by
  unfold tailWord_1619746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14769247497486086859555773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39384659993296231625482061 14769247497486086859555773)
  ·
    refine ⟨5538467811557282572333415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14769247497486086859555773 5538467811557282572333415)
    ·
      refine ⟨8307701717335923858500123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5538467811557282572333415 8307701717335923858500123)
      ·
        refine ⟨12461552576003885787750185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307701717335923858500123 12461552576003885787750185)
        ·
          refine ⟨9346164432002914340812639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12461552576003885787750185 9346164432002914340812639)
          ·
            refine ⟨14019246648004371511218959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346164432002914340812639 14019246648004371511218959)
            ·
              refine ⟨21028869972006557266828439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14019246648004371511218959 21028869972006557266828439)
              ·
                refine ⟨31543304958009835900242659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21028869972006557266828439 31543304958009835900242659)
                ·
                  refine ⟨47314957437014753850363989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31543304958009835900242659 47314957437014753850363989)
                  ·
                    refine ⟨554472157465016646683953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47314957437014753850363989 554472157465016646683953)
                    ·
                      rfl

theorem cell22_1619746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1619746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619746 prefixEnd_1619746 := by exact prefixLift 1619746
  have htrace : WordTrace (prefixWord ++ tailWord_1619746) baseStart_1619746 baseEnd_1619746 := by
    simpa [prefixWord, tailWord_1619746, baseEnd_1619746] using wordTrace_append hprefix tailTrace_1619746
  have hstable : (prefixWord ++ tailWord_1619746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619746).length < 2 ^ (prefixWord ++ tailWord_1619746).sum := by decide
  have hdescent : baseEnd_1619746 < baseStart_1619746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619765 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 3, 3]
def baseStart_1619765 : Nat := 118140960795 + 1619765 * 2 ^ 59
def prefixEnd_1619765 : Nat := 4983230072969 + 3 ^ 40 * 1619765 * 2
def baseEnd_1619765 : Nat := 554478661553306930458895

theorem tailTrace_1619765 : CollatzResearch.WordTrace tailWord_1619765 prefixEnd_1619765 554478661553306930458895 := by
  unfold tailWord_1619765
  simp only [CollatzResearch.WordTrace]
  refine ⟨59077682976875513683164749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39385121984583675788776499 59077682976875513683164749)
  ·
    refine ⟨22154131116328317631186781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59077682976875513683164749 22154131116328317631186781)
    ·
      refine ⟨8307799168623119111695043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22154131116328317631186781 8307799168623119111695043)
      ·
        refine ⟨12461698752934678667542565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8307799168623119111695043 12461698752934678667542565)
        ·
          refine ⟨2336568516175252250164231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12461698752934678667542565 2336568516175252250164231)
          ·
            refine ⟨3504852774262878375246347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336568516175252250164231 3504852774262878375246347)
            ·
              refine ⟨5257279161394317562869521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504852774262878375246347 5257279161394317562869521)
              ·
                refine ⟨3942959371045738172152141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257279161394317562869521 3942959371045738172152141)
                ·
                  refine ⟨1478609764142151814557053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3942959371045738172152141 1478609764142151814557053)
                  ·
                    refine ⟨554478661553306930458895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478609764142151814557053 554478661553306930458895)
                    ·
                      rfl

theorem cell22_1619765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_1619765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619765 prefixEnd_1619765 := by exact prefixLift 1619765
  have htrace : WordTrace (prefixWord ++ tailWord_1619765) baseStart_1619765 baseEnd_1619765 := by
    simpa [prefixWord, tailWord_1619765, baseEnd_1619765] using wordTrace_append hprefix tailTrace_1619765
  have hstable : (prefixWord ++ tailWord_1619765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619765).length < 2 ^ (prefixWord ++ tailWord_1619765).sum := by decide
  have hdescent : baseEnd_1619765 < baseStart_1619765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619868 : List Nat := [2, 2, 3, 3, 1, 1, 1, 9]
def baseStart_1619868 : Nat := 118140960795 + 1619868 * 2 ^ 59
def prefixEnd_1619868 : Nat := 4983230072969 + 3 ^ 40 * 1619868 * 2
def baseEnd_1619868 : Nat := 61612657839805443903731

theorem tailTrace_1619868 : CollatzResearch.WordTrace tailWord_1619868 prefixEnd_1619868 61612657839805443903731 := by
  unfold tailWord_1619868
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540719847751181137082129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39387626463668241516109505 29540719847751181137082129)
  ·
    refine ⟨22155539885813385852811597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29540719847751181137082129 22155539885813385852811597)
    ·
      refine ⟨8308327457180019694804349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22155539885813385852811597 8308327457180019694804349)
      ·
        refine ⟨3115622796442507385551631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8308327457180019694804349 3115622796442507385551631)
        ·
          refine ⟨4673434194663761078327447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115622796442507385551631 4673434194663761078327447)
          ·
            refine ⟨7010151291995641617491171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673434194663761078327447 7010151291995641617491171)
            ·
              refine ⟨10515226937993462426236757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010151291995641617491171 10515226937993462426236757)
              ·
                refine ⟨61612657839805443903731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10515226937993462426236757 61612657839805443903731)
                ·
                  rfl

theorem cell22_1619868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_1619868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619868 prefixEnd_1619868 := by exact prefixLift 1619868
  have htrace : WordTrace (prefixWord ++ tailWord_1619868) baseStart_1619868 baseEnd_1619868 := by
    simpa [prefixWord, tailWord_1619868, baseEnd_1619868] using wordTrace_append hprefix tailTrace_1619868
  have hstable : (prefixWord ++ tailWord_1619868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619868).length < 2 ^ (prefixWord ++ tailWord_1619868).sum := by decide
  have hdescent : baseEnd_1619868 < baseStart_1619868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619881 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1619881 : Nat := 118140960795 + 1619881 * 2 ^ 59
def prefixEnd_1619881 : Nat := 4983230072969 + 3 ^ 40 * 1619881 * 2
def baseEnd_1619881 : Nat := 554518370723921294558539

theorem tailTrace_1619881 : CollatzResearch.WordTrace tailWord_1619881 prefixEnd_1619881 554518370723921294558539 := by
  unfold tailWord_1619881
  simp only [CollatzResearch.WordTrace]
  refine ⟨59081913844455265494387497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39387942562970176996258331 59081913844455265494387497)
  ·
    refine ⟨44311435383341449120790623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59081913844455265494387497 44311435383341449120790623)
    ·
      refine ⟨66467153075012173681185935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44311435383341449120790623 66467153075012173681185935)
      ·
        refine ⟨99700729612518260521778903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66467153075012173681185935 99700729612518260521778903)
        ·
          refine ⟨149551094418777390782668355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99700729612518260521778903 149551094418777390782668355)
          ·
            refine ⟨224326641628166086174002533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149551094418777390782668355 224326641628166086174002533)
            ·
              refine ⟨42061245305281141157625475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224326641628166086174002533 42061245305281141157625475)
              ·
                refine ⟨63091867957921711736438213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42061245305281141157625475 63091867957921711736438213)
                ·
                  refine ⟨11829725242110320950582165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63091867957921711736438213 11829725242110320950582165)
                  ·
                    refine ⟨554518370723921294558539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11829725242110320950582165 554518370723921294558539)
                    ·
                      rfl

theorem cell22_1619881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1619881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619881 prefixEnd_1619881 := by exact prefixLift 1619881
  have htrace : WordTrace (prefixWord ++ tailWord_1619881) baseStart_1619881 baseEnd_1619881 := by
    simpa [prefixWord, tailWord_1619881, baseEnd_1619881] using wordTrace_append hprefix tailTrace_1619881
  have hstable : (prefixWord ++ tailWord_1619881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619881).length < 2 ^ (prefixWord ++ tailWord_1619881).sum := by decide
  have hdescent : baseEnd_1619881 < baseStart_1619881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619928 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_1619928 : Nat := 118140960795 + 1619928 * 2 ^ 59
def prefixEnd_1619928 : Nat := 4983230072969 + 3 ^ 40 * 1619928 * 2
def baseEnd_1619928 : Nat := 554534459784428838633395

theorem tailTrace_1619928 : CollatzResearch.WordTrace tailWord_1619928 prefixEnd_1619928 554534459784428838633395 := by
  unfold tailWord_1619928
  simp only [CollatzResearch.WordTrace]
  refine ⟨29541814037642496260674219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39389085383523328347565625 29541814037642496260674219)
  ·
    refine ⟨44312721056463744391011329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29541814037642496260674219 44312721056463744391011329)
    ·
      refine ⟨33234540792347808293258497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44312721056463744391011329 33234540792347808293258497)
      ·
        refine ⟨24925905594260856219943873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33234540792347808293258497 24925905594260856219943873)
        ·
          refine ⟨18694429195695642164957905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24925905594260856219943873 18694429195695642164957905)
          ·
            refine ⟨14020821896771731623718429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18694429195695642164957905 14020821896771731623718429)
            ·
              refine ⟨5257808211289399358894411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14020821896771731623718429 5257808211289399358894411)
              ·
                refine ⟨7886712316934099038341617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257808211289399358894411 7886712316934099038341617)
                ·
                  refine ⟨5915034237700574278756213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7886712316934099038341617 5915034237700574278756213)
                  ·
                    refine ⟨554534459784428838633395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5915034237700574278756213 554534459784428838633395)
                    ·
                      rfl

theorem cell22_1619928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_1619928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619928 prefixEnd_1619928 := by exact prefixLift 1619928
  have htrace : WordTrace (prefixWord ++ tailWord_1619928) baseStart_1619928 baseEnd_1619928 := by
    simpa [prefixWord, tailWord_1619928, baseEnd_1619928] using wordTrace_append hprefix tailTrace_1619928
  have hstable : (prefixWord ++ tailWord_1619928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619928).length < 2 ^ (prefixWord ++ tailWord_1619928).sum := by decide
  have hdescent : baseEnd_1619928 < baseStart_1619928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1619975 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 6]
def baseStart_1619975 : Nat := 118140960795 + 1619975 * 2 ^ 59
def prefixEnd_1619975 : Nat := 4983230072969 + 3 ^ 40 * 1619975 * 2
def baseEnd_1619975 : Nat := 184850182948312127569417

theorem tailTrace_1619975 : CollatzResearch.WordTrace tailWord_1619975 prefixEnd_1619975 184850182948312127569417 := by
  unfold tailWord_1619975
  simp only [CollatzResearch.WordTrace]
  refine ⟨59085342306114719548309379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39390228204076479698872919 59085342306114719548309379)
  ·
    refine ⟨88628013459172079322464069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59085342306114719548309379 88628013459172079322464069)
    ·
      refine ⟨16617752523594764872962013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88628013459172079322464069 16617752523594764872962013)
      ·
        refine ⟨6231657196348036827360755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16617752523594764872962013 6231657196348036827360755)
        ·
          refine ⟨9347485794522055241041133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231657196348036827360755 9347485794522055241041133)
          ·
            refine ⟨3505307172945770715390425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9347485794522055241041133 3505307172945770715390425)
            ·
              refine ⟨2628980379709328036542819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505307172945770715390425 2628980379709328036542819)
              ·
                refine ⟨3943470569563992054814229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628980379709328036542819 3943470569563992054814229)
                ·
                  refine ⟨184850182948312127569417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3943470569563992054814229 184850182948312127569417)
                  ·
                    rfl

theorem cell22_1619975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 6].length) (baseStart_1619975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1619975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1619975 prefixEnd_1619975 := by exact prefixLift 1619975
  have htrace : WordTrace (prefixWord ++ tailWord_1619975) baseStart_1619975 baseEnd_1619975 := by
    simpa [prefixWord, tailWord_1619975, baseEnd_1619975] using wordTrace_append hprefix tailTrace_1619975
  have hstable : (prefixWord ++ tailWord_1619975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1619975).length < 2 ^ (prefixWord ++ tailWord_1619975).sum := by decide
  have hdescent : baseEnd_1619975 < baseStart_1619975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1619975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620003 : List Nat := [1, 1, 1, 4, 3, 1, 3, 8]
def baseStart_1620003 : Nat := 118140960795 + 1620003 * 2 ^ 59
def prefixEnd_1620003 : Nat := 4983230072969 + 3 ^ 40 * 1620003 * 2
def baseEnd_1620003 : Nat := 61617792646350404778685

theorem tailTrace_1620003 : CollatzResearch.WordTrace tailWord_1620003 prefixEnd_1620003 61617792646350404778685 := by
  unfold tailWord_1620003
  simp only [CollatzResearch.WordTrace]
  refine ⟨59086363550013280330328663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39390909033342186886885775 59086363550013280330328663)
  ·
    refine ⟨88629545325019920495492995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59086363550013280330328663 88629545325019920495492995)
    ·
      refine ⟨132944317987529880743239493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88629545325019920495492995 132944317987529880743239493)
      ·
        refine ⟨24927059622661852639357405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132944317987529880743239493 24927059622661852639357405)
        ·
          refine ⟨9347647358498194739759027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24927059622661852639357405 9347647358498194739759027)
          ·
            refine ⟨14021471037747292109638541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347647358498194739759027 14021471037747292109638541)
            ·
              refine ⟨5258051639155234541114453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14021471037747292109638541 5258051639155234541114453)
              ·
                refine ⟨61617792646350404778685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5258051639155234541114453 61617792646350404778685)
                ·
                  rfl

theorem cell22_1620003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 8].length) (baseStart_1620003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620003 prefixEnd_1620003 := by exact prefixLift 1620003
  have htrace : WordTrace (prefixWord ++ tailWord_1620003) baseStart_1620003 baseEnd_1620003 := by
    simpa [prefixWord, tailWord_1620003, baseEnd_1620003] using wordTrace_append hprefix tailTrace_1620003
  have hstable : (prefixWord ++ tailWord_1620003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620003).length < 2 ^ (prefixWord ++ tailWord_1620003).sum := by decide
  have hdescent : baseEnd_1620003 < baseStart_1620003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620022 : List Nat := [5, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1620022 : Nat := 118140960795 + 1620022 * 2 ^ 59
def prefixEnd_1620022 : Nat := 4983230072969 + 3 ^ 40 * 1620022 * 2
def baseEnd_1620022 : Nat := 554566637905443926783107

theorem tailTrace_1620022 : CollatzResearch.WordTrace tailWord_1620022 prefixEnd_1620022 554566637905443926783107 := by
  unfold tailWord_1620022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692941033559027910954395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39391371024629631050180213 3692941033559027910954395)
  ·
    refine ⟨5539411550338541866431593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3692941033559027910954395 5539411550338541866431593)
    ·
      refine ⟨4154558662753906399823695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5539411550338541866431593 4154558662753906399823695)
      ·
        refine ⟨6231837994130859599735543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154558662753906399823695 6231837994130859599735543)
        ·
          refine ⟨9347756991196289399603315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231837994130859599735543 9347756991196289399603315)
          ·
            refine ⟨14021635486794434099404973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9347756991196289399603315 14021635486794434099404973)
            ·
              refine ⟨5258113307547912787276865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14021635486794434099404973 5258113307547912787276865)
              ·
                refine ⟨3943584980660934590457649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258113307547912787276865 3943584980660934590457649)
                ·
                  refine ⟨2957688735495700942843237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3943584980660934590457649 2957688735495700942843237)
                  ·
                    refine ⟨554566637905443926783107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2957688735495700942843237 554566637905443926783107)
                    ·
                      rfl

theorem cell22_1620022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1620022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620022 prefixEnd_1620022 := by exact prefixLift 1620022
  have htrace : WordTrace (prefixWord ++ tailWord_1620022) baseStart_1620022 baseEnd_1620022 := by
    simpa [prefixWord, tailWord_1620022, baseEnd_1620022] using wordTrace_append hprefix tailTrace_1620022
  have hstable : (prefixWord ++ tailWord_1620022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620022).length < 2 ^ (prefixWord ++ tailWord_1620022).sum := by decide
  have hdescent : baseEnd_1620022 < baseStart_1620022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620035 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 3, 3]
def baseStart_1620035 : Nat := 118140960795 + 1620035 * 2 ^ 59
def prefixEnd_1620035 : Nat := 4983230072969 + 3 ^ 40 * 1620035 * 2
def baseEnd_1620035 : Nat := 554571088071116226208067

theorem tailTrace_1620035 : CollatzResearch.WordTrace tailWord_1620035 prefixEnd_1620035 554571088071116226208067 := by
  unfold tailWord_1620035
  simp only [CollatzResearch.WordTrace]
  refine ⟨59087530685897349795493559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39391687123931566530329039 59087530685897349795493559)
  ·
    refine ⟨88631296028846024693240339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59087530685897349795493559 88631296028846024693240339)
    ·
      refine ⟨132946944043269037039860509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88631296028846024693240339 132946944043269037039860509)
      ·
        refine ⟨49855104016225888889947691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132946944043269037039860509 49855104016225888889947691)
        ·
          refine ⟨74782656024338833334921537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49855104016225888889947691 74782656024338833334921537)
          ·
            refine ⟨56086992018254125001191153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74782656024338833334921537 56086992018254125001191153)
            ·
              refine ⟨42065244013690593750893365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56086992018254125001191153 42065244013690593750893365)
              ·
                refine ⟨3943616626283493164146253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42065244013690593750893365 3943616626283493164146253)
                ·
                  refine ⟨1478856234856309936554845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3943616626283493164146253 1478856234856309936554845)
                  ·
                    refine ⟨554571088071116226208067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478856234856309936554845 554571088071116226208067)
                    ·
                      rfl

theorem cell22_1620035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 3].length) (baseStart_1620035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620035 prefixEnd_1620035 := by exact prefixLift 1620035
  have htrace : WordTrace (prefixWord ++ tailWord_1620035) baseStart_1620035 baseEnd_1620035 := by
    simpa [prefixWord, tailWord_1620035, baseEnd_1620035] using wordTrace_append hprefix tailTrace_1620035
  have hstable : (prefixWord ++ tailWord_1620035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620035).length < 2 ^ (prefixWord ++ tailWord_1620035).sum := by decide
  have hdescent : baseEnd_1620035 < baseStart_1620035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620063 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 3, 7]
def baseStart_1620063 : Nat := 118140960795 + 1620063 * 2 ^ 59
def prefixEnd_1620063 : Nat := 4983230072969 + 3 ^ 40 * 1620063 * 2
def baseEnd_1620063 : Nat := 554580673043333486507981

theorem tailTrace_1620063 : CollatzResearch.WordTrace tailWord_1620063 prefixEnd_1620063 554580673043333486507981 := by
  unfold tailWord_1620063
  simp only [CollatzResearch.WordTrace]
  refine ⟨59088551929795910577512843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39392367953197273718341895 59088551929795910577512843)
  ·
    refine ⟨88632827894693865866269265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59088551929795910577512843 88632827894693865866269265)
    ·
      refine ⟨66474620921020399399701949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88632827894693865866269265 66474620921020399399701949)
      ·
        refine ⟨24927982845382649774888231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66474620921020399399701949 24927982845382649774888231)
        ·
          refine ⟨37391974268073974662332347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24927982845382649774888231 37391974268073974662332347)
          ·
            refine ⟨56087961402110961993498521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37391974268073974662332347 56087961402110961993498521)
            ·
              refine ⟨42065971051583221495123891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56087961402110961993498521 42065971051583221495123891)
              ·
                refine ⟨63098956577374832242685837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42065971051583221495123891 63098956577374832242685837)
                ·
                  refine ⟨23662108716515562091007189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63098956577374832242685837 23662108716515562091007189)
                  ·
                    refine ⟨554580673043333486507981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23662108716515562091007189 554580673043333486507981)
                    ·
                      rfl

theorem cell22_1620063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 7].length) (baseStart_1620063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620063 prefixEnd_1620063 := by exact prefixLift 1620063
  have htrace : WordTrace (prefixWord ++ tailWord_1620063) baseStart_1620063 baseEnd_1620063 := by
    simpa [prefixWord, tailWord_1620063, baseEnd_1620063] using wordTrace_append hprefix tailTrace_1620063
  have hstable : (prefixWord ++ tailWord_1620063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620063).length < 2 ^ (prefixWord ++ tailWord_1620063).sum := by decide
  have hdescent : baseEnd_1620063 < baseStart_1620063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620082 : List Nat := [3, 2, 1, 2, 2, 3, 2, 2, 5]
def baseStart_1620082 : Nat := 118140960795 + 1620082 * 2 ^ 59
def prefixEnd_1620082 : Nat := 4983230072969 + 3 ^ 40 * 1620082 * 2
def baseEnd_1620082 : Nat := 184862392377207923427641

theorem tailTrace_1620082 : CollatzResearch.WordTrace tailWord_1620082 prefixEnd_1620082 184862392377207923427641 := by
  unfold tailWord_1620082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14772311229181769205613625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39392829944484717881636333 14772311229181769205613625)
  ·
    refine ⟨11079233421886326904210219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14772311229181769205613625 11079233421886326904210219)
    ·
      refine ⟨16618850132829490356315329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11079233421886326904210219 16618850132829490356315329)
      ·
        refine ⟨12464137599622117767236497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16618850132829490356315329 12464137599622117767236497)
        ·
          refine ⟨9348103199716588325427373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12464137599622117767236497 9348103199716588325427373)
          ·
            refine ⟨3505538699893720622035265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9348103199716588325427373 3505538699893720622035265)
            ·
              refine ⟨2629154024920290466526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505538699893720622035265 2629154024920290466526449)
              ·
                refine ⟨1971865518690217849894837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629154024920290466526449 1971865518690217849894837)
                ·
                  refine ⟨184862392377207923427641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1971865518690217849894837 184862392377207923427641)
                  ·
                    rfl

theorem cell22_1620082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_1620082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620082 prefixEnd_1620082 := by exact prefixLift 1620082
  have htrace : WordTrace (prefixWord ++ tailWord_1620082) baseStart_1620082 baseEnd_1620082 := by
    simpa [prefixWord, tailWord_1620082, baseEnd_1620082] using wordTrace_append hprefix tailTrace_1620082
  have hstable : (prefixWord ++ tailWord_1620082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620082).length < 2 ^ (prefixWord ++ tailWord_1620082).sum := by decide
  have hdescent : baseEnd_1620082 < baseStart_1620082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620086 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 1, 3]
def baseStart_1620086 : Nat := 118140960795 + 1620086 * 2 ^ 59
def prefixEnd_1620086 : Nat := 4983230072969 + 3 ^ 40 * 1620086 * 2
def baseEnd_1620086 : Nat := 554588546413369093182911

theorem tailTrace_1620086 : CollatzResearch.WordTrace tailWord_1620086 prefixEnd_1620086 554588546413369093182911 := by
  unfold tailWord_1620086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3693086925544536594100007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39392927205808390337066741 3693086925544536594100007)
  ·
    refine ⟨5539630388316804891150011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3693086925544536594100007 5539630388316804891150011)
    ·
      refine ⟨8309445582475207336725017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5539630388316804891150011 8309445582475207336725017)
      ·
        refine ⟨6232084186856405502543763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8309445582475207336725017 6232084186856405502543763)
        ·
          refine ⟨9348126280284608253815645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6232084186856405502543763 9348126280284608253815645)
          ·
            refine ⟨3505547355106728095180867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9348126280284608253815645 3505547355106728095180867)
            ·
              refine ⟨5258321032660092142771301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505547355106728095180867 5258321032660092142771301)
              ·
                refine ⟨985935193623767276769619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5258321032660092142771301 985935193623767276769619)
                ·
                  refine ⟨1478902790435650915154429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985935193623767276769619 1478902790435650915154429)
                  ·
                    refine ⟨554588546413369093182911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1478902790435650915154429 554588546413369093182911)
                    ·
                      rfl

theorem cell22_1620086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_1620086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620086 prefixEnd_1620086 := by exact prefixLift 1620086
  have htrace : WordTrace (prefixWord ++ tailWord_1620086) baseStart_1620086 baseEnd_1620086 := by
    simpa [prefixWord, tailWord_1620086, baseEnd_1620086] using wordTrace_append hprefix tailTrace_1620086
  have hstable : (prefixWord ++ tailWord_1620086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620086).length < 2 ^ (prefixWord ++ tailWord_1620086).sum := by decide
  have hdescent : baseEnd_1620086 < baseStart_1620086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620097 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1620097 : Nat := 118140960795 + 1620097 * 2 ^ 59
def prefixEnd_1620097 : Nat := 4983230072969 + 3 ^ 40 * 1620097 * 2
def baseEnd_1620097 : Nat := 554592311938168731157877

theorem tailTrace_1620097 : CollatzResearch.WordTrace tailWord_1620097 prefixEnd_1620097 554592311938168731157877 := by
  unfold tailWord_1620097
  simp only [CollatzResearch.WordTrace]
  refine ⟨59089792011672734384250545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39393194674448489589500363 59089792011672734384250545)
  ·
    refine ⟨44317344008754550788187909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59089792011672734384250545 44317344008754550788187909)
    ·
      refine ⟨8309502001641478272785233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44317344008754550788187909 8309502001641478272785233)
      ·
        refine ⟨6232126501231108704588925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8309502001641478272785233 6232126501231108704588925)
        ·
          refine ⟨2337047437961665764220847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6232126501231108704588925 2337047437961665764220847)
          ·
            refine ⟨3505571156942498646331271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337047437961665764220847 3505571156942498646331271)
            ·
              refine ⟨5258356735413747969496907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505571156942498646331271 5258356735413747969496907)
              ·
                refine ⟨7887535103120621954245361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5258356735413747969496907 7887535103120621954245361)
                ·
                  refine ⟨5915651327340466465684021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7887535103120621954245361 5915651327340466465684021)
                  ·
                    refine ⟨554592311938168731157877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5915651327340466465684021 554592311938168731157877)
                    ·
                      rfl

theorem cell22_1620097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1620097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620097 prefixEnd_1620097 := by exact prefixLift 1620097
  have htrace : WordTrace (prefixWord ++ tailWord_1620097) baseStart_1620097 baseEnd_1620097 := by
    simpa [prefixWord, tailWord_1620097, baseEnd_1620097] using wordTrace_append hprefix tailTrace_1620097
  have hstable : (prefixWord ++ tailWord_1620097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620097).length < 2 ^ (prefixWord ++ tailWord_1620097).sum := by decide
  have hdescent : baseEnd_1620097 < baseStart_1620097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620129 : List Nat := [1, 2, 3, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1620129 : Nat := 118140960795 + 1620129 * 2 ^ 59
def prefixEnd_1620129 : Nat := 4983230072969 + 3 ^ 40 * 1620129 * 2
def baseEnd_1620129 : Nat := 554603266192131314357779

theorem tailTrace_1620129 : CollatzResearch.WordTrace tailWord_1620129 prefixEnd_1620129 554603266192131314357779 := by
  unfold tailWord_1620129
  simp only [CollatzResearch.WordTrace]
  refine ⟨59090959147556803849415441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39393972765037869232943627 59090959147556803849415441)
  ·
    refine ⟨44318219360667602887061581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59090959147556803849415441 44318219360667602887061581)
    ·
      refine ⟨16619332260250351082648093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44318219360667602887061581 16619332260250351082648093)
      ·
        refine ⟨6232249597593881655993035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16619332260250351082648093 6232249597593881655993035)
        ·
          refine ⟨9348374396390822483989553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6232249597593881655993035 9348374396390822483989553)
          ·
            refine ⟨7011280797293116862992165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9348374396390822483989553 7011280797293116862992165)
            ·
              refine ⟨1314615149492459411811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7011280797293116862992165 1314615149492459411811031)
              ·
                refine ⟨1971922724238689117716547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314615149492459411811031 1971922724238689117716547)
                ·
                  refine ⟨2957884086358033676574821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971922724238689117716547 2957884086358033676574821)
                  ·
                    refine ⟨554603266192131314357779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2957884086358033676574821 554603266192131314357779)
                    ·
                      rfl

theorem cell22_1620129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1620129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620129 prefixEnd_1620129 := by exact prefixLift 1620129
  have htrace : WordTrace (prefixWord ++ tailWord_1620129) baseStart_1620129 baseEnd_1620129 := by
    simpa [prefixWord, tailWord_1620129, baseEnd_1620129] using wordTrace_append hprefix tailTrace_1620129
  have hstable : (prefixWord ++ tailWord_1620129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620129).length < 2 ^ (prefixWord ++ tailWord_1620129).sum := by decide
  have hdescent : baseEnd_1620129 < baseStart_1620129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620170 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 2, 7]
def baseStart_1620170 : Nat := 118140960795 + 1620170 * 2 ^ 59
def prefixEnd_1620170 : Nat := 4983230072969 + 3 ^ 40 * 1620170 * 2
def baseEnd_1620170 : Nat := 554617301330020874082653

theorem tailTrace_1620170 : CollatzResearch.WordTrace tailWord_1620170 prefixEnd_1620170 554617301330020874082653 := by
  unfold tailWord_1620170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773113635102066962914491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39394969693605511901105309 14773113635102066962914491)
  ·
    refine ⟨22159670452653100444371737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14773113635102066962914491 22159670452653100444371737)
    ·
      refine ⟨16619752839489825333278803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22159670452653100444371737 16619752839489825333278803)
      ·
        refine ⟨24929629259234737999918205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16619752839489825333278803 24929629259234737999918205)
        ·
          refine ⟨9348610972213026749969327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24929629259234737999918205 9348610972213026749969327)
          ·
            refine ⟨14022916458319540124953991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9348610972213026749969327 14022916458319540124953991)
            ·
              refine ⟨21034374687479310187430987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14022916458319540124953991 21034374687479310187430987)
              ·
                refine ⟨31551562031218965281146481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21034374687479310187430987 31551562031218965281146481)
                ·
                  refine ⟨23663671523414223960859861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31551562031218965281146481 23663671523414223960859861)
                  ·
                    refine ⟨554617301330020874082653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23663671523414223960859861 554617301330020874082653)
                    ·
                      rfl

theorem cell22_1620170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_1620170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620170 prefixEnd_1620170 := by exact prefixLift 1620170
  have htrace : WordTrace (prefixWord ++ tailWord_1620170) baseStart_1620170 baseEnd_1620170 := by
    simpa [prefixWord, tailWord_1620170, baseEnd_1620170] using wordTrace_append hprefix tailTrace_1620170
  have hstable : (prefixWord ++ tailWord_1620170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620170).length < 2 ^ (prefixWord ++ tailWord_1620170).sum := by decide
  have hdescent : baseEnd_1620170 < baseStart_1620170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620328 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_1620328 : Nat := 118140960795 + 1620328 * 2 ^ 59
def prefixEnd_1620328 : Nat := 4983230072969 + 3 ^ 40 * 1620328 * 2
def baseEnd_1620328 : Nat := 554671387958961128632169

theorem tailTrace_1620328 : CollatzResearch.WordTrace tailWord_1620328 prefixEnd_1620328 554671387958961128632169 := by
  unfold tailWord_1620328
  simp only [CollatzResearch.WordTrace]
  refine ⟨29549108636917930417954819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39398811515890573890606425 29549108636917930417954819)
  ·
    refine ⟨44323662955376895626932229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29549108636917930417954819 44323662955376895626932229)
    ·
      refine ⟨8310686804133167930049793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44323662955376895626932229 8310686804133167930049793)
      ·
        refine ⟨6233015103099875947537345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8310686804133167930049793 6233015103099875947537345)
        ·
          refine ⟨4674761327324906960653009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6233015103099875947537345 4674761327324906960653009)
          ·
            refine ⟨3506070995493680220489757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674761327324906960653009 3506070995493680220489757)
            ·
              refine ⟨1314776623310130082683659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3506070995493680220489757 1314776623310130082683659)
              ·
                refine ⟨1972164934965195124025489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314776623310130082683659 1972164934965195124025489)
                ·
                  refine ⟨1479123701223896343019117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972164934965195124025489 1479123701223896343019117)
                  ·
                    refine ⟨554671387958961128632169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479123701223896343019117 554671387958961128632169)
                    ·
                      rfl

theorem cell22_1620328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_1620328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620328 prefixEnd_1620328 := by exact prefixLift 1620328
  have htrace : WordTrace (prefixWord ++ tailWord_1620328) baseStart_1620328 baseEnd_1620328 := by
    simpa [prefixWord, tailWord_1620328, baseEnd_1620328] using wordTrace_append hprefix tailTrace_1620328
  have hstable : (prefixWord ++ tailWord_1620328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620328).length < 2 ^ (prefixWord ++ tailWord_1620328).sum := by decide
  have hdescent : baseEnd_1620328 < baseStart_1620328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620341 : List Nat := [1, 3, 4, 1, 2, 3, 2, 6]
def baseStart_1620341 : Nat := 118140960795 + 1620341 * 2 ^ 59
def prefixEnd_1620341 : Nat := 4983230072969 + 3 ^ 40 * 1620341 * 2
def baseEnd_1620341 : Nat := 61630648680514825339681

theorem tailTrace_1620341 : CollatzResearch.WordTrace tailWord_1620341 prefixEnd_1620341 61630648680514825339681 := by
  unfold tailWord_1620341
  simp only [CollatzResearch.WordTrace]
  refine ⟨59098691422788764056132877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39399127615192509370755251 59098691422788764056132877)
  ·
    refine ⟨22162009283545786521049829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59098691422788764056132877 22162009283545786521049829)
    ·
      refine ⟨4155376740664834972696843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22162009283545786521049829 4155376740664834972696843)
      ·
        refine ⟨6233065110997252459045265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155376740664834972696843 6233065110997252459045265)
        ·
          refine ⟨4674798833247939344283949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6233065110997252459045265 4674798833247939344283949)
          ·
            refine ⟨1753049562467977254106481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4674798833247939344283949 1753049562467977254106481)
            ·
              refine ⟨1314787171850982940579861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1753049562467977254106481 1314787171850982940579861)
              ·
                refine ⟨61630648680514825339681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1314787171850982940579861 61630648680514825339681)
                ·
                  rfl

theorem cell22_1620341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 6].length) (baseStart_1620341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620341 prefixEnd_1620341 := by exact prefixLift 1620341
  have htrace : WordTrace (prefixWord ++ tailWord_1620341) baseStart_1620341 baseEnd_1620341 := by
    simpa [prefixWord, tailWord_1620341, baseEnd_1620341] using wordTrace_append hprefix tailTrace_1620341
  have hstable : (prefixWord ++ tailWord_1620341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620341).length < 2 ^ (prefixWord ++ tailWord_1620341).sum := by decide
  have hdescent : baseEnd_1620341 < baseStart_1620341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620427 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 3, 6]
def baseStart_1620427 : Nat := 118140960795 + 1620427 * 2 ^ 59
def prefixEnd_1620427 : Nat := 4983230072969 + 3 ^ 40 * 1620427 * 2
def baseEnd_1620427 : Nat := 554705277682157870406865

theorem tailTrace_1620427 : CollatzResearch.WordTrace tailWord_1620427 prefixEnd_1620427 554705277682157870406865 := by
  unfold tailWord_1620427
  simp only [CollatzResearch.WordTrace]
  refine ⟨59101828100477200743763535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39401218733651467162509023 59101828100477200743763535)
  ·
    refine ⟨88652742150715801115645303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59101828100477200743763535 88652742150715801115645303)
    ·
      refine ⟨132979113226073701673467955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88652742150715801115645303 132979113226073701673467955)
      ·
        refine ⟨199468669839110552510201933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132979113226073701673467955 199468669839110552510201933)
        ·
          refine ⟨74800751189666457191325725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199468669839110552510201933 74800751189666457191325725)
          ·
            refine ⟨28050281696124921446747147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74800751189666457191325725 28050281696124921446747147)
            ·
              refine ⟨42075422544187382170120721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28050281696124921446747147 42075422544187382170120721)
              ·
                refine ⟨31556566908140536627590541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42075422544187382170120721 31556566908140536627590541)
                ·
                  refine ⟨11833712590552701235346453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31556566908140536627590541 11833712590552701235346453)
                  ·
                    refine ⟨554705277682157870406865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11833712590552701235346453 554705277682157870406865)
                    ·
                      rfl

theorem cell22_1620427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 6].length) (baseStart_1620427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620427 prefixEnd_1620427 := by exact prefixLift 1620427
  have htrace : WordTrace (prefixWord ++ tailWord_1620427) baseStart_1620427 baseEnd_1620427 := by
    simpa [prefixWord, tailWord_1620427, baseEnd_1620427] using wordTrace_append hprefix tailTrace_1620427
  have hstable : (prefixWord ++ tailWord_1620427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620427).length < 2 ^ (prefixWord ++ tailWord_1620427).sum := by decide
  have hdescent : baseEnd_1620427 < baseStart_1620427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1620457 : Nat := 118140960795 + 1620457 * 2 ^ 59
def prefixEnd_1620457 : Nat := 4983230072969 + 3 ^ 40 * 1620457 * 2
def baseEnd_1620457 : Nat := 554715547295247792156773

theorem tailTrace_1620457 : CollatzResearch.WordTrace tailWord_1620457 prefixEnd_1620457 554715547295247792156773 := by
  unfold tailWord_1620457
  simp only [CollatzResearch.WordTrace]
  refine ⟨59102922290368515867355625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39401948193579010578237083 59102922290368515867355625)
  ·
    refine ⟨44327191717776386900516719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59102922290368515867355625 44327191717776386900516719)
    ·
      refine ⟨66490787576664580350775079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44327191717776386900516719 66490787576664580350775079)
      ·
        refine ⟨99736181364996870526162619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66490787576664580350775079 99736181364996870526162619)
        ·
          refine ⟨149604272047495305789243929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99736181364996870526162619 149604272047495305789243929)
          ·
            refine ⟨112203204035621479341932947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149604272047495305789243929 112203204035621479341932947)
            ·
              refine ⟨168304806053432219012899421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112203204035621479341932947 168304806053432219012899421)
              ·
                refine ⟨63114302270037082129837283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168304806053432219012899421 63114302270037082129837283)
                ·
                  refine ⟨94671453405055623194755925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63114302270037082129837283 94671453405055623194755925)
                  ·
                    refine ⟨554715547295247792156773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94671453405055623194755925 554715547295247792156773)
                    ·
                      rfl

theorem cell22_1620457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1620457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620457 prefixEnd_1620457 := by exact prefixLift 1620457
  have htrace : WordTrace (prefixWord ++ tailWord_1620457) baseStart_1620457 baseEnd_1620457 := by
    simpa [prefixWord, tailWord_1620457, baseEnd_1620457] using wordTrace_append hprefix tailTrace_1620457
  have hstable : (prefixWord ++ tailWord_1620457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620457).length < 2 ^ (prefixWord ++ tailWord_1620457).sum := by decide
  have hdescent : baseEnd_1620457 < baseStart_1620457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620459 : List Nat := [1, 1, 1, 1, 2, 3, 7, 6]
def baseStart_1620459 : Nat := 118140960795 + 1620459 * 2 ^ 59
def prefixEnd_1620459 : Nat := 4983230072969 + 3 ^ 40 * 1620459 * 2
def baseEnd_1620459 : Nat := 61635136881791161511863

theorem tailTrace_1620459 : CollatzResearch.WordTrace tailWord_1620459 prefixEnd_1620459 61635136881791161511863 := by
  unfold tailWord_1620459
  simp only [CollatzResearch.WordTrace]
  refine ⟨59102995236361270208928431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39401996824240846805952287 59102995236361270208928431)
  ·
    refine ⟨88654492854541905313392647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59102995236361270208928431 88654492854541905313392647)
    ·
      refine ⟨132981739281812857970088971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88654492854541905313392647 132981739281812857970088971)
      ·
        refine ⟨199472608922719286955133457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132981739281812857970088971 199472608922719286955133457)
        ·
          refine ⟨149604456692039465216350093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199472608922719286955133457 149604456692039465216350093)
          ·
            refine ⟨56101671259514799456131285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149604456692039465216350093 56101671259514799456131285)
            ·
              refine ⟨1314882920144878112253077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 56101671259514799456131285 1314882920144878112253077)
              ·
                refine ⟨61635136881791161511863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1314882920144878112253077 61635136881791161511863)
                ·
                  rfl

theorem cell22_1620459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7, 6].length) (baseStart_1620459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620459 prefixEnd_1620459 := by exact prefixLift 1620459
  have htrace : WordTrace (prefixWord ++ tailWord_1620459) baseStart_1620459 baseEnd_1620459 := by
    simpa [prefixWord, tailWord_1620459, baseEnd_1620459] using wordTrace_append hprefix tailTrace_1620459
  have hstable : (prefixWord ++ tailWord_1620459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620459).length < 2 ^ (prefixWord ++ tailWord_1620459).sum := by decide
  have hdescent : baseEnd_1620459 < baseStart_1620459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620461 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1620461 : Nat := 118140960795 + 1620461 * 2 ^ 59
def prefixEnd_1620461 : Nat := 4983230072969 + 3 ^ 40 * 1620461 * 2
def baseEnd_1620461 : Nat := 554716916576993115056761

theorem tailTrace_1620461 : CollatzResearch.WordTrace tailWord_1620461 prefixEnd_1620461 554716916576993115056761 := by
  unfold tailWord_1620461
  simp only [CollatzResearch.WordTrace]
  refine ⟨59103068182354024550501237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39402045454902683033667491 59103068182354024550501237)
  ·
    refine ⟨5540912642095689801609491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59103068182354024550501237 5540912642095689801609491)
    ·
      refine ⟨8311368963143534702414237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5540912642095689801609491 8311368963143534702414237)
      ·
        refine ⟨3116763361178825513405339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8311368963143534702414237 3116763361178825513405339)
        ·
          refine ⟨4675145041768238270108009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116763361178825513405339 4675145041768238270108009)
          ·
            refine ⟨3506358781326178702581007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4675145041768238270108009 3506358781326178702581007)
            ·
              refine ⟨5259538171989268053871511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3506358781326178702581007 5259538171989268053871511)
              ·
                refine ⟨7889307257983902080807267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5259538171989268053871511 7889307257983902080807267)
                ·
                  refine ⟨11833960886975853121210901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7889307257983902080807267 11833960886975853121210901)
                  ·
                    refine ⟨554716916576993115056761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11833960886975853121210901 554716916576993115056761)
                    ·
                      rfl

theorem cell22_1620461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1620461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620461 prefixEnd_1620461 := by exact prefixLift 1620461
  have htrace : WordTrace (prefixWord ++ tailWord_1620461) baseStart_1620461 baseEnd_1620461 := by
    simpa [prefixWord, tailWord_1620461, baseEnd_1620461] using wordTrace_append hprefix tailTrace_1620461
  have hstable : (prefixWord ++ tailWord_1620461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620461).length < 2 ^ (prefixWord ++ tailWord_1620461).sum := by decide
  have hdescent : baseEnd_1620461 < baseStart_1620461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620491 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 3, 3]
def baseStart_1620491 : Nat := 118140960795 + 1620491 * 2 ^ 59
def prefixEnd_1620491 : Nat := 4983230072969 + 3 ^ 40 * 1620491 * 2
def baseEnd_1620491 : Nat := 554727186190083036806669

theorem tailTrace_1620491 : CollatzResearch.WordTrace tailWord_1620491 prefixEnd_1620491 554727186190083036806669 := by
  unfold tailWord_1620491
  simp only [CollatzResearch.WordTrace]
  refine ⟨59104162372245339674093327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39402774914830226449395551 59104162372245339674093327)
  ·
    refine ⟨88656243558368009511139991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59104162372245339674093327 88656243558368009511139991)
    ·
      refine ⟨132984365337552014266709987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88656243558368009511139991 132984365337552014266709987)
      ·
        refine ⟨199476548006328021400064981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132984365337552014266709987 199476548006328021400064981)
        ·
          refine ⟨4675231593898313001564023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 199476548006328021400064981 4675231593898313001564023)
          ·
            refine ⟨7012847390847469502346035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4675231593898313001564023 7012847390847469502346035)
            ·
              refine ⟨10519271086271204253519053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012847390847469502346035 10519271086271204253519053)
              ·
                refine ⟨3944726657351701595069645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10519271086271204253519053 3944726657351701595069645)
                ·
                  refine ⟨1479272496506888098151117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3944726657351701595069645 1479272496506888098151117)
                  ·
                    refine ⟨554727186190083036806669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479272496506888098151117 554727186190083036806669)
                    ·
                      rfl

theorem cell22_1620491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 3, 3].length) (baseStart_1620491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620491 prefixEnd_1620491 := by exact prefixLift 1620491
  have htrace : WordTrace (prefixWord ++ tailWord_1620491) baseStart_1620491 baseEnd_1620491 := by
    simpa [prefixWord, tailWord_1620491, baseEnd_1620491] using wordTrace_append hprefix tailTrace_1620491
  have hstable : (prefixWord ++ tailWord_1620491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620491).length < 2 ^ (prefixWord ++ tailWord_1620491).sum := by decide
  have hdescent : baseEnd_1620491 < baseStart_1620491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620542 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1620542 : Nat := 118140960795 + 1620542 * 2 ^ 59
def prefixEnd_1620542 : Nat := 4983230072969 + 3 ^ 40 * 1620542 * 2
def baseEnd_1620542 : Nat := 554744644532335903781513

theorem tailTrace_1620542 : CollatzResearch.WordTrace tailWord_1620542 prefixEnd_1620542 554744644532335903781513 := by
  unfold tailWord_1620542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7388252811882571923024985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39404014996707050256133253 7388252811882571923024985)
  ·
    refine ⟨5541189608911928942268739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7388252811882571923024985 5541189608911928942268739)
    ·
      refine ⟨8311784413367893413403109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541189608911928942268739 8311784413367893413403109)
      ·
        refine ⟨1558459577506480015013083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8311784413367893413403109 1558459577506480015013083)
        ·
          refine ⟨2337689366259720022519625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558459577506480015013083 2337689366259720022519625)
          ·
            refine ⟨1753267024694790016889719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2337689366259720022519625 1753267024694790016889719)
            ·
              refine ⟨2629900537042185025334579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753267024694790016889719 2629900537042185025334579)
              ·
                refine ⟨3944850805563277538001869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629900537042185025334579 3944850805563277538001869)
                ·
                  refine ⟨1479319052086229076750701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3944850805563277538001869 1479319052086229076750701)
                  ·
                    refine ⟨554744644532335903781513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479319052086229076750701 554744644532335903781513)
                    ·
                      rfl

theorem cell22_1620542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1620542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620542 prefixEnd_1620542 := by exact prefixLift 1620542
  have htrace : WordTrace (prefixWord ++ tailWord_1620542) baseStart_1620542 baseEnd_1620542 := by
    simpa [prefixWord, tailWord_1620542, baseEnd_1620542] using wordTrace_append hprefix tailTrace_1620542
  have hstable : (prefixWord ++ tailWord_1620542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620542).length < 2 ^ (prefixWord ++ tailWord_1620542).sum := by decide
  have hdescent : baseEnd_1620542 < baseStart_1620542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620594 : List Nat := [3, 2, 1, 2, 14]
def baseStart_1620594 : Nat := 118140960795 + 1620594 * 2 ^ 59
def prefixEnd_1620594 : Nat := 4983230072969 + 3 ^ 40 * 1620594 * 2
def baseEnd_1620594 : Nat := 2282973025493930458771

theorem tailTrace_1620594 : CollatzResearch.WordTrace tailWord_1620594 prefixEnd_1620594 2282973025493930458771 := by
  unfold tailWord_1620594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776979772718047066273209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39405279393914792176728557 14776979772718047066273209)
  ·
    refine ⟨11082734829538535299704907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14776979772718047066273209 11082734829538535299704907)
    ·
      refine ⟨16624102244307802949557361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082734829538535299704907 16624102244307802949557361)
      ·
        refine ⟨12468076683230852212168021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16624102244307802949557361 12468076683230852212168021)
        ·
          refine ⟨2282973025493930458771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 12468076683230852212168021 2282973025493930458771)
          ·
            rfl

theorem cell22_1620594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 14].length) (baseStart_1620594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620594 prefixEnd_1620594 := by exact prefixLift 1620594
  have htrace : WordTrace (prefixWord ++ tailWord_1620594) baseStart_1620594 baseEnd_1620594 := by
    simpa [prefixWord, tailWord_1620594, baseEnd_1620594] using wordTrace_append hprefix tailTrace_1620594
  have hstable : (prefixWord ++ tailWord_1620594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620594).length < 2 ^ (prefixWord ++ tailWord_1620594).sum := by decide
  have hdescent : baseEnd_1620594 < baseStart_1620594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620671 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1620671 : Nat := 118140960795 + 1620671 * 2 ^ 59
def prefixEnd_1620671 : Nat := 4983230072969 + 3 ^ 40 * 1620671 * 2
def baseEnd_1620671 : Nat := 554788803868622567306117

theorem tailTrace_1620671 : CollatzResearch.WordTrace tailWord_1620671 prefixEnd_1620671 554788803868622567306117 := by
  unfold tailWord_1620671
  simp only [CollatzResearch.WordTrace]
  refine ⟨59110727511593230415645867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39407151674395486943763911 59110727511593230415645867)
  ·
    refine ⟨88666091267389845623468801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59110727511593230415645867 88666091267389845623468801)
    ·
      refine ⟨66499568450542384217601601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88666091267389845623468801 66499568450542384217601601)
      ·
        refine ⟨49874676337906788163201201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66499568450542384217601601 49874676337906788163201201)
        ·
          refine ⟨37406007253430091122400901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49874676337906788163201201 37406007253430091122400901)
          ·
            refine ⟨7013626360018142085450169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37406007253430091122400901 7013626360018142085450169)
            ·
              refine ⟨5260219770013606564087627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7013626360018142085450169 5260219770013606564087627)
              ·
                refine ⟨7890329655020409846131441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260219770013606564087627 7890329655020409846131441)
                ·
                  refine ⟨5917747241265307384598581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7890329655020409846131441 5917747241265307384598581)
                  ·
                    refine ⟨554788803868622567306117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5917747241265307384598581 554788803868622567306117)
                    ·
                      rfl

theorem cell22_1620671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1620671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620671 prefixEnd_1620671 := by exact prefixLift 1620671
  have htrace : WordTrace (prefixWord ++ tailWord_1620671) baseStart_1620671 baseEnd_1620671 := by
    simpa [prefixWord, tailWord_1620671, baseEnd_1620671] using wordTrace_append hprefix tailTrace_1620671
  have hstable : (prefixWord ++ tailWord_1620671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620671).length < 2 ^ (prefixWord ++ tailWord_1620671).sum := by decide
  have hdescent : baseEnd_1620671 < baseStart_1620671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620703 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 1, 4]
def baseStart_1620703 : Nat := 118140960795 + 1620703 * 2 ^ 59
def prefixEnd_1620703 : Nat := 4983230072969 + 3 ^ 40 * 1620703 * 2
def baseEnd_1620703 : Nat := 554799758122585150506019

theorem tailTrace_1620703 : CollatzResearch.WordTrace tailWord_1620703 prefixEnd_1620703 554799758122585150506019 := by
  unfold tailWord_1620703
  simp only [CollatzResearch.WordTrace]
  refine ⟨59111894647477299880810763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39407929764984866587207175 59111894647477299880810763)
  ·
    refine ⟨88667841971215949821216145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59111894647477299880810763 88667841971215949821216145)
    ·
      refine ⟨66500881478411962365912109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88667841971215949821216145 66500881478411962365912109)
      ·
        refine ⟨24937830554404485887217041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66500881478411962365912109 24937830554404485887217041)
        ·
          refine ⟨18703372915803364415412781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24937830554404485887217041 18703372915803364415412781)
          ·
            refine ⟨7013764843426261655779793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18703372915803364415412781 7013764843426261655779793)
            ·
              refine ⟨5260323632569696241834845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7013764843426261655779793 5260323632569696241834845)
              ·
                refine ⟨1972621362213636090688067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260323632569696241834845 1972621362213636090688067)
                ·
                  refine ⟨2958932043320454136032101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972621362213636090688067 2958932043320454136032101)
                  ·
                    refine ⟨554799758122585150506019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2958932043320454136032101 554799758122585150506019)
                    ·
                      rfl

theorem cell22_1620703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 4].length) (baseStart_1620703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620703 prefixEnd_1620703 := by exact prefixLift 1620703
  have htrace : WordTrace (prefixWord ++ tailWord_1620703) baseStart_1620703 baseEnd_1620703 := by
    simpa [prefixWord, tailWord_1620703, baseEnd_1620703] using wordTrace_append hprefix tailTrace_1620703
  have hstable : (prefixWord ++ tailWord_1620703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620703).length < 2 ^ (prefixWord ++ tailWord_1620703).sum := by decide
  have hdescent : baseEnd_1620703 < baseStart_1620703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620718 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_1620718 : Nat := 118140960795 + 1620718 * 2 ^ 59
def prefixEnd_1620718 : Nat := 4983230072969 + 3 ^ 40 * 1620718 * 2
def baseEnd_1620718 : Nat := 184934964309710037126991

theorem tailTrace_1620718 : CollatzResearch.WordTrace tailWord_1620718 prefixEnd_1620718 184934964309710037126991 := by
  unfold tailWord_1620718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389055217802869680325851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39408294494948638295071205 7389055217802869680325851)
  ·
    refine ⟨11083582826704304520488777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7389055217802869680325851 11083582826704304520488777)
    ·
      refine ⟨8312687120028228390366583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11083582826704304520488777 8312687120028228390366583)
      ·
        refine ⟨12469030680042342585549875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312687120028228390366583 12469030680042342585549875)
        ·
          refine ⟨18703546020063513878324813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469030680042342585549875 18703546020063513878324813)
          ·
            refine ⟨7013829757523817704371805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18703546020063513878324813 7013829757523817704371805)
            ·
              refine ⟨2630186159071431639139427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7013829757523817704371805 2630186159071431639139427)
              ·
                refine ⟨3945279238607147458709141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630186159071431639139427 3945279238607147458709141)
                ·
                  refine ⟨184934964309710037126991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3945279238607147458709141 184934964309710037126991)
                  ·
                    rfl

theorem cell22_1620718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_1620718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620718 prefixEnd_1620718 := by exact prefixLift 1620718
  have htrace : WordTrace (prefixWord ++ tailWord_1620718) baseStart_1620718 baseEnd_1620718 := by
    simpa [prefixWord, tailWord_1620718, baseEnd_1620718] using wordTrace_append hprefix tailTrace_1620718
  have hstable : (prefixWord ++ tailWord_1620718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620718).length < 2 ^ (prefixWord ++ tailWord_1620718).sum := by decide
  have hdescent : baseEnd_1620718 < baseStart_1620718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620746 : List Nat := [3, 1, 2, 2, 1, 2, 1, 10]
def baseStart_1620746 : Nat := 118140960795 + 1620746 * 2 ^ 59
def prefixEnd_1620746 : Nat := 4983230072969 + 3 ^ 40 * 1620746 * 2
def baseEnd_1620746 : Nat := 61646053100149707964543

theorem tailTrace_1620746 : CollatzResearch.WordTrace tailWord_1620746 prefixEnd_1620746 61646053100149707964543 := by
  unfold tailWord_1620746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778365746580379556156523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39408975324214345483084061 14778365746580379556156523)
  ·
    refine ⟨22167548619870569334234785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14778365746580379556156523 22167548619870569334234785)
    ·
      refine ⟨16625661464902927000676089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22167548619870569334234785 16625661464902927000676089)
      ·
        refine ⟨12469246098677195250507067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16625661464902927000676089 12469246098677195250507067)
        ·
          refine ⟨18703869148015792875760601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469246098677195250507067 18703869148015792875760601)
          ·
            refine ⟨14027901861011844656820451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18703869148015792875760601 14027901861011844656820451)
            ·
              refine ⟨21041852791517766985230677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14027901861011844656820451 21041852791517766985230677)
              ·
                refine ⟨61646053100149707964543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21041852791517766985230677 61646053100149707964543)
                ·
                  rfl

theorem cell22_1620746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_1620746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620746 prefixEnd_1620746 := by exact prefixLift 1620746
  have htrace : WordTrace (prefixWord ++ tailWord_1620746) baseStart_1620746 baseEnd_1620746 := by
    simpa [prefixWord, tailWord_1620746, baseEnd_1620746] using wordTrace_append hprefix tailTrace_1620746
  have hstable : (prefixWord ++ tailWord_1620746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620746).length < 2 ^ (prefixWord ++ tailWord_1620746).sum := by decide
  have hdescent : baseEnd_1620746 < baseStart_1620746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620754 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1620754 : Nat := 118140960795 + 1620754 * 2 ^ 59
def prefixEnd_1620754 : Nat := 4983230072969 + 3 ^ 40 * 1620754 * 2
def baseEnd_1620754 : Nat := 554817216464838017480863

theorem tailTrace_1620754 : CollatzResearch.WordTrace tailWord_1620754 prefixEnd_1620754 554817216464838017480863 := by
  unfold tailWord_1620754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778438692573133897729329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39409169846861690393944877 14778438692573133897729329)
  ·
    refine ⟨11083829019429850423296997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14778438692573133897729329 11083829019429850423296997)
    ·
      refine ⟨2078217941143096954368187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11083829019429850423296997 2078217941143096954368187)
      ·
        refine ⟨3117326911714645431552281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078217941143096954368187 3117326911714645431552281)
        ·
          refine ⟨2337995183785984073664211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117326911714645431552281 2337995183785984073664211)
          ·
            refine ⟨3506992775678976110496317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337995183785984073664211 3506992775678976110496317)
            ·
              refine ⟨1315122290879616041436119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3506992775678976110496317 1315122290879616041436119)
              ·
                refine ⟨1972683436319424062154179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315122290879616041436119 1972683436319424062154179)
                ·
                  refine ⟨2959025154479136093231269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972683436319424062154179 2959025154479136093231269)
                  ·
                    refine ⟨554817216464838017480863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959025154479136093231269 554817216464838017480863)
                    ·
                      rfl

theorem cell22_1620754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1620754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620754 prefixEnd_1620754 := by exact prefixLift 1620754
  have htrace : WordTrace (prefixWord ++ tailWord_1620754) baseStart_1620754 baseEnd_1620754 := by
    simpa [prefixWord, tailWord_1620754, baseEnd_1620754] using wordTrace_append hprefix tailTrace_1620754
  have hstable : (prefixWord ++ tailWord_1620754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620754).length < 2 ^ (prefixWord ++ tailWord_1620754).sum := by decide
  have hdescent : baseEnd_1620754 < baseStart_1620754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620812 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 1, 3]
def baseStart_1620812 : Nat := 118140960795 + 1620812 * 2 ^ 59
def prefixEnd_1620812 : Nat := 4983230072969 + 3 ^ 40 * 1620812 * 2
def baseEnd_1620812 : Nat := 554837071050145199530685

theorem tailTrace_1620812 : CollatzResearch.WordTrace tailWord_1620812 prefixEnd_1620812 554837071050145199530685 := by
  unfold tailWord_1620812
  simp only [CollatzResearch.WordTrace]
  refine ⟨29557935102041205748264345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39410580136054940997685793 29557935102041205748264345)
  ·
    refine ⟨22168451326530904311198259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29557935102041205748264345 22168451326530904311198259)
    ·
      refine ⟨33252676989796356466797389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22168451326530904311198259 33252676989796356466797389)
      ·
        refine ⟨12469753871173633675049021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33252676989796356466797389 12469753871173633675049021)
        ·
          refine ⟨4676157701690112628143383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12469753871173633675049021 4676157701690112628143383)
          ·
            refine ⟨7014236552535168942215075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676157701690112628143383 7014236552535168942215075)
            ·
              refine ⟨10521354828802753413322613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014236552535168942215075 10521354828802753413322613)
              ·
                refine ⟨986377015200258132498995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10521354828802753413322613 986377015200258132498995)
                ·
                  refine ⟨1479565522800387198748493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986377015200258132498995 1479565522800387198748493)
                  ·
                    refine ⟨554837071050145199530685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479565522800387198748493 554837071050145199530685)
                    ·
                      rfl

theorem cell22_1620812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 1, 3].length) (baseStart_1620812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620812 prefixEnd_1620812 := by exact prefixLift 1620812
  have htrace : WordTrace (prefixWord ++ tailWord_1620812) baseStart_1620812 baseEnd_1620812 := by
    simpa [prefixWord, tailWord_1620812, baseEnd_1620812] using wordTrace_append hprefix tailTrace_1620812
  have hstable : (prefixWord ++ tailWord_1620812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620812).length < 2 ^ (prefixWord ++ tailWord_1620812).sum := by decide
  have hdescent : baseEnd_1620812 < baseStart_1620812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620823 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 2, 5]
def baseStart_1620823 : Nat := 118140960795 + 1620823 * 2 ^ 59
def prefixEnd_1620823 : Nat := 4983230072969 + 3 ^ 40 * 1620823 * 2
def baseEnd_1620823 : Nat := 554840836574944837505651

theorem tailTrace_1620823 : CollatzResearch.WordTrace tailWord_1620823 prefixEnd_1620823 554840836574944837505651 := by
  unfold tailWord_1620823
  simp only [CollatzResearch.WordTrace]
  refine ⟨59116271407042560375179123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39410847604695040250119415 59116271407042560375179123)
  ·
    refine ⟨88674407110563840562768685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59116271407042560375179123 88674407110563840562768685)
    ·
      refine ⟨33252902666461440211038257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88674407110563840562768685 33252902666461440211038257)
      ·
        refine ⟨24939676999846080158278693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33252902666461440211038257 24939676999846080158278693)
        ·
          refine ⟨4676189437471140029677255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24939676999846080158278693 4676189437471140029677255)
          ·
            refine ⟨7014284156206710044515883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676189437471140029677255 7014284156206710044515883)
            ·
              refine ⟨10521426234310065066773825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014284156206710044515883 10521426234310065066773825)
              ·
                refine ⟨7891069675732548800080369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10521426234310065066773825 7891069675732548800080369)
                ·
                  refine ⟨5918302256799411600060277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7891069675732548800080369 5918302256799411600060277)
                  ·
                    refine ⟨554840836574944837505651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5918302256799411600060277 554840836574944837505651)
                    ·
                      rfl

theorem cell22_1620823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_1620823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620823 prefixEnd_1620823 := by exact prefixLift 1620823
  have htrace : WordTrace (prefixWord ++ tailWord_1620823) baseStart_1620823 baseEnd_1620823 := by
    simpa [prefixWord, tailWord_1620823, baseEnd_1620823] using wordTrace_append hprefix tailTrace_1620823
  have hstable : (prefixWord ++ tailWord_1620823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620823).length < 2 ^ (prefixWord ++ tailWord_1620823).sum := by decide
  have hdescent : baseEnd_1620823 < baseStart_1620823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620825 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 5]
def baseStart_1620825 : Nat := 118140960795 + 1620825 * 2 ^ 59
def prefixEnd_1620825 : Nat := 4983230072969 + 3 ^ 40 * 1620825 * 2
def baseEnd_1620825 : Nat := 184947173738605832985215

theorem tailTrace_1620825 : CollatzResearch.WordTrace tailWord_1620825 prefixEnd_1620825 184947173738605832985215 := by
  unfold tailWord_1620825
  simp only [CollatzResearch.WordTrace]
  refine ⟨59116344353035314716751929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39410896235356876477834619 59116344353035314716751929)
  ·
    refine ⟨44337258264776486037563947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59116344353035314716751929 44337258264776486037563947)
    ·
      refine ⟨66505887397164729056345921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44337258264776486037563947 66505887397164729056345921)
      ·
        refine ⟨49879415547873546792259441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66505887397164729056345921 49879415547873546792259441)
        ·
          refine ⟨37409561660905160094194581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49879415547873546792259441 37409561660905160094194581)
          ·
            refine ⟨1753573202854929379415371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37409561660905160094194581 1753573202854929379415371)
            ·
              refine ⟨2630359804282394069123057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753573202854929379415371 2630359804282394069123057)
              ·
                refine ⟨1972769853211795551842293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630359804282394069123057 1972769853211795551842293)
                ·
                  refine ⟨184947173738605832985215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1972769853211795551842293 184947173738605832985215)
                  ·
                    rfl

theorem cell22_1620825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 5].length) (baseStart_1620825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620825 prefixEnd_1620825 := by exact prefixLift 1620825
  have htrace : WordTrace (prefixWord ++ tailWord_1620825) baseStart_1620825 baseEnd_1620825 := by
    simpa [prefixWord, tailWord_1620825, baseEnd_1620825] using wordTrace_append hprefix tailTrace_1620825
  have hstable : (prefixWord ++ tailWord_1620825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620825).length < 2 ^ (prefixWord ++ tailWord_1620825).sum := by decide
  have hdescent : baseEnd_1620825 < baseStart_1620825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620868 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1620868 : Nat := 118140960795 + 1620868 * 2 ^ 59
def prefixEnd_1620868 : Nat := 4983230072969 + 3 ^ 40 * 1620868 * 2
def baseEnd_1620868 : Nat := 554856240994579720130513

theorem tailTrace_1620868 : CollatzResearch.WordTrace tailWord_1620868 prefixEnd_1620868 554856240994579720130513 := by
  unfold tailWord_1620868
  simp only [CollatzResearch.WordTrace]
  refine ⟨29558956345939766530283629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39411941794586355373711505 29558956345939766530283629)
  ·
    refine ⟨11084608629727412448856361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29558956345939766530283629 11084608629727412448856361)
    ·
      refine ⟨8313456472295559336642271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11084608629727412448856361 8313456472295559336642271)
      ·
        refine ⟨12470184708443339004963407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313456472295559336642271 12470184708443339004963407)
        ·
          refine ⟨18705277062665008507445111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12470184708443339004963407 18705277062665008507445111)
          ·
            refine ⟨28057915593997512761167667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18705277062665008507445111 28057915593997512761167667)
            ·
              refine ⟨42086873390996269141751501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28057915593997512761167667 42086873390996269141751501)
              ·
                refine ⟨15782577521623600928156813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42086873390996269141751501 15782577521623600928156813)
                ·
                  refine ⟨5918466570608850348058805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15782577521623600928156813 5918466570608850348058805)
                  ·
                    refine ⟨554856240994579720130513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5918466570608850348058805 554856240994579720130513)
                    ·
                      rfl

theorem cell22_1620868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1620868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620868 prefixEnd_1620868 := by exact prefixLift 1620868
  have htrace : WordTrace (prefixWord ++ tailWord_1620868) baseStart_1620868 baseEnd_1620868 := by
    simpa [prefixWord, tailWord_1620868, baseEnd_1620868] using wordTrace_append hprefix tailTrace_1620868
  have hstable : (prefixWord ++ tailWord_1620868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620868).length < 2 ^ (prefixWord ++ tailWord_1620868).sum := by decide
  have hdescent : baseEnd_1620868 < baseStart_1620868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620885 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 4, 3]
def baseStart_1620885 : Nat := 118140960795 + 1620885 * 2 ^ 59
def prefixEnd_1620885 : Nat := 4983230072969 + 3 ^ 40 * 1620885 * 2
def baseEnd_1620885 : Nat := 554862060441997342455461

theorem tailTrace_1620885 : CollatzResearch.WordTrace tailWord_1620885 prefixEnd_1620885 554862060441997342455461 := by
  unfold tailWord_1620885
  simp only [CollatzResearch.WordTrace]
  refine ⟨59118532732817944963936109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39412355155211963309290739 59118532732817944963936109)
  ·
    refine ⟨22169449774806729361476041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59118532732817944963936109 22169449774806729361476041)
    ·
      refine ⟨16627087331105047021107031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22169449774806729361476041 16627087331105047021107031)
      ·
        refine ⟨24940630996657570531660547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16627087331105047021107031 24940630996657570531660547)
        ·
          refine ⟨37410946494986355797490821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24940630996657570531660547 37410946494986355797490821)
          ·
            refine ⟨7014552467809941712029529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37410946494986355797490821 7014552467809941712029529)
            ·
              refine ⟨5260914350857456284022147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7014552467809941712029529 5260914350857456284022147)
              ·
                refine ⟨7891371526286184426033221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5260914350857456284022147 7891371526286184426033221)
                ·
                  refine ⟨1479632161178659579881229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7891371526286184426033221 1479632161178659579881229)
                  ·
                    refine ⟨554862060441997342455461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479632161178659579881229 554862060441997342455461)
                    ·
                      rfl

theorem cell22_1620885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_1620885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620885 prefixEnd_1620885 := by exact prefixLift 1620885
  have htrace : WordTrace (prefixWord ++ tailWord_1620885) baseStart_1620885 baseEnd_1620885 := by
    simpa [prefixWord, tailWord_1620885, baseEnd_1620885] using wordTrace_append hprefix tailTrace_1620885
  have hstable : (prefixWord ++ tailWord_1620885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620885).length < 2 ^ (prefixWord ++ tailWord_1620885).sum := by decide
  have hdescent : baseEnd_1620885 < baseStart_1620885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620887 : List Nat := [1, 1, 3, 3, 1, 2, 5, 2, 4]
def baseStart_1620887 : Nat := 118140960795 + 1620887 * 2 ^ 59
def prefixEnd_1620887 : Nat := 4983230072969 + 3 ^ 40 * 1620887 * 2
def baseEnd_1620887 : Nat := 184954248360956667968485

theorem tailTrace_1620887 : CollatzResearch.WordTrace tailWord_1620887 prefixEnd_1620887 184954248360956667968485 := by
  unfold tailWord_1620887
  simp only [CollatzResearch.WordTrace]
  refine ⟨59118605678810699305508915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39412403785873799537005943 59118605678810699305508915)
  ·
    refine ⟨88677908518216048958263373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59118605678810699305508915 88677908518216048958263373)
    ·
      refine ⟨33254215694331018359348765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88677908518216048958263373 33254215694331018359348765)
      ·
        refine ⟨12470330885374131884755787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33254215694331018359348765 12470330885374131884755787)
        ·
          refine ⟨18705496328061197827133681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12470330885374131884755787 18705496328061197827133681)
          ·
            refine ⟨14029122246045898370350261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18705496328061197827133681 14029122246045898370350261)
            ·
              refine ⟨1315230210566802972220337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14029122246045898370350261 1315230210566802972220337)
              ·
                refine ⟨986422657925102229165253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315230210566802972220337 986422657925102229165253)
                ·
                  refine ⟨184954248360956667968485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986422657925102229165253 184954248360956667968485)
                  ·
                    rfl

theorem cell22_1620887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 5, 2, 4].length) (baseStart_1620887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620887 prefixEnd_1620887 := by exact prefixLift 1620887
  have htrace : WordTrace (prefixWord ++ tailWord_1620887) baseStart_1620887 baseEnd_1620887 := by
    simpa [prefixWord, tailWord_1620887, baseEnd_1620887] using wordTrace_append hprefix tailTrace_1620887
  have hstable : (prefixWord ++ tailWord_1620887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620887).length < 2 ^ (prefixWord ++ tailWord_1620887).sum := by decide
  have hdescent : baseEnd_1620887 < baseStart_1620887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620932 : List Nat := [2, 3, 3, 3, 2, 9]
def baseStart_1620932 : Nat := 118140960795 + 1620932 * 2 ^ 59
def prefixEnd_1620932 : Nat := 4983230072969 + 3 ^ 40 * 1620932 * 2
def baseEnd_1620932 : Nat := 6850347524722282549757

theorem tailTrace_1620932 : CollatzResearch.WordTrace tailWord_1620932 prefixEnd_1620932 6850347524722282549757 := by
  unfold tailWord_1620932
  simp only [CollatzResearch.WordTrace]
  refine ⟨29560123481823835995448525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39413497975765114660598033 29560123481823835995448525)
  ·
    refine ⟨11085046305683938498293197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29560123481823835995448525 11085046305683938498293197)
    ·
      refine ⟨4156892364631476936859949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11085046305683938498293197 4156892364631476936859949)
      ·
        refine ⟨1558834636736803851322481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4156892364631476936859949 1558834636736803851322481)
        ·
          refine ⟨1169125977552602888491861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1558834636736803851322481 1169125977552602888491861)
          ·
            refine ⟨6850347524722282549757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1169125977552602888491861 6850347524722282549757)
            ·
              rfl

theorem cell22_1620932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 9].length) (baseStart_1620932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620932 prefixEnd_1620932 := by exact prefixLift 1620932
  have htrace : WordTrace (prefixWord ++ tailWord_1620932) baseStart_1620932 baseEnd_1620932 := by
    simpa [prefixWord, tailWord_1620932, baseEnd_1620932] using wordTrace_append hprefix tailTrace_1620932
  have hstable : (prefixWord ++ tailWord_1620932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620932).length < 2 ^ (prefixWord ++ tailWord_1620932).sum := by decide
  have hdescent : baseEnd_1620932 < baseStart_1620932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1620994 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1620994 : Nat := 118140960795 + 1620994 * 2 ^ 59
def prefixEnd_1620994 : Nat := 4983230072969 + 3 ^ 40 * 1620994 * 2
def baseEnd_1620994 : Nat := 184966457789852463826709

theorem tailTrace_1620994 : CollatzResearch.WordTrace tailWord_1620994 prefixEnd_1620994 184966457789852463826709 := by
  unfold tailWord_1620994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14780627072355764144913509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39415005526282037719769357 14780627072355764144913509)
  ·
    refine ⟨2771367576066705777171283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14780627072355764144913509 2771367576066705777171283)
    ·
      refine ⟨4157051364100058665756925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771367576066705777171283 4157051364100058665756925)
      ·
        refine ⟨1558894261537521999658847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4157051364100058665756925 1558894261537521999658847)
        ·
          refine ⟨2338341392306282999488271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558894261537521999658847 2338341392306282999488271)
          ·
            refine ⟨3507512088459424499232407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338341392306282999488271 3507512088459424499232407)
            ·
              refine ⟨5261268132689136748848611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507512088459424499232407 5261268132689136748848611)
              ·
                refine ⟨7891902199033705123272917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261268132689136748848611 7891902199033705123272917)
                ·
                  refine ⟨184966457789852463826709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7891902199033705123272917 184966457789852463826709)
                  ·
                    rfl

theorem cell22_1620994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1620994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1620994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1620994 prefixEnd_1620994 := by exact prefixLift 1620994
  have htrace : WordTrace (prefixWord ++ tailWord_1620994) baseStart_1620994 baseEnd_1620994 := by
    simpa [prefixWord, tailWord_1620994, baseEnd_1620994] using wordTrace_append hprefix tailTrace_1620994
  have hstable : (prefixWord ++ tailWord_1620994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1620994).length < 2 ^ (prefixWord ++ tailWord_1620994).sum := by decide
  have hdescent : baseEnd_1620994 < baseStart_1620994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1620994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621035 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 2, 4]
def baseStart_1621035 : Nat := 118140960795 + 1621035 * 2 ^ 59
def prefixEnd_1621035 : Nat := 4983230072969 + 3 ^ 40 * 1621035 * 2
def baseEnd_1621035 : Nat := 554913408507446951205001

theorem tailTrace_1621035 : CollatzResearch.WordTrace tailWord_1621035 prefixEnd_1621035 554913408507446951205001 := by
  unfold tailWord_1621035
  simp only [CollatzResearch.WordTrace]
  refine ⟨59124003682274520581896559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39416002454849680387931039 59124003682274520581896559)
  ·
    refine ⟨88686005523411780872844839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59124003682274520581896559 88686005523411780872844839)
    ·
      refine ⟨133029008285117671309267259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88686005523411780872844839 133029008285117671309267259)
      ·
        refine ⟨199543512427676506963900889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133029008285117671309267259 199543512427676506963900889)
        ·
          refine ⟨149657634320757380222925667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199543512427676506963900889 149657634320757380222925667)
          ·
            refine ⟨224486451481136070334388501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149657634320757380222925667 224486451481136070334388501)
            ·
              refine ⟨10522802413178253296924461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224486451481136070334388501 10522802413178253296924461)
              ·
                refine ⟨3946050904941844986346673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10522802413178253296924461 3946050904941844986346673)
                ·
                  refine ⟨2959538178706383739760005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946050904941844986346673 2959538178706383739760005)
                  ·
                    refine ⟨554913408507446951205001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959538178706383739760005 554913408507446951205001)
                    ·
                      rfl

theorem cell22_1621035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 4].length) (baseStart_1621035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621035 prefixEnd_1621035 := by exact prefixLift 1621035
  have htrace : WordTrace (prefixWord ++ tailWord_1621035) baseStart_1621035 baseEnd_1621035 := by
    simpa [prefixWord, tailWord_1621035, baseEnd_1621035] using wordTrace_append hprefix tailTrace_1621035
  have hstable : (prefixWord ++ tailWord_1621035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621035).length < 2 ^ (prefixWord ++ tailWord_1621035).sum := by decide
  have hdescent : baseEnd_1621035 < baseStart_1621035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621052 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_1621052 : Nat := 118140960795 + 1621052 * 2 ^ 59
def prefixEnd_1621052 : Nat := 4983230072969 + 3 ^ 40 * 1621052 * 2
def baseEnd_1621052 : Nat := 554919227954864573529949

theorem tailTrace_1621052 : CollatzResearch.WordTrace tailWord_1621052 prefixEnd_1621052 554919227954864573529949 := by
  unfold tailWord_1621052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29562311861606466242632705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39416415815475288323510273 29562311861606466242632705)
  ·
    refine ⟨22171733896204849681974529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29562311861606466242632705 22171733896204849681974529)
    ·
      refine ⟨16628800422153637261480897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22171733896204849681974529 16628800422153637261480897)
      ·
        refine ⟨12471600316615227946110673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16628800422153637261480897 12471600316615227946110673)
        ·
          refine ⟨9353700237461420959583005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12471600316615227946110673 9353700237461420959583005)
          ·
            refine ⟨3507637589048032859843627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9353700237461420959583005 3507637589048032859843627)
            ·
              refine ⟨5261456383572049289765441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507637589048032859843627 5261456383572049289765441)
              ·
                refine ⟨3946092287679036967324081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261456383572049289765441 3946092287679036967324081)
                ·
                  refine ⟨2959569215759277725493061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946092287679036967324081 2959569215759277725493061)
                  ·
                    refine ⟨554919227954864573529949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959569215759277725493061 554919227954864573529949)
                    ·
                      rfl

theorem cell22_1621052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_1621052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621052 prefixEnd_1621052 := by exact prefixLift 1621052
  have htrace : WordTrace (prefixWord ++ tailWord_1621052) baseStart_1621052 baseEnd_1621052 := by
    simpa [prefixWord, tailWord_1621052, baseEnd_1621052] using wordTrace_append hprefix tailTrace_1621052
  have hstable : (prefixWord ++ tailWord_1621052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621052).length < 2 ^ (prefixWord ++ tailWord_1621052).sum := by decide
  have hdescent : baseEnd_1621052 < baseStart_1621052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621054 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1621054 : Nat := 118140960795 + 1621054 * 2 ^ 59
def prefixEnd_1621054 : Nat := 4983230072969 + 3 ^ 40 * 1621054 * 2
def baseEnd_1621054 : Nat := 554919912595737234979943

theorem tailTrace_1621054 : CollatzResearch.WordTrace tailWord_1621054 prefixEnd_1621054 554919912595737234979943 := by
  unfold tailWord_1621054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390587083650710853354777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39416464446137124551225477 7390587083650710853354777)
  ·
    refine ⟨5542940312738033140016083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7390587083650710853354777 5542940312738033140016083)
    ·
      refine ⟨8314410469107049710024125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5542940312738033140016083 8314410469107049710024125)
      ·
        refine ⟨3117903925915143641259047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8314410469107049710024125 3117903925915143641259047)
        ·
          refine ⟨4676855888872715461888571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117903925915143641259047 4676855888872715461888571)
          ·
            refine ⟨7015283833309073192832857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676855888872715461888571 7015283833309073192832857)
            ·
              refine ⟨5261462874981804894624643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7015283833309073192832857 5261462874981804894624643)
              ·
                refine ⟨7892194312472707341936965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261462874981804894624643 7892194312472707341936965)
                ·
                  refine ⟨1479786433588632626613181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7892194312472707341936965 1479786433588632626613181)
                  ·
                    refine ⟨554919912595737234979943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479786433588632626613181 554919912595737234979943)
                    ·
                      rfl

theorem cell22_1621054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1621054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621054 prefixEnd_1621054 := by exact prefixLift 1621054
  have htrace : WordTrace (prefixWord ++ tailWord_1621054) baseStart_1621054 baseEnd_1621054 := by
    simpa [prefixWord, tailWord_1621054, baseEnd_1621054] using wordTrace_append hprefix tailTrace_1621054
  have hstable : (prefixWord ++ tailWord_1621054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621054).length < 2 ^ (prefixWord ++ tailWord_1621054).sum := by decide
  have hdescent : baseEnd_1621054 < baseStart_1621054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621086 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1621086 : Nat := 118140960795 + 1621086 * 2 ^ 59
def prefixEnd_1621086 : Nat := 4983230072969 + 3 ^ 40 * 1621086 * 2
def baseEnd_1621086 : Nat := 554930866849699818179845

theorem tailTrace_1621086 : CollatzResearch.WordTrace tailWord_1621086 prefixEnd_1621086 554930866849699818179845 := by
  unfold tailWord_1621086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390732975636219536500389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39417242536726504194668741 7390732975636219536500389)
  ·
    refine ⟨1385762432931791163093823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7390732975636219536500389 1385762432931791163093823)
    ·
      refine ⟨2078643649397686744640735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385762432931791163093823 2078643649397686744640735)
      ·
        refine ⟨3117965474096530116961103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2078643649397686744640735 3117965474096530116961103)
        ·
          refine ⟨4676948211144795175441655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117965474096530116961103 4676948211144795175441655)
          ·
            refine ⟨7015422316717192763162483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676948211144795175441655 7015422316717192763162483)
            ·
              refine ⟨10523133475075789144743725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015422316717192763162483 10523133475075789144743725)
              ·
                refine ⟨3946175053153420929278897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10523133475075789144743725 3946175053153420929278897)
                ·
                  refine ⟨2959631289865065696959173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946175053153420929278897 2959631289865065696959173)
                  ·
                    refine ⟨554930866849699818179845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2959631289865065696959173 554930866849699818179845)
                    ·
                      rfl

theorem cell22_1621086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1621086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621086 prefixEnd_1621086 := by exact prefixLift 1621086
  have htrace : WordTrace (prefixWord ++ tailWord_1621086) baseStart_1621086 baseEnd_1621086 := by
    simpa [prefixWord, tailWord_1621086, baseEnd_1621086] using wordTrace_append hprefix tailTrace_1621086
  have hstable : (prefixWord ++ tailWord_1621086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621086).length < 2 ^ (prefixWord ++ tailWord_1621086).sum := by decide
  have hdescent : baseEnd_1621086 < baseStart_1621086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621118 : List Nat := [4, 2, 4, 1, 1, 2, 1, 7]
def baseStart_1621118 : Nat := 118140960795 + 1621118 * 2 ^ 59
def prefixEnd_1621118 : Nat := 4983230072969 + 3 ^ 40 * 1621118 * 2
def baseEnd_1621118 : Nat := 61660202344851377931083

theorem tailTrace_1621118 : CollatzResearch.WordTrace tailWord_1621118 prefixEnd_1621118 61660202344851377931083 := by
  unfold tailWord_1621118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390878867621728219646001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39418020627315883838112005 7390878867621728219646001)
  ·
    refine ⟨5543159150716296164734501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7390878867621728219646001 5543159150716296164734501)
    ·
      refine ⟨1039342340759305530887719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5543159150716296164734501 1039342340759305530887719)
      ·
        refine ⟨1559013511138958296331579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039342340759305530887719 1559013511138958296331579)
        ·
          refine ⟨2338520266708437444497369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1559013511138958296331579 2338520266708437444497369)
          ·
            refine ⟨1753890200031328083373027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2338520266708437444497369 1753890200031328083373027)
            ·
              refine ⟨2630835300046992125059541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753890200031328083373027 2630835300046992125059541)
              ·
                refine ⟨61660202344851377931083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2630835300046992125059541 61660202344851377931083)
                ·
                  rfl

theorem cell22_1621118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_1621118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621118 prefixEnd_1621118 := by exact prefixLift 1621118
  have htrace : WordTrace (prefixWord ++ tailWord_1621118) baseStart_1621118 baseEnd_1621118 := by
    simpa [prefixWord, tailWord_1621118, baseEnd_1621118] using wordTrace_append hprefix tailTrace_1621118
  have hstable : (prefixWord ++ tailWord_1621118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621118).length < 2 ^ (prefixWord ++ tailWord_1621118).sum := by decide
  have hdescent : baseEnd_1621118 < baseStart_1621118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621202 : List Nat := [3, 2, 2, 2, 1, 1, 3, 8]
def baseStart_1621202 : Nat := 118140960795 + 1621202 * 2 ^ 59
def prefixEnd_1621202 : Nat := 4983230072969 + 3 ^ 40 * 1621202 * 2
def baseEnd_1621202 : Nat := 61663397335590464697721

theorem tailTrace_1621202 : CollatzResearch.WordTrace tailWord_1621202 prefixEnd_1621202 61663397335590464697721 := by
  unfold tailWord_1621202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782523668167377025806465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39420063115113005402150573 14782523668167377025806465)
  ·
    refine ⟨11086892751125532769354849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14782523668167377025806465 11086892751125532769354849)
    ·
      refine ⟨8315169563344149577016137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11086892751125532769354849 8315169563344149577016137)
      ·
        refine ⟨6236377172508112182762103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8315169563344149577016137 6236377172508112182762103)
        ·
          refine ⟨9354565758762168274143155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6236377172508112182762103 9354565758762168274143155)
          ·
            refine ⟨14031848638143252411214733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354565758762168274143155 14031848638143252411214733)
            ·
              refine ⟨5261943239303719654205525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14031848638143252411214733 5261943239303719654205525)
              ·
                refine ⟨61663397335590464697721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5261943239303719654205525 61663397335590464697721)
                ·
                  rfl

theorem cell22_1621202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 8].length) (baseStart_1621202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621202 prefixEnd_1621202 := by exact prefixLift 1621202
  have htrace : WordTrace (prefixWord ++ tailWord_1621202) baseStart_1621202 baseEnd_1621202 := by
    simpa [prefixWord, tailWord_1621202, baseEnd_1621202] using wordTrace_append hprefix tailTrace_1621202
  have hstable : (prefixWord ++ tailWord_1621202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621202).length < 2 ^ (prefixWord ++ tailWord_1621202).sum := by decide
  have hdescent : baseEnd_1621202 < baseStart_1621202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621208 : List Nat := [2, 1, 2, 2, 6, 1, 1, 3, 4]
def baseStart_1621208 : Nat := 118140960795 + 1621208 * 2 ^ 59
def prefixEnd_1621208 : Nat := 4983230072969 + 3 ^ 40 * 1621208 * 2
def baseEnd_1621208 : Nat := 184990876647644055543157

theorem tailTrace_1621208 : CollatzResearch.WordTrace tailWord_1621208 prefixEnd_1621208 184990876647644055543157 := by
  unfold tailWord_1621208
  simp only [CollatzResearch.WordTrace]
  refine ⟨29565156755323885563972139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39420209007098514085296185 29565156755323885563972139)
  ·
    refine ⟨44347735132985828345958209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29565156755323885563972139 44347735132985828345958209)
    ·
      refine ⟨33260801349739371259468657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44347735132985828345958209 33260801349739371259468657)
      ·
        refine ⟨24945601012304528444601493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33260801349739371259468657 24945601012304528444601493)
        ·
          refine ⟨1169325047451774770840695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24945601012304528444601493 1169325047451774770840695)
          ·
            refine ⟨1753987571177662156261043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169325047451774770840695 1753987571177662156261043)
            ·
              refine ⟨2630981356766493234391565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1753987571177662156261043 2630981356766493234391565)
              ·
                refine ⟨986618008787434962896837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2630981356766493234391565 986618008787434962896837)
                ·
                  refine ⟨184990876647644055543157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986618008787434962896837 184990876647644055543157)
                  ·
                    rfl

theorem cell22_1621208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 3, 4].length) (baseStart_1621208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621208 prefixEnd_1621208 := by exact prefixLift 1621208
  have htrace : WordTrace (prefixWord ++ tailWord_1621208) baseStart_1621208 baseEnd_1621208 := by
    simpa [prefixWord, tailWord_1621208, baseEnd_1621208] using wordTrace_append hprefix tailTrace_1621208
  have hstable : (prefixWord ++ tailWord_1621208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621208).length < 2 ^ (prefixWord ++ tailWord_1621208).sum := by decide
  have hdescent : baseEnd_1621208 < baseStart_1621208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621285 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 1, 3]
def baseStart_1621285 : Nat := 118140960795 + 1621285 * 2 ^ 59
def prefixEnd_1621285 : Nat := 4983230072969 + 3 ^ 40 * 1621285 * 2
def baseEnd_1621285 : Nat := 554998988616529632454235

theorem tailTrace_1621285 : CollatzResearch.WordTrace tailWord_1621285 prefixEnd_1621285 554998988616529632454235 := by
  unfold tailWord_1621285
  simp only [CollatzResearch.WordTrace]
  refine ⟨59133121931368813278497309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39422081287579208852331539 59133121931368813278497309)
  ·
    refine ⟨22174920724263304979436491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59133121931368813278497309 22174920724263304979436491)
    ·
      refine ⟨33262381086394957469154737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22174920724263304979436491 33262381086394957469154737)
      ·
        refine ⟨24946785814796218101866053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33262381086394957469154737 24946785814796218101866053)
        ·
          refine ⟨4677522340274290894099885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24946785814796218101866053 4677522340274290894099885)
          ·
            refine ⟨1754070877602859085287457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4677522340274290894099885 1754070877602859085287457)
            ·
              refine ⟨1315553158202144313965593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754070877602859085287457 1315553158202144313965593)
              ·
                refine ⟨986664868651608235474195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1315553158202144313965593 986664868651608235474195)
                ·
                  refine ⟨1479997302977412353211293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986664868651608235474195 1479997302977412353211293)
                  ·
                    refine ⟨554998988616529632454235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479997302977412353211293 554998988616529632454235)
                    ·
                      rfl

theorem cell22_1621285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_1621285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621285 prefixEnd_1621285 := by exact prefixLift 1621285
  have htrace : WordTrace (prefixWord ++ tailWord_1621285) baseStart_1621285 baseEnd_1621285 := by
    simpa [prefixWord, tailWord_1621285, baseEnd_1621285] using wordTrace_append hprefix tailTrace_1621285
  have hstable : (prefixWord ++ tailWord_1621285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621285).length < 2 ^ (prefixWord ++ tailWord_1621285).sum := by decide
  have hdescent : baseEnd_1621285 < baseStart_1621285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621292 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 6]
def baseStart_1621292 : Nat := 118140960795 + 1621292 * 2 ^ 59
def prefixEnd_1621292 : Nat := 4983230072969 + 3 ^ 40 * 1621292 * 2
def baseEnd_1621292 : Nat := 185000461619861315843071

theorem tailTrace_1621292 : CollatzResearch.WordTrace tailWord_1621292 prefixEnd_1621292 185000461619861315843071 := by
  unfold tailWord_1621292
  simp only [CollatzResearch.WordTrace]
  refine ⟨29566688621171726737001065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39422251494895635649334753 29566688621171726737001065)
  ·
    refine ⟨22175016465878795052750799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29566688621171726737001065 22175016465878795052750799)
    ·
      refine ⟨33262524698818192579126199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22175016465878795052750799 33262524698818192579126199)
      ·
        refine ⟨49893787048227288868689299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33262524698818192579126199 49893787048227288868689299)
        ·
          refine ⟨74840680572340933303033949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49893787048227288868689299 74840680572340933303033949)
          ·
            refine ⟨28065255214627849988637731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74840680572340933303033949 28065255214627849988637731)
            ·
              refine ⟨42097882821941774982956597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28065255214627849988637731 42097882821941774982956597)
              ·
                refine ⟨3946676514557041404652181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42097882821941774982956597 3946676514557041404652181)
                ·
                  refine ⟨185000461619861315843071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3946676514557041404652181 185000461619861315843071)
                  ·
                    rfl

theorem cell22_1621292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_1621292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621292 prefixEnd_1621292 := by exact prefixLift 1621292
  have htrace : WordTrace (prefixWord ++ tailWord_1621292) baseStart_1621292 baseEnd_1621292 := by
    simpa [prefixWord, tailWord_1621292, baseEnd_1621292] using wordTrace_append hprefix tailTrace_1621292
  have hstable : (prefixWord ++ tailWord_1621292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621292).length < 2 ^ (prefixWord ++ tailWord_1621292).sum := by decide
  have hdescent : baseEnd_1621292 < baseStart_1621292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621324 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_1621324 : Nat := 118140960795 + 1621324 * 2 ^ 59
def prefixEnd_1621324 : Nat := 4983230072969 + 3 ^ 40 * 1621324 * 2
def baseEnd_1621324 : Nat := 555012339113546530729115

theorem tailTrace_1621324 : CollatzResearch.WordTrace tailWord_1621324 prefixEnd_1621324 555012339113546530729115 := by
  unfold tailWord_1621324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29567272189113761469583513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39423029585485015292778017 29567272189113761469583513)
  ·
    refine ⟨22175454141835321102187635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29567272189113761469583513 22175454141835321102187635)
    ·
      refine ⟨33263181212752981653281453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22175454141835321102187635 33263181212752981653281453)
      ·
        refine ⟨12473692954782368119980545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33263181212752981653281453 12473692954782368119980545)
        ·
          refine ⟨9355269716086776089985409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12473692954782368119980545 9355269716086776089985409)
          ·
            refine ⟨7016452287065082067489057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9355269716086776089985409 7016452287065082067489057)
            ·
              refine ⟨5262339215298811550616793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7016452287065082067489057 5262339215298811550616793)
              ·
                refine ⟨3946754411474108662962595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5262339215298811550616793 3946754411474108662962595)
                ·
                  refine ⟨5920131617211162994443893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946754411474108662962595 5920131617211162994443893)
                  ·
                    refine ⟨555012339113546530729115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5920131617211162994443893 555012339113546530729115)
                    ·
                      rfl

theorem cell22_1621324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_1621324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621324 prefixEnd_1621324 := by exact prefixLift 1621324
  have htrace : WordTrace (prefixWord ++ tailWord_1621324) baseStart_1621324 baseEnd_1621324 := by
    simpa [prefixWord, tailWord_1621324, baseEnd_1621324] using wordTrace_append hprefix tailTrace_1621324
  have hstable : (prefixWord ++ tailWord_1621324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621324).length < 2 ^ (prefixWord ++ tailWord_1621324).sum := by decide
  have hdescent : baseEnd_1621324 < baseStart_1621324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621326 : List Nat := [4, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_1621326 : Nat := 118140960795 + 1621326 * 2 ^ 59
def prefixEnd_1621326 : Nat := 4983230072969 + 3 ^ 40 * 1621326 * 2
def baseEnd_1621326 : Nat := 185004341251473064059703

theorem tailTrace_1621326 : CollatzResearch.WordTrace tailWord_1621326 prefixEnd_1621326 185004341251473064059703 := by
  unfold tailWord_1621326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391827165527534660092479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39423078216146851520493221 7391827165527534660092479)
  ·
    refine ⟨11087740748291301990138719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7391827165527534660092479 11087740748291301990138719)
    ·
      refine ⟨16631611122436952985208079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11087740748291301990138719 16631611122436952985208079)
      ·
        refine ⟨24947416683655429477812119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16631611122436952985208079 24947416683655429477812119)
        ·
          refine ⟨37421125025483144216718179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24947416683655429477812119 37421125025483144216718179)
          ·
            refine ⟨56131687538224716325077269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37421125025483144216718179 56131687538224716325077269)
            ·
              refine ⟨2631172853354283577737997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56131687538224716325077269 2631172853354283577737997)
              ·
                refine ⟨986689820007856341651749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631172853354283577737997 986689820007856341651749)
                ·
                  refine ⟨185004341251473064059703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986689820007856341651749 185004341251473064059703)
                  ·
                    rfl

theorem cell22_1621326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_1621326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621326 prefixEnd_1621326 := by exact prefixLift 1621326
  have htrace : WordTrace (prefixWord ++ tailWord_1621326) baseStart_1621326 baseEnd_1621326 := by
    simpa [prefixWord, tailWord_1621326, baseEnd_1621326] using wordTrace_append hprefix tailTrace_1621326
  have hstable : (prefixWord ++ tailWord_1621326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621326).length < 2 ^ (prefixWord ++ tailWord_1621326).sum := by decide
  have hdescent : baseEnd_1621326 < baseStart_1621326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621399 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 5]
def baseStart_1621399 : Nat := 118140960795 + 1621399 * 2 ^ 59
def prefixEnd_1621399 : Nat := 4983230072969 + 3 ^ 40 * 1621399 * 2
def baseEnd_1621399 : Nat := 185012671048757111701295

theorem tailTrace_1621399 : CollatzResearch.WordTrace tailWord_1621399 prefixEnd_1621399 185012671048757111701295 := by
  unfold tailWord_1621399
  simp only [CollatzResearch.WordTrace]
  refine ⟨59137279852955810748147251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39424853235303873832098167 59137279852955810748147251)
  ·
    refine ⟨88705919779433716122220877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59137279852955810748147251 88705919779433716122220877)
    ·
      refine ⟨33264719917287643545832829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88705919779433716122220877 33264719917287643545832829)
      ·
        refine ⟨12474269968982866329687311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33264719917287643545832829 12474269968982866329687311)
        ·
          refine ⟨18711404953474299494530967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12474269968982866329687311 18711404953474299494530967)
          ·
            refine ⟨28067107430211449241796451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18711404953474299494530967 28067107430211449241796451)
            ·
              refine ⟨42100661145317173862694677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28067107430211449241796451 42100661145317173862694677)
              ·
                refine ⟨1973468491186742524813813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42100661145317173862694677 1973468491186742524813813)
                ·
                  refine ⟨185012671048757111701295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1973468491186742524813813 185012671048757111701295)
                  ·
                    rfl

theorem cell22_1621399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 5].length) (baseStart_1621399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621399 prefixEnd_1621399 := by exact prefixLift 1621399
  have htrace : WordTrace (prefixWord ++ tailWord_1621399) baseStart_1621399 baseEnd_1621399 := by
    simpa [prefixWord, tailWord_1621399, baseEnd_1621399] using wordTrace_append hprefix tailTrace_1621399
  have hstable : (prefixWord ++ tailWord_1621399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621399).length < 2 ^ (prefixWord ++ tailWord_1621399).sum := by decide
  have hdescent : baseEnd_1621399 < baseStart_1621399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621493 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_1621493 : Nat := 118140960795 + 1621493 * 2 ^ 59
def prefixEnd_1621493 : Nat := 4983230072969 + 3 ^ 40 * 1621493 * 2
def baseEnd_1621493 : Nat := 555070191267286423253597

theorem tailTrace_1621493 : CollatzResearch.WordTrace tailWord_1621493 prefixEnd_1621493 555070191267286423253597 := by
  unfold tailWord_1621493
  simp only [CollatzResearch.WordTrace]
  refine ⟨59140708314615264802069133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39427138876410176534712755 59140708314615264802069133)
  ·
    refine ⟨22177765617980724300775925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59140708314615264802069133 22177765617980724300775925)
    ·
      refine ⟨2079165526685692903197743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22177765617980724300775925 2079165526685692903197743)
      ·
        refine ⟨3118748290028539354796615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079165526685692903197743 3118748290028539354796615)
        ·
          refine ⟨4678122435042809032194923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118748290028539354796615 4678122435042809032194923)
          ·
            refine ⟨7017183652564213548292385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678122435042809032194923 7017183652564213548292385)
            ·
              refine ⟨5262887739423160161219289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7017183652564213548292385 5262887739423160161219289)
              ·
                refine ⟨3947165804567370120914467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5262887739423160161219289 3947165804567370120914467)
                ·
                  refine ⟨5920748706851055181371701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947165804567370120914467 5920748706851055181371701)
                  ·
                    refine ⟨555070191267286423253597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5920748706851055181371701 555070191267286423253597)
                    ·
                      rfl

theorem cell22_1621493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_1621493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621493 prefixEnd_1621493 := by exact prefixLift 1621493
  have htrace : WordTrace (prefixWord ++ tailWord_1621493) baseStart_1621493 baseEnd_1621493 := by
    simpa [prefixWord, tailWord_1621493, baseEnd_1621493] using wordTrace_append hprefix tailTrace_1621493
  have hstable : (prefixWord ++ tailWord_1621493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621493).length < 2 ^ (prefixWord ++ tailWord_1621493).sum := by decide
  have hdescent : baseEnd_1621493 < baseStart_1621493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621538 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1621538 : Nat := 118140960795 + 1621538 * 2 ^ 59
def prefixEnd_1621538 : Nat := 4983230072969 + 3 ^ 40 * 1621538 * 2
def baseEnd_1621538 : Nat := 555085595686921305878459

theorem tailTrace_1621538 : CollatzResearch.WordTrace tailWord_1621538 prefixEnd_1621538 555085595686921305878459 := by
  unfold tailWord_1621538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14785587399863059371864317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39428233066301491658304845 14785587399863059371864317)
  ·
    refine ⟨5544595274948647264449119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14785587399863059371864317 5544595274948647264449119)
    ·
      refine ⟨8316892912422970896673679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5544595274948647264449119 8316892912422970896673679)
      ·
        refine ⟨12475339368634456345010519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8316892912422970896673679 12475339368634456345010519)
        ·
          refine ⟨18713009052951684517515779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475339368634456345010519 18713009052951684517515779)
          ·
            refine ⟨28069513579427526776273669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713009052951684517515779 28069513579427526776273669)
            ·
              refine ⟨5263033796142661270551313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28069513579427526776273669 5263033796142661270551313)
              ·
                refine ⟨3947275347106995952913485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263033796142661270551313 3947275347106995952913485)
                ·
                  refine ⟨1480228255165123482342557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3947275347106995952913485 1480228255165123482342557)
                  ·
                    refine ⟨555085595686921305878459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480228255165123482342557 555085595686921305878459)
                    ·
                      rfl

theorem cell22_1621538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1621538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621538 prefixEnd_1621538 := by exact prefixLift 1621538
  have htrace : WordTrace (prefixWord ++ tailWord_1621538) baseStart_1621538 baseEnd_1621538 := by
    simpa [prefixWord, tailWord_1621538, baseEnd_1621538] using wordTrace_append hprefix tailTrace_1621538
  have hstable : (prefixWord ++ tailWord_1621538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621538).length < 2 ^ (prefixWord ++ tailWord_1621538).sum := by decide
  have hdescent : baseEnd_1621538 < baseStart_1621538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621555 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 1, 3]
def baseStart_1621555 : Nat := 118140960795 + 1621555 * 2 ^ 59
def prefixEnd_1621555 : Nat := 4983230072969 + 3 ^ 40 * 1621555 * 2
def baseEnd_1621555 : Nat := 555091415134338928203407

theorem tailTrace_1621555 : CollatzResearch.WordTrace tailWord_1621555 prefixEnd_1621555 555091415134338928203407 := by
  unfold tailWord_1621555
  simp only [CollatzResearch.WordTrace]
  refine ⟨59142969640390649390826119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39428646426927099593884079 59142969640390649390826119)
  ·
    refine ⟨88714454460585974086239179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59142969640390649390826119 88714454460585974086239179)
    ·
      refine ⟨133071681690878961129358769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88714454460585974086239179 133071681690878961129358769)
      ·
        refine ⟨99803761268159220847019077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133071681690878961129358769 99803761268159220847019077)
        ·
          refine ⟨18713205237779853908816077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99803761268159220847019077 18713205237779853908816077)
          ·
            refine ⟨7017451964167445215806029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18713205237779853908816077 7017451964167445215806029)
            ·
              refine ⟨2631544486562791955927261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7017451964167445215806029 2631544486562791955927261)
              ·
                refine ⟨986829182461046983472723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631544486562791955927261 986829182461046983472723)
                ·
                  refine ⟨1480243773691570475209085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986829182461046983472723 1480243773691570475209085)
                  ·
                    refine ⟨555091415134338928203407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480243773691570475209085 555091415134338928203407)
                    ·
                      rfl

theorem cell22_1621555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 1, 3].length) (baseStart_1621555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621555 prefixEnd_1621555 := by exact prefixLift 1621555
  have htrace : WordTrace (prefixWord ++ tailWord_1621555) baseStart_1621555 baseEnd_1621555 := by
    simpa [prefixWord, tailWord_1621555, baseEnd_1621555] using wordTrace_append hprefix tailTrace_1621555
  have hstable : (prefixWord ++ tailWord_1621555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621555).length < 2 ^ (prefixWord ++ tailWord_1621555).sum := by decide
  have hdescent : baseEnd_1621555 < baseStart_1621555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621626 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 4, 4]
def baseStart_1621626 : Nat := 118140960795 + 1621626 * 2 ^ 59
def prefixEnd_1621626 : Nat := 4983230072969 + 3 ^ 40 * 1621626 * 2
def baseEnd_1621626 : Nat := 555115719885318409678189

theorem tailTrace_1621626 : CollatzResearch.WordTrace tailWord_1621626 prefixEnd_1621626 555115719885318409678189 := by
  unfold tailWord_1621626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786389805783357129165183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39430372815422285677773821 14786389805783357129165183)
  ·
    refine ⟨22179584708675035693747775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14786389805783357129165183 22179584708675035693747775)
    ·
      refine ⟨33269377063012553540621663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22179584708675035693747775 33269377063012553540621663)
      ·
        refine ⟨49904065594518830310932495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33269377063012553540621663 49904065594518830310932495)
        ·
          refine ⟨74856098391778245466398743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49904065594518830310932495 74856098391778245466398743)
          ·
            refine ⟨112284147587667368199598115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74856098391778245466398743 112284147587667368199598115)
            ·
              refine ⟨168426221381501052299397173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112284147587667368199598115 168426221381501052299397173)
              ·
                refine ⟨15789958254515723653068485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168426221381501052299397173 15789958254515723653068485)
                ·
                  refine ⟨2960617172721698184950341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15789958254515723653068485 2960617172721698184950341)
                  ·
                    refine ⟨555115719885318409678189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2960617172721698184950341 555115719885318409678189)
                    ·
                      rfl

theorem cell22_1621626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_1621626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621626 prefixEnd_1621626 := by exact prefixLift 1621626
  have htrace : WordTrace (prefixWord ++ tailWord_1621626) baseStart_1621626 baseEnd_1621626 := by
    simpa [prefixWord, tailWord_1621626, baseEnd_1621626] using wordTrace_append hprefix tailTrace_1621626
  have hstable : (prefixWord ++ tailWord_1621626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621626).length < 2 ^ (prefixWord ++ tailWord_1621626).sum := by decide
  have hdescent : baseEnd_1621626 < baseStart_1621626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621641 : List Nat := [1, 2, 1, 1, 4, 1, 5, 7]
def baseStart_1621641 : Nat := 118140960795 + 1621641 * 2 ^ 59
def prefixEnd_1621641 : Nat := 4983230072969 + 3 ^ 40 * 1621641 * 2
def baseEnd_1621641 : Nat := 61680094965762596728127

theorem tailTrace_1621641 : CollatzResearch.WordTrace tailWord_1621641 prefixEnd_1621641 61680094965762596728127 := by
  unfold tailWord_1621641
  simp only [CollatzResearch.WordTrace]
  refine ⟨59146106318079086078456777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39430737545386057385637851 59146106318079086078456777)
  ·
    refine ⟨44359579738559314558842583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59146106318079086078456777 44359579738559314558842583)
    ·
      refine ⟨66539369607838971838263875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44359579738559314558842583 66539369607838971838263875)
      ·
        refine ⟨99809054411758457757395813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66539369607838971838263875 99809054411758457757395813)
        ·
          refine ⟨18714197702204710829511715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99809054411758457757395813 18714197702204710829511715)
          ·
            refine ⟨28071296553307066244267573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18714197702204710829511715 28071296553307066244267573)
            ·
              refine ⟨2631684051872537460400085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28071296553307066244267573 2631684051872537460400085)
              ·
                refine ⟨61680094965762596728127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2631684051872537460400085 61680094965762596728127)
                ·
                  rfl

theorem cell22_1621641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 7].length) (baseStart_1621641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621641 prefixEnd_1621641 := by exact prefixLift 1621641
  have htrace : WordTrace (prefixWord ++ tailWord_1621641) baseStart_1621641 baseEnd_1621641 := by
    simpa [prefixWord, tailWord_1621641, baseEnd_1621641] using wordTrace_append hprefix tailTrace_1621641
  have hstable : (prefixWord ++ tailWord_1621641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621641).length < 2 ^ (prefixWord ++ tailWord_1621641).sum := by decide
  have hdescent : baseEnd_1621641 < baseStart_1621641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621666 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1621666 : Nat := 118140960795 + 1621666 * 2 ^ 59
def prefixEnd_1621666 : Nat := 4983230072969 + 3 ^ 40 * 1621666 * 2
def baseEnd_1621666 : Nat := 555129412702771638678067

theorem tailTrace_1621666 : CollatzResearch.WordTrace tailWord_1621666 prefixEnd_1621666 555129412702771638678067 := by
  unfold tailWord_1621666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786754535747128837029213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39431345428659010232077901 14786754535747128837029213)
  ·
    refine ⟨5545032950905173313885955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14786754535747128837029213 5545032950905173313885955)
    ·
      refine ⟨8317549426357759970828933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5545032950905173313885955 8317549426357759970828933)
      ·
        refine ⟨1559540517442079994530425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8317549426357759970828933 1559540517442079994530425)
        ·
          refine ⟨1169655388081559995897819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559540517442079994530425 1169655388081559995897819)
          ·
            refine ⟨1754483082122339993846729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169655388081559995897819 1754483082122339993846729)
            ·
              refine ⟨1315862311591754995385047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1754483082122339993846729 1315862311591754995385047)
              ·
                refine ⟨1973793467387632493077571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315862311591754995385047 1973793467387632493077571)
                ·
                  refine ⟨2960690201081448739616357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973793467387632493077571 2960690201081448739616357)
                  ·
                    refine ⟨555129412702771638678067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2960690201081448739616357 555129412702771638678067)
                    ·
                      rfl

theorem cell22_1621666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1621666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621666 prefixEnd_1621666 := by exact prefixLift 1621666
  have htrace : WordTrace (prefixWord ++ tailWord_1621666) baseStart_1621666 baseEnd_1621666 := by
    simpa [prefixWord, tailWord_1621666, baseEnd_1621666] using wordTrace_append hprefix tailTrace_1621666
  have hstable : (prefixWord ++ tailWord_1621666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621666).length < 2 ^ (prefixWord ++ tailWord_1621666).sum := by decide
  have hdescent : baseEnd_1621666 < baseStart_1621666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621690 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_1621690 : Nat := 118140960795 + 1621690 * 2 ^ 59
def prefixEnd_1621690 : Nat := 4983230072969 + 3 ^ 40 * 1621690 * 2
def baseEnd_1621690 : Nat := 555137628393243576077993

theorem tailTrace_1621690 : CollatzResearch.WordTrace tailWord_1621690 prefixEnd_1621690 555137628393243576077993 := by
  unfold tailWord_1621690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786973373725391861747631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39431928996601044964660349 14786973373725391861747631)
  ·
    refine ⟨22180460060588087792621447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14786973373725391861747631 22180460060588087792621447)
    ·
      refine ⟨33270690090882131688932171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22180460060588087792621447 33270690090882131688932171)
      ·
        refine ⟨49906035136323197533398257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33270690090882131688932171 49906035136323197533398257)
        ·
          refine ⟨37429526352242398150048693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49906035136323197533398257 37429526352242398150048693)
          ·
            refine ⟨3509018095522724826567065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37429526352242398150048693 3509018095522724826567065)
            ·
              refine ⟨2631763571642043619925299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509018095522724826567065 2631763571642043619925299)
              ·
                refine ⟨3947645357463065429887949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631763571642043619925299 3947645357463065429887949)
                ·
                  refine ⟨1480367009048649536207981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3947645357463065429887949 1480367009048649536207981)
                  ·
                    refine ⟨555137628393243576077993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480367009048649536207981 555137628393243576077993)
                    ·
                      rfl

theorem cell22_1621690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_1621690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621690 prefixEnd_1621690 := by exact prefixLift 1621690
  have htrace : WordTrace (prefixWord ++ tailWord_1621690) baseStart_1621690 baseEnd_1621690 := by
    simpa [prefixWord, tailWord_1621690, baseEnd_1621690] using wordTrace_append hprefix tailTrace_1621690
  have hstable : (prefixWord ++ tailWord_1621690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621690).length < 2 ^ (prefixWord ++ tailWord_1621690).sum := by decide
  have hdescent : baseEnd_1621690 < baseStart_1621690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621797 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 2, 3]
def baseStart_1621797 : Nat := 118140960795 + 1621797 * 2 ^ 59
def prefixEnd_1621797 : Nat := 4983230072969 + 3 ^ 40 * 1621797 * 2
def baseEnd_1621797 : Nat := 555174256679930963652665

theorem tailTrace_1621797 : CollatzResearch.WordTrace tailWord_1621797 prefixEnd_1621797 555174256679930963652665 := by
  unfold tailWord_1621797
  simp only [CollatzResearch.WordTrace]
  refine ⟨59151796105513924721135645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39434530737009283147423763 59151796105513924721135645)
  ·
    refine ⟨22181923539567721770425867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59151796105513924721135645 22181923539567721770425867)
    ·
      refine ⟨33272885309351582655638801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22181923539567721770425867 33272885309351582655638801)
      ·
        refine ⟨24954663982013686991729101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33272885309351582655638801 24954663982013686991729101)
        ·
          refine ⟨9357998993255132621898413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24954663982013686991729101 9357998993255132621898413)
          ·
            refine ⟨3509249622470674733211905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9357998993255132621898413 3509249622470674733211905)
            ·
              refine ⟨2631937216853006049908929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509249622470674733211905 2631937216853006049908929)
              ·
                refine ⟨1973952912639754537431697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631937216853006049908929 1973952912639754537431697)
                ·
                  refine ⟨1480464684479815903073773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973952912639754537431697 1480464684479815903073773)
                  ·
                    refine ⟨555174256679930963652665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480464684479815903073773 555174256679930963652665)
                    ·
                      rfl

theorem cell22_1621797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_1621797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621797 prefixEnd_1621797 := by exact prefixLift 1621797
  have htrace : WordTrace (prefixWord ++ tailWord_1621797) baseStart_1621797 baseEnd_1621797 := by
    simpa [prefixWord, tailWord_1621797, baseEnd_1621797] using wordTrace_append hprefix tailTrace_1621797
  have hstable : (prefixWord ++ tailWord_1621797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621797).length < 2 ^ (prefixWord ++ tailWord_1621797).sum := by decide
  have hdescent : baseEnd_1621797 < baseStart_1621797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621810 : List Nat := [3, 2, 1, 1, 3, 4, 1, 7]
def baseStart_1621810 : Nat := 118140960795 + 1621810 * 2 ^ 59
def prefixEnd_1621810 : Nat := 4983230072969 + 3 ^ 40 * 1621810 * 2
def baseEnd_1621810 : Nat := 61686522982844807008625

theorem tailTrace_1621810 : CollatzResearch.WordTrace tailWord_1621810 prefixEnd_1621810 61686522982844807008625 := by
  unfold tailWord_1621810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788067563616706985339721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39434846836311218627572589 14788067563616706985339721)
  ·
    refine ⟨11091050672712530239004791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14788067563616706985339721 11091050672712530239004791)
    ·
      refine ⟨16636576009068795358507187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11091050672712530239004791 16636576009068795358507187)
      ·
        refine ⟨24954864013603193037760781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16636576009068795358507187 24954864013603193037760781)
        ·
          refine ⟨9358074005101197389160293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24954864013603193037760781 9358074005101197389160293)
          ·
            refine ⟨1754638875956474510467555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9358074005101197389160293 1754638875956474510467555)
            ·
              refine ⟨2631958313934711765701333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754638875956474510467555 2631958313934711765701333)
              ·
                refine ⟨61686522982844807008625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2631958313934711765701333 61686522982844807008625)
                ·
                  rfl

theorem cell22_1621810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_1621810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621810 prefixEnd_1621810 := by exact prefixLift 1621810
  have htrace : WordTrace (prefixWord ++ tailWord_1621810) baseStart_1621810 baseEnd_1621810 := by
    simpa [prefixWord, tailWord_1621810, baseEnd_1621810] using wordTrace_append hprefix tailTrace_1621810
  have hstable : (prefixWord ++ tailWord_1621810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621810).length < 2 ^ (prefixWord ++ tailWord_1621810).sum := by decide
  have hdescent : baseEnd_1621810 < baseStart_1621810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621814 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1621814 : Nat := 118140960795 + 1621814 * 2 ^ 59
def prefixEnd_1621814 : Nat := 4983230072969 + 3 ^ 40 * 1621814 * 2
def baseEnd_1621814 : Nat := 555180076127348585977613

theorem tailTrace_1621814 : CollatzResearch.WordTrace tailWord_1621814 prefixEnd_1621814 555180076127348585977613 := by
  unfold tailWord_1621814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697026009153271039031531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39434944097634891083002997 3697026009153271039031531)
  ·
    refine ⟨5545539013729906558547297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3697026009153271039031531 5545539013729906558547297)
    ·
      refine ⟨4159154260297429918910473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5545539013729906558547297 4159154260297429918910473)
      ·
        refine ⟨3119365695223072439182855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4159154260297429918910473 3119365695223072439182855)
        ·
          refine ⟨4679048542834608658774283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119365695223072439182855 4679048542834608658774283)
          ·
            refine ⟨7018572814251912988161425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679048542834608658774283 7018572814251912988161425)
            ·
              refine ⟨5263929610688934741121069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7018572814251912988161425 5263929610688934741121069)
              ·
                refine ⟨1973973604008350527920401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5263929610688934741121069 1973973604008350527920401)
                ·
                  refine ⟨1480480203006262895940301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1973973604008350527920401 1480480203006262895940301)
                  ·
                    refine ⟨555180076127348585977613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480480203006262895940301 555180076127348585977613)
                    ·
                      rfl

theorem cell22_1621814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1621814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621814 prefixEnd_1621814 := by exact prefixLift 1621814
  have htrace : WordTrace (prefixWord ++ tailWord_1621814) baseStart_1621814 baseEnd_1621814 := by
    simpa [prefixWord, tailWord_1621814, baseEnd_1621814] using wordTrace_append hprefix tailTrace_1621814
  have hstable : (prefixWord ++ tailWord_1621814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621814).length < 2 ^ (prefixWord ++ tailWord_1621814).sum := by decide
  have hdescent : baseEnd_1621814 < baseStart_1621814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621855 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 5]
def baseStart_1621855 : Nat := 118140960795 + 1621855 * 2 ^ 59
def prefixEnd_1621855 : Nat := 4983230072969 + 3 ^ 40 * 1621855 * 2
def baseEnd_1621855 : Nat := 185064703755079381900829

theorem tailTrace_1621855 : CollatzResearch.WordTrace tailWord_1621855 prefixEnd_1621855 185064703755079381900829 := by
  unfold tailWord_1621855
  simp only [CollatzResearch.WordTrace]
  refine ⟨59153911539303800626747019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39435941026202533751164679 59153911539303800626747019)
  ·
    refine ⟨88730867308955700940120529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59153911539303800626747019 88730867308955700940120529)
    ·
      refine ⟨66548150481716775705090397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88730867308955700940120529 66548150481716775705090397)
      ·
        refine ⟨24955556430643790889408899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66548150481716775705090397 24955556430643790889408899)
        ·
          refine ⟨37433334645965686334113349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24955556430643790889408899 37433334645965686334113349)
          ·
            refine ⟨7018750246118566187646253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37433334645965686334113349 7018750246118566187646253)
            ·
              refine ⟨2632031342294462320367345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7018750246118566187646253 2632031342294462320367345)
              ·
                refine ⟨1974023506720846740275509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632031342294462320367345 1974023506720846740275509)
                ·
                  refine ⟨185064703755079381900829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1974023506720846740275509 185064703755079381900829)
                  ·
                    rfl

theorem cell22_1621855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 5].length) (baseStart_1621855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621855 prefixEnd_1621855 := by exact prefixLift 1621855
  have htrace : WordTrace (prefixWord ++ tailWord_1621855) baseStart_1621855 baseEnd_1621855 := by
    simpa [prefixWord, tailWord_1621855, baseEnd_1621855] using wordTrace_append hprefix tailTrace_1621855
  have hstable : (prefixWord ++ tailWord_1621855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621855).length < 2 ^ (prefixWord ++ tailWord_1621855).sum := by decide
  have hdescent : baseEnd_1621855 < baseStart_1621855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621910 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1621910 : Nat := 118140960795 + 1621910 * 2 ^ 59
def prefixEnd_1621910 : Nat := 4983230072969 + 3 ^ 40 * 1621910 * 2
def baseEnd_1621910 : Nat := 555212938889236335577319

theorem tailTrace_1621910 : CollatzResearch.WordTrace tailWord_1621910 prefixEnd_1621910 555212938889236335577319 := by
  unfold tailWord_1621910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697244847131534063749949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39437278369403030013332789 3697244847131534063749949)
  ·
    refine ⟨1386466817674325273906231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3697244847131534063749949 1386466817674325273906231)
    ·
      refine ⟨2079700226511487910859347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386466817674325273906231 2079700226511487910859347)
      ·
        refine ⟨3119550339767231866289021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079700226511487910859347 3119550339767231866289021)
        ·
          refine ⟨1169831377412711949858383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3119550339767231866289021 1169831377412711949858383)
          ·
            refine ⟨1754747066119067924787575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169831377412711949858383 1754747066119067924787575)
            ·
              refine ⟨2632120599178601887181363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754747066119067924787575 2632120599178601887181363)
              ·
                refine ⟨3948180898767902830772045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632120599178601887181363 3948180898767902830772045)
                ·
                  refine ⟨1480567837037963561539517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3948180898767902830772045 1480567837037963561539517)
                  ·
                    refine ⟨555212938889236335577319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480567837037963561539517 555212938889236335577319)
                    ·
                      rfl

theorem cell22_1621910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1621910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621910 prefixEnd_1621910 := by exact prefixLift 1621910
  have htrace : WordTrace (prefixWord ++ tailWord_1621910) baseStart_1621910 baseEnd_1621910 := by
    simpa [prefixWord, tailWord_1621910, baseEnd_1621910] using wordTrace_append hprefix tailTrace_1621910
  have hstable : (prefixWord ++ tailWord_1621910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621910).length < 2 ^ (prefixWord ++ tailWord_1621910).sum := by decide
  have hdescent : baseEnd_1621910 < baseStart_1621910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1621917 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 6]
def baseStart_1621917 : Nat := 118140960795 + 1621917 * 2 ^ 59
def prefixEnd_1621917 : Nat := 4983230072969 + 3 ^ 40 * 1621917 * 2
def baseEnd_1621917 : Nat := 185071778377430216884099

theorem tailTrace_1621917 : CollatzResearch.WordTrace tailWord_1621917 prefixEnd_1621917 185071778377430216884099 := by
  unfold tailWord_1621917
  simp only [CollatzResearch.WordTrace]
  refine ⟨59156172865079185215504005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39437448576719456810336003 59156172865079185215504005)
  ·
    refine ⟨11091782412202347227907001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59156172865079185215504005 11091782412202347227907001)
    ·
      refine ⟨8318836809151760420930251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11091782412202347227907001 8318836809151760420930251)
      ·
        refine ⟨12478255213727640631395377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318836809151760420930251 12478255213727640631395377)
        ·
          refine ⟨9358691410295730473546533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12478255213727640631395377 9358691410295730473546533)
          ·
            refine ⟨1754754639430449463789975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9358691410295730473546533 1754754639430449463789975)
            ·
              refine ⟨2632131959145674195684963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754754639430449463789975 2632131959145674195684963)
              ·
                refine ⟨3948197938718511293527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632131959145674195684963 3948197938718511293527445)
                ·
                  refine ⟨185071778377430216884099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3948197938718511293527445 185071778377430216884099)
                  ·
                    rfl

theorem cell22_1621917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 6].length) (baseStart_1621917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1621917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1621917 prefixEnd_1621917 := by exact prefixLift 1621917
  have htrace : WordTrace (prefixWord ++ tailWord_1621917) baseStart_1621917 baseEnd_1621917 := by
    simpa [prefixWord, tailWord_1621917, baseEnd_1621917] using wordTrace_append hprefix tailTrace_1621917
  have hstable : (prefixWord ++ tailWord_1621917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1621917).length < 2 ^ (prefixWord ++ tailWord_1621917).sum := by decide
  have hdescent : baseEnd_1621917 < baseStart_1621917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1621917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622035 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 6]
def baseStart_1622035 : Nat := 118140960795 + 1622035 * 2 ^ 59
def prefixEnd_1622035 : Nat := 4983230072969 + 3 ^ 40 * 1622035 * 2
def baseEnd_1622035 : Nat := 185085242981259225400645

theorem tailTrace_1622035 : CollatzResearch.WordTrace tailWord_1622035 prefixEnd_1622035 185085242981259225400645 := by
  unfold tailWord_1622035
  simp only [CollatzResearch.WordTrace]
  refine ⟨59160476678651691368299559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39440317785767794245533039 59160476678651691368299559)
  ·
    refine ⟨88740715017977537052449339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59160476678651691368299559 88740715017977537052449339)
    ·
      refine ⟨133111072526966305578674009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88740715017977537052449339 133111072526966305578674009)
      ·
        refine ⟨99833304395224729184005507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133111072526966305578674009 99833304395224729184005507)
        ·
          refine ⟨149749956592837093776008261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99833304395224729184005507 149749956592837093776008261)
          ·
            refine ⟨28078116861156955083001549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149749956592837093776008261 28078116861156955083001549)
            ·
              refine ⟨10529293822933858156125581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28078116861156955083001549 10529293822933858156125581)
              ·
                refine ⟨3948485183600196808547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10529293822933858156125581 3948485183600196808547093)
                ·
                  refine ⟨185085242981259225400645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3948485183600196808547093 185085242981259225400645)
                  ·
                    rfl

theorem cell22_1622035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 6].length) (baseStart_1622035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622035 prefixEnd_1622035 := by exact prefixLift 1622035
  have htrace : WordTrace (prefixWord ++ tailWord_1622035) baseStart_1622035 baseEnd_1622035 := by
    simpa [prefixWord, tailWord_1622035, baseEnd_1622035] using wordTrace_append hprefix tailTrace_1622035
  have hstable : (prefixWord ++ tailWord_1622035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622035).length < 2 ^ (prefixWord ++ tailWord_1622035).sum := by decide
  have hdescent : baseEnd_1622035 < baseStart_1622035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622067 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 4, 3]
def baseStart_1622067 : Nat := 118140960795 + 1622067 * 2 ^ 59
def prefixEnd_1622067 : Nat := 4983230072969 + 3 ^ 40 * 1622067 * 2
def baseEnd_1622067 : Nat := 555266683197740259401837

theorem tailTrace_1622067 : CollatzResearch.WordTrace tailWord_1622067 prefixEnd_1622067 555266683197740259401837 := by
  unfold tailWord_1622067
  simp only [CollatzResearch.WordTrace]
  refine ⟨59161643814535760833464455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39441095876357173888976303 59161643814535760833464455)
  ·
    refine ⟨88742465721803641250196683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59161643814535760833464455 88742465721803641250196683)
    ·
      refine ⟨133113698582705461875295025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88742465721803641250196683 133113698582705461875295025)
      ·
        refine ⟨99835273937029096406471269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133113698582705461875295025 99835273937029096406471269)
        ·
          refine ⟨18719113863192955576213363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99835273937029096406471269 18719113863192955576213363)
          ·
            refine ⟨28078670794789433364320045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18719113863192955576213363 28078670794789433364320045)
            ·
              refine ⟨10529501548046037511620017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28078670794789433364320045 10529501548046037511620017)
              ·
                refine ⟨7897126161034528133715013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10529501548046037511620017 7897126161034528133715013)
                ·
                  refine ⟨1480711155193974025071565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7897126161034528133715013 1480711155193974025071565)
                  ·
                    refine ⟨555266683197740259401837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480711155193974025071565 555266683197740259401837)
                    ·
                      rfl

theorem cell22_1622067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 4, 3].length) (baseStart_1622067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622067 prefixEnd_1622067 := by exact prefixLift 1622067
  have htrace : WordTrace (prefixWord ++ tailWord_1622067) baseStart_1622067 baseEnd_1622067 := by
    simpa [prefixWord, tailWord_1622067, baseEnd_1622067] using wordTrace_append hprefix tailTrace_1622067
  have hstable : (prefixWord ++ tailWord_1622067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622067).length < 2 ^ (prefixWord ++ tailWord_1622067).sum := by decide
  have hdescent : baseEnd_1622067 < baseStart_1622067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622069 : List Nat := [1, 3, 3, 1, 1, 1, 5, 3, 4]
def baseStart_1622069 : Nat := 118140960795 + 1622069 * 2 ^ 59
def prefixEnd_1622069 : Nat := 4983230072969 + 3 ^ 40 * 1622069 * 2
def baseEnd_1622069 : Nat := 185089122612870973617277

theorem tailTrace_1622069 : CollatzResearch.WordTrace tailWord_1622069 prefixEnd_1622069 185089122612870973617277 := by
  unfold tailWord_1622069
  simp only [CollatzResearch.WordTrace]
  refine ⟨59161716760528515175037261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39441144507019010116691507 59161716760528515175037261)
  ·
    refine ⟨22185643785198193190638973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59161716760528515175037261 22185643785198193190638973)
    ·
      refine ⟨8319616419449322446489615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22185643785198193190638973 8319616419449322446489615)
      ·
        refine ⟨12479424629173983669734423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8319616419449322446489615 12479424629173983669734423)
        ·
          refine ⟨18719136943760975504601635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12479424629173983669734423 18719136943760975504601635)
          ·
            refine ⟨28078705415641463256902453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18719136943760975504601635 28078705415641463256902453)
            ·
              refine ⟨2632378632716387180334605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28078705415641463256902453 2632378632716387180334605)
              ·
                refine ⟨987141987268645192625477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2632378632716387180334605 987141987268645192625477)
                ·
                  refine ⟨185089122612870973617277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987141987268645192625477 185089122612870973617277)
                  ·
                    rfl

theorem cell22_1622069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_1622069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622069 prefixEnd_1622069 := by exact prefixLift 1622069
  have htrace : WordTrace (prefixWord ++ tailWord_1622069) baseStart_1622069 baseEnd_1622069 := by
    simpa [prefixWord, tailWord_1622069, baseEnd_1622069] using wordTrace_append hprefix tailTrace_1622069
  have hstable : (prefixWord ++ tailWord_1622069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622069).length < 2 ^ (prefixWord ++ tailWord_1622069).sum := by decide
  have hdescent : baseEnd_1622069 < baseStart_1622069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622080 : List Nat := [2, 1, 1, 2, 2, 4, 10]
def baseStart_1622080 : Nat := 118140960795 + 1622080 * 2 ^ 59
def prefixEnd_1622080 : Nat := 4983230072969 + 3 ^ 40 * 1622080 * 2
def baseEnd_1622080 : Nat := 20565597531978242919511

theorem tailTrace_1622080 : CollatzResearch.WordTrace tailWord_1622080 prefixEnd_1622080 20565597531978242919511 := by
  unfold tailWord_1622080
  simp only [CollatzResearch.WordTrace]
  refine ⟨29581058981744332026843847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39441411975659109369125129 29581058981744332026843847)
  ·
    refine ⟨44371588472616498040265771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29581058981744332026843847 44371588472616498040265771)
    ·
      refine ⟨66557382708924747060398657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44371588472616498040265771 66557382708924747060398657)
      ·
        refine ⟨49918037031693560295298993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66557382708924747060398657 49918037031693560295298993)
        ·
          refine ⟨37438527773770170221474245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49918037031693560295298993 37438527773770170221474245)
          ·
            refine ⟨7019723957581906916526421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37438527773770170221474245 7019723957581906916526421)
            ·
              refine ⟨20565597531978242919511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7019723957581906916526421 20565597531978242919511)
              ·
                rfl

theorem cell22_1622080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 10].length) (baseStart_1622080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622080 prefixEnd_1622080 := by exact prefixLift 1622080
  have htrace : WordTrace (prefixWord ++ tailWord_1622080) baseStart_1622080 baseEnd_1622080 := by
    simpa [prefixWord, tailWord_1622080, baseEnd_1622080] using wordTrace_append hprefix tailTrace_1622080
  have hstable : (prefixWord ++ tailWord_1622080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622080).length < 2 ^ (prefixWord ++ tailWord_1622080).sum := by decide
  have hdescent : baseEnd_1622080 < baseStart_1622080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622101 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 2, 3]
def baseStart_1622101 : Nat := 118140960795 + 1622101 * 2 ^ 59
def prefixEnd_1622101 : Nat := 4983230072969 + 3 ^ 40 * 1622101 * 2
def baseEnd_1622101 : Nat := 555278322092575504051733

theorem tailTrace_1622101 : CollatzResearch.WordTrace tailWord_1622101 prefixEnd_1622101 555278322092575504051733 := by
  unfold tailWord_1622101
  simp only [CollatzResearch.WordTrace]
  refine ⟨59162883896412584640202157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39441922597608389760134771 59162883896412584640202157)
  ·
    refine ⟨22186081461154719240075809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59162883896412584640202157 22186081461154719240075809)
    ·
      refine ⟨16639561095866039430056857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22186081461154719240075809 16639561095866039430056857)
      ·
        refine ⟨12479670821899529572542643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16639561095866039430056857 12479670821899529572542643)
        ·
          refine ⟨18719506232849294358813965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12479670821899529572542643 18719506232849294358813965)
          ·
            refine ⟨7019814837318485384555237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18719506232849294358813965 7019814837318485384555237)
            ·
              refine ⟨1316215281997216009604107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7019814837318485384555237 1316215281997216009604107)
              ·
                refine ⟨1974322922995824014406161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316215281997216009604107 1974322922995824014406161)
                ·
                  refine ⟨1480742192246868010804621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974322922995824014406161 1480742192246868010804621)
                  ·
                    refine ⟨555278322092575504051733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480742192246868010804621 555278322092575504051733)
                    ·
                      rfl

theorem cell22_1622101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_1622101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622101 prefixEnd_1622101 := by exact prefixLift 1622101
  have htrace : WordTrace (prefixWord ++ tailWord_1622101) baseStart_1622101 baseEnd_1622101 := by
    simpa [prefixWord, tailWord_1622101, baseEnd_1622101] using wordTrace_append hprefix tailTrace_1622101
  have hstable : (prefixWord ++ tailWord_1622101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622101).length < 2 ^ (prefixWord ++ tailWord_1622101).sum := by decide
  have hdescent : baseEnd_1622101 < baseStart_1622101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622193 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 5]
def baseStart_1622193 : Nat := 118140960795 + 1622193 * 2 ^ 59
def prefixEnd_1622193 : Nat := 4983230072969 + 3 ^ 40 * 1622193 * 2
def baseEnd_1622193 : Nat := 185103271857572643583817

theorem tailTrace_1622193 : CollatzResearch.WordTrace tailWord_1622193 prefixEnd_1622193 185103271857572643583817 := by
  unfold tailWord_1622193
  simp only [CollatzResearch.WordTrace]
  refine ⟨59166239412079284352551233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39444159608052856235034155 59166239412079284352551233)
  ·
    refine ⟨44374679559059463264413425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59166239412079284352551233 44374679559059463264413425)
    ·
      refine ⟨33281009669294597448310069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44374679559059463264413425 33281009669294597448310069)
      ·
        refine ⟨3120094656496368510779069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33281009669294597448310069 3120094656496368510779069)
        ·
          refine ⟨1170035496186138191542151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3120094656496368510779069 1170035496186138191542151)
          ·
            refine ⟨1755053244279207287313227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170035496186138191542151 1755053244279207287313227)
            ·
              refine ⟨2632579866418810930969841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755053244279207287313227 2632579866418810930969841)
              ·
                refine ⟨1974434899814108198227381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632579866418810930969841 1974434899814108198227381)
                ·
                  refine ⟨185103271857572643583817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1974434899814108198227381 185103271857572643583817)
                  ·
                    rfl

theorem cell22_1622193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 5].length) (baseStart_1622193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622193 prefixEnd_1622193 := by exact prefixLift 1622193
  have htrace : WordTrace (prefixWord ++ tailWord_1622193) baseStart_1622193 baseEnd_1622193 := by
    simpa [prefixWord, tailWord_1622193, baseEnd_1622193] using wordTrace_append hprefix tailTrace_1622193
  have hstable : (prefixWord ++ tailWord_1622193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622193).length < 2 ^ (prefixWord ++ tailWord_1622193).sum := by decide
  have hdescent : baseEnd_1622193 < baseStart_1622193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622202 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 3, 5]
def baseStart_1622202 : Nat := 118140960795 + 1622202 * 2 ^ 59
def prefixEnd_1622202 : Nat := 4983230072969 + 3 ^ 40 * 1622202 * 2
def baseEnd_1622202 : Nat := 555312896456644907276423

theorem tailTrace_1622202 : CollatzResearch.WordTrace tailWord_1622202 prefixEnd_1622202 555312896456644907276423 := by
  unfold tailWord_1622202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14791641917261669722407215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39444378446031119259752573 14791641917261669722407215)
  ·
    refine ⟨22187462875892504583610823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14791641917261669722407215 22187462875892504583610823)
    ·
      refine ⟨33281194313838756875416235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187462875892504583610823 33281194313838756875416235)
      ·
        refine ⟨49921791470758135313124353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33281194313838756875416235 49921791470758135313124353)
        ·
          refine ⟨37441343603068601484843265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49921791470758135313124353 37441343603068601484843265)
          ·
            refine ⟨28081007702301451113632449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37441343603068601484843265 28081007702301451113632449)
            ·
              refine ⟨21060755776726088335224337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28081007702301451113632449 21060755776726088335224337)
              ·
                refine ⟨15795566832544566251418253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21060755776726088335224337 15795566832544566251418253)
                ·
                  refine ⟨5923337562204212344281845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15795566832544566251418253 5923337562204212344281845)
                  ·
                    refine ⟨555312896456644907276423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5923337562204212344281845 555312896456644907276423)
                    ·
                      rfl

theorem cell22_1622202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_1622202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622202 prefixEnd_1622202 := by exact prefixLift 1622202
  have htrace : WordTrace (prefixWord ++ tailWord_1622202) baseStart_1622202 baseEnd_1622202 := by
    simpa [prefixWord, tailWord_1622202, baseEnd_1622202] using wordTrace_append hprefix tailTrace_1622202
  have hstable : (prefixWord ++ tailWord_1622202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622202).length < 2 ^ (prefixWord ++ tailWord_1622202).sum := by decide
  have hdescent : baseEnd_1622202 < baseStart_1622202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622210 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1622210 : Nat := 118140960795 + 1622210 * 2 ^ 59
def prefixEnd_1622210 : Nat := 4983230072969 + 3 ^ 40 * 1622210 * 2
def baseEnd_1622210 : Nat := 185105211673378517692133

theorem tailTrace_1622210 : CollatzResearch.WordTrace tailWord_1622210 prefixEnd_1622210 185105211673378517692133 := by
  unfold tailWord_1622210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14791714863254424063980021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39444572968678464170613389 14791714863254424063980021)
  ·
    refine ⟨1386723268430102255998127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14791714863254424063980021 1386723268430102255998127)
    ·
      refine ⟨2080084902645153383997191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386723268430102255998127 2080084902645153383997191)
      ·
        refine ⟨3120127353967730075995787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080084902645153383997191 3120127353967730075995787)
        ·
          refine ⟨4680191030951595113993681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120127353967730075995787 4680191030951595113993681)
          ·
            refine ⟨3510143273213696335495261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4680191030951595113993681 3510143273213696335495261)
            ·
              refine ⟨1316303727455136125810723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510143273213696335495261 1316303727455136125810723)
              ·
                refine ⟨1974455591182704188716085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316303727455136125810723 1974455591182704188716085)
                ·
                  refine ⟨185105211673378517692133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1974455591182704188716085 185105211673378517692133)
                  ·
                    rfl

theorem cell22_1622210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1622210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622210 prefixEnd_1622210 := by exact prefixLift 1622210
  have htrace : WordTrace (prefixWord ++ tailWord_1622210) baseStart_1622210 baseEnd_1622210 := by
    simpa [prefixWord, tailWord_1622210, baseEnd_1622210] using wordTrace_append hprefix tailTrace_1622210
  have hstable : (prefixWord ++ tailWord_1622210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622210).length < 2 ^ (prefixWord ++ tailWord_1622210).sum := by decide
  have hdescent : baseEnd_1622210 < baseStart_1622210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622217 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 6, 4]
def baseStart_1622217 : Nat := 118140960795 + 1622217 * 2 ^ 59
def prefixEnd_1622217 : Nat := 4983230072969 + 3 ^ 40 * 1622217 * 2
def baseEnd_1622217 : Nat := 555318031263189868151377

theorem tailTrace_1622217 : CollatzResearch.WordTrace tailWord_1622217 prefixEnd_1622217 555318031263189868151377 := by
  unfold tailWord_1622217
  simp only [CollatzResearch.WordTrace]
  refine ⟨59167114763992336451424905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39444743175994890967616603 59167114763992336451424905)
  ·
    refine ⟨44375336072994252338568679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59167114763992336451424905 44375336072994252338568679)
    ·
      refine ⟨66563004109491378507853019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44375336072994252338568679 66563004109491378507853019)
      ·
        refine ⟨99844506164237067761779529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66563004109491378507853019 99844506164237067761779529)
        ·
          refine ⟨74883379623177800821334647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99844506164237067761779529 74883379623177800821334647)
          ·
            refine ⟨112325069434766701232001971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74883379623177800821334647 112325069434766701232001971)
            ·
              refine ⟨168487604152150051848002957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112325069434766701232001971 168487604152150051848002957)
              ·
                refine ⟨63182851557056269443001109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168487604152150051848002957 63182851557056269443001109)
                ·
                  refine ⟨2961696166737012630140677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63182851557056269443001109 2961696166737012630140677)
                  ·
                    refine ⟨555318031263189868151377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961696166737012630140677 555318031263189868151377)
                    ·
                      rfl

theorem cell22_1622217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_1622217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622217 prefixEnd_1622217 := by exact prefixLift 1622217
  have htrace : WordTrace (prefixWord ++ tailWord_1622217) baseStart_1622217 baseEnd_1622217 := by
    simpa [prefixWord, tailWord_1622217, baseEnd_1622217] using wordTrace_append hprefix tailTrace_1622217
  have hstable : (prefixWord ++ tailWord_1622217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622217).length < 2 ^ (prefixWord ++ tailWord_1622217).sum := by decide
  have hdescent : baseEnd_1622217 < baseStart_1622217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622277 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 9]
def baseStart_1622277 : Nat := 118140960795 + 1622277 * 2 ^ 59
def prefixEnd_1622277 : Nat := 4983230072969 + 3 ^ 40 * 1622277 * 2
def baseEnd_1622277 : Nat := 185112856829789903883731

theorem tailTrace_1622277 : CollatzResearch.WordTrace tailWord_1622277 prefixEnd_1622277 185112856829789903883731 := by
  unfold tailWord_1622277
  simp only [CollatzResearch.WordTrace]
  refine ⟨59169303143774966698609085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39446202095849977799072723 59169303143774966698609085)
  ·
    refine ⟨22188488678915612511978407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59169303143774966698609085 22188488678915612511978407)
    ·
      refine ⟨33282733018373418767967611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22188488678915612511978407 33282733018373418767967611)
      ·
        refine ⟨49924099527560128151951417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33282733018373418767967611 49924099527560128151951417)
        ·
          refine ⟨37443074645670096113963563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49924099527560128151951417 37443074645670096113963563)
          ·
            refine ⟨56164611968505144170945345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37443074645670096113963563 56164611968505144170945345)
            ·
              refine ⟨42123458976378858128209009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56164611968505144170945345 42123458976378858128209009)
              ·
                refine ⟨31592594232284143596156757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42123458976378858128209009 31592594232284143596156757)
                ·
                  refine ⟨185112856829789903883731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31592594232284143596156757 185112856829789903883731)
                  ·
                    rfl

theorem cell22_1622277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_1622277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622277 prefixEnd_1622277 := by exact prefixLift 1622277
  have htrace : WordTrace (prefixWord ++ tailWord_1622277) baseStart_1622277 baseEnd_1622277 := by
    simpa [prefixWord, tailWord_1622277, baseEnd_1622277] using wordTrace_append hprefix tailTrace_1622277
  have hstable : (prefixWord ++ tailWord_1622277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622277).length < 2 ^ (prefixWord ++ tailWord_1622277).sum := by decide
  have hdescent : baseEnd_1622277 < baseStart_1622277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622371 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 4, 3]
def baseStart_1622371 : Nat := 118140960795 + 1622371 * 2 ^ 59
def prefixEnd_1622371 : Nat := 4983230072969 + 3 ^ 40 * 1622371 * 2
def baseEnd_1622371 : Nat := 555370748610384799800905

theorem tailTrace_1622371 : CollatzResearch.WordTrace tailWord_1622371 prefixEnd_1622371 555370748610384799800905 := by
  unfold tailWord_1622371
  simp only [CollatzResearch.WordTrace]
  refine ⟨59172731605434420752530967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39448487736956280501687311 59172731605434420752530967)
  ·
    refine ⟨88759097408151631128796451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59172731605434420752530967 88759097408151631128796451)
    ·
      refine ⟨133138646112227446693194677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88759097408151631128796451 133138646112227446693194677)
      ·
        refine ⟨12481748073021323127487001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133138646112227446693194677 12481748073021323127487001)
        ·
          refine ⟨9361311054765992345615251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12481748073021323127487001 9361311054765992345615251)
          ·
            refine ⟨14041966582148988518422877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361311054765992345615251 14041966582148988518422877)
            ·
              refine ⟨5265737468305870694408579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14041966582148988518422877 5265737468305870694408579)
              ·
                refine ⟨7898606202458806041612869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265737468305870694408579 7898606202458806041612869)
                ·
                  refine ⟨1480988662961026132802413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7898606202458806041612869 1480988662961026132802413)
                  ·
                    refine ⟨555370748610384799800905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1480988662961026132802413 555370748610384799800905)
                    ·
                      rfl

theorem cell22_1622371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 3].length) (baseStart_1622371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622371 prefixEnd_1622371 := by exact prefixLift 1622371
  have htrace : WordTrace (prefixWord ++ tailWord_1622371) baseStart_1622371 baseEnd_1622371 := by
    simpa [prefixWord, tailWord_1622371, baseEnd_1622371] using wordTrace_append hprefix tailTrace_1622371
  have hstable : (prefixWord ++ tailWord_1622371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622371).length < 2 ^ (prefixWord ++ tailWord_1622371).sum := by decide
  have hdescent : baseEnd_1622371 < baseStart_1622371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622401 : List Nat := [1, 2, 4, 3, 1, 2, 1, 8]
def baseStart_1622401 : Nat := 118140960795 + 1622401 * 2 ^ 59
def prefixEnd_1622401 : Nat := 4983230072969 + 3 ^ 40 * 1622401 * 2
def baseEnd_1622401 : Nat := 61709002024830524616757

theorem tailTrace_1622401 : CollatzResearch.WordTrace tailWord_1622401 prefixEnd_1622401 61709002024830524616757 := by
  unfold tailWord_1622401
  simp only [CollatzResearch.WordTrace]
  refine ⟨59173825795325735876123057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39449217196883823917415371 59173825795325735876123057)
  ·
    refine ⟨44380369346494301907092293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59173825795325735876123057 44380369346494301907092293)
    ·
      refine ⟨8321319252467681607579805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44380369346494301907092293 8321319252467681607579805)
      ·
        refine ⟨3120494719675380602842427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8321319252467681607579805 3120494719675380602842427)
        ·
          refine ⟨4680742079513070904263641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120494719675380602842427 4680742079513070904263641)
          ·
            refine ⟨3510556559634803178197731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4680742079513070904263641 3510556559634803178197731)
            ·
              refine ⟨5265834839452204767296597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510556559634803178197731 5265834839452204767296597)
              ·
                refine ⟨61709002024830524616757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5265834839452204767296597 61709002024830524616757)
                ·
                  rfl

theorem cell22_1622401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 8].length) (baseStart_1622401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622401 prefixEnd_1622401 := by exact prefixLift 1622401
  have htrace : WordTrace (prefixWord ++ tailWord_1622401) baseStart_1622401 baseEnd_1622401 := by
    simpa [prefixWord, tailWord_1622401, baseEnd_1622401] using wordTrace_append hprefix tailTrace_1622401
  have hstable : (prefixWord ++ tailWord_1622401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622401).length < 2 ^ (prefixWord ++ tailWord_1622401).sum := by decide
  have hdescent : baseEnd_1622401 < baseStart_1622401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622444 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_1622444 : Nat := 118140960795 + 1622444 * 2 ^ 59
def prefixEnd_1622444 : Nat := 4983230072969 + 3 ^ 40 * 1622444 * 2
def baseEnd_1622444 : Nat := 555395738002236942725681

theorem tailTrace_1622444 : CollatzResearch.WordTrace tailWord_1622444 prefixEnd_1622444 555395738002236942725681 := by
  unfold tailWord_1622444
  simp only [CollatzResearch.WordTrace]
  refine ⟨29587697067084977109969193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39450262756113302813292257 29587697067084977109969193)
  ·
    refine ⟨22190772800313732832476895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29587697067084977109969193 22190772800313732832476895)
    ·
      refine ⟨33286159200470599248715343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22190772800313732832476895 33286159200470599248715343)
      ·
        refine ⟨49929238800705898873073015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33286159200470599248715343 49929238800705898873073015)
        ·
          refine ⟨74893858201058848309609523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49929238800705898873073015 74893858201058848309609523)
          ·
            refine ⟨112340787301588272464414285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74893858201058848309609523 112340787301588272464414285)
            ·
              refine ⟨42127795238095602174155357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112340787301588272464414285 42127795238095602174155357)
              ·
                refine ⟨15797923214285850815308259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42127795238095602174155357 15797923214285850815308259)
                ·
                  refine ⟨23696884821428776222962389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15797923214285850815308259 23696884821428776222962389)
                  ·
                    refine ⟨555395738002236942725681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23696884821428776222962389 555395738002236942725681)
                    ·
                      rfl

theorem cell22_1622444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_1622444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622444 prefixEnd_1622444 := by exact prefixLift 1622444
  have htrace : WordTrace (prefixWord ++ tailWord_1622444) baseStart_1622444 baseEnd_1622444 := by
    simpa [prefixWord, tailWord_1622444, baseEnd_1622444] using wordTrace_append hprefix tailTrace_1622444
  have hstable : (prefixWord ++ tailWord_1622444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622444).length < 2 ^ (prefixWord ++ tailWord_1622444).sum := by decide
  have hdescent : baseEnd_1622444 < baseStart_1622444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622484 : List Nat := [2, 4, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1622484 : Nat := 118140960795 + 1622484 * 2 ^ 59
def prefixEnd_1622484 : Nat := 4983230072969 + 3 ^ 40 * 1622484 * 2
def baseEnd_1622484 : Nat := 555409430819690171725559

theorem tailTrace_1622484 : CollatzResearch.WordTrace tailWord_1622484 prefixEnd_1622484 555409430819690171725559 := by
  unfold tailWord_1622484
  simp only [CollatzResearch.WordTrace]
  refine ⟨29588426527012520525697253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39451235369350027367596337 29588426527012520525697253)
  ·
    refine ⟨5547829973814847598568235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29588426527012520525697253 5547829973814847598568235)
    ·
      refine ⟨8321744960722271397852353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547829973814847598568235 8321744960722271397852353)
      ·
        refine ⟨6241308720541703548389265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8321744960722271397852353 6241308720541703548389265)
        ·
          refine ⟨4680981540406277661291949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6241308720541703548389265 4680981540406277661291949)
          ·
            refine ⟨1755368077652354122984481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4680981540406277661291949 1755368077652354122984481)
            ·
              refine ⟨1316526058239265592238361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755368077652354122984481 1316526058239265592238361)
              ·
                refine ⟨987394543679449194178771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316526058239265592238361 987394543679449194178771)
                ·
                  refine ⟨1481091815519173791268157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987394543679449194178771 1481091815519173791268157)
                  ·
                    refine ⟨555409430819690171725559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481091815519173791268157 555409430819690171725559)
                    ·
                      rfl

theorem cell22_1622484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1622484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622484 prefixEnd_1622484 := by exact prefixLift 1622484
  have htrace : WordTrace (prefixWord ++ tailWord_1622484) baseStart_1622484 baseEnd_1622484 := by
    simpa [prefixWord, tailWord_1622484, baseEnd_1622484] using wordTrace_append hprefix tailTrace_1622484
  have hstable : (prefixWord ++ tailWord_1622484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622484).length < 2 ^ (prefixWord ++ tailWord_1622484).sum := by decide
  have hdescent : baseEnd_1622484 < baseStart_1622484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622540 : List Nat := [2, 2, 1, 2, 4, 1, 3, 2, 2, 3]
def baseStart_1622540 : Nat := 118140960795 + 1622540 * 2 ^ 59
def prefixEnd_1622540 : Nat := 4983230072969 + 3 ^ 40 * 1622540 * 2
def baseEnd_1622540 : Nat := 555428600764124692325387

theorem tailTrace_1622540 : CollatzResearch.WordTrace tailWord_1622540 prefixEnd_1622540 555428600764124692325387 := by
  unfold tailWord_1622540
  simp only [CollatzResearch.WordTrace]
  refine ⟨29589447770911081307716537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39452597027881441743622049 29589447770911081307716537)
  ·
    refine ⟨22192085828183310980787403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29589447770911081307716537 22192085828183310980787403)
    ·
      refine ⟨33288128742274966471181105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22192085828183310980787403 33288128742274966471181105)
      ·
        refine ⟨24966096556706224853385829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33288128742274966471181105 24966096556706224853385829)
        ·
          refine ⟨4681143104382417160009843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24966096556706224853385829 4681143104382417160009843)
          ·
            refine ⟨7021714656573625740014765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681143104382417160009843 7021714656573625740014765)
            ·
              refine ⟨2633142996215109652505537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7021714656573625740014765 2633142996215109652505537)
              ·
                refine ⟨1974857247161332239379153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633142996215109652505537 1974857247161332239379153)
                ·
                  refine ⟨1481142935370999179534365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974857247161332239379153 1481142935370999179534365)
                  ·
                    refine ⟨555428600764124692325387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481142935370999179534365 555428600764124692325387)
                    ·
                      rfl

theorem cell22_1622540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 2, 2, 3].length) (baseStart_1622540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622540 prefixEnd_1622540 := by exact prefixLift 1622540
  have htrace : WordTrace (prefixWord ++ tailWord_1622540) baseStart_1622540 baseEnd_1622540 := by
    simpa [prefixWord, tailWord_1622540, baseEnd_1622540] using wordTrace_append hprefix tailTrace_1622540
  have hstable : (prefixWord ++ tailWord_1622540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622540).length < 2 ^ (prefixWord ++ tailWord_1622540).sum := by decide
  have hdescent : baseEnd_1622540 < baseStart_1622540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622557 : List Nat := [1, 4, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1622557 : Nat := 118140960795 + 1622557 * 2 ^ 59
def prefixEnd_1622557 : Nat := 4983230072969 + 3 ^ 40 * 1622557 * 2
def baseEnd_1622557 : Nat := 555434420211542314650335

theorem tailTrace_1622557 : CollatzResearch.WordTrace tailWord_1622557 prefixEnd_1622557 555434420211542314650335 := by
  unfold tailWord_1622557
  simp only [CollatzResearch.WordTrace]
  refine ⟨59179515582760574518801925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39453010388507049679201283 59179515582760574518801925)
  ·
    refine ⟨11096159171767607722275361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59179515582760574518801925 11096159171767607722275361)
    ·
      refine ⟨8322119378825705791706521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11096159171767607722275361 8322119378825705791706521)
      ·
        refine ⟨6241589534119279343779891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8322119378825705791706521 6241589534119279343779891)
        ·
          refine ⟨9362384301178919015669837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241589534119279343779891 9362384301178919015669837)
          ·
            refine ⟨3510894112942094630876189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9362384301178919015669837 3510894112942094630876189)
            ·
              refine ⟨1316585292353285486578571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510894112942094630876189 1316585292353285486578571)
              ·
                refine ⟨1974877938529928229867857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316585292353285486578571 1974877938529928229867857)
                ·
                  refine ⟨1481158453897446172400893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1974877938529928229867857 1481158453897446172400893)
                  ·
                    refine ⟨555434420211542314650335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481158453897446172400893 555434420211542314650335)
                    ·
                      rfl

theorem cell22_1622557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1622557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622557 prefixEnd_1622557 := by exact prefixLift 1622557
  have htrace : WordTrace (prefixWord ++ tailWord_1622557) baseStart_1622557 baseEnd_1622557 := by
    simpa [prefixWord, tailWord_1622557, baseEnd_1622557] using wordTrace_append hprefix tailTrace_1622557
  have hstable : (prefixWord ++ tailWord_1622557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622557).length < 2 ^ (prefixWord ++ tailWord_1622557).sum := by decide
  have hdescent : baseEnd_1622557 < baseStart_1622557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622570 : List Nat := [3, 1, 4, 1, 1, 4, 2, 6]
def baseStart_1622570 : Nat := 118140960795 + 1622570 * 2 ^ 59
def prefixEnd_1622570 : Nat := 4983230072969 + 3 ^ 40 * 1622570 * 2
def baseEnd_1622570 : Nat := 61715430041912734897255

theorem tailTrace_1622570 : CollatzResearch.WordTrace tailWord_1622570 prefixEnd_1622570 61715430041912734897255 := by
  unfold tailWord_1622570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14794997432928369434756291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39453326487808985159350109 14794997432928369434756291)
  ·
    refine ⟨22192496149392554152134437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14794997432928369434756291 22192496149392554152134437)
    ·
      refine ⟨4161093028011103903525207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22192496149392554152134437 4161093028011103903525207)
      ·
        refine ⟨6241639542016655855287811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4161093028011103903525207 6241639542016655855287811)
        ·
          refine ⟨9362459313024983782931717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241639542016655855287811 9362459313024983782931717)
          ·
            refine ⟨1755461121192184459299697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9362459313024983782931717 1755461121192184459299697)
            ·
              refine ⟨1316595840894138344474773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755461121192184459299697 1316595840894138344474773)
              ·
                refine ⟨61715430041912734897255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1316595840894138344474773 61715430041912734897255)
                ·
                  rfl

theorem cell22_1622570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 6].length) (baseStart_1622570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622570 prefixEnd_1622570 := by exact prefixLift 1622570
  have htrace : WordTrace (prefixWord ++ tailWord_1622570) baseStart_1622570 baseEnd_1622570 := by
    simpa [prefixWord, tailWord_1622570, baseEnd_1622570] using wordTrace_append hprefix tailTrace_1622570
  have hstable : (prefixWord ++ tailWord_1622570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622570).length < 2 ^ (prefixWord ++ tailWord_1622570).sum := by decide
  have hdescent : baseEnd_1622570 < baseStart_1622570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622581 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1622581 : Nat := 118140960795 + 1622581 * 2 ^ 59
def prefixEnd_1622581 : Nat := 4983230072969 + 3 ^ 40 * 1622581 * 2
def baseEnd_1622581 : Nat := 185147545300671417350087

theorem tailTrace_1622581 : CollatzResearch.WordTrace tailWord_1622581 prefixEnd_1622581 185147545300671417350087 := by
  unfold tailWord_1622581
  simp only [CollatzResearch.WordTrace]
  refine ⟨59180390934673626617675597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39453593956449084411783731 59180390934673626617675597)
  ·
    refine ⟨22192646600502609981628349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59180390934673626617675597 22192646600502609981628349)
    ·
      refine ⟨8322242475188478743110631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22192646600502609981628349 8322242475188478743110631)
      ·
        refine ⟨12483363712782718114665947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8322242475188478743110631 12483363712782718114665947)
        ·
          refine ⟨18725045569174077171998921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12483363712782718114665947 18725045569174077171998921)
          ·
            refine ⟨14043784176880557878999191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18725045569174077171998921 14043784176880557878999191)
            ·
              refine ⟨21065676265320836818498787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14043784176880557878999191 21065676265320836818498787)
              ·
                refine ⟨31598514397981255227748181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21065676265320836818498787 31598514397981255227748181)
                ·
                  refine ⟨185147545300671417350087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31598514397981255227748181 185147545300671417350087)
                  ·
                    rfl

theorem cell22_1622581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1622581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622581 prefixEnd_1622581 := by exact prefixLift 1622581
  have htrace : WordTrace (prefixWord ++ tailWord_1622581) baseStart_1622581 baseEnd_1622581 := by
    simpa [prefixWord, tailWord_1622581, baseEnd_1622581] using wordTrace_append hprefix tailTrace_1622581
  have hstable : (prefixWord ++ tailWord_1622581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622581).length < 2 ^ (prefixWord ++ tailWord_1622581).sum := by decide
  have hdescent : baseEnd_1622581 < baseStart_1622581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622628 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1622628 : Nat := 118140960795 + 1622628 * 2 ^ 59
def prefixEnd_1622628 : Nat := 4983230072969 + 3 ^ 40 * 1622628 * 2
def baseEnd_1622628 : Nat := 555458724962521796125117

theorem tailTrace_1622628 : CollatzResearch.WordTrace tailWord_1622628 prefixEnd_1622628 555458724962521796125117 := by
  unfold tailWord_1622628
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591052582751676822318269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39454736777002235763091025 29591052582751676822318269)
  ·
    refine ⟨11096644718531878808369351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29591052582751676822318269 11096644718531878808369351)
    ·
      refine ⟨16644967077797818212554027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096644718531878808369351 16644967077797818212554027)
      ·
        refine ⟨24967450616696727318831041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16644967077797818212554027 24967450616696727318831041)
        ·
          refine ⟨18725587962522545489123281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24967450616696727318831041 18725587962522545489123281)
          ·
            refine ⟨14044190971891909116842461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18725587962522545489123281 14044190971891909116842461)
            ·
              refine ⟨5266571614459465918815923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14044190971891909116842461 5266571614459465918815923)
              ·
                refine ⟨7899857421689198878223885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266571614459465918815923 7899857421689198878223885)
                ·
                  refine ⟨2962446533133449579333957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7899857421689198878223885 2962446533133449579333957)
                  ·
                    refine ⟨555458724962521796125117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2962446533133449579333957 555458724962521796125117)
                    ·
                      rfl

theorem cell22_1622628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1622628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622628 prefixEnd_1622628 := by exact prefixLift 1622628
  have htrace : WordTrace (prefixWord ++ tailWord_1622628) baseStart_1622628 baseEnd_1622628 := by
    simpa [prefixWord, tailWord_1622628, baseEnd_1622628] using wordTrace_append hprefix tailTrace_1622628
  have hstable : (prefixWord ++ tailWord_1622628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622628).length < 2 ^ (prefixWord ++ tailWord_1622628).sum := by decide
  have hdescent : baseEnd_1622628 < baseStart_1622628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622705 : List Nat := [1, 2, 2, 6, 1, 1, 9]
def baseStart_1622705 : Nat := 118140960795 + 1622705 * 2 ^ 59
def prefixEnd_1622705 : Nat := 4983230072969 + 3 ^ 40 * 1622705 * 2
def baseEnd_1622705 : Nat := 20573521616152565257403

theorem tailTrace_1622705 : CollatzResearch.WordTrace tailWord_1622705 prefixEnd_1622705 20573521616152565257403 := by
  unfold tailWord_1622705
  simp only [CollatzResearch.WordTrace]
  refine ⟨59184913586224395795189569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39456609057482930530126379 59184913586224395795189569)
  ·
    refine ⟨44388685189668296846392177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59184913586224395795189569 44388685189668296846392177)
    ·
      refine ⟨33291513892251222634794133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44388685189668296846392177 33291513892251222634794133)
      ·
        refine ⟨1560539713699276061005975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33291513892251222634794133 1560539713699276061005975)
        ·
          refine ⟨2340809570548914091508963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560539713699276061005975 2340809570548914091508963)
          ·
            refine ⟨3511214355823371137263445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340809570548914091508963 3511214355823371137263445)
            ·
              refine ⟨20573521616152565257403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3511214355823371137263445 20573521616152565257403)
              ·
                rfl

theorem cell22_1622705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 9].length) (baseStart_1622705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622705 prefixEnd_1622705 := by exact prefixLift 1622705
  have htrace : WordTrace (prefixWord ++ tailWord_1622705) baseStart_1622705 baseEnd_1622705 := by
    simpa [prefixWord, tailWord_1622705, baseEnd_1622705] using wordTrace_append hprefix tailTrace_1622705
  have hstable : (prefixWord ++ tailWord_1622705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622705).length < 2 ^ (prefixWord ++ tailWord_1622705).sum := by decide
  have hdescent : baseEnd_1622705 < baseStart_1622705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622709 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1622709 : Nat := 118140960795 + 1622709 * 2 ^ 59
def prefixEnd_1622709 : Nat := 4983230072969 + 3 ^ 40 * 1622709 * 2
def baseEnd_1622709 : Nat := 555486452917864584849869

theorem tailTrace_1622709 : CollatzResearch.WordTrace tailWord_1622709 prefixEnd_1622709 555486452917864584849869 := by
  unfold tailWord_1622709
  simp only [CollatzResearch.WordTrace]
  refine ⟨59185059478209904478335181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39456706318806602985556787 59185059478209904478335181)
  ·
    refine ⟨22194397304328714179375693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59185059478209904478335181 22194397304328714179375693)
    ·
      refine ⟨8322898989123267817265885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22194397304328714179375693 8322898989123267817265885)
      ·
        refine ⟨3121087120921225431474707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8322898989123267817265885 3121087120921225431474707)
        ·
          refine ⟨4681630681381838147212061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121087120921225431474707 4681630681381838147212061)
          ·
            refine ⟨1755611505518189305204523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4681630681381838147212061 1755611505518189305204523)
            ·
              refine ⟨2633417258277283957806785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755611505518189305204523 2633417258277283957806785)
              ·
                refine ⟨1975062943707962968355089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633417258277283957806785 1975062943707962968355089)
                ·
                  refine ⟨1481297207780972226266317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1975062943707962968355089 1481297207780972226266317)
                  ·
                    refine ⟨555486452917864584849869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481297207780972226266317 555486452917864584849869)
                    ·
                      rfl

theorem cell22_1622709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1622709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622709 prefixEnd_1622709 := by exact prefixLift 1622709
  have htrace : WordTrace (prefixWord ++ tailWord_1622709) baseStart_1622709 baseEnd_1622709 := by
    simpa [prefixWord, tailWord_1622709, baseEnd_1622709] using wordTrace_append hprefix tailTrace_1622709
  have hstable : (prefixWord ++ tailWord_1622709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622709).length < 2 ^ (prefixWord ++ tailWord_1622709).sum := by decide
  have hdescent : baseEnd_1622709 < baseStart_1622709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622720 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_1622720 : Nat := 118140960795 + 1622720 * 2 ^ 59
def prefixEnd_1622720 : Nat := 4983230072969 + 3 ^ 40 * 1622720 * 2
def baseEnd_1622720 : Nat := 555490218442664222824835

theorem tailTrace_1622720 : CollatzResearch.WordTrace tailWord_1622720 prefixEnd_1622720 555490218442664222824835 := by
  unfold tailWord_1622720
  simp only [CollatzResearch.WordTrace]
  refine ⟨29592730340585026678492807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39456973787446702237990409 29592730340585026678492807)
  ·
    refine ⟨44389095510877540017739211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29592730340585026678492807 44389095510877540017739211)
    ·
      refine ⟨66583643266316310026608817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44389095510877540017739211 66583643266316310026608817)
      ·
        refine ⟨49937732449737232519956613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66583643266316310026608817 49937732449737232519956613)
        ·
          refine ⟨9363324834325731097491865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49937732449737232519956613 9363324834325731097491865)
          ·
            refine ⟨7022493625744298323118899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9363324834325731097491865 7022493625744298323118899)
            ·
              refine ⟨10533740438616447484678349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022493625744298323118899 10533740438616447484678349)
              ·
                refine ⟨3950152664481167806754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10533740438616447484678349 3950152664481167806754381)
                ·
                  refine ⟨1481307249180437927532893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3950152664481167806754381 1481307249180437927532893)
                  ·
                    refine ⟨555490218442664222824835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481307249180437927532893 555490218442664222824835)
                    ·
                      rfl

theorem cell22_1622720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_1622720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622720 prefixEnd_1622720 := by exact prefixLift 1622720
  have htrace : WordTrace (prefixWord ++ tailWord_1622720) baseStart_1622720 baseEnd_1622720 := by
    simpa [prefixWord, tailWord_1622720, baseEnd_1622720] using wordTrace_append hprefix tailTrace_1622720
  have hstable : (prefixWord ++ tailWord_1622720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622720).length < 2 ^ (prefixWord ++ tailWord_1622720).sum := by decide
  have hdescent : baseEnd_1622720 < baseStart_1622720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622726 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 1, 5]
def baseStart_1622726 : Nat := 118140960795 + 1622726 * 2 ^ 59
def prefixEnd_1622726 : Nat := 4983230072969 + 3 ^ 40 * 1622726 * 2
def baseEnd_1622726 : Nat := 555492272365282207174817

theorem tailTrace_1622726 : CollatzResearch.WordTrace tailWord_1622726 prefixEnd_1622726 555492272365282207174817 := by
  unfold tailWord_1622726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849552484973384886928251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 39457119679432210921136021 1849552484973384886928251)
  ·
    refine ⟨2774328727460077330392377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1849552484973384886928251 2774328727460077330392377)
    ·
      refine ⟨2080746545595057997794283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2774328727460077330392377 2080746545595057997794283)
      ·
        refine ⟨3121119818392586996691425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080746545595057997794283 3121119818392586996691425)
        ·
          refine ⟨2340839863794440247518569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121119818392586996691425 2340839863794440247518569)
          ·
            refine ⟨1755629897845830185638927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2340839863794440247518569 1755629897845830185638927)
            ·
              refine ⟨2633444846768745278458391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755629897845830185638927 2633444846768745278458391)
              ·
                refine ⟨3950167270153117917687587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633444846768745278458391 3950167270153117917687587)
                ·
                  refine ⟨5925250905229676876531381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950167270153117917687587 5925250905229676876531381)
                  ·
                    refine ⟨555492272365282207174817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5925250905229676876531381 555492272365282207174817)
                    ·
                      rfl

theorem cell22_1622726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_1622726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622726 prefixEnd_1622726 := by exact prefixLift 1622726
  have htrace : WordTrace (prefixWord ++ tailWord_1622726) baseStart_1622726 baseEnd_1622726 := by
    simpa [prefixWord, tailWord_1622726, baseEnd_1622726] using wordTrace_append hprefix tailTrace_1622726
  have hstable : (prefixWord ++ tailWord_1622726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622726).length < 2 ^ (prefixWord ++ tailWord_1622726).sum := by decide
  have hdescent : baseEnd_1622726 < baseStart_1622726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622763 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_1622763 : Nat := 118140960795 + 1622763 * 2 ^ 59
def prefixEnd_1622763 : Nat := 4983230072969 + 3 ^ 40 * 1622763 * 2
def baseEnd_1622763 : Nat := 555504938221426443999703

theorem tailTrace_1622763 : CollatzResearch.WordTrace tailWord_1622763 prefixEnd_1622763 555504938221426443999703 := by
  unfold tailWord_1622763
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187029020014271700800943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39458019346676181133867295 59187029020014271700800943)
  ·
    refine ⟨88780543530021407551201415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59187029020014271700800943 88780543530021407551201415)
    ·
      refine ⟨133170815295032111326802123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88780543530021407551201415 133170815295032111326802123)
      ·
        refine ⟨199756222942548166990203185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133170815295032111326802123 199756222942548166990203185)
        ·
          refine ⟨149817167206911125242652389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199756222942548166990203185 149817167206911125242652389)
          ·
            refine ⟨28090718851295835982997323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149817167206911125242652389 28090718851295835982997323)
            ·
              refine ⟨42136078276943753974495985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28090718851295835982997323 42136078276943753974495985)
              ·
                refine ⟨31602058707707815480871989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42136078276943753974495985 31602058707707815480871989)
                ·
                  refine ⟨2962693003847607701331749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31602058707707815480871989 2962693003847607701331749)
                  ·
                    refine ⟨555504938221426443999703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2962693003847607701331749 555504938221426443999703)
                    ·
                      rfl

theorem cell22_1622763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_1622763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622763 prefixEnd_1622763 := by exact prefixLift 1622763
  have htrace : WordTrace (prefixWord ++ tailWord_1622763) baseStart_1622763 baseEnd_1622763 := by
    simpa [prefixWord, tailWord_1622763, baseEnd_1622763] using wordTrace_append hprefix tailTrace_1622763
  have hstable : (prefixWord ++ tailWord_1622763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622763).length < 2 ^ (prefixWord ++ tailWord_1622763).sum := by decide
  have hdescent : baseEnd_1622763 < baseStart_1622763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622810 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1622810 : Nat := 118140960795 + 1622810 * 2 ^ 59
def prefixEnd_1622810 : Nat := 4983230072969 + 3 ^ 40 * 1622810 * 2
def baseEnd_1622810 : Nat := 555521027281933988074559

theorem tailTrace_1622810 : CollatzResearch.WordTrace tailWord_1622810 prefixEnd_1622810 555521027281933988074559 := by
  unfold tailWord_1622810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797185812710999681940471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39459162167229332485174589 14797185812710999681940471)
  ·
    refine ⟨22195778719066499522910707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14797185812710999681940471 22195778719066499522910707)
    ·
      refine ⟨33293668078599749284366061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22195778719066499522910707 33293668078599749284366061)
      ·
        refine ⟨12485125529474905981637273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33293668078599749284366061 12485125529474905981637273)
        ·
          refine ⟨9363844147106179486227955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12485125529474905981637273 9363844147106179486227955)
          ·
            refine ⟨14045766220659269229341933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9363844147106179486227955 14045766220659269229341933)
            ·
              refine ⟨5267162332747225961003225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14045766220659269229341933 5267162332747225961003225)
              ·
                refine ⟨3950371749560419470752419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267162332747225961003225 3950371749560419470752419)
                ·
                  refine ⟨5925557624340629206128629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950371749560419470752419 5925557624340629206128629)
                  ·
                    refine ⟨555521027281933988074559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5925557624340629206128629 555521027281933988074559)
                    ·
                      rfl

theorem cell22_1622810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1622810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622810 prefixEnd_1622810 := by exact prefixLift 1622810
  have htrace : WordTrace (prefixWord ++ tailWord_1622810) baseStart_1622810 baseEnd_1622810 := by
    simpa [prefixWord, tailWord_1622810, baseEnd_1622810] using wordTrace_append hprefix tailTrace_1622810
  have hstable : (prefixWord ++ tailWord_1622810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622810).length < 2 ^ (prefixWord ++ tailWord_1622810).sum := by decide
  have hdescent : baseEnd_1622810 < baseStart_1622810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622947 : List Nat := [1, 1, 1, 4, 1, 2, 2, 6, 4]
def baseStart_1622947 : Nat := 118140960795 + 1622947 * 2 ^ 59
def prefixEnd_1622947 : Nat := 4983230072969 + 3 ^ 40 * 1622947 * 2
def baseEnd_1622947 : Nat := 185189308393903765799713

theorem tailTrace_1622947 : CollatzResearch.WordTrace tailWord_1622947 prefixEnd_1622947 185189308393903765799713 := by
  unfold tailWord_1622947
  simp only [CollatzResearch.WordTrace]
  refine ⟨59193740051347671125499095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39462493367565114083666063 59193740051347671125499095)
  ·
    refine ⟨88790610077021506688248643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59193740051347671125499095 88790610077021506688248643)
    ·
      refine ⟨133185915115532260032372965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88790610077021506688248643 133185915115532260032372965)
      ·
        refine ⟨24972359084162298756069931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133185915115532260032372965 24972359084162298756069931)
        ·
          refine ⟨37458538626243448134104897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24972359084162298756069931 37458538626243448134104897)
          ·
            refine ⟨28093903969682586100578673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37458538626243448134104897 28093903969682586100578673)
            ·
              refine ⟨21070427977261939575434005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28093903969682586100578673 21070427977261939575434005)
              ·
                refine ⟨987676311434153417598469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21070427977261939575434005 987676311434153417598469)
                ·
                  refine ⟨185189308393903765799713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987676311434153417598469 185189308393903765799713)
                  ·
                    rfl

theorem cell22_1622947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 4].length) (baseStart_1622947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622947 prefixEnd_1622947 := by exact prefixLift 1622947
  have htrace : WordTrace (prefixWord ++ tailWord_1622947) baseStart_1622947 baseEnd_1622947 := by
    simpa [prefixWord, tailWord_1622947, baseEnd_1622947] using wordTrace_append hprefix tailTrace_1622947
  have hstable : (prefixWord ++ tailWord_1622947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622947).length < 2 ^ (prefixWord ++ tailWord_1622947).sum := by decide
  have hdescent : baseEnd_1622947 < baseStart_1622947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622994 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1622994 : Nat := 118140960795 + 1622994 * 2 ^ 59
def prefixEnd_1622994 : Nat := 4983230072969 + 3 ^ 40 * 1622994 * 2
def baseEnd_1622994 : Nat := 555584014242218841473995

theorem tailTrace_1622994 : CollatzResearch.WordTrace tailWord_1622994 prefixEnd_1622994 555584014242218841473995 := by
  unfold tailWord_1622994
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798863570544349538115009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39463636188118265434973357 14798863570544349538115009)
  ·
    refine ⟨11099147677908262153586257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14798863570544349538115009 11099147677908262153586257)
    ·
      refine ⟨8324360758431196615189693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11099147677908262153586257 8324360758431196615189693)
      ·
        refine ⟨3121635284411698730696135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8324360758431196615189693 3121635284411698730696135)
        ·
          refine ⟨4682452926617548096044203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121635284411698730696135 4682452926617548096044203)
          ·
            refine ⟨7023679389926322144066305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682452926617548096044203 7023679389926322144066305)
            ·
              refine ⟨5267759542444741608049729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7023679389926322144066305 5267759542444741608049729)
              ·
                refine ⟨3950819656833556206037297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267759542444741608049729 3950819656833556206037297)
                ·
                  refine ⟨2963114742625167154527973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950819656833556206037297 2963114742625167154527973)
                  ·
                    refine ⟨555584014242218841473995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963114742625167154527973 555584014242218841473995)
                    ·
                      rfl

theorem cell22_1622994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1622994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622994 prefixEnd_1622994 := by exact prefixLift 1622994
  have htrace : WordTrace (prefixWord ++ tailWord_1622994) baseStart_1622994 baseEnd_1622994 := by
    simpa [prefixWord, tailWord_1622994, baseEnd_1622994] using wordTrace_append hprefix tailTrace_1622994
  have hstable : (prefixWord ++ tailWord_1622994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622994).length < 2 ^ (prefixWord ++ tailWord_1622994).sum := by decide
  have hdescent : baseEnd_1622994 < baseStart_1622994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622996 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 2, 3]
def baseStart_1622996 : Nat := 118140960795 + 1622996 * 2 ^ 59
def prefixEnd_1622996 : Nat := 4983230072969 + 3 ^ 40 * 1622996 * 2
def baseEnd_1622996 : Nat := 555584698883091502923989

theorem tailTrace_1622996 : CollatzResearch.WordTrace tailWord_1622996 prefixEnd_1622996 555584698883091502923989 := by
  unfold tailWord_1622996
  simp only [CollatzResearch.WordTrace]
  refine ⟨29597763614085076247016421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39463684818780101662688561 29597763614085076247016421)
  ·
    refine ⟨5549580677640951796315579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29597763614085076247016421 5549580677640951796315579)
    ·
      refine ⟨8324371016461427694473369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5549580677640951796315579 8324371016461427694473369)
      ·
        refine ⟨6243278262346070770855027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8324371016461427694473369 6243278262346070770855027)
        ·
          refine ⟨9364917393519106156282541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243278262346070770855027 9364917393519106156282541)
          ·
            refine ⟨3511844022569664808605953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9364917393519106156282541 3511844022569664808605953)
            ·
              refine ⟨2633883016927248606454465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511844022569664808605953 2633883016927248606454465)
              ·
                refine ⟨1975412262695436454840849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633883016927248606454465 1975412262695436454840849)
                ·
                  refine ⟨1481559197021577341130637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1975412262695436454840849 1481559197021577341130637)
                  ·
                    refine ⟨555584698883091502923989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481559197021577341130637 555584698883091502923989)
                    ·
                      rfl

theorem cell22_1622996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_1622996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622996 prefixEnd_1622996 := by exact prefixLift 1622996
  have htrace : WordTrace (prefixWord ++ tailWord_1622996) baseStart_1622996 baseEnd_1622996 := by
    simpa [prefixWord, tailWord_1622996, baseEnd_1622996] using wordTrace_append hprefix tailTrace_1622996
  have hstable : (prefixWord ++ tailWord_1622996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622996).length < 2 ^ (prefixWord ++ tailWord_1622996).sum := by decide
  have hdescent : baseEnd_1622996 < baseStart_1622996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1622998 : List Nat := [5, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_1622998 : Nat := 118140960795 + 1622998 * 2 ^ 59
def prefixEnd_1622998 : Nat := 4983230072969 + 3 ^ 40 * 1622998 * 2
def baseEnd_1622998 : Nat := 185195127841321388124661

theorem tailTrace_1622998 : CollatzResearch.WordTrace tailWord_1622998 prefixEnd_1622998 185195127841321388124661 := by
  unfold tailWord_1622998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3699725010885181677225353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 39463733449441937890403765 3699725010885181677225353)
  ·
    refine ⟨2774793758163886257919015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3699725010885181677225353 2774793758163886257919015)
    ·
      refine ⟨4162190637245829386878523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2774793758163886257919015 4162190637245829386878523)
      ·
        refine ⟨6243285955868744080317785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162190637245829386878523 6243285955868744080317785)
        ·
          refine ⟨4682464466901558060238339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243285955868744080317785 4682464466901558060238339)
          ·
            refine ⟨7023696700352337090357509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682464466901558060238339 7023696700352337090357509)
            ·
              refine ⟨1316943131316063204442033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7023696700352337090357509 1316943131316063204442033)
              ·
                refine ⟨987707348487047403331525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1316943131316063204442033 987707348487047403331525)
                ·
                  refine ⟨185195127841321388124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987707348487047403331525 185195127841321388124661)
                  ·
                    rfl

theorem cell22_1622998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_1622998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1622998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1622998 prefixEnd_1622998 := by exact prefixLift 1622998
  have htrace : WordTrace (prefixWord ++ tailWord_1622998) baseStart_1622998 baseEnd_1622998 := by
    simpa [prefixWord, tailWord_1622998, baseEnd_1622998] using wordTrace_append hprefix tailTrace_1622998
  have hstable : (prefixWord ++ tailWord_1622998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1622998).length < 2 ^ (prefixWord ++ tailWord_1622998).sum := by decide
  have hdescent : baseEnd_1622998 < baseStart_1622998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1622998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623020 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 11]
def baseStart_1623020 : Nat := 118140960795 + 1623020 * 2 ^ 59
def prefixEnd_1623020 : Nat := 4983230072969 + 3 ^ 40 * 1623020 * 2
def baseEnd_1623020 : Nat := 185197638191187813441305

theorem tailTrace_1623020 : CollatzResearch.WordTrace tailWord_1623020 prefixEnd_1623020 185197638191187813441305 := by
  unfold tailWord_1623020
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598201290041602296453257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39464268386722136395271009 29598201290041602296453257)
  ·
    refine ⟨22198650967531201722339943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29598201290041602296453257 22198650967531201722339943)
    ·
      refine ⟨33297976451296802583509915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22198650967531201722339943 33297976451296802583509915)
      ·
        refine ⟨49946964676945203875264873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33297976451296802583509915 49946964676945203875264873)
        ·
          refine ⟨37460223507708902906448655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49946964676945203875264873 37460223507708902906448655)
          ·
            refine ⟨56190335261563354359672983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37460223507708902906448655 56190335261563354359672983)
            ·
              refine ⟨84285502892345031539509475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56190335261563354359672983 84285502892345031539509475)
              ·
                refine ⟨126428254338517547309264213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84285502892345031539509475 126428254338517547309264213)
                ·
                  refine ⟨185197638191187813441305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 126428254338517547309264213 185197638191187813441305)
                  ·
                    rfl

theorem cell22_1623020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 11].length) (baseStart_1623020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623020 prefixEnd_1623020 := by exact prefixLift 1623020
  have htrace : WordTrace (prefixWord ++ tailWord_1623020) baseStart_1623020 baseEnd_1623020 := by
    simpa [prefixWord, tailWord_1623020, baseEnd_1623020] using wordTrace_append hprefix tailTrace_1623020
  have hstable : (prefixWord ++ tailWord_1623020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623020).length < 2 ^ (prefixWord ++ tailWord_1623020).sum := by decide
  have hdescent : baseEnd_1623020 < baseStart_1623020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623026 : List Nat := [3, 2, 1, 5, 1, 1, 3, 6]
def baseStart_1623026 : Nat := 118140960795 + 1623026 * 2 ^ 59
def prefixEnd_1623026 : Nat := 4983230072969 + 3 ^ 40 * 1623026 * 2
def baseEnd_1623026 : Nat := 61732774277353491630433

theorem tailTrace_1623026 : CollatzResearch.WordTrace tailWord_1623026 prefixEnd_1623026 61732774277353491630433 := by
  unfold tailWord_1623026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799155354515366904406233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39464414278707645078416621 14799155354515366904406233)
  ·
    refine ⟨11099366515886525178304675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14799155354515366904406233 11099366515886525178304675)
    ·
      refine ⟨16649049773829787767457013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11099366515886525178304675 16649049773829787767457013)
      ·
        refine ⟨1560848416296542603199095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16649049773829787767457013 1560848416296542603199095)
        ·
          refine ⟨2341272624444813904798643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560848416296542603199095 2341272624444813904798643)
          ·
            refine ⟨3511908936667220857197965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341272624444813904798643 3511908936667220857197965)
            ·
              refine ⟨1316965851250207821449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3511908936667220857197965 1316965851250207821449237)
              ·
                refine ⟨61732774277353491630433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1316965851250207821449237 61732774277353491630433)
                ·
                  rfl

theorem cell22_1623026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_1623026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623026 prefixEnd_1623026 := by exact prefixLift 1623026
  have htrace : WordTrace (prefixWord ++ tailWord_1623026) baseStart_1623026 baseEnd_1623026 := by
    simpa [prefixWord, tailWord_1623026, baseEnd_1623026] using wordTrace_append hprefix tailTrace_1623026
  have hstable : (prefixWord ++ tailWord_1623026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623026).length < 2 ^ (prefixWord ++ tailWord_1623026).sum := by decide
  have hdescent : baseEnd_1623026 < baseStart_1623026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623035 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_1623035 : Nat := 118140960795 + 1623035 * 2 ^ 59
def prefixEnd_1623035 : Nat := 4983230072969 + 3 ^ 40 * 1623035 * 2
def baseEnd_1623035 : Nat := 555598049380108401198869

theorem tailTrace_1623035 : CollatzResearch.WordTrace tailWord_1623035 prefixEnd_1623035 555598049380108401198869 := by
  unfold tailWord_1623035
  simp only [CollatzResearch.WordTrace]
  refine ⟨59196949675028862154702559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39464633116685908103135039 59196949675028862154702559)
  ·
    refine ⟨88795424512543293232053839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59196949675028862154702559 88795424512543293232053839)
    ·
      refine ⟨133193136768814939848080759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88795424512543293232053839 133193136768814939848080759)
      ·
        refine ⟨199789705153222409772121139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133193136768814939848080759 199789705153222409772121139)
        ·
          refine ⟨299684557729833614658181709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199789705153222409772121139 299684557729833614658181709)
          ·
            refine ⟨112381709148687605496818141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299684557729833614658181709 112381709148687605496818141)
            ·
              refine ⟨42143140930757852061306803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112381709148687605496818141 42143140930757852061306803)
              ·
                refine ⟨63214711396136778091960205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42143140930757852061306803 63214711396136778091960205)
                ·
                  refine ⟨23705516773551291784485077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63214711396136778091960205 23705516773551291784485077)
                  ·
                    refine ⟨555598049380108401198869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23705516773551291784485077 555598049380108401198869)
                    ·
                      rfl

theorem cell22_1623035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_1623035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623035 prefixEnd_1623035 := by exact prefixLift 1623035
  have htrace : WordTrace (prefixWord ++ tailWord_1623035) baseStart_1623035 baseEnd_1623035 := by
    simpa [prefixWord, tailWord_1623035, baseEnd_1623035] using wordTrace_append hprefix tailTrace_1623035
  have hstable : (prefixWord ++ tailWord_1623035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623035).length < 2 ^ (prefixWord ++ tailWord_1623035).sum := by decide
  have hdescent : baseEnd_1623035 < baseStart_1623035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623041 : List Nat := [1, 2, 4, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1623041 : Nat := 118140960795 + 1623041 * 2 ^ 59
def prefixEnd_1623041 : Nat := 4983230072969 + 3 ^ 40 * 1623041 * 2
def baseEnd_1623041 : Nat := 555600103302726385548851

theorem tailTrace_1623041 : CollatzResearch.WordTrace tailWord_1623041 prefixEnd_1623041 555600103302726385548851 := by
  unfold tailWord_1623041
  simp only [CollatzResearch.WordTrace]
  refine ⟨59197168513007125179420977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39464779008671416786280651 59197168513007125179420977)
  ·
    refine ⟨44397876384755343884565733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59197168513007125179420977 44397876384755343884565733)
    ·
      refine ⟨8324601822141626978356075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44397876384755343884565733 8324601822141626978356075)
      ·
        refine ⟨12486902733212440467534113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8324601822141626978356075 12486902733212440467534113)
        ·
          refine ⟨9365177049909330350650585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12486902733212440467534113 9365177049909330350650585)
          ·
            refine ⟨7023882787431997762987939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9365177049909330350650585 7023882787431997762987939)
            ·
              refine ⟨10535824181147996644481909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7023882787431997762987939 10535824181147996644481909)
              ·
                refine ⟨987733516982624685420179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10535824181147996644481909 987733516982624685420179)
                ·
                  refine ⟨1481600275473937028130269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987733516982624685420179 1481600275473937028130269)
                  ·
                    refine ⟨555600103302726385548851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481600275473937028130269 555600103302726385548851)
                    ·
                      rfl

theorem cell22_1623041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1623041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623041 prefixEnd_1623041 := by exact prefixLift 1623041
  have htrace : WordTrace (prefixWord ++ tailWord_1623041) baseStart_1623041 baseEnd_1623041 := by
    simpa [prefixWord, tailWord_1623041, baseEnd_1623041] using wordTrace_append hprefix tailTrace_1623041
  have hstable : (prefixWord ++ tailWord_1623041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623041).length < 2 ^ (prefixWord ++ tailWord_1623041).sum := by decide
  have hdescent : baseEnd_1623041 < baseStart_1623041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623052 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 2, 5]
def baseStart_1623052 : Nat := 118140960795 + 1623052 * 2 ^ 59
def prefixEnd_1623052 : Nat := 4983230072969 + 3 ^ 40 * 1623052 * 2
def baseEnd_1623052 : Nat := 555603868827526023523817

theorem tailTrace_1623052 : CollatzResearch.WordTrace tailWord_1623052 prefixEnd_1623052 555603868827526023523817 := by
  unfold tailWord_1623052
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598784857983637029035705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39465046477311516038714273 29598784857983637029035705)
  ·
    refine ⟨22199088643487727771776779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29598784857983637029035705 22199088643487727771776779)
    ·
      refine ⟨33298632965231591657665169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22199088643487727771776779 33298632965231591657665169)
      ·
        refine ⟨24973974723923693743248877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33298632965231591657665169 24973974723923693743248877)
        ·
          refine ⟨9365240521471385153718329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24973974723923693743248877 9365240521471385153718329)
          ·
            refine ⟨7023930391103538865288747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9365240521471385153718329 7023930391103538865288747)
            ·
              refine ⟨10535895586655308297933121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7023930391103538865288747 10535895586655308297933121)
              ·
                refine ⟨7901921689991481223449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10535895586655308297933121 7901921689991481223449841)
                ·
                  refine ⟨5926441267493610917587381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7901921689991481223449841 5926441267493610917587381)
                  ·
                    refine ⟨555603868827526023523817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5926441267493610917587381 555603868827526023523817)
                    ·
                      rfl

theorem cell22_1623052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_1623052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623052 prefixEnd_1623052 := by exact prefixLift 1623052
  have htrace : WordTrace (prefixWord ++ tailWord_1623052) baseStart_1623052 baseEnd_1623052 := by
    simpa [prefixWord, tailWord_1623052, baseEnd_1623052] using wordTrace_append hprefix tailTrace_1623052
  have hstable : (prefixWord ++ tailWord_1623052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623052).length < 2 ^ (prefixWord ++ tailWord_1623052).sum := by decide
  have hdescent : baseEnd_1623052 < baseStart_1623052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623054 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_1623054 : Nat := 118140960795 + 1623054 * 2 ^ 59
def prefixEnd_1623054 : Nat := 4983230072969 + 3 ^ 40 * 1623054 * 2
def baseEnd_1623054 : Nat := 185201517822799561657937

theorem tailTrace_1623054 : CollatzResearch.WordTrace tailWord_1623054 prefixEnd_1623054 185201517822799561657937 := by
  unfold tailWord_1623054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399705332745003549955527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39465095107973352266429477 7399705332745003549955527)
  ·
    refine ⟨11099557999117505324933291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7399705332745003549955527 11099557999117505324933291)
    ·
      refine ⟨16649336998676257987399937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11099557999117505324933291 16649336998676257987399937)
      ·
        refine ⟨12487002749007193490549953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16649336998676257987399937 12487002749007193490549953)
        ·
          refine ⟨9365252061755395117912465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12487002749007193490549953 9365252061755395117912465)
          ·
            refine ⟨7023939046316546338434349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9365252061755395117912465 7023939046316546338434349)
            ·
              refine ⟨2633977142368704876912881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7023939046316546338434349 2633977142368704876912881)
              ·
                refine ⟨1975482856776528657684661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633977142368704876912881 1975482856776528657684661)
                ·
                  refine ⟨185201517822799561657937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1975482856776528657684661 185201517822799561657937)
                  ·
                    rfl

theorem cell22_1623054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_1623054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623054 prefixEnd_1623054 := by exact prefixLift 1623054
  have htrace : WordTrace (prefixWord ++ tailWord_1623054) baseStart_1623054 baseEnd_1623054 := by
    simpa [prefixWord, tailWord_1623054, baseEnd_1623054] using wordTrace_append hprefix tailTrace_1623054
  have hstable : (prefixWord ++ tailWord_1623054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623054).length < 2 ^ (prefixWord ++ tailWord_1623054).sum := by decide
  have hdescent : baseEnd_1623054 < baseStart_1623054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623084 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_1623084 : Nat := 118140960795 + 1623084 * 2 ^ 59
def prefixEnd_1623084 : Nat := 4983230072969 + 3 ^ 40 * 1623084 * 2
def baseEnd_1623084 : Nat := 555614823081488606723719

theorem tailTrace_1623084 : CollatzResearch.WordTrace tailWord_1623084 prefixEnd_1623084 555614823081488606723719 := by
  unfold tailWord_1623084
  simp only [CollatzResearch.WordTrace]
  refine ⟨29599368425925671761618153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39465824567900895682157537 29599368425925671761618153)
  ·
    refine ⟨22199526319444253821213615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29599368425925671761618153 22199526319444253821213615)
    ·
      refine ⟨33299289479166380731820423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22199526319444253821213615 33299289479166380731820423)
      ·
        refine ⟨49948934218749571097730635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33299289479166380731820423 49948934218749571097730635)
        ·
          refine ⟨74923401328124356646595953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49948934218749571097730635 74923401328124356646595953)
          ·
            refine ⟨56192550996093267484946965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74923401328124356646595953 56192550996093267484946965)
            ·
              refine ⟨2634025827941871913356889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56192550996093267484946965 2634025827941871913356889)
              ·
                refine ⟨1975519370956403935017667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634025827941871913356889 1975519370956403935017667)
                ·
                  refine ⟨2963279056434605902526501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975519370956403935017667 2963279056434605902526501)
                  ·
                    refine ⟨555614823081488606723719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963279056434605902526501 555614823081488606723719)
                    ·
                      rfl

theorem cell22_1623084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_1623084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623084 prefixEnd_1623084 := by exact prefixLift 1623084
  have htrace : WordTrace (prefixWord ++ tailWord_1623084) baseStart_1623084 baseEnd_1623084 := by
    simpa [prefixWord, tailWord_1623084, baseEnd_1623084] using wordTrace_append hprefix tailTrace_1623084
  have hstable : (prefixWord ++ tailWord_1623084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623084).length < 2 ^ (prefixWord ++ tailWord_1623084).sum := by decide
  have hdescent : baseEnd_1623084 < baseStart_1623084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623114 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1623114 : Nat := 118140960795 + 1623114 * 2 ^ 59
def prefixEnd_1623114 : Nat := 4983230072969 + 3 ^ 40 * 1623114 * 2
def baseEnd_1623114 : Nat := 555625092694578528473627

theorem tailTrace_1623114 : CollatzResearch.WordTrace tailWord_1623114 prefixEnd_1623114 555625092694578528473627 := by
  unfold tailWord_1623114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799957760435664661707099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39466554027828439097885597 14799957760435664661707099)
  ·
    refine ⟨22199936640653496992560649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14799957760435664661707099 22199936640653496992560649)
    ·
      refine ⟨16649952480490122744420487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22199936640653496992560649 16649952480490122744420487)
      ·
        refine ⟨24974928720735184116630731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16649952480490122744420487 24974928720735184116630731)
        ·
          refine ⟨37462393081102776174946097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24974928720735184116630731 37462393081102776174946097)
          ·
            refine ⟨28096794810827082131209573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37462393081102776174946097 28096794810827082131209573)
            ·
              refine ⟨5268149027030077899601795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28096794810827082131209573 5268149027030077899601795)
              ·
                refine ⟨7902223540545116849402693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268149027030077899601795 7902223540545116849402693)
                ·
                  refine ⟨1481666913852209409263005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7902223540545116849402693 1481666913852209409263005)
                  ·
                    refine ⟨555625092694578528473627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481666913852209409263005 555625092694578528473627)
                    ·
                      rfl

theorem cell22_1623114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1623114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623114 prefixEnd_1623114 := by exact prefixLift 1623114
  have htrace : WordTrace (prefixWord ++ tailWord_1623114) baseStart_1623114 baseEnd_1623114 := by
    simpa [prefixWord, tailWord_1623114, baseEnd_1623114] using wordTrace_append hprefix tailTrace_1623114
  have hstable : (prefixWord ++ tailWord_1623114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623114).length < 2 ^ (prefixWord ++ tailWord_1623114).sum := by decide
  have hdescent : baseEnd_1623114 < baseStart_1623114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623146 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1623146 : Nat := 118140960795 + 1623146 * 2 ^ 59
def prefixEnd_1623146 : Nat := 4983230072969 + 3 ^ 40 * 1623146 * 2
def baseEnd_1623146 : Nat := 555636046948541111673529

theorem tailTrace_1623146 : CollatzResearch.WordTrace tailWord_1623146 prefixEnd_1623146 555636046948541111673529 := by
  unfold tailWord_1623146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800249544406682027998323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39467332118417818741328861 14800249544406682027998323)
  ·
    refine ⟨22200374316610023041997485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800249544406682027998323 22200374316610023041997485)
    ·
      refine ⟨8325140368728758640749057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22200374316610023041997485 8325140368728758640749057)
      ·
        refine ⟨6243855276546568980561793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8325140368728758640749057 6243855276546568980561793)
        ·
          refine ⟨4682891457409926735421345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243855276546568980561793 4682891457409926735421345)
          ·
            refine ⟨3512168593057445051566009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682891457409926735421345 3512168593057445051566009)
            ·
              refine ⟨2634126444793083788674507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512168593057445051566009 2634126444793083788674507)
              ·
                refine ⟨3951189667189625683011761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634126444793083788674507 3951189667189625683011761)
                ·
                  refine ⟨2963392250392219262258821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951189667189625683011761 2963392250392219262258821)
                  ·
                    refine ⟨555636046948541111673529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963392250392219262258821 555636046948541111673529)
                    ·
                      rfl

theorem cell22_1623146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1623146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623146 prefixEnd_1623146 := by exact prefixLift 1623146
  have htrace : WordTrace (prefixWord ++ tailWord_1623146) baseStart_1623146 baseEnd_1623146 := by
    simpa [prefixWord, tailWord_1623146, baseEnd_1623146] using wordTrace_append hprefix tailTrace_1623146
  have hstable : (prefixWord ++ tailWord_1623146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623146).length < 2 ^ (prefixWord ++ tailWord_1623146).sum := by decide
  have hdescent : baseEnd_1623146 < baseStart_1623146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623187 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_1623187 : Nat := 118140960795 + 1623187 * 2 ^ 59
def prefixEnd_1623187 : Nat := 4983230072969 + 3 ^ 40 * 1623187 * 2
def baseEnd_1623187 : Nat := 555650082086430671398403

theorem tailTrace_1623187 : CollatzResearch.WordTrace tailWord_1623187 prefixEnd_1623187 555650082086430671398403 := by
  unfold tailWord_1623187
  simp only [CollatzResearch.WordTrace]
  refine ⟨59202493570478192114235815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39468329046985461409490543 59202493570478192114235815)
  ·
    refine ⟨88803740355717288171353723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59202493570478192114235815 88803740355717288171353723)
    ·
      refine ⟨133205610533575932257030585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88803740355717288171353723 133205610533575932257030585)
      ·
        refine ⟨99904207900181949192772939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133205610533575932257030585 99904207900181949192772939)
        ·
          refine ⟨149856311850272923789159409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99904207900181949192772939 149856311850272923789159409)
          ·
            refine ⟨112392233887704692841869557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149856311850272923789159409 112392233887704692841869557)
            ·
              refine ⟨10536771926972314953925271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112392233887704692841869557 10536771926972314953925271)
              ·
                refine ⟨15805157890458472430887907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10536771926972314953925271 15805157890458472430887907)
                ·
                  refine ⟨23707736835687708646331861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15805157890458472430887907 23707736835687708646331861)
                  ·
                    refine ⟨555650082086430671398403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23707736835687708646331861 555650082086430671398403)
                    ·
                      rfl

theorem cell22_1623187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_1623187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623187 prefixEnd_1623187 := by exact prefixLift 1623187
  have htrace : WordTrace (prefixWord ++ tailWord_1623187) baseStart_1623187 baseEnd_1623187 := by
    simpa [prefixWord, tailWord_1623187, baseEnd_1623187] using wordTrace_append hprefix tailTrace_1623187
  have hstable : (prefixWord ++ tailWord_1623187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623187).length < 2 ^ (prefixWord ++ tailWord_1623187).sum := by decide
  have hdescent : baseEnd_1623187 < baseStart_1623187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623210 : List Nat := [3, 1, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1623210 : Nat := 118140960795 + 1623210 * 2 ^ 59
def prefixEnd_1623210 : Nat := 4983230072969 + 3 ^ 40 * 1623210 * 2
def baseEnd_1623210 : Nat := 555657955456466278073333

theorem tailTrace_1623210 : CollatzResearch.WordTrace tailWord_1623210 prefixEnd_1623210 555657955456466278073333 := by
  unfold tailWord_1623210
  simp only [CollatzResearch.WordTrace]
  refine ⟨14800833112348716760580771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39468888299596578028215389 14800833112348716760580771)
  ·
    refine ⟨22201249668523075140871157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14800833112348716760580771 22201249668523075140871157)
    ·
      refine ⟨2081367156424038294456671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22201249668523075140871157 2081367156424038294456671)
      ·
        refine ⟨3122050734636057441685007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081367156424038294456671 3122050734636057441685007)
        ·
          refine ⟨4683076101954086162527511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122050734636057441685007 4683076101954086162527511)
          ·
            refine ⟨7024614152931129243791267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683076101954086162527511 7024614152931129243791267)
            ·
              refine ⟨10536921229396693865686901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024614152931129243791267 10536921229396693865686901)
              ·
                refine ⟨987836365255940049908147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10536921229396693865686901 987836365255940049908147)
                ·
                  refine ⟨1481754547883910074862221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987836365255940049908147 1481754547883910074862221)
                  ·
                    refine ⟨555657955456466278073333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481754547883910074862221 555657955456466278073333)
                    ·
                      rfl

theorem cell22_1623210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1623210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623210 prefixEnd_1623210 := by exact prefixLift 1623210
  have htrace : WordTrace (prefixWord ++ tailWord_1623210) baseStart_1623210 baseEnd_1623210 := by
    simpa [prefixWord, tailWord_1623210, baseEnd_1623210] using wordTrace_append hprefix tailTrace_1623210
  have hstable : (prefixWord ++ tailWord_1623210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623210).length < 2 ^ (prefixWord ++ tailWord_1623210).sum := by decide
  have hdescent : baseEnd_1623210 < baseStart_1623210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623253 : List Nat := [1, 3, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1623253 : Nat := 118140960795 + 1623253 * 2 ^ 59
def prefixEnd_1623253 : Nat := 4983230072969 + 3 ^ 40 * 1623253 * 2
def baseEnd_1623253 : Nat := 555672675235228499248201

theorem tailTrace_1623253 : CollatzResearch.WordTrace tailWord_1623253 prefixEnd_1623253 555672675235228499248201 := by
  unfold tailWord_1623253
  simp only [CollatzResearch.WordTrace]
  refine ⟨59204900788239085386138413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39469933858826056924092275 59204900788239085386138413)
  ·
    refine ⟨22201837795589657019801905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59204900788239085386138413 22201837795589657019801905)
    ·
      refine ⟨16651378346692242764851429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22201837795589657019801905 16651378346692242764851429)
      ·
        refine ⟨3122133440004795518409643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16651378346692242764851429 3122133440004795518409643)
        ·
          refine ⟨4683200160007193277614465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122133440004795518409643 4683200160007193277614465)
          ·
            refine ⟨3512400120005394958210849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683200160007193277614465 3512400120005394958210849)
            ·
              refine ⟨2634300090004046218658137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512400120005394958210849 2634300090004046218658137)
              ·
                refine ⟨1975725067503034663993603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634300090004046218658137 1975725067503034663993603)
                ·
                  refine ⟨2963587601254551995990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975725067503034663993603 2963587601254551995990405)
                  ·
                    refine ⟨555672675235228499248201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963587601254551995990405 555672675235228499248201)
                    ·
                      rfl

theorem cell22_1623253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1623253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623253 prefixEnd_1623253 := by exact prefixLift 1623253
  have htrace : WordTrace (prefixWord ++ tailWord_1623253) baseStart_1623253 baseEnd_1623253 := by
    simpa [prefixWord, tailWord_1623253, baseEnd_1623253] using wordTrace_append hprefix tailTrace_1623253
  have hstable : (prefixWord ++ tailWord_1623253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623253).length < 2 ^ (prefixWord ++ tailWord_1623253).sum := by decide
  have hdescent : baseEnd_1623253 < baseStart_1623253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623264 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_1623264 : Nat := 118140960795 + 1623264 * 2 ^ 59
def prefixEnd_1623264 : Nat := 4983230072969 + 3 ^ 40 * 1623264 * 2
def baseEnd_1623264 : Nat := 555676440760028137223167

theorem tailTrace_1623264 : CollatzResearch.WordTrace tailWord_1623264 prefixEnd_1623264 555676440760028137223167 := by
  unfold tailWord_1623264
  simp only [CollatzResearch.WordTrace]
  refine ⟨29602650995599617132394423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39470201327466156176525897 29602650995599617132394423)
  ·
    refine ⟨44403976493399425698591635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29602650995599617132394423 44403976493399425698591635)
    ·
      refine ⟨66605964740099138547887453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44403976493399425698591635 66605964740099138547887453)
      ·
        refine ⟨24977236777537176955457795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66605964740099138547887453 24977236777537176955457795)
        ·
          refine ⟨37465855166305765433186693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24977236777537176955457795 37465855166305765433186693)
          ·
            refine ⟨7024847843682331018722505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37465855166305765433186693 7024847843682331018722505)
            ·
              refine ⟨5268635882761748264041879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7024847843682331018722505 5268635882761748264041879)
              ·
                refine ⟨7902953824142622396062819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268635882761748264041879 7902953824142622396062819)
                ·
                  refine ⟨11854430736213933594094229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7902953824142622396062819 11854430736213933594094229)
                  ·
                    refine ⟨555676440760028137223167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11854430736213933594094229 555676440760028137223167)
                    ·
                      rfl

theorem cell22_1623264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_1623264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623264 prefixEnd_1623264 := by exact prefixLift 1623264
  have htrace : WordTrace (prefixWord ++ tailWord_1623264) baseStart_1623264 baseEnd_1623264 := by
    simpa [prefixWord, tailWord_1623264, baseEnd_1623264] using wordTrace_append hprefix tailTrace_1623264
  have hstable : (prefixWord ++ tailWord_1623264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623264).length < 2 ^ (prefixWord ++ tailWord_1623264).sum := by decide
  have hdescent : baseEnd_1623264 < baseStart_1623264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623300 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1623300 : Nat := 118140960795 + 1623300 * 2 ^ 59
def prefixEnd_1623300 : Nat := 4983230072969 + 3 ^ 40 * 1623300 * 2
def baseEnd_1623300 : Nat := 555688764295736043323057

theorem tailTrace_1623300 : CollatzResearch.WordTrace tailWord_1623300 prefixEnd_1623300 555688764295736043323057 := by
  unfold tailWord_1623300
  simp only [CollatzResearch.WordTrace]
  refine ⟨29603307509534406206549677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39471076679379208275399569 29603307509534406206549677)
  ·
    refine ⟨11101240316075402327456129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29603307509534406206549677 11101240316075402327456129)
    ·
      refine ⟨8325930237056551745592097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11101240316075402327456129 8325930237056551745592097)
      ·
        refine ⟨6244447677792413809194073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8325930237056551745592097 6244447677792413809194073)
        ·
          refine ⟨4683335758344310356895555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6244447677792413809194073 4683335758344310356895555)
          ·
            refine ⟨7025003637516465535343333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683335758344310356895555 7025003637516465535343333)
            ·
              refine ⟨1317188182034337287876875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7025003637516465535343333 1317188182034337287876875)
              ·
                refine ⟨1975782273051505931815313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317188182034337287876875 1975782273051505931815313)
                ·
                  refine ⟨1481836704788629448861485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1975782273051505931815313 1481836704788629448861485)
                  ·
                    refine ⟨555688764295736043323057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481836704788629448861485 555688764295736043323057)
                    ·
                      rfl

theorem cell22_1623300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1623300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623300 prefixEnd_1623300 := by exact prefixLift 1623300
  have htrace : WordTrace (prefixWord ++ tailWord_1623300) baseStart_1623300 baseEnd_1623300 := by
    simpa [prefixWord, tailWord_1623300, baseEnd_1623300] using wordTrace_append hprefix tailTrace_1623300
  have hstable : (prefixWord ++ tailWord_1623300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623300).length < 2 ^ (prefixWord ++ tailWord_1623300).sum := by decide
  have hdescent : baseEnd_1623300 < baseStart_1623300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623324 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_1623324 : Nat := 118140960795 + 1623324 * 2 ^ 59
def prefixEnd_1623324 : Nat := 4983230072969 + 3 ^ 40 * 1623324 * 2
def baseEnd_1623324 : Nat := 185232326662069326907661

theorem tailTrace_1623324 : CollatzResearch.WordTrace tailWord_1623324 prefixEnd_1623324 185232326662069326907661 := by
  unfold tailWord_1623324
  simp only [CollatzResearch.WordTrace]
  refine ⟨29603745185490932255986513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39471660247321243007982017 29603745185490932255986513)
  ·
    refine ⟨22202808889118199191989885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29603745185490932255986513 22202808889118199191989885)
    ·
      refine ⟨8326053333419324696996207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22202808889118199191989885 8326053333419324696996207)
      ·
        refine ⟨12489080000128987045494311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8326053333419324696996207 12489080000128987045494311)
        ·
          refine ⟨18733620000193480568241467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12489080000128987045494311 18733620000193480568241467)
          ·
            refine ⟨28100430000290220852362201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18733620000193480568241467 28100430000290220852362201)
            ·
              refine ⟨21075322500217665639271651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28100430000290220852362201 21075322500217665639271651)
              ·
                refine ⟨31612983750326498458907477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21075322500217665639271651 31612983750326498458907477)
                ·
                  refine ⟨185232326662069326907661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31612983750326498458907477 185232326662069326907661)
                  ·
                    rfl

theorem cell22_1623324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_1623324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623324 prefixEnd_1623324 := by exact prefixLift 1623324
  have htrace : WordTrace (prefixWord ++ tailWord_1623324) baseStart_1623324 baseEnd_1623324 := by
    simpa [prefixWord, tailWord_1623324, baseEnd_1623324] using wordTrace_append hprefix tailTrace_1623324
  have hstable : (prefixWord ++ tailWord_1623324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623324).length < 2 ^ (prefixWord ++ tailWord_1623324).sum := by decide
  have hdescent : baseEnd_1623324 < baseStart_1623324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623345 : List Nat := [1, 2, 2, 3, 3, 2, 1, 4, 1, 3]
def baseStart_1623345 : Nat := 118140960795 + 1623345 * 2 ^ 59
def prefixEnd_1623345 : Nat := 4983230072969 + 3 ^ 40 * 1623345 * 2
def baseEnd_1623345 : Nat := 555704168715370925947919

theorem tailTrace_1623345 : CollatzResearch.WordTrace tailWord_1623345 prefixEnd_1623345 555704168715370925947919 := by
  unfold tailWord_1623345
  simp only [CollatzResearch.WordTrace]
  refine ⟨59208256303905785098487489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39472170869270523398991659 59208256303905785098487489)
  ·
    refine ⟨44406192227929338823865617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59208256303905785098487489 44406192227929338823865617)
    ·
      refine ⟨33304644170947004117899213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44406192227929338823865617 33304644170947004117899213)
      ·
        refine ⟨12489241564105126544212205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33304644170947004117899213 12489241564105126544212205)
        ·
          refine ⟨4683465586539422454079577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12489241564105126544212205 4683465586539422454079577)
          ·
            refine ⟨3512599189904566840559683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683465586539422454079577 3512599189904566840559683)
            ·
              refine ⟨5268898784856850260839525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512599189904566840559683 5268898784856850260839525)
              ·
                refine ⟨987918522160659423907411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5268898784856850260839525 987918522160659423907411)
                ·
                  refine ⟨1481877783240989135861117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 987918522160659423907411 1481877783240989135861117)
                  ·
                    refine ⟨555704168715370925947919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481877783240989135861117 555704168715370925947919)
                    ·
                      rfl

theorem cell22_1623345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_1623345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623345 prefixEnd_1623345 := by exact prefixLift 1623345
  have htrace : WordTrace (prefixWord ++ tailWord_1623345) baseStart_1623345 baseEnd_1623345 := by
    simpa [prefixWord, tailWord_1623345, baseEnd_1623345] using wordTrace_append hprefix tailTrace_1623345
  have hstable : (prefixWord ++ tailWord_1623345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623345).length < 2 ^ (prefixWord ++ tailWord_1623345).sum := by decide
  have hdescent : baseEnd_1623345 < baseStart_1623345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623356 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 2, 5]
def baseStart_1623356 : Nat := 118140960795 + 1623356 * 2 ^ 59
def prefixEnd_1623356 : Nat := 4983230072969 + 3 ^ 40 * 1623356 * 2
def baseEnd_1623356 : Nat := 555707934240170563922885

theorem tailTrace_1623356 : CollatzResearch.WordTrace tailWord_1623356 prefixEnd_1623356 555707934240170563922885 := by
  unfold tailWord_1623356
  simp only [CollatzResearch.WordTrace]
  refine ⟨29604328753432966988568961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39472438337910622651425281 29604328753432966988568961)
  ·
    refine ⟨22203246565074725241426721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29604328753432966988568961 22203246565074725241426721)
    ·
      refine ⟨16652434923806043931070041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22203246565074725241426721 16652434923806043931070041)
      ·
        refine ⟨12489326192854532948302531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16652434923806043931070041 12489326192854532948302531)
        ·
          refine ⟨18733989289281799422453797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12489326192854532948302531 18733989289281799422453797)
          ·
            refine ⟨3512622991740337391710087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18733989289281799422453797 3512622991740337391710087)
            ·
              refine ⟨5268934487610506087565131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512622991740337391710087 5268934487610506087565131)
              ·
                refine ⟨7903401731415759131347697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268934487610506087565131 7903401731415759131347697)
                ·
                  refine ⟨5927551298561819348510773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7903401731415759131347697 5927551298561819348510773)
                  ·
                    refine ⟨555707934240170563922885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5927551298561819348510773 555707934240170563922885)
                    ·
                      rfl

theorem cell22_1623356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_1623356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623356 prefixEnd_1623356 := by exact prefixLift 1623356
  have htrace : WordTrace (prefixWord ++ tailWord_1623356) baseStart_1623356 baseEnd_1623356 := by
    simpa [prefixWord, tailWord_1623356, baseEnd_1623356] using wordTrace_append hprefix tailTrace_1623356
  have hstable : (prefixWord ++ tailWord_1623356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623356).length < 2 ^ (prefixWord ++ tailWord_1623356).sum := by decide
  have hdescent : baseEnd_1623356 < baseStart_1623356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623369 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 8]
def baseStart_1623369 : Nat := 118140960795 + 1623369 * 2 ^ 59
def prefixEnd_1623369 : Nat := 4983230072969 + 3 ^ 40 * 1623369 * 2
def baseEnd_1623369 : Nat := 185237461468614287782615

theorem tailTrace_1623369 : CollatzResearch.WordTrace tailWord_1623369 prefixEnd_1623369 185237461468614287782615 := by
  unfold tailWord_1623369
  simp only [CollatzResearch.WordTrace]
  refine ⟨59209131655818837197361161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39472754437212558131574107 59209131655818837197361161)
  ·
    refine ⟨44406848741864127898020871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59209131655818837197361161 44406848741864127898020871)
    ·
      refine ⟨66610273112796191847031307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44406848741864127898020871 66610273112796191847031307)
      ·
        refine ⟨99915409669194287770546961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66610273112796191847031307 99915409669194287770546961)
        ·
          refine ⟨74936557251895715827910221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99915409669194287770546961 74936557251895715827910221)
          ·
            refine ⟨28101208969460893435466333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74936557251895715827910221 28101208969460893435466333)
            ·
              refine ⟨10537953363547835038299875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28101208969460893435466333 10537953363547835038299875)
              ·
                refine ⟨15806930045321752557449813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10537953363547835038299875 15806930045321752557449813)
                ·
                  refine ⟨185237461468614287782615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15806930045321752557449813 185237461468614287782615)
                  ·
                    rfl

theorem cell22_1623369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_1623369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623369 prefixEnd_1623369 := by exact prefixLift 1623369
  have htrace : WordTrace (prefixWord ++ tailWord_1623369) baseStart_1623369 baseEnd_1623369 := by
    simpa [prefixWord, tailWord_1623369, baseEnd_1623369] using wordTrace_append hprefix tailTrace_1623369
  have hstable : (prefixWord ++ tailWord_1623369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623369).length < 2 ^ (prefixWord ++ tailWord_1623369).sum := by decide
  have hdescent : baseEnd_1623369 < baseStart_1623369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623431 : List Nat := [1, 1, 4, 2, 2, 3, 1, 8]
def baseStart_1623431 : Nat := 118140960795 + 1623431 * 2 ^ 59
def prefixEnd_1623431 : Nat := 4983230072969 + 3 ^ 40 * 1623431 * 2
def baseEnd_1623431 : Nat := 61748178696988374255295

theorem tailTrace_1623431 : CollatzResearch.WordTrace tailWord_1623431 prefixEnd_1623431 61748178696988374255295 := by
  unfold tailWord_1623431
  simp only [CollatzResearch.WordTrace]
  refine ⟨59211392981594221786118147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39474261987729481190745431 59211392981594221786118147)
  ·
    refine ⟨88817089472391332679177221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59211392981594221786118147 88817089472391332679177221)
    ·
      refine ⟨16653204276073374877345729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88817089472391332679177221 16653204276073374877345729)
      ·
        refine ⟨12489903207055031158009297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16653204276073374877345729 12489903207055031158009297)
        ·
          refine ⟨9367427405291273368506973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12489903207055031158009297 9367427405291273368506973)
          ·
            refine ⟨3512785276984227513190115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9367427405291273368506973 3512785276984227513190115)
            ·
              refine ⟨5269177915476341269785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512785276984227513190115 5269177915476341269785173)
              ·
                refine ⟨61748178696988374255295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5269177915476341269785173 61748178696988374255295)
                ·
                  rfl

theorem cell22_1623431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 8].length) (baseStart_1623431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623431 prefixEnd_1623431 := by exact prefixLift 1623431
  have htrace : WordTrace (prefixWord ++ tailWord_1623431) baseStart_1623431 baseEnd_1623431 := by
    simpa [prefixWord, tailWord_1623431, baseEnd_1623431] using wordTrace_append hprefix tailTrace_1623431
  have hstable : (prefixWord ++ tailWord_1623431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623431).length < 2 ^ (prefixWord ++ tailWord_1623431).sum := by decide
  have hdescent : baseEnd_1623431 < baseStart_1623431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623448 : List Nat := [2, 1, 2, 5, 2, 2, 8]
def baseStart_1623448 : Nat := 118140960795 + 1623448 * 2 ^ 59
def prefixEnd_1623448 : Nat := 4983230072969 + 3 ^ 40 * 1623448 * 2
def baseEnd_1623448 : Nat := 20582941767418999652689

theorem tailTrace_1623448 : CollatzResearch.WordTrace tailWord_1623448 prefixEnd_1623448 20582941767418999652689 := by
  unfold tailWord_1623448
  simp only [CollatzResearch.WordTrace]
  refine ⟨29606006511266316844743499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39474675348355089126324665 29606006511266316844743499)
  ·
    refine ⟨44409009766899475267115249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29606006511266316844743499 44409009766899475267115249)
    ·
      refine ⟨33306757325174606450336437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44409009766899475267115249 33306757325174606450336437)
      ·
        refine ⟨3122508499235119354719041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33306757325174606450336437 3122508499235119354719041)
        ·
          refine ⟨2341881374426339516039281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122508499235119354719041 2341881374426339516039281)
          ·
            refine ⟨1756411030819754637029461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2341881374426339516039281 1756411030819754637029461)
            ·
              refine ⟨20582941767418999652689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1756411030819754637029461 20582941767418999652689)
              ·
                rfl

theorem cell22_1623448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 8].length) (baseStart_1623448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623448 prefixEnd_1623448 := by exact prefixLift 1623448
  have htrace : WordTrace (prefixWord ++ tailWord_1623448) baseStart_1623448 baseEnd_1623448 := by
    simpa [prefixWord, tailWord_1623448, baseEnd_1623448] using wordTrace_append hprefix tailTrace_1623448
  have hstable : (prefixWord ++ tailWord_1623448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623448).length < 2 ^ (prefixWord ++ tailWord_1623448).sum := by decide
  have hdescent : baseEnd_1623448 < baseStart_1623448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623454 : List Nat := [4, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1623454 : Nat := 118140960795 + 1623454 * 2 ^ 59
def prefixEnd_1623454 : Nat := 4983230072969 + 3 ^ 40 * 1623454 * 2
def baseEnd_1623454 : Nat := 185247160547643658324195

theorem tailTrace_1623454 : CollatzResearch.WordTrace tailWord_1623454 prefixEnd_1623454 185247160547643658324195 := by
  unfold tailWord_1623454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401528982563862089275677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39474821240340597809470277 7401528982563862089275677)
  ·
    refine ⟨2775573368461448283478379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7401528982563862089275677 2775573368461448283478379)
    ·
      refine ⟨4163360052692172425217569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2775573368461448283478379 4163360052692172425217569)
      ·
        refine ⟨3122520039519129318913177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4163360052692172425217569 3122520039519129318913177)
        ·
          refine ⟨2341890029639346989184883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122520039519129318913177 2341890029639346989184883)
          ·
            refine ⟨3512835044459020483777325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341890029639346989184883 3512835044459020483777325)
            ·
              refine ⟨1317313141672132681416497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3512835044459020483777325 1317313141672132681416497)
              ·
                refine ⟨987984856254099511062373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1317313141672132681416497 987984856254099511062373)
                ·
                  refine ⟨185247160547643658324195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 987984856254099511062373 185247160547643658324195)
                  ·
                    rfl

theorem cell22_1623454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1623454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623454 prefixEnd_1623454 := by exact prefixLift 1623454
  have htrace : WordTrace (prefixWord ++ tailWord_1623454) baseStart_1623454 baseEnd_1623454 := by
    simpa [prefixWord, tailWord_1623454, baseEnd_1623454] using wordTrace_append hprefix tailTrace_1623454
  have hstable : (prefixWord ++ tailWord_1623454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623454).length < 2 ^ (prefixWord ++ tailWord_1623454).sum := by decide
  have hdescent : baseEnd_1623454 < baseStart_1623454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1623469 : List Nat := [1, 5, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1623469 : Nat := 118140960795 + 1623469 * 2 ^ 59
def prefixEnd_1623469 : Nat := 4983230072969 + 3 ^ 40 * 1623469 * 2
def baseEnd_1623469 : Nat := 555746616449475935847539

theorem tailTrace_1623469 : CollatzResearch.WordTrace tailWord_1623469 prefixEnd_1623469 555746616449475935847539 := by
  unfold tailWord_1623469
  simp only [CollatzResearch.WordTrace]
  refine ⟨59212778955456554276001461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39475185970304369517334307 59212778955456554276001461)
  ·
    refine ⟨5551198027074051963375137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59212778955456554276001461 5551198027074051963375137)
    ·
      refine ⟨4163398520305538972531353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5551198027074051963375137 4163398520305538972531353)
      ·
        refine ⟨3122548890229154229398515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4163398520305538972531353 3122548890229154229398515)
        ·
          refine ⟨4683823335343731344097773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122548890229154229398515 4683823335343731344097773)
          ·
            refine ⟨1756433750753899254036665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4683823335343731344097773 1756433750753899254036665)
            ·
              refine ⟨1317325313065424440527499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1756433750753899254036665 1317325313065424440527499)
              ·
                refine ⟨1975987969598136660791249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1317325313065424440527499 1975987969598136660791249)
                ·
                  refine ⟨1481990977198602495593437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1975987969598136660791249 1481990977198602495593437)
                  ·
                    refine ⟨555746616449475935847539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1481990977198602495593437 555746616449475935847539)
                    ·
                      rfl

theorem cell22_1623469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1623469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1623469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1623469 prefixEnd_1623469 := by exact prefixLift 1623469
  have htrace : WordTrace (prefixWord ++ tailWord_1623469) baseStart_1623469 baseEnd_1623469 := by
    simpa [prefixWord, tailWord_1623469, baseEnd_1623469] using wordTrace_append hprefix tailTrace_1623469
  have hstable : (prefixWord ++ tailWord_1623469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1623469).length < 2 ^ (prefixWord ++ tailWord_1623469).sum := by decide
  have hdescent : baseEnd_1623469 < baseStart_1623469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1623469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
