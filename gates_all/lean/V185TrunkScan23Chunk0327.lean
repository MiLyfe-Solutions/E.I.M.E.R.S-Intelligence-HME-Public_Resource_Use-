import V185TrunkScan23Chunk0326

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1932804 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_1932804 : Nat := 118140960795 + 1932804 * 2 ^ 59
def prefixEnd_1932804 : Nat := 4983230072969 + 3 ^ 40 * 1932804 * 2
def baseEnd_1932804 : Nat := 992457462932761129161203

theorem tailTrace_1932804 : CollatzResearch.WordTrace tailWord_1932804 prefixEnd_1932804 992457462932761129161203 := by
  unfold tailWord_1932804
  simp only [CollatzResearch.WordTrace]
  refine ⟨35247576644894339743986733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46996768859859119658648977 35247576644894339743986733)
  ·
    refine ⟨13217841241835377403995025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35247576644894339743986733 13217841241835377403995025)
    ·
      refine ⟨9913380931376533052996269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13217841241835377403995025 9913380931376533052996269)
      ·
        refine ⟨3717517849266199894873601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9913380931376533052996269 3717517849266199894873601)
        ·
          refine ⟨2788138386949649921155201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717517849266199894873601 2788138386949649921155201)
          ·
            refine ⟨2091103790212237440866401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788138386949649921155201 2091103790212237440866401)
            ·
              refine ⟨1568327842659178080649801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091103790212237440866401 1568327842659178080649801)
              ·
                refine ⟨1176245881994383560487351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568327842659178080649801 1176245881994383560487351)
                ·
                  refine ⟨1764368822991575340731027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176245881994383560487351 1764368822991575340731027)
                  ·
                    refine ⟨2646553234487363011096541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764368822991575340731027 2646553234487363011096541)
                    ·
                      refine ⟨992457462932761129161203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646553234487363011096541 992457462932761129161203)
                      ·
                        rfl

theorem cell23_1932804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_1932804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932804 prefixEnd_1932804 := by exact prefixLift 1932804
  have htrace : WordTrace (prefixWord ++ tailWord_1932804) baseStart_1932804 baseEnd_1932804 := by
    simpa [prefixWord, tailWord_1932804, baseEnd_1932804] using wordTrace_append hprefix tailTrace_1932804
  have hstable : (prefixWord ++ tailWord_1932804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932804).length < 2 ^ (prefixWord ++ tailWord_1932804).sum := by decide
  have hdescent : baseEnd_1932804 < baseStart_1932804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932809 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_1932809 : Nat := 118140960795 + 1932809 * 2 ^ 59
def prefixEnd_1932809 : Nat := 4983230072969 + 3 ^ 40 * 1932809 * 2
def baseEnd_1932809 : Nat := 992460030336033609598679

theorem tailTrace_1932809 : CollatzResearch.WordTrace tailWord_1932809 prefixEnd_1932809 992460030336033609598679 := by
  unfold tailWord_1932809
  simp only [CollatzResearch.WordTrace]
  refine ⟨70495335654770565341905481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46996890436513710227936987 70495335654770565341905481)
  ·
    refine ⟨52871501741077924006429111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70495335654770565341905481 52871501741077924006429111)
    ·
      refine ⟨79307252611616886009643667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52871501741077924006429111 79307252611616886009643667)
      ·
        refine ⟨118960878917425329014465501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79307252611616886009643667 118960878917425329014465501)
        ·
          refine ⟨44610329594034498380424563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118960878917425329014465501 44610329594034498380424563)
          ·
            refine ⟨66915494391051747570636845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44610329594034498380424563 66915494391051747570636845)
            ·
              refine ⟨25093310396644405338988817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66915494391051747570636845 25093310396644405338988817)
              ·
                refine ⟨18819982797483304004241613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25093310396644405338988817 18819982797483304004241613)
                ·
                  refine ⟨7057493549056239001590605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18819982797483304004241613 7057493549056239001590605)
                  ·
                    refine ⟨2646560080896089625596477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7057493549056239001590605 2646560080896089625596477)
                    ·
                      refine ⟨992460030336033609598679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646560080896089625596477 992460030336033609598679)
                      ·
                        rfl

theorem cell23_1932809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_1932809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932809 prefixEnd_1932809 := by exact prefixLift 1932809
  have htrace : WordTrace (prefixWord ++ tailWord_1932809) baseStart_1932809 baseEnd_1932809 := by
    simpa [prefixWord, tailWord_1932809, baseEnd_1932809] using wordTrace_append hprefix tailTrace_1932809
  have hstable : (prefixWord ++ tailWord_1932809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932809).length < 2 ^ (prefixWord ++ tailWord_1932809).sum := by decide
  have hdescent : baseEnd_1932809 < baseStart_1932809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932826 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3]
def baseStart_1932826 : Nat := 118140960795 + 1932826 * 2 ^ 59
def prefixEnd_1932826 : Nat := 4983230072969 + 3 ^ 40 * 1932826 * 2
def baseEnd_1932826 : Nat := 992468759507160043086101

theorem tailTrace_1932826 : CollatzResearch.WordTrace tailWord_1932826 prefixEnd_1932826 992468759507160043086101 := by
  unfold tailWord_1932826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17623988923927244311318583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46997303797139318163516221 17623988923927244311318583)
  ·
    refine ⟨26435983385890866466977875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17623988923927244311318583 26435983385890866466977875)
    ·
      refine ⟨39653975078836299700466813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26435983385890866466977875 39653975078836299700466813)
      ·
        refine ⟨14870240654563612387675055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39653975078836299700466813 14870240654563612387675055)
        ·
          refine ⟨22305360981845418581512583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14870240654563612387675055 22305360981845418581512583)
          ·
            refine ⟨33458041472768127872268875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22305360981845418581512583 33458041472768127872268875)
            ·
              refine ⟨50187062209152191808403313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33458041472768127872268875 50187062209152191808403313)
              ·
                refine ⟨37640296656864143856302485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50187062209152191808403313 37640296656864143856302485)
                ·
                  refine ⟨1764388905790506743264179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37640296656864143856302485 1764388905790506743264179)
                  ·
                    refine ⟨2646583358685760114896269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764388905790506743264179 2646583358685760114896269)
                    ·
                      refine ⟨992468759507160043086101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646583358685760114896269 992468759507160043086101)
                      ·
                        rfl

theorem cell23_1932826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_1932826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932826 prefixEnd_1932826 := by exact prefixLift 1932826
  have htrace : WordTrace (prefixWord ++ tailWord_1932826) baseStart_1932826 baseEnd_1932826 := by
    simpa [prefixWord, tailWord_1932826, baseEnd_1932826] using wordTrace_append hprefix tailTrace_1932826
  have hstable : (prefixWord ++ tailWord_1932826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932826).length < 2 ^ (prefixWord ++ tailWord_1932826).sum := by decide
  have hdescent : baseEnd_1932826 < baseStart_1932826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932829 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1932829 : Nat := 118140960795 + 1932829 * 2 ^ 59
def prefixEnd_1932829 : Nat := 4983230072969 + 3 ^ 40 * 1932829 * 2
def baseEnd_1932829 : Nat := 330823433316374510449529

theorem tailTrace_1932829 : CollatzResearch.WordTrace tailWord_1932829 prefixEnd_1932829 330823433316374510449529 := by
  unfold tailWord_1932829
  simp only [CollatzResearch.WordTrace]
  refine ⟨70496065114698108757633541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46997376743132072505089027 70496065114698108757633541)
  ·
    refine ⟨13218012209005895392056289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70496065114698108757633541 13218012209005895392056289)
    ·
      refine ⟨9913509156754421544042217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13218012209005895392056289 9913509156754421544042217)
      ·
        refine ⟨7435131867565816158031663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9913509156754421544042217 7435131867565816158031663)
        ·
          refine ⟨11152697801348724237047495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435131867565816158031663 11152697801348724237047495)
          ·
            refine ⟨16729046702023086355571243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11152697801348724237047495 16729046702023086355571243)
            ·
              refine ⟨25093570053034629533356865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16729046702023086355571243 25093570053034629533356865)
              ·
                refine ⟨18820177539775972150017649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25093570053034629533356865 18820177539775972150017649)
                ·
                  refine ⟨14115133154831979112513237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18820177539775972150017649 14115133154831979112513237)
                  ·
                    refine ⟨330823433316374510449529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14115133154831979112513237 330823433316374510449529)
                    ·
                      rfl

theorem cell23_1932829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1932829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932829 prefixEnd_1932829 := by exact prefixLift 1932829
  have htrace : WordTrace (prefixWord ++ tailWord_1932829) baseStart_1932829 baseEnd_1932829 := by
    simpa [prefixWord, tailWord_1932829, baseEnd_1932829] using wordTrace_append hprefix tailTrace_1932829
  have hstable : (prefixWord ++ tailWord_1932829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932829).length < 2 ^ (prefixWord ++ tailWord_1932829).sum := by decide
  have hdescent : baseEnd_1932829 < baseStart_1932829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932877 : List Nat := [1, 6, 1, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_1932877 : Nat := 118140960795 + 1932877 * 2 ^ 59
def prefixEnd_1932877 : Nat := 4983230072969 + 3 ^ 40 * 1932877 * 2
def baseEnd_1932877 : Nat := 992494947020539343548367

theorem tailTrace_1932877 : CollatzResearch.WordTrace tailWord_1932877 prefixEnd_1932877 992494947020539343548367 := by
  unfold tailWord_1932877
  simp only [CollatzResearch.WordTrace]
  refine ⟨70497815818524212955380885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46998543879016141970253923 70497815818524212955380885)
  ·
    refine ⟨3304585116493322482283479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70497815818524212955380885 3304585116493322482283479)
    ·
      refine ⟨4956877674739983723425219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3304585116493322482283479 4956877674739983723425219)
      ·
        refine ⟨7435316512109975585137829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4956877674739983723425219 7435316512109975585137829)
        ·
          refine ⟨1394121846020620422213343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7435316512109975585137829 1394121846020620422213343)
          ·
            refine ⟨2091182769030930633320015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394121846020620422213343 2091182769030930633320015)
            ·
              refine ⟨3136774153546395949980023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091182769030930633320015 3136774153546395949980023)
              ·
                refine ⟨4705161230319593924970035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136774153546395949980023 4705161230319593924970035)
                ·
                  refine ⟨7057741845479390887455053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4705161230319593924970035 7057741845479390887455053)
                  ·
                    refine ⟨2646653192054771582795645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7057741845479390887455053 2646653192054771582795645)
                    ·
                      refine ⟨992494947020539343548367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646653192054771582795645 992494947020539343548367)
                      ·
                        rfl

theorem cell23_1932877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_1932877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932877 prefixEnd_1932877 := by exact prefixLift 1932877
  have htrace : WordTrace (prefixWord ++ tailWord_1932877) baseStart_1932877 baseEnd_1932877 := by
    simpa [prefixWord, tailWord_1932877, baseEnd_1932877] using wordTrace_append hprefix tailTrace_1932877
  have hstable : (prefixWord ++ tailWord_1932877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932877).length < 2 ^ (prefixWord ++ tailWord_1932877).sum := by decide
  have hdescent : baseEnd_1932877 < baseStart_1932877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932923 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 5]
def baseStart_1932923 : Nat := 118140960795 + 1932923 * 2 ^ 59
def prefixEnd_1932923 : Nat := 4983230072969 + 3 ^ 40 * 1932923 * 2
def baseEnd_1932923 : Nat := 110279840792294018174795

theorem tailTrace_1932923 : CollatzResearch.WordTrace tailWord_1932923 prefixEnd_1932923 110279840792294018174795 := by
  unfold tailWord_1932923
  simp only [CollatzResearch.WordTrace]
  refine ⟨70499493576357562811555423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46999662384238375207703615 70499493576357562811555423)
  ·
    refine ⟨105749240364536344217333135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70499493576357562811555423 105749240364536344217333135)
    ·
      refine ⟨158623860546804516325999703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105749240364536344217333135 158623860546804516325999703)
      ·
        refine ⟨237935790820206774488999555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158623860546804516325999703 237935790820206774488999555)
        ·
          refine ⟨356903686230310161733499333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 237935790820206774488999555 356903686230310161733499333)
          ·
            refine ⟨66919441168183155325031125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 356903686230310161733499333 66919441168183155325031125)
            ·
              refine ⟨1568424402379292702930417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 66919441168183155325031125 1568424402379292702930417)
              ·
                refine ⟨1176318301784469527197813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568424402379292702930417 1176318301784469527197813)
                ·
                  refine ⟨110279840792294018174795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176318301784469527197813 110279840792294018174795)
                  ·
                    rfl

theorem cell23_1932923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 5].length) (baseStart_1932923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932923 prefixEnd_1932923 := by exact prefixLift 1932923
  have htrace : WordTrace (prefixWord ++ tailWord_1932923) baseStart_1932923 baseEnd_1932923 := by
    simpa [prefixWord, tailWord_1932923, baseEnd_1932923] using wordTrace_append hprefix tailTrace_1932923
  have hstable : (prefixWord ++ tailWord_1932923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932923).length < 2 ^ (prefixWord ++ tailWord_1932923).sum := by decide
  have hdescent : baseEnd_1932923 < baseStart_1932923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932949 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_1932949 : Nat := 118140960795 + 1932949 * 2 ^ 59
def prefixEnd_1932949 : Nat := 4983230072969 + 3 ^ 40 * 1932949 * 2
def baseEnd_1932949 : Nat := 330843972542554353949345

theorem tailTrace_1932949 : CollatzResearch.WordTrace tailWord_1932949 prefixEnd_1932949 330843972542554353949345 := by
  unfold tailWord_1932949
  simp only [CollatzResearch.WordTrace]
  refine ⟨70500441874263369252001901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47000294582842246168001267 70500441874263369252001901)
  ·
    refine ⟨26437665702848763469500713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70500441874263369252001901 26437665702848763469500713)
    ·
      refine ⟨19828249277136572602125535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26437665702848763469500713 19828249277136572602125535)
      ·
        refine ⟨29742373915704858903188303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19828249277136572602125535 29742373915704858903188303)
        ·
          refine ⟨44613560873557288354782455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29742373915704858903188303 44613560873557288354782455)
          ·
            refine ⟨66920341310335932532173683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44613560873557288354782455 66920341310335932532173683)
            ·
              refine ⟨100380511965503898798260525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66920341310335932532173683 100380511965503898798260525)
              ·
                refine ⟨37642691987063962049347697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100380511965503898798260525 37642691987063962049347697)
                ·
                  refine ⟨28232018990297971537010773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37642691987063962049347697 28232018990297971537010773)
                  ·
                    refine ⟨330843972542554353949345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28232018990297971537010773 330843972542554353949345)
                    ·
                      rfl

theorem cell23_1932949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_1932949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932949 prefixEnd_1932949 := by exact prefixLift 1932949
  have htrace : WordTrace (prefixWord ++ tailWord_1932949) baseStart_1932949 baseEnd_1932949 := by
    simpa [prefixWord, tailWord_1932949, baseEnd_1932949] using wordTrace_append hprefix tailTrace_1932949
  have hstable : (prefixWord ++ tailWord_1932949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932949).length < 2 ^ (prefixWord ++ tailWord_1932949).sum := by decide
  have hdescent : baseEnd_1932949 < baseStart_1932949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932973 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1932973 : Nat := 118140960795 + 1932973 * 2 ^ 59
def prefixEnd_1932973 : Nat := 4983230072969 + 3 ^ 40 * 1932973 * 2
def baseEnd_1932973 : Nat := 992544241163370967947925

theorem tailTrace_1932973 : CollatzResearch.WordTrace tailWord_1932973 prefixEnd_1932973 992544241163370967947925 := by
  unfold tailWord_1932973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70501317226176421350875573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47000878150784280900583715 70501317226176421350875573)
  ·
    refine ⟨6609498489954039501644585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70501317226176421350875573 6609498489954039501644585)
    ·
      refine ⟨4957123867465529626233439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6609498489954039501644585 4957123867465529626233439)
      ·
        refine ⟨7435685801198294439350159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957123867465529626233439 7435685801198294439350159)
        ·
          refine ⟨11153528701797441659025239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7435685801198294439350159 11153528701797441659025239)
          ·
            refine ⟨16730293052696162488537859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11153528701797441659025239 16730293052696162488537859)
            ·
              refine ⟨25095439579044243732806789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730293052696162488537859 25095439579044243732806789)
              ·
                refine ⟨4705394921070795699901273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25095439579044243732806789 4705394921070795699901273)
                ·
                  refine ⟨3529046190803096774925955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705394921070795699901273 3529046190803096774925955)
                  ·
                    refine ⟨5293569286204645162388933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3529046190803096774925955 5293569286204645162388933)
                    ·
                      refine ⟨992544241163370967947925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5293569286204645162388933 992544241163370967947925)
                      ·
                        rfl

theorem cell23_1932973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1932973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932973 prefixEnd_1932973 := by exact prefixLift 1932973
  have htrace : WordTrace (prefixWord ++ tailWord_1932973) baseStart_1932973 baseEnd_1932973 := by
    simpa [prefixWord, tailWord_1932973, baseEnd_1932973] using wordTrace_append hprefix tailTrace_1932973
  have hstable : (prefixWord ++ tailWord_1932973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932973).length < 2 ^ (prefixWord ++ tailWord_1932973).sum := by decide
  have hdescent : baseEnd_1932973 < baseStart_1932973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932974 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_1932974 : Nat := 118140960795 + 1932974 * 2 ^ 59
def prefixEnd_1932974 : Nat := 4983230072969 + 3 ^ 40 * 1932974 * 2
def baseEnd_1932974 : Nat := 110282750516002829337269

theorem tailTrace_1932974 : CollatzResearch.WordTrace tailWord_1932974 prefixEnd_1932974 110282750516002829337269 := by
  unfold tailWord_1932974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8812669212396599815207747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47000902466115199014441317 8812669212396599815207747)
  ·
    refine ⟨13219003818594899722811621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8812669212396599815207747 13219003818594899722811621)
    ·
      refine ⟨2478563215986543698027179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13219003818594899722811621 2478563215986543698027179)
      ·
        refine ⟨3717844823979815547040769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2478563215986543698027179 3717844823979815547040769)
        ·
          refine ⟨2788383617984861660280577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3717844823979815547040769 2788383617984861660280577)
          ·
            refine ⟨2091287713488646245210433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788383617984861660280577 2091287713488646245210433)
            ·
              refine ⟨1568465785116484683907825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091287713488646245210433 1568465785116484683907825)
              ·
                refine ⟨1176349338837363512930869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568465785116484683907825 1176349338837363512930869)
                ·
                  refine ⟨110282750516002829337269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176349338837363512930869 110282750516002829337269)
                  ·
                    rfl

theorem cell23_1932974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_1932974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932974 prefixEnd_1932974 := by exact prefixLift 1932974
  have htrace : WordTrace (prefixWord ++ tailWord_1932974) baseStart_1932974 baseEnd_1932974 := by
    simpa [prefixWord, tailWord_1932974, baseEnd_1932974] using wordTrace_append hprefix tailTrace_1932974
  have hstable : (prefixWord ++ tailWord_1932974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932974).length < 2 ^ (prefixWord ++ tailWord_1932974).sum := by decide
  have hdescent : baseEnd_1932974 < baseStart_1932974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1932990 : List Nat := [4, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2]
def baseStart_1932990 : Nat := 118140960795 + 1932990 * 2 ^ 59
def prefixEnd_1932990 : Nat := 4983230072969 + 3 ^ 40 * 1932990 * 2
def baseEnd_1932990 : Nat := 992552970334497401435347

theorem tailTrace_1932990 : CollatzResearch.WordTrace tailWord_1932990 prefixEnd_1932990 992552970334497401435347 := by
  unfold tailWord_1932990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8812742158389354156780553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47001291511409888836162949 8812742158389354156780553)
  ·
    refine ⟨6609556618792015617585415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8812742158389354156780553 6609556618792015617585415)
    ·
      refine ⟨9914334928188023426378123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609556618792015617585415 9914334928188023426378123)
      ·
        refine ⟨14871502392282035139567185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914334928188023426378123 14871502392282035139567185)
        ·
          refine ⟨11153626794211526354675389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14871502392282035139567185 11153626794211526354675389)
          ·
            refine ⟨4182610047829322383003271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11153626794211526354675389 4182610047829322383003271)
            ·
              refine ⟨6273915071743983574504907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4182610047829322383003271 6273915071743983574504907)
              ·
                refine ⟨9410872607615975361757361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6273915071743983574504907 9410872607615975361757361)
                ·
                  refine ⟨7058154455711981521318021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9410872607615975361757361 7058154455711981521318021)
                  ·
                    refine ⟨1323403960445996535247129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7058154455711981521318021 1323403960445996535247129)
                    ·
                      refine ⟨992552970334497401435347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323403960445996535247129 992552970334497401435347)
                      ·
                        rfl

theorem cell23_1932990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_1932990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1932990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1932990 prefixEnd_1932990 := by exact prefixLift 1932990
  have htrace : WordTrace (prefixWord ++ tailWord_1932990) baseStart_1932990 baseEnd_1932990 := by
    simpa [prefixWord, tailWord_1932990, baseEnd_1932990] using wordTrace_append hprefix tailTrace_1932990
  have hstable : (prefixWord ++ tailWord_1932990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1932990).length < 2 ^ (prefixWord ++ tailWord_1932990).sum := by decide
  have hdescent : baseEnd_1932990 < baseStart_1932990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1932990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933010 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1933010 : Nat := 118140960795 + 1933010 * 2 ^ 59
def prefixEnd_1933010 : Nat := 4983230072969 + 3 ^ 40 * 1933010 * 2
def baseEnd_1933010 : Nat := 992563239947587323185255

theorem tailTrace_1933010 : CollatzResearch.WordTrace tailWord_1933010 prefixEnd_1933010 992563239947587323185255 := by
  unfold tailWord_1933010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17625666681760594167493121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47001777818028251113314989 17625666681760594167493121)
  ·
    refine ⟨13219250011320445625619841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17625666681760594167493121 13219250011320445625619841)
    ·
      refine ⟨9914437508490334219214881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13219250011320445625619841 9914437508490334219214881)
      ·
        refine ⟨7435828131367750664411161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9914437508490334219214881 7435828131367750664411161)
        ·
          refine ⟨5576871098525812998308371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7435828131367750664411161 5576871098525812998308371)
          ·
            refine ⟨8365306647788719497462557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5576871098525812998308371 8365306647788719497462557)
            ·
              refine ⟨3136989992920769811548459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8365306647788719497462557 3136989992920769811548459)
              ·
                refine ⟨4705484989381154717322689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3136989992920769811548459 4705484989381154717322689)
                ·
                  refine ⟨3529113742035866037992017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4705484989381154717322689 3529113742035866037992017)
                  ·
                    refine ⟨2646835306526899528494013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529113742035866037992017 2646835306526899528494013)
                    ·
                      refine ⟨992563239947587323185255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646835306526899528494013 992563239947587323185255)
                      ·
                        rfl

theorem cell23_1933010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1933010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933010 prefixEnd_1933010 := by exact prefixLift 1933010
  have htrace : WordTrace (prefixWord ++ tailWord_1933010) baseStart_1933010 baseEnd_1933010 := by
    simpa [prefixWord, tailWord_1933010, baseEnd_1933010] using wordTrace_append hprefix tailTrace_1933010
  have hstable : (prefixWord ++ tailWord_1933010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933010).length < 2 ^ (prefixWord ++ tailWord_1933010).sum := by decide
  have hdescent : baseEnd_1933010 < baseStart_1933010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933023 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 3]
def baseStart_1933023 : Nat := 118140960795 + 1933023 * 2 ^ 59
def prefixEnd_1933023 : Nat := 4983230072969 + 3 ^ 40 * 1933023 * 2
def baseEnd_1933023 : Nat := 992569915196095772322695

theorem tailTrace_1933023 : CollatzResearch.WordTrace tailWord_1933023 prefixEnd_1933023 992569915196095772322695 := by
  unfold tailWord_1933023
  simp only [CollatzResearch.WordTrace]
  refine ⟨70503140875995279890195723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47002093917330186593463815 70503140875995279890195723)
  ·
    refine ⟨105754711313992919835293585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70503140875995279890195723 105754711313992919835293585)
    ·
      refine ⟨79316033485494689876470189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105754711313992919835293585 79316033485494689876470189)
      ·
        refine ⟨29743512557060508703676321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79316033485494689876470189 29743512557060508703676321)
        ·
          refine ⟨22307634417795381527757241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29743512557060508703676321 22307634417795381527757241)
          ·
            refine ⟨16730725813346536145817931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22307634417795381527757241 16730725813346536145817931)
            ·
              refine ⟨25096088720019804218726897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16730725813346536145817931 25096088720019804218726897)
              ·
                refine ⟨18822066540014853164045173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25096088720019804218726897 18822066540014853164045173)
                ·
                  refine ⟨1764568738126392484129235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18822066540014853164045173 1764568738126392484129235)
                  ·
                    refine ⟨2646853107189588726193853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764568738126392484129235 2646853107189588726193853)
                    ·
                      refine ⟨992569915196095772322695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646853107189588726193853 992569915196095772322695)
                      ·
                        rfl

theorem cell23_1933023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_1933023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933023 prefixEnd_1933023 := by exact prefixLift 1933023
  have htrace : WordTrace (prefixWord ++ tailWord_1933023) baseStart_1933023 baseEnd_1933023 := by
    simpa [prefixWord, tailWord_1933023, baseEnd_1933023] using wordTrace_append hprefix tailTrace_1933023
  have hstable : (prefixWord ++ tailWord_1933023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933023).length < 2 ^ (prefixWord ++ tailWord_1933023).sum := by decide
  have hdescent : baseEnd_1933023 < baseStart_1933023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933033 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 4, 3, 2]
def baseStart_1933033 : Nat := 118140960795 + 1933033 * 2 ^ 59
def prefixEnd_1933033 : Nat := 4983230072969 + 3 ^ 40 * 1933033 * 2
def baseEnd_1933033 : Nat := 992575050002640733197649

theorem tailTrace_1933033 : CollatzResearch.WordTrace tailWord_1933033 prefixEnd_1933033 992575050002640733197649 := by
  unfold tailWord_1933033
  simp only [CollatzResearch.WordTrace]
  refine ⟨70503505605959051598059753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47002337070639367732039835 70503505605959051598059753)
  ·
    refine ⟨52877629204469288698544815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70503505605959051598059753 52877629204469288698544815)
    ·
      refine ⟨79316443806703933047817223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52877629204469288698544815 79316443806703933047817223)
      ·
        refine ⟨118974665710055899571725835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79316443806703933047817223 118974665710055899571725835)
        ·
          refine ⟨178461998565083849357588753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118974665710055899571725835 178461998565083849357588753)
          ·
            refine ⟨133846498923812887018191565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178461998565083849357588753 133846498923812887018191565)
            ·
              refine ⟨50192437096429832631821837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133846498923812887018191565 50192437096429832631821837)
              ·
                refine ⟨18822163911161187236933189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50192437096429832631821837 18822163911161187236933189)
                ·
                  refine ⟨3529155733342722606924973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18822163911161187236933189 3529155733342722606924973)
                  ·
                    refine ⟨1323433400003520977596865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529155733342722606924973 1323433400003520977596865)
                    ·
                      refine ⟨992575050002640733197649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323433400003520977596865 992575050002640733197649)
                      ·
                        rfl

theorem cell23_1933033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 3, 2].length) (baseStart_1933033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933033 prefixEnd_1933033 := by exact prefixLift 1933033
  have htrace : WordTrace (prefixWord ++ tailWord_1933033) baseStart_1933033 baseEnd_1933033 := by
    simpa [prefixWord, tailWord_1933033, baseEnd_1933033] using wordTrace_append hprefix tailTrace_1933033
  have hstable : (prefixWord ++ tailWord_1933033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933033).length < 2 ^ (prefixWord ++ tailWord_1933033).sum := by decide
  have hdescent : baseEnd_1933033 < baseStart_1933033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933060 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1933060 : Nat := 118140960795 + 1933060 * 2 ^ 59
def prefixEnd_1933060 : Nat := 4983230072969 + 3 ^ 40 * 1933060 * 2
def baseEnd_1933060 : Nat := 330862971326770709186675

theorem tailTrace_1933060 : CollatzResearch.WordTrace tailWord_1933060 prefixEnd_1933060 330862971326770709186675 := by
  unfold tailWord_1933060
  simp only [CollatzResearch.WordTrace]
  refine ⟨35252245188430617604646317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47002993584574156806195089 35252245188430617604646317)
  ·
    refine ⟨13219591945661481601742369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35252245188430617604646317 13219591945661481601742369)
    ·
      refine ⟨9914693959246111201306777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13219591945661481601742369 9914693959246111201306777)
      ·
        refine ⟨7436020469434583400980083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9914693959246111201306777 7436020469434583400980083)
        ·
          refine ⟨11154030704151875101470125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436020469434583400980083 11154030704151875101470125)
          ·
            refine ⟨4182761514056953163051297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11154030704151875101470125 4182761514056953163051297)
            ·
              refine ⟨3137071135542714872288473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4182761514056953163051297 3137071135542714872288473)
              ·
                refine ⟨2352803351657036154216355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137071135542714872288473 2352803351657036154216355)
                ·
                  refine ⟨3529205027485554231324533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352803351657036154216355 3529205027485554231324533)
                  ·
                    refine ⟨330862971326770709186675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3529205027485554231324533 330862971326770709186675)
                    ·
                      rfl

theorem cell23_1933060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1933060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933060 prefixEnd_1933060 := by exact prefixLift 1933060
  have htrace : WordTrace (prefixWord ++ tailWord_1933060) baseStart_1933060 baseEnd_1933060 := by
    simpa [prefixWord, tailWord_1933060, baseEnd_1933060] using wordTrace_append hprefix tailTrace_1933060
  have hstable : (prefixWord ++ tailWord_1933060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933060).length < 2 ^ (prefixWord ++ tailWord_1933060).sum := by decide
  have hdescent : baseEnd_1933060 < baseStart_1933060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933080 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_1933080 : Nat := 118140960795 + 1933080 * 2 ^ 59
def prefixEnd_1933080 : Nat := 4983230072969 + 3 ^ 40 * 1933080 * 2
def baseEnd_1933080 : Nat := 992599183593402049309933

theorem tailTrace_1933080 : CollatzResearch.WordTrace tailWord_1933080 prefixEnd_1933080 992599183593402049309933 := by
  unfold tailWord_1933080
  simp only [CollatzResearch.WordTrace]
  refine ⟨35252609918394389312510347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47003479891192519083347129 35252609918394389312510347)
  ·
    refine ⟨52878914877591583968765521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35252609918394389312510347 52878914877591583968765521)
    ·
      refine ⟨39659186158193687976574141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52878914877591583968765521 39659186158193687976574141)
      ·
        refine ⟨14872194809322632991215303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39659186158193687976574141 14872194809322632991215303)
        ·
          refine ⟨22308292213983949486822955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14872194809322632991215303 22308292213983949486822955)
          ·
            refine ⟨33462438320975924230234433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22308292213983949486822955 33462438320975924230234433)
            ·
              refine ⟨25096828740731943172675825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33462438320975924230234433 25096828740731943172675825)
              ·
                refine ⟨18822621555548957379506869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25096828740731943172675825 18822621555548957379506869)
                ·
                  refine ⟨1764620770832714754328769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18822621555548957379506869 1764620770832714754328769)
                  ·
                    refine ⟨1323465578124536065746577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1764620770832714754328769 1323465578124536065746577)
                    ·
                      refine ⟨992599183593402049309933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323465578124536065746577 992599183593402049309933)
                      ·
                        rfl

theorem cell23_1933080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_1933080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933080 prefixEnd_1933080 := by exact prefixLift 1933080
  have htrace : WordTrace (prefixWord ++ tailWord_1933080) baseStart_1933080 baseEnd_1933080 := by
    simpa [prefixWord, tailWord_1933080, baseEnd_1933080] using wordTrace_append hprefix tailTrace_1933080
  have hstable : (prefixWord ++ tailWord_1933080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933080).length < 2 ^ (prefixWord ++ tailWord_1933080).sum := by decide
  have hdescent : baseEnd_1933080 < baseStart_1933080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933090 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_1933090 : Nat := 118140960795 + 1933090 * 2 ^ 59
def prefixEnd_1933090 : Nat := 4983230072969 + 3 ^ 40 * 1933090 * 2
def baseEnd_1933090 : Nat := 330868106133315670061629

theorem tailTrace_1933090 : CollatzResearch.WordTrace tailWord_1933090 prefixEnd_1933090 330868106133315670061629 := by
  unfold tailWord_1933090
  simp only [CollatzResearch.WordTrace]
  refine ⟨17626396141688137583221181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47003723044501700221923149 17626396141688137583221181)
  ·
    refine ⟨6609898553133051593707943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17626396141688137583221181 6609898553133051593707943)
    ·
      refine ⟨9914847829699577390561915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6609898553133051593707943 9914847829699577390561915)
      ·
        refine ⟨14872271744549366085842873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9914847829699577390561915 14872271744549366085842873)
        ·
          refine ⟨11154203808412024564382155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14872271744549366085842873 11154203808412024564382155)
          ·
            refine ⟨16731305712618036846573233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11154203808412024564382155 16731305712618036846573233)
            ·
              refine ⟨12548479284463527634929925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16731305712618036846573233 12548479284463527634929925)
              ·
                refine ⟨2352839865836911431549361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12548479284463527634929925 2352839865836911431549361)
                ·
                  refine ⟨1764629899377683573662021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2352839865836911431549361 1764629899377683573662021)
                  ·
                    refine ⟨330868106133315670061629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1764629899377683573662021 330868106133315670061629)
                    ·
                      rfl

theorem cell23_1933090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_1933090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933090 prefixEnd_1933090 := by exact prefixLift 1933090
  have htrace : WordTrace (prefixWord ++ tailWord_1933090) baseStart_1933090 baseEnd_1933090 := by
    simpa [prefixWord, tailWord_1933090, baseEnd_1933090] using wordTrace_append hprefix tailTrace_1933090
  have hstable : (prefixWord ++ tailWord_1933090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933090).length < 2 ^ (prefixWord ++ tailWord_1933090).sum := by decide
  have hdescent : baseEnd_1933090 < baseStart_1933090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933110 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1933110 : Nat := 118140960795 + 1933110 * 2 ^ 59
def prefixEnd_1933110 : Nat := 4983230072969 + 3 ^ 40 * 1933110 * 2
def baseEnd_1933110 : Nat := 992614588013036931934795

theorem tailTrace_1933110 : CollatzResearch.WordTrace tailWord_1933110 prefixEnd_1933110 992614588013036931934795 := by
  unfold tailWord_1933110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4406644626667505859288299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47004209351120062499075189 4406644626667505859288299)
  ·
    refine ⟨6609966940001258788932449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4406644626667505859288299 6609966940001258788932449)
    ·
      refine ⟨4957475205000944091699337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6609966940001258788932449 4957475205000944091699337)
      ·
        refine ⟨3718106403750708068774503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4957475205000944091699337 3718106403750708068774503)
        ·
          refine ⟨5577159605626062103161755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718106403750708068774503 5577159605626062103161755)
          ·
            refine ⟨8365739408439093154742633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577159605626062103161755 8365739408439093154742633)
            ·
              refine ⟨6274304556329319866056975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8365739408439093154742633 6274304556329319866056975)
              ·
                refine ⟨9411456834493979799085463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274304556329319866056975 9411456834493979799085463)
                ·
                  refine ⟨14117185251740969698628195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9411456834493979799085463 14117185251740969698628195)
                  ·
                    refine ⟨21175777877611454547942293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14117185251740969698628195 21175777877611454547942293)
                    ·
                      refine ⟨992614588013036931934795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21175777877611454547942293 992614588013036931934795)
                      ·
                        rfl

theorem cell23_1933110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1933110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933110 prefixEnd_1933110 := by exact prefixLift 1933110
  have htrace : WordTrace (prefixWord ++ tailWord_1933110) baseStart_1933110 baseEnd_1933110 := by
    simpa [prefixWord, tailWord_1933110, baseEnd_1933110] using wordTrace_append hprefix tailTrace_1933110
  have hstable : (prefixWord ++ tailWord_1933110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933110).length < 2 ^ (prefixWord ++ tailWord_1933110).sum := by decide
  have hdescent : baseEnd_1933110 < baseStart_1933110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933117 : List Nat := [1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_1933117 : Nat := 118140960795 + 1933117 * 2 ^ 59
def prefixEnd_1933117 : Nat := 4983230072969 + 3 ^ 40 * 1933117 * 2
def baseEnd_1933117 : Nat := 992618182377618404547263

theorem tailTrace_1933117 : CollatzResearch.WordTrace tailWord_1933117 prefixEnd_1933117 992618182377618404547263 := by
  unfold tailWord_1933117
  simp only [CollatzResearch.WordTrace]
  refine ⟨70506569337654733944117605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47004379558436489296078403 70506569337654733944117605)
  ·
    refine ⟨13219981750810262614522051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70506569337654733944117605 13219981750810262614522051)
    ·
      refine ⟨19829972626215393921783077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13219981750810262614522051 19829972626215393921783077)
      ·
        refine ⟨3718119867415386360334327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19829972626215393921783077 3718119867415386360334327)
        ·
          refine ⟨5577179801123079540501491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3718119867415386360334327 5577179801123079540501491)
          ·
            refine ⟨8365769701684619310752237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5577179801123079540501491 8365769701684619310752237)
            ·
              refine ⟨3137163638131732241532089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8365769701684619310752237 3137163638131732241532089)
              ·
                refine ⟨2352872728598799181149067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137163638131732241532089 2352872728598799181149067)
                ·
                  refine ⟨3529309092898198771723601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352872728598799181149067 3529309092898198771723601)
                  ·
                    refine ⟨2646981819673649078792701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529309092898198771723601 2646981819673649078792701)
                    ·
                      refine ⟨992618182377618404547263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2646981819673649078792701 992618182377618404547263)
                      ·
                        rfl

theorem cell23_1933117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_1933117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933117 prefixEnd_1933117 := by exact prefixLift 1933117
  have htrace : WordTrace (prefixWord ++ tailWord_1933117) baseStart_1933117 baseEnd_1933117 := by
    simpa [prefixWord, tailWord_1933117, baseEnd_1933117] using wordTrace_append hprefix tailTrace_1933117
  have hstable : (prefixWord ++ tailWord_1933117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933117).length < 2 ^ (prefixWord ++ tailWord_1933117).sum := by decide
  have hdescent : baseEnd_1933117 < baseStart_1933117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933191 : List Nat := [1, 1, 4, 2, 4, 2, 2, 1, 1, 3, 2]
def baseStart_1933191 : Nat := 118140960795 + 1933191 * 2 ^ 59
def prefixEnd_1933191 : Nat := 4983230072969 + 3 ^ 40 * 1933191 * 2
def baseEnd_1933191 : Nat := 992656179946051115021923

theorem tailTrace_1933191 : CollatzResearch.WordTrace tailWord_1933191 prefixEnd_1933191 992656179946051115021923 := by
  unfold tailWord_1933191
  simp only [CollatzResearch.WordTrace]
  refine ⟨70509268339386644582311427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47006178892924429721540951 70509268339386644582311427)
  ·
    refine ⟨105763902509079966873467141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70509268339386644582311427 105763902509079966873467141)
    ·
      refine ⟨19830731720452493788775089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105763902509079966873467141 19830731720452493788775089)
      ·
        refine ⟨14873048790339370341581317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19830731720452493788775089 14873048790339370341581317)
        ·
          refine ⟨2788696648188631939046497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14873048790339370341581317 2788696648188631939046497)
          ·
            refine ⟨2091522486141473954284873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788696648188631939046497 2091522486141473954284873)
            ·
              refine ⟨1568641864606105465713655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091522486141473954284873 1568641864606105465713655)
              ·
                refine ⟨2352962796909158198570483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1568641864606105465713655 2352962796909158198570483)
                ·
                  refine ⟨3529444195363737297855725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2352962796909158198570483 3529444195363737297855725)
                  ·
                    refine ⟨1323541573261401486695897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529444195363737297855725 1323541573261401486695897)
                    ·
                      refine ⟨992656179946051115021923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323541573261401486695897 992656179946051115021923)
                      ·
                        rfl

theorem cell23_1933191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_1933191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933191 prefixEnd_1933191 := by exact prefixLift 1933191
  have htrace : WordTrace (prefixWord ++ tailWord_1933191) baseStart_1933191 baseEnd_1933191 := by
    simpa [prefixWord, tailWord_1933191, baseEnd_1933191] using wordTrace_append hprefix tailTrace_1933191
  have hstable : (prefixWord ++ tailWord_1933191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933191).length < 2 ^ (prefixWord ++ tailWord_1933191).sum := by decide
  have hdescent : baseEnd_1933191 < baseStart_1933191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933198 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3]
def baseStart_1933198 : Nat := 118140960795 + 1933198 * 2 ^ 59
def prefixEnd_1933198 : Nat := 4983230072969 + 3 ^ 40 * 1933198 * 2
def baseEnd_1933198 : Nat := 992659774310632587634391

theorem tailTrace_1933198 : CollatzResearch.WordTrace tailWord_1933198 prefixEnd_1933198 992659774310632587634391 := by
  unfold tailWord_1933198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8813690456295160597227031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47006349100240856518544165 8813690456295160597227031)
  ·
    refine ⟨13220535684442740895840547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8813690456295160597227031 13220535684442740895840547)
    ·
      refine ⟨19830803526664111343760821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220535684442740895840547 19830803526664111343760821)
      ·
        refine ⟨1859137830624760438477577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19830803526664111343760821 1859137830624760438477577)
        ·
          refine ⟨1394353372968570328858183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859137830624760438477577 1394353372968570328858183)
          ·
            refine ⟨2091530059452855493287275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394353372968570328858183 2091530059452855493287275)
            ·
              refine ⟨3137295089179283239930913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091530059452855493287275 3137295089179283239930913)
              ·
                refine ⟨2352971316884462429948185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3137295089179283239930913 2352971316884462429948185)
                ·
                  refine ⟨1764728487663346822461139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2352971316884462429948185 1764728487663346822461139)
                  ·
                    refine ⟨2647092731495020233691709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764728487663346822461139 2647092731495020233691709)
                    ·
                      refine ⟨992659774310632587634391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647092731495020233691709 992659774310632587634391)
                      ·
                        rfl

theorem cell23_1933198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_1933198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933198 prefixEnd_1933198 := by exact prefixLift 1933198
  have htrace : WordTrace (prefixWord ++ tailWord_1933198) baseStart_1933198 baseEnd_1933198 := by
    simpa [prefixWord, tailWord_1933198, baseEnd_1933198] using wordTrace_append hprefix tailTrace_1933198
  have hstable : (prefixWord ++ tailWord_1933198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933198).length < 2 ^ (prefixWord ++ tailWord_1933198).sum := by decide
  have hdescent : baseEnd_1933198 < baseStart_1933198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933204 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_1933204 : Nat := 118140960795 + 1933204 * 2 ^ 59
def prefixEnd_1933204 : Nat := 4983230072969 + 3 ^ 40 * 1933204 * 2
def baseEnd_1933204 : Nat := 992662855194559564159363

theorem tailTrace_1933204 : CollatzResearch.WordTrace tailWord_1933204 prefixEnd_1933204 992662855194559564159363 := by
  unfold tailWord_1933204
  simp only [CollatzResearch.WordTrace]
  refine ⟨35254871244169773901267333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47006494992226365201689777 35254871244169773901267333)
  ·
    refine ⟨6610288358281832606487625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35254871244169773901267333 6610288358281832606487625)
    ·
      refine ⟨4957716268711374454865719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6610288358281832606487625 4957716268711374454865719)
      ·
        refine ⟨7436574403067061682298579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4957716268711374454865719 7436574403067061682298579)
        ·
          refine ⟨11154861604600592523447869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436574403067061682298579 11154861604600592523447869)
          ·
            refine ⟨4183073101725222196292951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11154861604600592523447869 4183073101725222196292951)
            ·
              refine ⟨6274609652587833294439427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183073101725222196292951 6274609652587833294439427)
              ·
                refine ⟨9411914478881749941659141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274609652587833294439427 9411914478881749941659141)
                ·
                  refine ⟨1764733964790328114061089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9411914478881749941659141 1764733964790328114061089)
                  ·
                    refine ⟨1323550473592746085545817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1764733964790328114061089 1323550473592746085545817)
                    ·
                      refine ⟨992662855194559564159363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323550473592746085545817 992662855194559564159363)
                      ·
                        rfl

theorem cell23_1933204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_1933204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933204 prefixEnd_1933204 := by exact prefixLift 1933204
  have htrace : WordTrace (prefixWord ++ tailWord_1933204) baseStart_1933204 baseEnd_1933204 := by
    simpa [prefixWord, tailWord_1933204, baseEnd_1933204] using wordTrace_append hprefix tailTrace_1933204
  have hstable : (prefixWord ++ tailWord_1933204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933204).length < 2 ^ (prefixWord ++ tailWord_1933204).sum := by decide
  have hdescent : baseEnd_1933204 < baseStart_1933204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933210 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 7]
def baseStart_1933210 : Nat := 118140960795 + 1933210 * 2 ^ 59
def prefixEnd_1933210 : Nat := 4983230072969 + 3 ^ 40 * 1933210 * 2
def baseEnd_1933210 : Nat := 110296215119831837853815

theorem tailTrace_1933210 : CollatzResearch.WordTrace tailWord_1933210 prefixEnd_1933210 110296215119831837853815 := by
  unfold tailWord_1933210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17627490331579452706813271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47006640884211873884835389 17627490331579452706813271)
  ·
    refine ⟨26441235497369179060219907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17627490331579452706813271 26441235497369179060219907)
    ·
      refine ⟨39661853246053768590329861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26441235497369179060219907 39661853246053768590329861)
      ·
        refine ⟨7436597483635081610686849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39661853246053768590329861 7436597483635081610686849)
        ·
          refine ⟨5577448112726311208015137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7436597483635081610686849 5577448112726311208015137)
          ·
            refine ⟨4183086084544733406011353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5577448112726311208015137 4183086084544733406011353)
            ·
              refine ⟨3137314563408550054508515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183086084544733406011353 3137314563408550054508515)
              ·
                refine ⟨4705971845112825081762773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137314563408550054508515 4705971845112825081762773)
                ·
                  refine ⟨110296215119831837853815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4705971845112825081762773 110296215119831837853815)
                  ·
                    rfl

theorem cell23_1933210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_1933210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933210 prefixEnd_1933210 := by exact prefixLift 1933210
  have htrace : WordTrace (prefixWord ++ tailWord_1933210) baseStart_1933210 baseEnd_1933210 := by
    simpa [prefixWord, tailWord_1933210, baseEnd_1933210] using wordTrace_append hprefix tailTrace_1933210
  have hstable : (prefixWord ++ tailWord_1933210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933210).length < 2 ^ (prefixWord ++ tailWord_1933210).sum := by decide
  have hdescent : baseEnd_1933210 < baseStart_1933210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933220 : List Nat := [2, 3, 1, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_1933220 : Nat := 118140960795 + 1933220 * 2 ^ 59
def prefixEnd_1933220 : Nat := 4983230072969 + 3 ^ 40 * 1933220 * 2
def baseEnd_1933220 : Nat := 992671070885031501559289

theorem tailTrace_1933220 : CollatzResearch.WordTrace tailWord_1933220 prefixEnd_1933220 992671070885031501559289 := by
  unfold tailWord_1933220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255163028140791267558557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47006884037521055023411409 35255163028140791267558557)
  ·
    refine ⟨13220686135552796725334459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35255163028140791267558557 13220686135552796725334459)
    ·
      refine ⟨19831029203329195088001689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13220686135552796725334459 19831029203329195088001689)
      ·
        refine ⟨14873271902496896316001267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19831029203329195088001689 14873271902496896316001267)
        ·
          refine ⟨22309907853745344474001901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14873271902496896316001267 22309907853745344474001901)
          ·
            refine ⟨8366215445154504177750713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22309907853745344474001901 8366215445154504177750713)
            ·
              refine ⟨6274661583865878133313035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366215445154504177750713 6274661583865878133313035)
              ·
                refine ⟨9411992375798817199969553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6274661583865878133313035 9411992375798817199969553)
                ·
                  refine ⟨7058994281849112899977165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9411992375798817199969553 7058994281849112899977165)
                  ·
                    refine ⟨2647122855693417337491437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7058994281849112899977165 2647122855693417337491437)
                    ·
                      refine ⟨992671070885031501559289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647122855693417337491437 992671070885031501559289)
                      ·
                        rfl

theorem cell23_1933220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_1933220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933220 prefixEnd_1933220 := by exact prefixLift 1933220
  have htrace : WordTrace (prefixWord ++ tailWord_1933220) baseStart_1933220 baseEnd_1933220 := by
    simpa [prefixWord, tailWord_1933220, baseEnd_1933220] using wordTrace_append hprefix tailTrace_1933220
  have hstable : (prefixWord ++ tailWord_1933220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933220).length < 2 ^ (prefixWord ++ tailWord_1933220).sum := by decide
  have hdescent : baseEnd_1933220 < baseStart_1933220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933260 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1933260 : Nat := 118140960795 + 1933260 * 2 ^ 59
def prefixEnd_1933260 : Nat := 4983230072969 + 3 ^ 40 * 1933260 * 2
def baseEnd_1933260 : Nat := 992691610111211345059105

theorem tailTrace_1933260 : CollatzResearch.WordTrace tailWord_1933260 prefixEnd_1933260 992691610111211345059105 := by
  unfold tailWord_1933260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35255892488068334683286617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47007856650757779577715489 35255892488068334683286617)
  ·
    refine ⟨26441919366051251012464963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35255892488068334683286617 26441919366051251012464963)
    ·
      refine ⟨39662879049076876518697445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26441919366051251012464963 39662879049076876518697445)
      ·
        refine ⟨7436789821701914347255771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39662879049076876518697445 7436789821701914347255771)
        ·
          refine ⟨11155184732552871520883657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7436789821701914347255771 11155184732552871520883657)
          ·
            refine ⟨8366388549414653640662743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11155184732552871520883657 8366388549414653640662743)
            ·
              refine ⟨12549582824121980460994115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8366388549414653640662743 12549582824121980460994115)
              ·
                refine ⟨18824374236182970691491173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12549582824121980460994115 18824374236182970691491173)
                ·
                  refine ⟨3529570169284307004654595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18824374236182970691491173 3529570169284307004654595)
                  ·
                    refine ⟨5294355253926460506981893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3529570169284307004654595 5294355253926460506981893)
                    ·
                      refine ⟨992691610111211345059105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5294355253926460506981893 992691610111211345059105)
                      ·
                        rfl

theorem cell23_1933260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1933260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933260 prefixEnd_1933260 := by exact prefixLift 1933260
  have htrace : WordTrace (prefixWord ++ tailWord_1933260) baseStart_1933260 baseEnd_1933260 := by
    simpa [prefixWord, tailWord_1933260, baseEnd_1933260] using wordTrace_append hprefix tailTrace_1933260
  have hstable : (prefixWord ++ tailWord_1933260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933260).length < 2 ^ (prefixWord ++ tailWord_1933260).sum := by decide
  have hdescent : baseEnd_1933260 < baseStart_1933260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933354 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_1933354 : Nat := 118140960795 + 1933354 * 2 ^ 59
def prefixEnd_1933354 : Nat := 4983230072969 + 3 ^ 40 * 1933354 * 2
def baseEnd_1933354 : Nat := 992739877292733977283673

theorem tailTrace_1933354 : CollatzResearch.WordTrace tailWord_1933354 prefixEnd_1933354 992739877292733977283673 := by
  unfold tailWord_1933354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628803359449030855123779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47010142291864082280330077 17628803359449030855123779)
  ·
    refine ⟨26443205039173546282685669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17628803359449030855123779 26443205039173546282685669)
    ·
      refine ⟨4958100944845039928003563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26443205039173546282685669 4958100944845039928003563)
      ·
        refine ⟨7437151417267559892005345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958100944845039928003563 7437151417267559892005345)
        ·
          refine ⟨5577863562950669919004009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7437151417267559892005345 5577863562950669919004009)
          ·
            refine ⟨4183397672213002439253007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5577863562950669919004009 4183397672213002439253007)
            ·
              refine ⟨6275096508319503658879511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183397672213002439253007 6275096508319503658879511)
              ·
                refine ⟨9412644762479255488319267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6275096508319503658879511 9412644762479255488319267)
                ·
                  refine ⟨14118967143718883232478901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9412644762479255488319267 14118967143718883232478901)
                  ·
                    refine ⟨1323653169723645303044897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14118967143718883232478901 1323653169723645303044897)
                    ·
                      refine ⟨992739877292733977283673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323653169723645303044897 992739877292733977283673)
                      ·
                        rfl

theorem cell23_1933354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_1933354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933354 prefixEnd_1933354 := by exact prefixLift 1933354
  have htrace : WordTrace (prefixWord ++ tailWord_1933354) baseStart_1933354 baseEnd_1933354 := by
    simpa [prefixWord, tailWord_1933354, baseEnd_1933354] using wordTrace_append hprefix tailTrace_1933354
  have hstable : (prefixWord ++ tailWord_1933354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933354).length < 2 ^ (prefixWord ++ tailWord_1933354).sum := by decide
  have hdescent : baseEnd_1933354 < baseStart_1933354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933360 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_1933360 : Nat := 118140960795 + 1933360 * 2 ^ 59
def prefixEnd_1933360 : Nat := 4983230072969 + 3 ^ 40 * 1933360 * 2
def baseEnd_1933360 : Nat := 330914319392220317936215

theorem tailTrace_1933360 : CollatzResearch.WordTrace tailWord_1933360 prefixEnd_1933360 330914319392220317936215 := by
  unfold tailWord_1933360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35257716137887193222606767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47010288183849590963475689 35257716137887193222606767)
  ·
    refine ⟨52886574206830789833910151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35257716137887193222606767 52886574206830789833910151)
    ·
      refine ⟨79329861310246184750865227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52886574206830789833910151 79329861310246184750865227)
      ·
        refine ⟨118994791965369277126297841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79329861310246184750865227 118994791965369277126297841)
        ·
          refine ⟨89246093974026957844723381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118994791965369277126297841 89246093974026957844723381)
          ·
            refine ⟨8366821310065027297942817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89246093974026957844723381 8366821310065027297942817)
            ·
              refine ⟨6275115982548770473457113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8366821310065027297942817 6275115982548770473457113)
              ·
                refine ⟨4706336986911577855092835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275115982548770473457113 4706336986911577855092835)
                ·
                  refine ⟨7059505480367366782639253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706336986911577855092835 7059505480367366782639253)
                  ·
                    refine ⟨330914319392220317936215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7059505480367366782639253 330914319392220317936215)
                    ·
                      rfl

theorem cell23_1933360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_1933360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933360 prefixEnd_1933360 := by exact prefixLift 1933360
  have htrace : WordTrace (prefixWord ++ tailWord_1933360) baseStart_1933360 baseEnd_1933360 := by
    simpa [prefixWord, tailWord_1933360, baseEnd_1933360] using wordTrace_append hprefix tailTrace_1933360
  have hstable : (prefixWord ++ tailWord_1933360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933360).length < 2 ^ (prefixWord ++ tailWord_1933360).sum := by decide
  have hdescent : baseEnd_1933360 < baseStart_1933360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933361 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 1, 1, 3]
def baseStart_1933361 : Nat := 118140960795 + 1933361 * 2 ^ 59
def prefixEnd_1933361 : Nat := 4983230072969 + 3 ^ 40 * 1933361 * 2
def baseEnd_1933361 : Nat := 992743471657315449896141

theorem tailTrace_1933361 : CollatzResearch.WordTrace tailWord_1933361 prefixEnd_1933361 992743471657315449896141 := by
  unfold tailWord_1933361
  simp only [CollatzResearch.WordTrace]
  refine ⟨70515468748770763615999937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47010312499180509077333291 70515468748770763615999937)
  ·
    refine ⟨52886601561578072711999953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70515468748770763615999937 52886601561578072711999953)
    ·
      refine ⟨39664951171183554533999965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52886601561578072711999953 39664951171183554533999965)
      ·
        refine ⟨14874356689193832950249987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39664951171183554533999965 14874356689193832950249987)
        ·
          refine ⟨22311535033790749425374981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874356689193832950249987 22311535033790749425374981)
          ·
            refine ⟨4183412818835765517257809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22311535033790749425374981 4183412818835765517257809)
            ·
              refine ⟨3137559614126824137943357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4183412818835765517257809 3137559614126824137943357)
              ·
                refine ⟨1176584855297559051728759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3137559614126824137943357 1176584855297559051728759)
                ·
                  refine ⟨1764877282946338577593139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176584855297559051728759 1764877282946338577593139)
                  ·
                    refine ⟨2647315924419507866389709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764877282946338577593139 2647315924419507866389709)
                    ·
                      refine ⟨992743471657315449896141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647315924419507866389709 992743471657315449896141)
                      ·
                        rfl

theorem cell23_1933361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_1933361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933361 prefixEnd_1933361 := by exact prefixLift 1933361
  have htrace : WordTrace (prefixWord ++ tailWord_1933361) baseStart_1933361 baseEnd_1933361 := by
    simpa [prefixWord, tailWord_1933361, baseEnd_1933361] using wordTrace_append hprefix tailTrace_1933361
  have hstable : (prefixWord ++ tailWord_1933361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933361).length < 2 ^ (prefixWord ++ tailWord_1933361).sum := by decide
  have hdescent : baseEnd_1933361 < baseStart_1933361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933370 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5]
def baseStart_1933370 : Nat := 118140960795 + 1933370 * 2 ^ 59
def prefixEnd_1933370 : Nat := 4983230072969 + 3 ^ 40 * 1933370 * 2
def baseEnd_1933370 : Nat := 992748092983205914683599

theorem tailTrace_1933370 : CollatzResearch.WordTrace tailWord_1933370 prefixEnd_1933370 992748092983205914683599 := by
  unfold tailWord_1933370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17628949251434539538269391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47010531337158772102051709 17628949251434539538269391)
  ·
    refine ⟨26443423877151809307404087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17628949251434539538269391 26443423877151809307404087)
    ·
      refine ⟨39665135815727713961106131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26443423877151809307404087 39665135815727713961106131)
      ·
        refine ⟨59497703723591570941659197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39665135815727713961106131 59497703723591570941659197)
        ·
          refine ⟨22311638896346839103122199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59497703723591570941659197 22311638896346839103122199)
          ·
            refine ⟨33467458344520258654683299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22311638896346839103122199 33467458344520258654683299)
            ·
              refine ⟨50201187516780387982024949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33467458344520258654683299 50201187516780387982024949)
              ·
                refine ⟨4706361329698161373314839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50201187516780387982024949 4706361329698161373314839)
                ·
                  refine ⟨7059541994547242059972259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706361329698161373314839 7059541994547242059972259)
                  ·
                    refine ⟨10589312991820863089958389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7059541994547242059972259 10589312991820863089958389)
                    ·
                      refine ⟨992748092983205914683599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10589312991820863089958389 992748092983205914683599)
                      ·
                        rfl

theorem cell23_1933370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_1933370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933370 prefixEnd_1933370 := by exact prefixLift 1933370
  have htrace : WordTrace (prefixWord ++ tailWord_1933370) baseStart_1933370 baseEnd_1933370 := by
    simpa [prefixWord, tailWord_1933370, baseEnd_1933370] using wordTrace_append hprefix tailTrace_1933370
  have hstable : (prefixWord ++ tailWord_1933370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933370).length < 2 ^ (prefixWord ++ tailWord_1933370).sum := by decide
  have hdescent : baseEnd_1933370 < baseStart_1933370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933394 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_1933394 : Nat := 118140960795 + 1933394 * 2 ^ 59
def prefixEnd_1933394 : Nat := 4983230072969 + 3 ^ 40 * 1933394 * 2
def baseEnd_1933394 : Nat := 330920138839637940261163

theorem tailTrace_1933394 : CollatzResearch.WordTrace tailWord_1933394 prefixEnd_1933394 330920138839637940261163 := by
  unfold tailWord_1933394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17629168089412802562987809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47011114905100806834634157 17629168089412802562987809)
  ·
    refine ⟨13221876067059601922240857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17629168089412802562987809 13221876067059601922240857)
    ·
      refine ⟨9916407050294701441680643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13221876067059601922240857 9916407050294701441680643)
      ·
        refine ⟨14874610575442052162520965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9916407050294701441680643 14874610575442052162520965)
        ·
          refine ⟨2788989482895384780472681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14874610575442052162520965 2788989482895384780472681)
          ·
            refine ⟨2091742112171538585354511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2788989482895384780472681 2091742112171538585354511)
            ·
              refine ⟨3137613168257307878031767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091742112171538585354511 3137613168257307878031767)
              ·
                refine ⟨4706419752385961817047651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137613168257307878031767 4706419752385961817047651)
                ·
                  refine ⟨7059629628578942725571477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706419752385961817047651 7059629628578942725571477)
                  ·
                    refine ⟨330920138839637940261163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7059629628578942725571477 330920138839637940261163)
                    ·
                      rfl

theorem cell23_1933394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_1933394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933394 prefixEnd_1933394 := by exact prefixLift 1933394
  have htrace : WordTrace (prefixWord ++ tailWord_1933394) baseStart_1933394 baseEnd_1933394 := by
    simpa [prefixWord, tailWord_1933394, baseEnd_1933394] using wordTrace_append hprefix tailTrace_1933394
  have hstable : (prefixWord ++ tailWord_1933394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933394).length < 2 ^ (prefixWord ++ tailWord_1933394).sum := by decide
  have hdescent : baseEnd_1933394 < baseStart_1933394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933397 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1933397 : Nat := 118140960795 + 1933397 * 2 ^ 59
def prefixEnd_1933397 : Nat := 4983230072969 + 3 ^ 40 * 1933397 * 2
def baseEnd_1933397 : Nat := 992761956960877309045975

theorem tailTrace_1933397 : CollatzResearch.WordTrace tailWord_1933397 prefixEnd_1933397 992761956960877309045975 := by
  unfold tailWord_1933397
  simp only [CollatzResearch.WordTrace]
  refine ⟨70516781776640341764310445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47011187851093561176206963 70516781776640341764310445)
  ·
    refine ⟨26443793166240128161616417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70516781776640341764310445 26443793166240128161616417)
    ·
      refine ⟨19832844874680096121212313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26443793166240128161616417 19832844874680096121212313)
      ·
        refine ⟨14874633656010072090909235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19832844874680096121212313 14874633656010072090909235)
        ·
          refine ⟨22311950484015108136363853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14874633656010072090909235 22311950484015108136363853)
          ·
            refine ⟨8366981431505665551136445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22311950484015108136363853 8366981431505665551136445)
            ·
              refine ⟨3137618036814624581676167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8366981431505665551136445 3137618036814624581676167)
              ·
                refine ⟨4706427055221936872514251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137618036814624581676167 4706427055221936872514251)
                ·
                  refine ⟨7059640582832905308771377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4706427055221936872514251 7059640582832905308771377)
                  ·
                    refine ⟨5294730437124678981578533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7059640582832905308771377 5294730437124678981578533)
                    ·
                      refine ⟨992761956960877309045975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5294730437124678981578533 992761956960877309045975)
                      ·
                        rfl

theorem cell23_1933397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1933397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933397 prefixEnd_1933397 := by exact prefixLift 1933397
  have htrace : WordTrace (prefixWord ++ tailWord_1933397) baseStart_1933397 baseEnd_1933397 := by
    simpa [prefixWord, tailWord_1933397, baseEnd_1933397] using wordTrace_append hprefix tailTrace_1933397
  have hstable : (prefixWord ++ tailWord_1933397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933397).length < 2 ^ (prefixWord ++ tailWord_1933397).sum := by decide
  have hdescent : baseEnd_1933397 < baseStart_1933397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933404 : List Nat := [2, 2, 4, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_1933404 : Nat := 118140960795 + 1933404 * 2 ^ 59
def prefixEnd_1933404 : Nat := 4983230072969 + 3 ^ 40 * 1933404 * 2
def baseEnd_1933404 : Nat := 992765551325458781658443

theorem tailTrace_1933404 : CollatzResearch.WordTrace tailWord_1933404 prefixEnd_1933404 992765551325458781658443 := by
  unfold tailWord_1933404
  simp only [CollatzResearch.WordTrace]
  refine ⟨35258518543807490979907633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47011358058409987973210177 35258518543807490979907633)
  ·
    refine ⟨26443888907855618234930725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35258518543807490979907633 26443888907855618234930725)
    ·
      refine ⟨4958229170222928419049511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26443888907855618234930725 4958229170222928419049511)
      ·
        refine ⟨7437343755334392628574267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958229170222928419049511 7437343755334392628574267)
        ·
          refine ⟨11156015633001588942861401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7437343755334392628574267 11156015633001588942861401)
          ·
            refine ⟨8367011724751191707146051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11156015633001588942861401 8367011724751191707146051)
            ·
              refine ⟨12550517587126787560719077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8367011724751191707146051 12550517587126787560719077)
              ·
                refine ⟨2353222047586272667634827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12550517587126787560719077 2353222047586272667634827)
                ·
                  refine ⟨3529833071379409001452241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353222047586272667634827 3529833071379409001452241)
                  ·
                    refine ⟨2647374803534556751089181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3529833071379409001452241 2647374803534556751089181)
                    ·
                      refine ⟨992765551325458781658443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647374803534556751089181 992765551325458781658443)
                      ·
                        rfl

theorem cell23_1933404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_1933404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933404 prefixEnd_1933404 := by exact prefixLift 1933404
  have htrace : WordTrace (prefixWord ++ tailWord_1933404) baseStart_1933404 baseEnd_1933404 := by
    simpa [prefixWord, tailWord_1933404, baseEnd_1933404] using wordTrace_append hprefix tailTrace_1933404
  have hstable : (prefixWord ++ tailWord_1933404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933404).length < 2 ^ (prefixWord ++ tailWord_1933404).sum := by decide
  have hdescent : baseEnd_1933404 < baseStart_1933404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933417 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 3]
def baseStart_1933417 : Nat := 118140960795 + 1933417 * 2 ^ 59
def prefixEnd_1933417 : Nat := 4983230072969 + 3 ^ 40 * 1933417 * 2
def baseEnd_1933417 : Nat := 992772226573967230795883

theorem tailTrace_1933417 : CollatzResearch.WordTrace tailWord_1933417 prefixEnd_1933417 992772226573967230795883 := by
  unfold tailWord_1933417
  simp only [CollatzResearch.WordTrace]
  refine ⟨70517511236567885180038505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47011674157711923453359003 70517511236567885180038505)
  ·
    refine ⟨52888133427425913885028879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70517511236567885180038505 52888133427425913885028879)
    ·
      refine ⟨79332200141138870827543319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52888133427425913885028879 79332200141138870827543319)
      ·
        refine ⟨118998300211708306241314979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79332200141138870827543319 118998300211708306241314979)
        ·
          refine ⟨178497450317562459361972469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118998300211708306241314979 178497450317562459361972469)
          ·
            refine ⟨16734135967271480565184919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178497450317562459361972469 16734135967271480565184919)
            ·
              refine ⟨25101203950907220847777379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16734135967271480565184919 25101203950907220847777379)
              ·
                refine ⟨37651805926360831271666069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25101203950907220847777379 37651805926360831271666069)
                ·
                  refine ⟨1764928402798163965859347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 37651805926360831271666069 1764928402798163965859347)
                  ·
                    refine ⟨2647392604197245948789021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1764928402798163965859347 2647392604197245948789021)
                    ·
                      refine ⟨992772226573967230795883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647392604197245948789021 992772226573967230795883)
                      ·
                        rfl

theorem cell23_1933417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_1933417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933417 prefixEnd_1933417 := by exact prefixLift 1933417
  have htrace : WordTrace (prefixWord ++ tailWord_1933417) baseStart_1933417 baseEnd_1933417 := by
    simpa [prefixWord, tailWord_1933417, baseEnd_1933417] using wordTrace_append hprefix tailTrace_1933417
  have hstable : (prefixWord ++ tailWord_1933417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933417).length < 2 ^ (prefixWord ++ tailWord_1933417).sum := by decide
  have hdescent : baseEnd_1933417 < baseStart_1933417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933440 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1933440 : Nat := 118140960795 + 1933440 * 2 ^ 59
def prefixEnd_1933440 : Nat := 4983230072969 + 3 ^ 40 * 1933440 * 2
def baseEnd_1933440 : Nat := 992784036629020640808277

theorem tailTrace_1933440 : CollatzResearch.WordTrace tailWord_1933440 prefixEnd_1933440 992784036629020640808277 := by
  unfold tailWord_1933440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259175057742280054062887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47012233410323040072083849 35259175057742280054062887)
  ·
    refine ⟨52888762586613420081094331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35259175057742280054062887 52888762586613420081094331)
    ·
      refine ⟨79333143879920130121641497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52888762586613420081094331 79333143879920130121641497)
      ·
        refine ⟨59499857909940097591231123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79333143879920130121641497 59499857909940097591231123)
        ·
          refine ⟨89249786864910146386846685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59499857909940097591231123 89249786864910146386846685)
          ·
            refine ⟨33468670074341304895067507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89249786864910146386846685 33468670074341304895067507)
            ·
              refine ⟨50203005111511957342601261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33468670074341304895067507 50203005111511957342601261)
              ·
                refine ⟨18826126916816984003475473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50203005111511957342601261 18826126916816984003475473)
                ·
                  refine ⟨14119595187612738002606605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18826126916816984003475473 14119595187612738002606605)
                  ·
                    refine ⟨5294848195354776750977477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14119595187612738002606605 5294848195354776750977477)
                    ·
                      refine ⟨992784036629020640808277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5294848195354776750977477 992784036629020640808277)
                      ·
                        rfl

theorem cell23_1933440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1933440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933440 prefixEnd_1933440 := by exact prefixLift 1933440
  have htrace : WordTrace (prefixWord ++ tailWord_1933440) baseStart_1933440 baseEnd_1933440 := by
    simpa [prefixWord, tailWord_1933440, baseEnd_1933440] using wordTrace_append hprefix tailTrace_1933440
  have hstable : (prefixWord ++ tailWord_1933440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933440).length < 2 ^ (prefixWord ++ tailWord_1933440).sum := by decide
  have hdescent : baseEnd_1933440 < baseStart_1933440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933444 : List Nat := [2, 3, 2, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_1933444 : Nat := 118140960795 + 1933444 * 2 ^ 59
def prefixEnd_1933444 : Nat := 4983230072969 + 3 ^ 40 * 1933444 * 2
def baseEnd_1933444 : Nat := 992786090551638625158259

theorem tailTrace_1933444 : CollatzResearch.WordTrace tailWord_1933444 prefixEnd_1933444 992786090551638625158259 := by
  unfold tailWord_1933444
  simp only [CollatzResearch.WordTrace]
  refine ⟨35259248003735034395635693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47012330671646712527514257 35259248003735034395635693)
  ·
    refine ⟨13222218001400637898363385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35259248003735034395635693 13222218001400637898363385)
    ·
      refine ⟨9916663501050478423772539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13222218001400637898363385 9916663501050478423772539)
      ·
        refine ⟨14874995251575717635658809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9916663501050478423772539 14874995251575717635658809)
        ·
          refine ⟨11156246438681788226744107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14874995251575717635658809 11156246438681788226744107)
          ·
            refine ⟨16734369658022682340116161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11156246438681788226744107 16734369658022682340116161)
            ·
              refine ⟨12550777243517011755087121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16734369658022682340116161 12550777243517011755087121)
              ·
                refine ⟨9413082932637758816315341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12550777243517011755087121 9413082932637758816315341)
                ·
                  refine ⟨3529906099739159556118253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9413082932637758816315341 3529906099739159556118253)
                  ·
                    refine ⟨1323714787402184833544345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3529906099739159556118253 1323714787402184833544345)
                    ·
                      refine ⟨992786090551638625158259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323714787402184833544345 992786090551638625158259)
                      ·
                        rfl

theorem cell23_1933444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_1933444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933444 prefixEnd_1933444 := by exact prefixLift 1933444
  have htrace : WordTrace (prefixWord ++ tailWord_1933444) baseStart_1933444 baseEnd_1933444 := by
    simpa [prefixWord, tailWord_1933444, baseEnd_1933444] using wordTrace_append hprefix tailTrace_1933444
  have hstable : (prefixWord ++ tailWord_1933444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933444).length < 2 ^ (prefixWord ++ tailWord_1933444).sum := by decide
  have hdescent : baseEnd_1933444 < baseStart_1933444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933457 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_1933457 : Nat := 118140960795 + 1933457 * 2 ^ 59
def prefixEnd_1933457 : Nat := 4983230072969 + 3 ^ 40 * 1933457 * 2
def baseEnd_1933457 : Nat := 992792765800147074295699

theorem tailTrace_1933457 : CollatzResearch.WordTrace tailWord_1933457 prefixEnd_1933457 992792765800147074295699 := by
  unfold tailWord_1933457
  simp only [CollatzResearch.WordTrace]
  refine ⟨70518970156422972011494625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47012646770948648007663083 70518970156422972011494625)
  ·
    refine ⟨52889227617317229008620969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70518970156422972011494625 52889227617317229008620969)
    ·
      refine ⟨39666920712987921756465727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52889227617317229008620969 39666920712987921756465727)
      ·
        refine ⟨59500381069481882634698591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39666920712987921756465727 59500381069481882634698591)
        ·
          refine ⟨89250571604222823952047887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59500381069481882634698591 89250571604222823952047887)
          ·
            refine ⟨133875857406334235928071831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89250571604222823952047887 133875857406334235928071831)
            ·
              refine ⟨200813786109501353892107747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133875857406334235928071831 200813786109501353892107747)
              ·
                refine ⟨301220679164252030838161621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200813786109501353892107747 301220679164252030838161621)
                ·
                  refine ⟨7059859667912156972769413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 301220679164252030838161621 7059859667912156972769413)
                  ·
                    refine ⟨1323723687733529432394265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7059859667912156972769413 1323723687733529432394265)
                    ·
                      refine ⟨992792765800147074295699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323723687733529432394265 992792765800147074295699)
                      ·
                        rfl

theorem cell23_1933457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_1933457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933457 prefixEnd_1933457 := by exact prefixLift 1933457
  have htrace : WordTrace (prefixWord ++ tailWord_1933457) baseStart_1933457 baseEnd_1933457 := by
    simpa [prefixWord, tailWord_1933457, baseEnd_1933457] using wordTrace_append hprefix tailTrace_1933457
  have hstable : (prefixWord ++ tailWord_1933457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933457).length < 2 ^ (prefixWord ++ tailWord_1933457).sum := by decide
  have hdescent : baseEnd_1933457 < baseStart_1933457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933486 : List Nat := [4, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1933486 : Nat := 118140960795 + 1933486 * 2 ^ 59
def prefixEnd_1933486 : Nat := 4983230072969 + 3 ^ 40 * 1933486 * 2
def baseEnd_1933486 : Nat := 992807656739127460833067

theorem tailTrace_1933486 : CollatzResearch.WordTrace tailWord_1933486 prefixEnd_1933486 992807656739127460833067 := by
  unfold tailWord_1933486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815003484164738745537539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47013351915545273309533541 8815003484164738745537539)
  ·
    refine ⟨13222505226247108118306309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8815003484164738745537539 13222505226247108118306309)
    ·
      refine ⟨2479219729921332772182433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13222505226247108118306309 2479219729921332772182433)
      ·
        refine ⟨1859414797440999579136825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2479219729921332772182433 1859414797440999579136825)
        ·
          refine ⟨1394561098080749684352619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1859414797440999579136825 1394561098080749684352619)
          ·
            refine ⟨2091841647121124526528929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1394561098080749684352619 2091841647121124526528929)
            ·
              refine ⟨1568881235340843394896697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2091841647121124526528929 1568881235340843394896697)
              ·
                refine ⟨1176660926505632546172523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1568881235340843394896697 1176660926505632546172523)
                ·
                  refine ⟨1764991389758448819258785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176660926505632546172523 1764991389758448819258785)
                  ·
                    refine ⟨1323743542318836614444089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1764991389758448819258785 1323743542318836614444089)
                    ·
                      refine ⟨992807656739127460833067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323743542318836614444089 992807656739127460833067)
                      ·
                        rfl

theorem cell23_1933486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1933486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933486 prefixEnd_1933486 := by exact prefixLift 1933486
  have htrace : WordTrace (prefixWord ++ tailWord_1933486) baseStart_1933486 baseEnd_1933486 := by
    simpa [prefixWord, tailWord_1933486, baseEnd_1933486] using wordTrace_append hprefix tailTrace_1933486
  have hstable : (prefixWord ++ tailWord_1933486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933486).length < 2 ^ (prefixWord ++ tailWord_1933486).sum := by decide
  have hdescent : baseEnd_1933486 < baseStart_1933486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933508 : List Nat := [2, 3, 3, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_1933508 : Nat := 118140960795 + 1933508 * 2 ^ 59
def prefixEnd_1933508 : Nat := 4983230072969 + 3 ^ 40 * 1933508 * 2
def baseEnd_1933508 : Nat := 992818953313526374757965

theorem tailTrace_1933508 : CollatzResearch.WordTrace tailWord_1933508 prefixEnd_1933508 992818953313526374757965 := by
  unfold tailWord_1933508
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260415139619103860800589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47013886852825471814400785 35260415139619103860800589)
  ·
    refine ⟨13222655677357163947800221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35260415139619103860800589 13222655677357163947800221)
    ·
      refine ⟨4958495879008936480425083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13222655677357163947800221 4958495879008936480425083)
      ·
        refine ⟨7437743818513404720637625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958495879008936480425083 7437743818513404720637625)
        ·
          refine ⟨5578307863885053540478219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7437743818513404720637625 5578307863885053540478219)
          ·
            refine ⟨8367461795827580310717329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578307863885053540478219 8367461795827580310717329)
            ·
              refine ⟨6275596346870685233037997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8367461795827580310717329 6275596346870685233037997)
              ·
                refine ⟨2353348630076506962389249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6275596346870685233037997 2353348630076506962389249)
                ·
                  refine ⟨1765011472557380221791937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2353348630076506962389249 1765011472557380221791937)
                  ·
                    refine ⟨1323758604418035166343953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1765011472557380221791937 1323758604418035166343953)
                    ·
                      refine ⟨992818953313526374757965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323758604418035166343953 992818953313526374757965)
                      ·
                        rfl

theorem cell23_1933508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_1933508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933508 prefixEnd_1933508 := by exact prefixLift 1933508
  have htrace : WordTrace (prefixWord ++ tailWord_1933508) baseStart_1933508 baseEnd_1933508 := by
    simpa [prefixWord, tailWord_1933508, baseEnd_1933508] using wordTrace_append hprefix tailTrace_1933508
  have hstable : (prefixWord ++ tailWord_1933508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933508).length < 2 ^ (prefixWord ++ tailWord_1933508).sum := by decide
  have hdescent : baseEnd_1933508 < baseStart_1933508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933520 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_1933520 : Nat := 118140960795 + 1933520 * 2 ^ 59
def prefixEnd_1933520 : Nat := 4983230072969 + 3 ^ 40 * 1933520 * 2
def baseEnd_1933520 : Nat := 992825115081380327807909

theorem tailTrace_1933520 : CollatzResearch.WordTrace tailWord_1933520 prefixEnd_1933520 992825115081380327807909 := by
  unfold tailWord_1933520
  simp only [CollatzResearch.WordTrace]
  refine ⟨35260633977597366885519007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47014178636796489180692009 35260633977597366885519007)
  ·
    refine ⟨52890950966396050328278511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35260633977597366885519007 52890950966396050328278511)
    ·
      refine ⟨79336426449594075492417767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52890950966396050328278511 79336426449594075492417767)
      ·
        refine ⟨119004639674391113238626651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79336426449594075492417767 119004639674391113238626651)
        ·
          refine ⟨178506959511586669857939977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119004639674391113238626651 178506959511586669857939977)
          ·
            refine ⟨133880219633690002393454983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178506959511586669857939977 133880219633690002393454983)
            ·
              refine ⟨200820329450535003590182475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133880219633690002393454983 200820329450535003590182475)
              ·
                refine ⟨301230494175802505385273713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200820329450535003590182475 301230494175802505385273713)
                ·
                  refine ⟨225922870631851879038955285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301230494175802505385273713 225922870631851879038955285)
                  ·
                    refine ⟨10590134560868056829951029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 225922870631851879038955285 10590134560868056829951029)
                    ·
                      refine ⟨992825115081380327807909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10590134560868056829951029 992825115081380327807909)
                      ·
                        rfl

theorem cell23_1933520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_1933520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933520 prefixEnd_1933520 := by exact prefixLift 1933520
  have htrace : WordTrace (prefixWord ++ tailWord_1933520) baseStart_1933520 baseEnd_1933520 := by
    simpa [prefixWord, tailWord_1933520, baseEnd_1933520] using wordTrace_append hprefix tailTrace_1933520
  have hstable : (prefixWord ++ tailWord_1933520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933520).length < 2 ^ (prefixWord ++ tailWord_1933520).sum := by decide
  have hdescent : baseEnd_1933520 < baseStart_1933520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933547 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4]
def baseStart_1933547 : Nat := 118140960795 + 1933547 * 2 ^ 59
def prefixEnd_1933547 : Nat := 4983230072969 + 3 ^ 40 * 1933547 * 2
def baseEnd_1933547 : Nat := 992838979059051722170285

theorem tailTrace_1933547 : CollatzResearch.WordTrace tailWord_1933547 prefixEnd_1933547 992838979059051722170285 := by
  unfold tailWord_1933547
  simp only [CollatzResearch.WordTrace]
  refine ⟨70522252726096917382270895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47014835150731278254847263 70522252726096917382270895)
  ·
    refine ⟨105783379089145376073406343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70522252726096917382270895 105783379089145376073406343)
    ·
      refine ⟨158675068633718064110109515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105783379089145376073406343 158675068633718064110109515)
      ·
        refine ⟨238012602950577096165164273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158675068633718064110109515 238012602950577096165164273)
        ·
          refine ⟨178509452212932822123873205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238012602950577096165164273 178509452212932822123873205)
          ·
            refine ⟨16735261144962452074113113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178509452212932822123873205 16735261144962452074113113)
            ·
              refine ⟨12551445858721839055584835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16735261144962452074113113 12551445858721839055584835)
              ·
                refine ⟨18827168788082758583377253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12551445858721839055584835 18827168788082758583377253)
                ·
                  refine ⟨3530094147765517234383235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18827168788082758583377253 3530094147765517234383235)
                  ·
                    refine ⟨5295141221648275851574853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530094147765517234383235 5295141221648275851574853)
                    ·
                      refine ⟨992838979059051722170285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5295141221648275851574853 992838979059051722170285)
                      ·
                        rfl

theorem cell23_1933547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4].length) (baseStart_1933547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933547 prefixEnd_1933547 := by exact prefixLift 1933547
  have htrace : WordTrace (prefixWord ++ tailWord_1933547) baseStart_1933547 baseEnd_1933547 := by
    simpa [prefixWord, tailWord_1933547, baseEnd_1933547] using wordTrace_append hprefix tailTrace_1933547
  have hstable : (prefixWord ++ tailWord_1933547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933547).length < 2 ^ (prefixWord ++ tailWord_1933547).sum := by decide
  have hdescent : baseEnd_1933547 < baseStart_1933547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933567 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_1933567 : Nat := 118140960795 + 1933567 * 2 ^ 59
def prefixEnd_1933567 : Nat := 4983230072969 + 3 ^ 40 * 1933567 * 2
def baseEnd_1933567 : Nat := 992849248672141643920193

theorem tailTrace_1933567 : CollatzResearch.WordTrace tailWord_1933567 prefixEnd_1933567 992849248672141643920193 := by
  unfold tailWord_1933567
  simp only [CollatzResearch.WordTrace]
  refine ⟨70522982186024460797998955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47015321457349640531999303 70522982186024460797998955)
  ·
    refine ⟨105784473279036691196998433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70522982186024460797998955 105784473279036691196998433)
    ·
      refine ⟨79338354959277518397748825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105784473279036691196998433 79338354959277518397748825)
      ·
        refine ⟨59503766219458138798311619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79338354959277518397748825 59503766219458138798311619)
        ·
          refine ⟨89255649329187208197467429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59503766219458138798311619 89255649329187208197467429)
          ·
            refine ⟨16735434249222601537025143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89255649329187208197467429 16735434249222601537025143)
            ·
              refine ⟨25103151373833902305537715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16735434249222601537025143 25103151373833902305537715)
              ·
                refine ⟨37654727060750853458306573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25103151373833902305537715 37654727060750853458306573)
                ·
                  refine ⟨14120522647781570046864965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37654727060750853458306573 14120522647781570046864965)
                  ·
                    refine ⟨2647597996459044383787181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14120522647781570046864965 2647597996459044383787181)
                    ·
                      refine ⟨992849248672141643920193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647597996459044383787181 992849248672141643920193)
                      ·
                        rfl

theorem cell23_1933567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_1933567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933567 prefixEnd_1933567 := by exact prefixLift 1933567
  have htrace : WordTrace (prefixWord ++ tailWord_1933567) baseStart_1933567 baseEnd_1933567 := by
    simpa [prefixWord, tailWord_1933567, baseEnd_1933567] using wordTrace_append hprefix tailTrace_1933567
  have hstable : (prefixWord ++ tailWord_1933567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933567).length < 2 ^ (prefixWord ++ tailWord_1933567).sum := by decide
  have hdescent : baseEnd_1933567 < baseStart_1933567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933598 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_1933598 : Nat := 118140960795 + 1933598 * 2 ^ 59
def prefixEnd_1933598 : Nat := 4983230072969 + 3 ^ 40 * 1933598 * 2
def baseEnd_1933598 : Nat := 992865166572431022632551

theorem tailTrace_1933598 : CollatzResearch.WordTrace tailWord_1933598 prefixEnd_1933598 992865166572431022632551 := by
  unfold tailWord_1933598
  simp only [CollatzResearch.WordTrace]
  refine ⟨8815514106114019136547181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47016075232608102061584965 8815514106114019136547181)
  ·
    refine ⟨3305817789792757176205193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8815514106114019136547181 3305817789792757176205193)
    ·
      refine ⟨2479363342344567882153895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3305817789792757176205193 2479363342344567882153895)
      ·
        refine ⟨3719045013516851823230843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479363342344567882153895 3719045013516851823230843)
        ·
          refine ⟨5578567520275277734846265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719045013516851823230843 5578567520275277734846265)
          ·
            refine ⟨4183925640206458301134699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5578567520275277734846265 4183925640206458301134699)
            ·
              refine ⟨6275888460309687451702049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4183925640206458301134699 6275888460309687451702049)
              ·
                refine ⟨4706916345232265588776537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6275888460309687451702049 4706916345232265588776537)
                ·
                  refine ⟨3530187258924199191582403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4706916345232265588776537 3530187258924199191582403)
                  ·
                    refine ⟨5295280888386298787373605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3530187258924199191582403 5295280888386298787373605)
                    ·
                      refine ⟨992865166572431022632551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5295280888386298787373605 992865166572431022632551)
                      ·
                        rfl

theorem cell23_1933598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_1933598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933598 prefixEnd_1933598 := by exact prefixLift 1933598
  have htrace : WordTrace (prefixWord ++ tailWord_1933598) baseStart_1933598 baseEnd_1933598 := by
    simpa [prefixWord, tailWord_1933598, baseEnd_1933598] using wordTrace_append hprefix tailTrace_1933598
  have hstable : (prefixWord ++ tailWord_1933598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933598).length < 2 ^ (prefixWord ++ tailWord_1933598).sum := by decide
  have hdescent : baseEnd_1933598 < baseStart_1933598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933608 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1933608 : Nat := 118140960795 + 1933608 * 2 ^ 59
def prefixEnd_1933608 : Nat := 4983230072969 + 3 ^ 40 * 1933608 * 2
def baseEnd_1933608 : Nat := 330956767126325327835835

theorem tailTrace_1933608 : CollatzResearch.WordTrace tailWord_1933608 prefixEnd_1933608 330956767126325327835835 := by
  unfold tailWord_1933608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262238789437962400120739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47016318385917283200160985 35262238789437962400120739)
  ·
    refine ⟨52893358184156943600181109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262238789437962400120739 52893358184156943600181109)
    ·
      refine ⟨4958752329764713462516979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52893358184156943600181109 4958752329764713462516979)
      ·
        refine ⟨7438128494647070193775469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4958752329764713462516979 7438128494647070193775469)
        ·
          refine ⟨2789298185492651322665801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7438128494647070193775469 2789298185492651322665801)
          ·
            refine ⟨2091973639119488491999351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2789298185492651322665801 2091973639119488491999351)
            ·
              refine ⟨3137960458679232737999027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2091973639119488491999351 3137960458679232737999027)
              ·
                refine ⟨4706940688018849106998541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3137960458679232737999027 4706940688018849106998541)
                ·
                  refine ⟨1765102758007068415124453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4706940688018849106998541 1765102758007068415124453)
                  ·
                    refine ⟨330956767126325327835835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765102758007068415124453 330956767126325327835835)
                    ·
                      rfl

theorem cell23_1933608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1933608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933608 prefixEnd_1933608 := by exact prefixLift 1933608
  have htrace : WordTrace (prefixWord ++ tailWord_1933608) baseStart_1933608 baseEnd_1933608 := by
    simpa [prefixWord, tailWord_1933608, baseEnd_1933608] using wordTrace_append hprefix tailTrace_1933608
  have hstable : (prefixWord ++ tailWord_1933608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933608).length < 2 ^ (prefixWord ++ tailWord_1933608).sum := by decide
  have hdescent : baseEnd_1933608 < baseStart_1933608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933624 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_1933624 : Nat := 118140960795 + 1933624 * 2 ^ 59
def prefixEnd_1933624 : Nat := 4983230072969 + 3 ^ 40 * 1933624 * 2
def baseEnd_1933624 : Nat := 992878517069447920907431

theorem tailTrace_1933624 : CollatzResearch.WordTrace tailWord_1933624 prefixEnd_1933624 992878517069447920907431 := by
  unfold tailWord_1933624
  simp only [CollatzResearch.WordTrace]
  refine ⟨35262530573408979766411963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47016707431211973021882617 35262530573408979766411963)
  ·
    refine ⟨52893795860113469649617945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35262530573408979766411963 52893795860113469649617945)
    ·
      refine ⟨39670346895085102237213459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52893795860113469649617945 39670346895085102237213459)
      ·
        refine ⟨59505520342627653355820189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39670346895085102237213459 59505520342627653355820189)
        ·
          refine ⟨22314570128485370008432571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59505520342627653355820189 22314570128485370008432571)
          ·
            refine ⟨33471855192728055012648857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22314570128485370008432571 33471855192728055012648857)
            ·
              refine ⟨25103891394546041259486643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33471855192728055012648857 25103891394546041259486643)
              ·
                refine ⟨37655837091819061889229965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25103891394546041259486643 37655837091819061889229965)
                ·
                  refine ⟨14120938909432148208461237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37655837091819061889229965 14120938909432148208461237)
                  ·
                    refine ⟨1323838022759263894543241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14120938909432148208461237 1323838022759263894543241)
                    ·
                      refine ⟨992878517069447920907431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323838022759263894543241 992878517069447920907431)
                      ·
                        rfl

theorem cell23_1933624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_1933624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933624 prefixEnd_1933624 := by exact prefixLift 1933624
  have htrace : WordTrace (prefixWord ++ tailWord_1933624) baseStart_1933624 baseEnd_1933624 := by
    simpa [prefixWord, tailWord_1933624, baseEnd_1933624] using wordTrace_append hprefix tailTrace_1933624
  have hstable : (prefixWord ++ tailWord_1933624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933624).length < 2 ^ (prefixWord ++ tailWord_1933624).sum := by decide
  have hdescent : baseEnd_1933624 < baseStart_1933624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933705 : List Nat := [1, 2, 1, 1, 6, 1, 1, 5, 1, 2, 2]
def baseStart_1933705 : Nat := 118140960795 + 1933705 * 2 ^ 59
def prefixEnd_1933705 : Nat := 4983230072969 + 3 ^ 40 * 1933705 * 2
def baseEnd_1933705 : Nat := 992920109002462103994559

theorem tailTrace_1933705 : CollatzResearch.WordTrace tailWord_1933705 prefixEnd_1933705 992920109002462103994559 := by
  unfold tailWord_1933705
  simp only [CollatzResearch.WordTrace]
  refine ⟨70528015459524510366522569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47018676973016340244348379 70528015459524510366522569)
  ·
    refine ⟨52896011594643382774891927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70528015459524510366522569 52896011594643382774891927)
    ·
      refine ⟨79344017391965074162337891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52896011594643382774891927 79344017391965074162337891)
      ·
        refine ⟨119016026087947611243506837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79344017391965074162337891 119016026087947611243506837)
        ·
          refine ⟨5578876222872544277039383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119016026087947611243506837 5578876222872544277039383)
          ·
            refine ⟨8368314334308816415559075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5578876222872544277039383 8368314334308816415559075)
            ·
              refine ⟨12552471501463224623338613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368314334308816415559075 12552471501463224623338613)
              ·
                refine ⟨1176794203262177308437995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12552471501463224623338613 1176794203262177308437995)
                ·
                  refine ⟨1765191304893265962656993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176794203262177308437995 1765191304893265962656993)
                  ·
                    refine ⟨1323893478669949471992745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1765191304893265962656993 1323893478669949471992745)
                    ·
                      refine ⟨992920109002462103994559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323893478669949471992745 992920109002462103994559)
                      ·
                        rfl

theorem cell23_1933705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 1, 2, 2].length) (baseStart_1933705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933705 prefixEnd_1933705 := by exact prefixLift 1933705
  have htrace : WordTrace (prefixWord ++ tailWord_1933705) baseStart_1933705 baseEnd_1933705 := by
    simpa [prefixWord, tailWord_1933705, baseEnd_1933705] using wordTrace_append hprefix tailTrace_1933705
  have hstable : (prefixWord ++ tailWord_1933705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933705).length < 2 ^ (prefixWord ++ tailWord_1933705).sum := by decide
  have hdescent : baseEnd_1933705 < baseStart_1933705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933708 : List Nat := [2, 2, 1, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_1933708 : Nat := 118140960795 + 1933708 * 2 ^ 59
def prefixEnd_1933708 : Nat := 4983230072969 + 3 ^ 40 * 1933708 * 2
def baseEnd_1933708 : Nat := 992921649444425592257045

theorem tailTrace_1933708 : CollatzResearch.WordTrace tailWord_1933708 prefixEnd_1933708 992921649444425592257045 := by
  unfold tailWord_1933708
  simp only [CollatzResearch.WordTrace]
  refine ⟨35264062439256820939440889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47018749919009094585921185 35264062439256820939440889)
  ·
    refine ⟨26448046829442615704580667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35264062439256820939440889 26448046829442615704580667)
    ·
      refine ⟨39672070244163923556871001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26448046829442615704580667 39672070244163923556871001)
      ·
        refine ⟨29754052683122942667653251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39672070244163923556871001 29754052683122942667653251)
        ·
          refine ⟨44631079024684414001479877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29754052683122942667653251 44631079024684414001479877)
          ·
            refine ⟨8368327317128327625277477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44631079024684414001479877 8368327317128327625277477)
            ·
              refine ⟨1569061371961561429739527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8368327317128327625277477 1569061371961561429739527)
              ·
                refine ⟨2353592057942342144609291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569061371961561429739527 2353592057942342144609291)
                ·
                  refine ⟨3530388086913513216913937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353592057942342144609291 3530388086913513216913937)
                  ·
                    refine ⟨2647791065185134912685453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3530388086913513216913937 2647791065185134912685453)
                    ·
                      refine ⟨992921649444425592257045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647791065185134912685453 992921649444425592257045)
                      ·
                        rfl

theorem cell23_1933708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_1933708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933708 prefixEnd_1933708 := by exact prefixLift 1933708
  have htrace : WordTrace (prefixWord ++ tailWord_1933708) baseStart_1933708 baseEnd_1933708 := by
    simpa [prefixWord, tailWord_1933708, baseEnd_1933708] using wordTrace_append hprefix tailTrace_1933708
  have hstable : (prefixWord ++ tailWord_1933708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933708).length < 2 ^ (prefixWord ++ tailWord_1933708).sum := by decide
  have hdescent : baseEnd_1933708 < baseStart_1933708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933721 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 3]
def baseStart_1933721 : Nat := 118140960795 + 1933721 * 2 ^ 59
def prefixEnd_1933721 : Nat := 4983230072969 + 3 ^ 40 * 1933721 * 2
def baseEnd_1933721 : Nat := 992928324692934041394485

theorem tailTrace_1933721 : CollatzResearch.WordTrace tailWord_1933721 prefixEnd_1933721 992928324692934041394485 := by
  unfold tailWord_1933721
  simp only [CollatzResearch.WordTrace]
  refine ⟨70528599027466545099105017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47019066018311030066070011 70528599027466545099105017)
  ·
    refine ⟨52896449270599908824328763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70528599027466545099105017 52896449270599908824328763)
    ·
      refine ⟨79344673905899863236493145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52896449270599908824328763 79344673905899863236493145)
      ·
        refine ⟨59508505429424897427369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79344673905899863236493145 59508505429424897427369859)
        ·
          refine ⟨89262758144137346141054789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59508505429424897427369859 89262758144137346141054789)
          ·
            refine ⟨16736767152025752401447773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89262758144137346141054789 16736767152025752401447773)
            ·
              refine ⟨6276287682009657150542915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16736767152025752401447773 6276287682009657150542915)
              ·
                refine ⟨9414431523014485725814373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6276287682009657150542915 9414431523014485725814373)
                ·
                  refine ⟨1765205910565216073590195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9414431523014485725814373 1765205910565216073590195)
                  ·
                    refine ⟨2647808865847824110385293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1765205910565216073590195 2647808865847824110385293)
                    ·
                      refine ⟨992928324692934041394485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2647808865847824110385293 992928324692934041394485)
                      ·
                        rfl

theorem cell23_1933721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_1933721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933721 prefixEnd_1933721 := by exact prefixLift 1933721
  have htrace : WordTrace (prefixWord ++ tailWord_1933721) baseStart_1933721 baseEnd_1933721 := by
    simpa [prefixWord, tailWord_1933721, baseEnd_1933721] using wordTrace_append hprefix tailTrace_1933721
  have hstable : (prefixWord ++ tailWord_1933721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933721).length < 2 ^ (prefixWord ++ tailWord_1933721).sum := by decide
  have hdescent : baseEnd_1933721 < baseStart_1933721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933835 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 5]
def baseStart_1933835 : Nat := 118140960795 + 1933835 * 2 ^ 59
def prefixEnd_1933835 : Nat := 4983230072969 + 3 ^ 40 * 1933835 * 2
def baseEnd_1933835 : Nat := 110331873498616288374329

theorem tailTrace_1933835 : CollatzResearch.WordTrace tailWord_1933835 prefixEnd_1933835 110331873498616288374329 := by
  unfold tailWord_1933835
  simp only [CollatzResearch.WordTrace]
  refine ⟨70532756949053542568754959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47021837966035695045836639 70532756949053542568754959)
  ·
    refine ⟨105799135423580313853132439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70532756949053542568754959 105799135423580313853132439)
    ·
      refine ⟨158698703135370470779698659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105799135423580313853132439 158698703135370470779698659)
      ·
        refine ⟨238048054703055706169547989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158698703135370470779698659 238048054703055706169547989)
        ·
          refine ⟨5579251282102868113348781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 238048054703055706169547989 5579251282102868113348781)
          ·
            refine ⟨2092219230788575542505793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5579251282102868113348781 2092219230788575542505793)
            ·
              refine ⟨1569164423091431656879345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092219230788575542505793 1569164423091431656879345)
              ·
                refine ⟨1176873317318573742659509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569164423091431656879345 1176873317318573742659509)
                ·
                  refine ⟨110331873498616288374329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176873317318573742659509 110331873498616288374329)
                  ·
                    rfl

theorem cell23_1933835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 5].length) (baseStart_1933835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933835 prefixEnd_1933835 := by exact prefixLift 1933835
  have htrace : WordTrace (prefixWord ++ tailWord_1933835) baseStart_1933835 baseEnd_1933835 := by
    simpa [prefixWord, tailWord_1933835, baseEnd_1933835] using wordTrace_append hprefix tailTrace_1933835
  have hstable : (prefixWord ++ tailWord_1933835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933835).length < 2 ^ (prefixWord ++ tailWord_1933835).sum := by decide
  have hdescent : baseEnd_1933835 < baseStart_1933835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933838 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2]
def baseStart_1933838 : Nat := 118140960795 + 1933838 * 2 ^ 59
def prefixEnd_1933838 : Nat := 4983230072969 + 3 ^ 40 * 1933838 * 2
def baseEnd_1933838 : Nat := 992988401929510083631447

theorem tailTrace_1933838 : CollatzResearch.WordTrace tailWord_1933838 prefixEnd_1933838 992988401929510083631447 := by
  unfold tailWord_1933838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8816608296005334260139271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47021910912028449387409445 8816608296005334260139271)
  ·
    refine ⟨13224912444008001390208907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8816608296005334260139271 13224912444008001390208907)
    ·
      refine ⟨19837368666012002085313361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13224912444008001390208907 19837368666012002085313361)
      ·
        refine ⟨14878026499509001563985021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19837368666012002085313361 14878026499509001563985021)
        ·
          refine ⟨5579259937315875586494383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14878026499509001563985021 5579259937315875586494383)
          ·
            refine ⟨8368889905973813379741575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579259937315875586494383 8368889905973813379741575)
            ·
              refine ⟨12553334858960720069612363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8368889905973813379741575 12553334858960720069612363)
              ·
                refine ⟨18830002288441080104418545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12553334858960720069612363 18830002288441080104418545)
                ·
                  refine ⟨14122501716330810078313909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18830002288441080104418545 14122501716330810078313909)
                  ·
                    refine ⟨1323984535906013444841929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14122501716330810078313909 1323984535906013444841929)
                    ·
                      refine ⟨992988401929510083631447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1323984535906013444841929 992988401929510083631447)
                      ·
                        rfl

theorem cell23_1933838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2].length) (baseStart_1933838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933838 prefixEnd_1933838 := by exact prefixLift 1933838
  have htrace : WordTrace (prefixWord ++ tailWord_1933838) baseStart_1933838 baseEnd_1933838 := by
    simpa [prefixWord, tailWord_1933838, baseEnd_1933838] using wordTrace_append hprefix tailTrace_1933838
  have hstable : (prefixWord ++ tailWord_1933838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933838).length < 2 ^ (prefixWord ++ tailWord_1933838).sum := by decide
  have hdescent : baseEnd_1933838 < baseStart_1933838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933861 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_1933861 : Nat := 118140960795 + 1933861 * 2 ^ 59
def prefixEnd_1933861 : Nat := 4983230072969 + 3 ^ 40 * 1933861 * 2
def baseEnd_1933861 : Nat := 331000070661521164547947

theorem tailTrace_1933861 : CollatzResearch.WordTrace tailWord_1933861 prefixEnd_1933861 331000070661521164547947 := by
  unfold tailWord_1933861
  simp only [CollatzResearch.WordTrace]
  refine ⟨70533705246959349009201437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47022470164639566006134291 70533705246959349009201437)
  ·
    refine ⟨26450139467609755878450539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70533705246959349009201437 26450139467609755878450539)
    ·
      refine ⟨39675209201414633817675809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26450139467609755878450539 39675209201414633817675809)
      ·
        refine ⟨29756406901060975363256857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39675209201414633817675809 29756406901060975363256857)
        ·
          refine ⟨22317305175795731522442643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29756406901060975363256857 22317305175795731522442643)
          ·
            refine ⟨33475957763693597283663965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22317305175795731522442643 33475957763693597283663965)
            ·
              refine ⟨12553484161385098981373987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33475957763693597283663965 12553484161385098981373987)
              ·
                refine ⟨18830226242077648472060981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12553484161385098981373987 18830226242077648472060981)
                ·
                  refine ⟨1765333710194779544255717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18830226242077648472060981 1765333710194779544255717)
                  ·
                    refine ⟨331000070661521164547947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765333710194779544255717 331000070661521164547947)
                    ·
                      rfl

theorem cell23_1933861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_1933861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933861 prefixEnd_1933861 := by exact prefixLift 1933861
  have htrace : WordTrace (prefixWord ++ tailWord_1933861) baseStart_1933861 baseEnd_1933861 := by
    simpa [prefixWord, tailWord_1933861, baseEnd_1933861] using wordTrace_append hprefix tailTrace_1933861
  have hstable : (prefixWord ++ tailWord_1933861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933861).length < 2 ^ (prefixWord ++ tailWord_1933861).sum := by decide
  have hdescent : baseEnd_1933861 < baseStart_1933861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933869 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 5]
def baseStart_1933869 : Nat := 118140960795 + 1933869 * 2 ^ 59
def prefixEnd_1933869 : Nat := 4983230072969 + 3 ^ 40 * 1933869 * 2
def baseEnd_1933869 : Nat := 110333813314422162482645

theorem tailTrace_1933869 : CollatzResearch.WordTrace tailWord_1933869 prefixEnd_1933869 110333813314422162482645 := by
  unfold tailWord_1933869
  simp only [CollatzResearch.WordTrace]
  refine ⟨70533997030930366375492661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47022664687286910916995107 70533997030930366375492661)
  ·
    refine ⟨6612562221649721847702437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70533997030930366375492661 6612562221649721847702437)
    ·
      refine ⟨1239855416559322846444207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6612562221649721847702437 1239855416559322846444207)
      ·
        refine ⟨1859783124838984269666311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1239855416559322846444207 1859783124838984269666311)
        ·
          refine ⟨2789674687258476404499467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1859783124838984269666311 2789674687258476404499467)
          ·
            refine ⟨4184512030887714606749201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2789674687258476404499467 4184512030887714606749201)
            ·
              refine ⟨3138384023165785955061901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4184512030887714606749201 3138384023165785955061901)
              ·
                refine ⟨1176894008687169733148213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3138384023165785955061901 1176894008687169733148213)
                ·
                  refine ⟨110333813314422162482645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1176894008687169733148213 110333813314422162482645)
                  ·
                    rfl

theorem cell23_1933869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_1933869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933869 prefixEnd_1933869 := by exact prefixLift 1933869
  have htrace : WordTrace (prefixWord ++ tailWord_1933869) baseStart_1933869 baseEnd_1933869 := by
    simpa [prefixWord, tailWord_1933869, baseEnd_1933869] using wordTrace_append hprefix tailTrace_1933869
  have hstable : (prefixWord ++ tailWord_1933869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933869).length < 2 ^ (prefixWord ++ tailWord_1933869).sum := by decide
  have hdescent : baseEnd_1933869 < baseStart_1933869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933895 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 1, 4]
def baseStart_1933895 : Nat := 118140960795 + 1933895 * 2 ^ 59
def prefixEnd_1933895 : Nat := 4983230072969 + 3 ^ 40 * 1933895 * 2
def baseEnd_1933895 : Nat := 331005890108938786872895

theorem tailTrace_1933895 : CollatzResearch.WordTrace tailWord_1933895 prefixEnd_1933895 331005890108938786872895 := by
  unfold tailWord_1933895
  simp only [CollatzResearch.WordTrace]
  refine ⟨70534945328836172815939139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47023296885890781877292759 70534945328836172815939139)
  ·
    refine ⟨105802417993254259223908709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70534945328836172815939139 105802417993254259223908709)
    ·
      refine ⟨19837953373735173604482883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105802417993254259223908709 19837953373735173604482883)
      ·
        refine ⟨29756930060602760406724325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19837953373735173604482883 29756930060602760406724325)
        ·
          refine ⟨5579424386363017576260811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29756930060602760406724325 5579424386363017576260811)
          ·
            refine ⟨8369136579544526364391217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579424386363017576260811 8369136579544526364391217)
            ·
              refine ⟨6276852434658394773293413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8369136579544526364391217 6276852434658394773293413)
              ·
                refine ⟨1176909831498449019992515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6276852434658394773293413 1176909831498449019992515)
                ·
                  refine ⟨1765364747247673529988773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1176909831498449019992515 1765364747247673529988773)
                  ·
                    refine ⟨331005890108938786872895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765364747247673529988773 331005890108938786872895)
                    ·
                      rfl

theorem cell23_1933895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_1933895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933895 prefixEnd_1933895 := by exact prefixLift 1933895
  have htrace : WordTrace (prefixWord ++ tailWord_1933895) baseStart_1933895 baseEnd_1933895 := by
    simpa [prefixWord, tailWord_1933895, baseEnd_1933895] using wordTrace_append hprefix tailTrace_1933895
  have hstable : (prefixWord ++ tailWord_1933895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933895).length < 2 ^ (prefixWord ++ tailWord_1933895).sum := by decide
  have hdescent : baseEnd_1933895 < baseStart_1933895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933904 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_1933904 : Nat := 118140960795 + 1933904 * 2 ^ 59
def prefixEnd_1933904 : Nat := 4983230072969 + 3 ^ 40 * 1933904 * 2
def baseEnd_1933904 : Nat := 331007430550902275135381

theorem tailTrace_1933904 : CollatzResearch.WordTrace tailWord_1933904 prefixEnd_1933904 331007430550902275135381 := by
  unfold tailWord_1933904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35267636792901783676508383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47023515723869044902011177 35267636792901783676508383)
  ·
    refine ⟨52901455189352675514762575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35267636792901783676508383 52901455189352675514762575)
    ·
      refine ⟨79352182784029013272143863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52901455189352675514762575 79352182784029013272143863)
      ·
        refine ⟨119028274176043519908215795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79352182784029013272143863 119028274176043519908215795)
        ·
          refine ⟨178542411264065279862323693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119028274176043519908215795 178542411264065279862323693)
          ·
            refine ⟨66953404224024479948371385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178542411264065279862323693 66953404224024479948371385)
            ·
              refine ⟨50215053168018359961278539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66953404224024479948371385 50215053168018359961278539)
              ·
                refine ⟨75322579752027539941917809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50215053168018359961278539 75322579752027539941917809)
                ·
                  refine ⟨56491934814020654956438357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75322579752027539941917809 56491934814020654956438357)
                  ·
                    refine ⟨331007430550902275135381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 56491934814020654956438357 331007430550902275135381)
                    ·
                      rfl

theorem cell23_1933904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_1933904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933904 prefixEnd_1933904 := by exact prefixLift 1933904
  have htrace : WordTrace (prefixWord ++ tailWord_1933904) baseStart_1933904 baseEnd_1933904 := by
    simpa [prefixWord, tailWord_1933904, baseEnd_1933904] using wordTrace_append hprefix tailTrace_1933904
  have hstable : (prefixWord ++ tailWord_1933904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933904).length < 2 ^ (prefixWord ++ tailWord_1933904).sum := by decide
  have hdescent : baseEnd_1933904 < baseStart_1933904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933945 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 2, 3, 2]
def baseStart_1933945 : Nat := 118140960795 + 1933945 * 2 ^ 59
def prefixEnd_1933945 : Nat := 4983230072969 + 3 ^ 40 * 1933945 * 2
def baseEnd_1933945 : Nat := 993043344359541164993455

theorem tailTrace_1933945 : CollatzResearch.WordTrace tailWord_1933945 prefixEnd_1933945 993043344359541164993455 := by
  unfold tailWord_1933945
  simp only [CollatzResearch.WordTrace]
  refine ⟨70536768978655031355259289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47024512652436687570172859 70536768978655031355259289)
  ·
    refine ⟨52902576733991273516444467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70536768978655031355259289 52902576733991273516444467)
    ·
      refine ⟨79353865100986910274666701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52902576733991273516444467 79353865100986910274666701)
      ·
        refine ⟨29757699412870091353000013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79353865100986910274666701 29757699412870091353000013)
        ·
          refine ⟨11159137279826284257375005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29757699412870091353000013 11159137279826284257375005)
          ·
            refine ⟨4184676479934856596515627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11159137279826284257375005 4184676479934856596515627)
            ·
              refine ⟨6277014719902284894773441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184676479934856596515627 6277014719902284894773441)
              ·
                refine ⟨4707761039926713671080081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277014719902284894773441 4707761039926713671080081)
                ·
                  refine ⟨3530820779945035253310061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4707761039926713671080081 3530820779945035253310061)
                  ·
                    refine ⟨1324057792479388219991273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3530820779945035253310061 1324057792479388219991273)
                    ·
                      refine ⟨993043344359541164993455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324057792479388219991273 993043344359541164993455)
                      ·
                        rfl

theorem cell23_1933945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_1933945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933945 prefixEnd_1933945 := by exact prefixLift 1933945
  have htrace : WordTrace (prefixWord ++ tailWord_1933945) baseStart_1933945 baseEnd_1933945 := by
    simpa [prefixWord, tailWord_1933945, baseEnd_1933945] using wordTrace_append hprefix tailTrace_1933945
  have hstable : (prefixWord ++ tailWord_1933945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933945).length < 2 ^ (prefixWord ++ tailWord_1933945).sum := by decide
  have hdescent : baseEnd_1933945 < baseStart_1933945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933961 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_1933961 : Nat := 118140960795 + 1933961 * 2 ^ 59
def prefixEnd_1933961 : Nat := 4983230072969 + 3 ^ 40 * 1933961 * 2
def baseEnd_1933961 : Nat := 993051560050013102393381

theorem tailTrace_1933961 : CollatzResearch.WordTrace tailWord_1933961 prefixEnd_1933961 993051560050013102393381 := by
  unfold tailWord_1933961
  simp only [CollatzResearch.WordTrace]
  refine ⟨70537352546597066087841737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47024901697731377391894491 70537352546597066087841737)
  ·
    refine ⟨52903014409947799565881303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70537352546597066087841737 52903014409947799565881303)
    ·
      refine ⟨79354521614921699348821955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52903014409947799565881303 79354521614921699348821955)
      ·
        refine ⟨119031782422382549023232933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79354521614921699348821955 119031782422382549023232933)
        ·
          refine ⟨22318459204196727941856175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119031782422382549023232933 22318459204196727941856175)
          ·
            refine ⟨33477688806295091912784263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22318459204196727941856175 33477688806295091912784263)
            ·
              refine ⟨50216533209442637869176395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33477688806295091912784263 50216533209442637869176395)
              ·
                refine ⟨75324799814163956803764593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50216533209442637869176395 75324799814163956803764593)
                ·
                  refine ⟨56493599860622967602823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75324799814163956803764593 56493599860622967602823445)
                  ·
                    refine ⟨2648137493466701606382349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56493599860622967602823445 2648137493466701606382349)
                    ·
                      refine ⟨993051560050013102393381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2648137493466701606382349 993051560050013102393381)
                      ·
                        rfl

theorem cell23_1933961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_1933961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933961 prefixEnd_1933961 := by exact prefixLift 1933961
  have htrace : WordTrace (prefixWord ++ tailWord_1933961) baseStart_1933961 baseEnd_1933961 := by
    simpa [prefixWord, tailWord_1933961, baseEnd_1933961] using wordTrace_append hprefix tailTrace_1933961
  have hstable : (prefixWord ++ tailWord_1933961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933961).length < 2 ^ (prefixWord ++ tailWord_1933961).sum := by decide
  have hdescent : baseEnd_1933961 < baseStart_1933961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933972 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1933972 : Nat := 118140960795 + 1933972 * 2 ^ 59
def prefixEnd_1933972 : Nat := 4983230072969 + 3 ^ 40 * 1933972 * 2
def baseEnd_1933972 : Nat := 331019069445737519785277

theorem tailTrace_1933972 : CollatzResearch.WordTrace tailWord_1933972 prefixEnd_1933972 331019069445737519785277 := by
  unfold tailWord_1933972
  simp only [CollatzResearch.WordTrace]
  refine ⟨35268876874778607483246085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47025169166371476644328113 35268876874778607483246085)
  ·
    refine ⟨6612914414020988903108641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35268876874778607483246085 6612914414020988903108641)
    ·
      refine ⟨4959685810515741677331481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6612914414020988903108641 4959685810515741677331481)
      ·
        refine ⟨3719764357886806257998611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4959685810515741677331481 3719764357886806257998611)
        ·
          refine ⟨5579646536830209386997917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719764357886806257998611 5579646536830209386997917)
          ·
            refine ⟨2092367451311328520124219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5579646536830209386997917 2092367451311328520124219)
            ·
              refine ⟨3138551176966992780186329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092367451311328520124219 3138551176966992780186329)
              ·
                refine ⟨2353913382725244585139747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3138551176966992780186329 2353913382725244585139747)
                ·
                  refine ⟨3530870074087866877709621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2353913382725244585139747 3530870074087866877709621)
                  ·
                    refine ⟨331019069445737519785277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3530870074087866877709621 331019069445737519785277)
                    ·
                      rfl

theorem cell23_1933972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1933972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933972 prefixEnd_1933972 := by exact prefixLift 1933972
  have htrace : WordTrace (prefixWord ++ tailWord_1933972) baseStart_1933972 baseEnd_1933972 := by
    simpa [prefixWord, tailWord_1933972, baseEnd_1933972] using wordTrace_append hprefix tailTrace_1933972
  have hstable : (prefixWord ++ tailWord_1933972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933972).length < 2 ^ (prefixWord ++ tailWord_1933972).sum := by decide
  have hdescent : baseEnd_1933972 < baseStart_1933972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933975 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 5, 2, 2]
def baseStart_1933975 : Nat := 118140960795 + 1933975 * 2 ^ 59
def prefixEnd_1933975 : Nat := 4983230072969 + 3 ^ 40 * 1933975 * 2
def baseEnd_1933975 : Nat := 993058748779176047618317

theorem tailTrace_1933975 : CollatzResearch.WordTrace tailWord_1933975 prefixEnd_1933975 993058748779176047618317 := by
  unfold tailWord_1933975
  simp only [CollatzResearch.WordTrace]
  refine ⟨70537863168546346478851379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47025242112364230985900919 70537863168546346478851379)
  ·
    refine ⟨105806794752819519718277069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70537863168546346478851379 105806794752819519718277069)
    ·
      refine ⟨39677548032307319894353901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105806794752819519718277069 39677548032307319894353901)
      ·
        refine ⟨14879080512115244960382713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39677548032307319894353901 14879080512115244960382713)
        ·
          refine ⟨11159310384086433720287035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14879080512115244960382713 11159310384086433720287035)
          ·
            refine ⟨16738965576129650580430553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159310384086433720287035 16738965576129650580430553)
            ·
              refine ⟨12554224182097237935322915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16738965576129650580430553 12554224182097237935322915)
              ·
                refine ⟨18831336273145856902984373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554224182097237935322915 18831336273145856902984373)
                ·
                  refine ⟨1765437775607424084654785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18831336273145856902984373 1765437775607424084654785)
                  ·
                    refine ⟨1324078331705568063491089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1765437775607424084654785 1324078331705568063491089)
                    ·
                      refine ⟨993058748779176047618317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324078331705568063491089 993058748779176047618317)
                      ·
                        rfl

theorem cell23_1933975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_1933975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933975 prefixEnd_1933975 := by exact prefixLift 1933975
  have htrace : WordTrace (prefixWord ++ tailWord_1933975) baseStart_1933975 baseEnd_1933975 := by
    simpa [prefixWord, tailWord_1933975, baseEnd_1933975] using wordTrace_append hprefix tailTrace_1933975
  have hstable : (prefixWord ++ tailWord_1933975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933975).length < 2 ^ (prefixWord ++ tailWord_1933975).sum := by decide
  have hdescent : baseEnd_1933975 < baseStart_1933975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933981 : List Nat := [1, 4, 2, 1, 1, 1, 4, 9]
def baseStart_1933981 : Nat := 118140960795 + 1933981 * 2 ^ 59
def prefixEnd_1933981 : Nat := 4983230072969 + 3 ^ 40 * 1933981 * 2
def baseEnd_1933981 : Nat := 36780067765300112005307

theorem tailTrace_1933981 : CollatzResearch.WordTrace tailWord_1933981 prefixEnd_1933981 36780067765300112005307 := by
  unfold tailWord_1933981
  simp only [CollatzResearch.WordTrace]
  refine ⟨70538082006524609503569797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47025388004349739669046531 70538082006524609503569797)
  ·
    refine ⟨13225890376223364281919337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70538082006524609503569797 13225890376223364281919337)
    ·
      refine ⟨9919417782167523211439503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13225890376223364281919337 9919417782167523211439503)
      ·
        refine ⟨14879126673251284817159255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919417782167523211439503 14879126673251284817159255)
        ·
          refine ⟨22318690009876927225738883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14879126673251284817159255 22318690009876927225738883)
          ·
            refine ⟨33478035014815390838608325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22318690009876927225738883 33478035014815390838608325)
            ·
              refine ⟨6277131565277885782239061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33478035014815390838608325 6277131565277885782239061)
              ·
                refine ⟨36780067765300112005307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6277131565277885782239061 36780067765300112005307)
                ·
                  rfl

theorem cell23_1933981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 9].length) (baseStart_1933981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933981 prefixEnd_1933981 := by exact prefixLift 1933981
  have htrace : WordTrace (prefixWord ++ tailWord_1933981) baseStart_1933981 baseEnd_1933981 := by
    simpa [prefixWord, tailWord_1933981, baseEnd_1933981] using wordTrace_append hprefix tailTrace_1933981
  have hstable : (prefixWord ++ tailWord_1933981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933981).length < 2 ^ (prefixWord ++ tailWord_1933981).sum := by decide
  have hdescent : baseEnd_1933981 < baseStart_1933981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933988 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_1933988 : Nat := 118140960795 + 1933988 * 2 ^ 59
def prefixEnd_1933988 : Nat := 4983230072969 + 3 ^ 40 * 1933988 * 2
def baseEnd_1933988 : Nat := 993065424027684496755757

theorem tailTrace_1933988 : CollatzResearch.WordTrace tailWord_1933988 prefixEnd_1933988 993065424027684496755757 := by
  unfold tailWord_1933988
  simp only [CollatzResearch.WordTrace]
  refine ⟨35269168658749624849537309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47025558211666166466049745 35269168658749624849537309)
  ·
    refine ⟨13225938247031109318576491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35269168658749624849537309 13225938247031109318576491)
    ·
      refine ⟨19838907370546663977864737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13225938247031109318576491 19838907370546663977864737)
      ·
        refine ⟨14879180527909997983398553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19838907370546663977864737 14879180527909997983398553)
        ·
          refine ⟨11159385395932498487548915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14879180527909997983398553 11159385395932498487548915)
          ·
            refine ⟨16739078093898747731323373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159385395932498487548915 16739078093898747731323373)
            ·
              refine ⟨6277154285212030399246265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16739078093898747731323373 6277154285212030399246265)
              ·
                refine ⟨4707865713909022799434699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277154285212030399246265 4707865713909022799434699)
                ·
                  refine ⟨7061798570863534199152049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707865713909022799434699 7061798570863534199152049)
                  ·
                    refine ⟨5296348928147650649364037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7061798570863534199152049 5296348928147650649364037)
                    ·
                      refine ⟨993065424027684496755757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5296348928147650649364037 993065424027684496755757)
                      ·
                        rfl

theorem cell23_1933988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_1933988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933988 prefixEnd_1933988 := by exact prefixLift 1933988
  have htrace : WordTrace (prefixWord ++ tailWord_1933988) baseStart_1933988 baseEnd_1933988 := by
    simpa [prefixWord, tailWord_1933988, baseEnd_1933988] using wordTrace_append hprefix tailTrace_1933988
  have hstable : (prefixWord ++ tailWord_1933988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933988).length < 2 ^ (prefixWord ++ tailWord_1933988).sum := by decide
  have hdescent : baseEnd_1933988 < baseStart_1933988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1933998 : List Nat := [4, 1, 4, 1, 1, 12]
def baseStart_1933998 : Nat := 118140960795 + 1933998 * 2 ^ 59
def prefixEnd_1933998 : Nat := 4983230072969 + 3 ^ 40 * 1933998 * 2
def baseEnd_1933998 : Nat := 4086710118659380484077

theorem tailTrace_1933998 : CollatzResearch.WordTrace tailWord_1933998 prefixEnd_1933998 4086710118659380484077 := by
  unfold tailWord_1933998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8817337755932877675867331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47025801364975347604625765 8817337755932877675867331)
  ·
    refine ⟨13226006633899316513800997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8817337755932877675867331 13226006633899316513800997)
    ·
      refine ⟨2479876243856121846337687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13226006633899316513800997 2479876243856121846337687)
      ·
        refine ⟨3719814365784182769506531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2479876243856121846337687 3719814365784182769506531)
        ·
          refine ⟨5579721548676274154259797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3719814365784182769506531 5579721548676274154259797)
          ·
            refine ⟨4086710118659380484077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5579721548676274154259797 4086710118659380484077)
            ·
              rfl

theorem cell23_1933998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 12].length) (baseStart_1933998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1933998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1933998 prefixEnd_1933998 := by exact prefixLift 1933998
  have htrace : WordTrace (prefixWord ++ tailWord_1933998) baseStart_1933998 baseEnd_1933998 := by
    simpa [prefixWord, tailWord_1933998, baseEnd_1933998] using wordTrace_append hprefix tailTrace_1933998
  have hstable : (prefixWord ++ tailWord_1933998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1933998).length < 2 ^ (prefixWord ++ tailWord_1933998).sum := by decide
  have hdescent : baseEnd_1933998 < baseStart_1933998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1933998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934041 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_1934041 : Nat := 118140960795 + 1934041 * 2 ^ 59
def prefixEnd_1934041 : Nat := 4983230072969 + 3 ^ 40 * 1934041 * 2
def baseEnd_1934041 : Nat := 331030879500790929797671

theorem tailTrace_1934041 : CollatzResearch.WordTrace tailWord_1934041 prefixEnd_1934041 331030879500790929797671 := by
  unfold tailWord_1934041
  simp only [CollatzResearch.WordTrace]
  refine ⟨70540270386307239750753977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47026846924204826500502651 70540270386307239750753977)
  ·
    refine ⟨52905202789730429813065483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70540270386307239750753977 52905202789730429813065483)
    ·
      refine ⟨79357804184595644719598225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52905202789730429813065483 79357804184595644719598225)
      ·
        refine ⟨59518353138446733539698669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79357804184595644719598225 59518353138446733539698669)
        ·
          refine ⟨22319382426917525077387001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59518353138446733539698669 22319382426917525077387001)
          ·
            refine ⟨16739536820188143808040251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22319382426917525077387001 16739536820188143808040251)
            ·
              refine ⟨25109305230282215712060377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16739536820188143808040251 25109305230282215712060377)
              ·
                refine ⟨18831978922711661784045283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25109305230282215712060377 18831978922711661784045283)
                ·
                  refine ⟨28247968384067492676067925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18831978922711661784045283 28247968384067492676067925)
                  ·
                    refine ⟨331030879500790929797671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28247968384067492676067925 331030879500790929797671)
                    ·
                      rfl

theorem cell23_1934041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_1934041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934041 prefixEnd_1934041 := by exact prefixLift 1934041
  have htrace : WordTrace (prefixWord ++ tailWord_1934041) baseStart_1934041 baseEnd_1934041 := by
    simpa [prefixWord, tailWord_1934041, baseEnd_1934041] using wordTrace_append hprefix tailTrace_1934041
  have hstable : (prefixWord ++ tailWord_1934041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934041).length < 2 ^ (prefixWord ++ tailWord_1934041).sum := by decide
  have hdescent : baseEnd_1934041 < baseStart_1934041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934052 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_1934052 : Nat := 118140960795 + 1934052 * 2 ^ 59
def prefixEnd_1934052 : Nat := 4983230072969 + 3 ^ 40 * 1934052 * 2
def baseEnd_1934052 : Nat := 993098286789572246355463

theorem tailTrace_1934052 : CollatzResearch.WordTrace tailWord_1934052 prefixEnd_1934052 993098286789572246355463 := by
  unfold tailWord_1934052
  simp only [CollatzResearch.WordTrace]
  refine ⟨35270335794633694314702205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47027114392844925752936273 35270335794633694314702205)
  ·
    refine ⟨13226375922987635368013327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35270335794633694314702205 13226375922987635368013327)
    ·
      refine ⟨19839563884481453052019991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13226375922987635368013327 19839563884481453052019991)
      ·
        refine ⟨29759345826722179578029987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19839563884481453052019991 29759345826722179578029987)
        ·
          refine ⟨44639018740083269367044981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29759345826722179578029987 44639018740083269367044981)
          ·
            refine ⟨4184908006882806503160467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44639018740083269367044981 4184908006882806503160467)
            ·
              refine ⟨6277362010324209754740701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4184908006882806503160467 6277362010324209754740701)
              ·
                refine ⟨2354010753871578658027763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6277362010324209754740701 2354010753871578658027763)
                ·
                  refine ⟨3531016130807367987041645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354010753871578658027763 3531016130807367987041645)
                  ·
                    refine ⟨1324131049052762995140617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531016130807367987041645 1324131049052762995140617)
                    ·
                      refine ⟨993098286789572246355463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324131049052762995140617 993098286789572246355463)
                      ·
                        rfl

theorem cell23_1934052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_1934052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934052 prefixEnd_1934052 := by exact prefixLift 1934052
  have htrace : WordTrace (prefixWord ++ tailWord_1934052) baseStart_1934052 baseEnd_1934052 := by
    simpa [prefixWord, tailWord_1934052, baseEnd_1934052] using wordTrace_append hprefix tailTrace_1934052
  have hstable : (prefixWord ++ tailWord_1934052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934052).length < 2 ^ (prefixWord ++ tailWord_1934052).sum := by decide
  have hdescent : baseEnd_1934052 < baseStart_1934052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934088 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 7]
def baseStart_1934088 : Nat := 118140960795 + 1934088 * 2 ^ 59
def prefixEnd_1934088 : Nat := 4983230072969 + 3 ^ 40 * 1934088 * 2
def baseEnd_1934088 : Nat := 110346308010348233945033

theorem tailTrace_1934088 : CollatzResearch.WordTrace tailWord_1934088 prefixEnd_1934088 110346308010348233945033 := by
  unfold tailWord_1934088
  simp only [CollatzResearch.WordTrace]
  refine ⟨35270992308568483388857459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47027989744757977851809945 35270992308568483388857459)
  ·
    refine ⟨52906488462852725083286189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35270992308568483388857459 52906488462852725083286189)
    ·
      refine ⟨19839933173569771906232321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52906488462852725083286189 19839933173569771906232321)
      ·
        refine ⟨14879949880177328929674241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19839933173569771906232321 14879949880177328929674241)
        ·
          refine ⟨11159962410132996697255681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14879949880177328929674241 11159962410132996697255681)
          ·
            refine ⟨8369971807599747522941761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11159962410132996697255681 8369971807599747522941761)
            ·
              refine ⟨6277478855699810642206321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8369971807599747522941761 6277478855699810642206321)
              ·
                refine ⟨4708109141774857981654741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277478855699810642206321 4708109141774857981654741)
                ·
                  refine ⟨110346308010348233945033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4708109141774857981654741 110346308010348233945033)
                  ·
                    rfl

theorem cell23_1934088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_1934088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934088 prefixEnd_1934088 := by exact prefixLift 1934088
  have htrace : WordTrace (prefixWord ++ tailWord_1934088) baseStart_1934088 baseEnd_1934088 := by
    simpa [prefixWord, tailWord_1934088, baseEnd_1934088] using wordTrace_append hprefix tailTrace_1934088
  have hstable : (prefixWord ++ tailWord_1934088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934088).length < 2 ^ (prefixWord ++ tailWord_1934088).sum := by decide
  have hdescent : baseEnd_1934088 < baseStart_1934088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934172 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1934172 : Nat := 118140960795 + 1934172 * 2 ^ 59
def prefixEnd_1934172 : Nat := 4983230072969 + 3 ^ 40 * 1934172 * 2
def baseEnd_1934172 : Nat := 993159904468111776854911

theorem tailTrace_1934172 : CollatzResearch.WordTrace tailWord_1934172 prefixEnd_1934172 993159904468111776854911 := by
  unfold tailWord_1934172
  simp only [CollatzResearch.WordTrace]
  refine ⟨35272524174416324561886385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47030032232555099415848513 35272524174416324561886385)
  ·
    refine ⟨26454393130812243421414789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35272524174416324561886385 26454393130812243421414789)
    ·
      refine ⟨4960198712027295641515273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26454393130812243421414789 4960198712027295641515273)
      ·
        refine ⟨3720149034020471731136455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4960198712027295641515273 3720149034020471731136455)
        ·
          refine ⟨5580223551030707596704683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720149034020471731136455 5580223551030707596704683)
          ·
            refine ⟨8370335326546061395057025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580223551030707596704683 8370335326546061395057025)
            ·
              refine ⟨6277751494909546046292769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8370335326546061395057025 6277751494909546046292769)
              ·
                refine ⟨4708313621182159534719577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277751494909546046292769 4708313621182159534719577)
                ·
                  refine ⟨3531235215886619651039683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708313621182159534719577 3531235215886619651039683)
                  ·
                    refine ⟨5296852823829929476559525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3531235215886619651039683 5296852823829929476559525)
                    ·
                      refine ⟨993159904468111776854911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5296852823829929476559525 993159904468111776854911)
                      ·
                        rfl

theorem cell23_1934172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1934172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934172 prefixEnd_1934172 := by exact prefixLift 1934172
  have htrace : WordTrace (prefixWord ++ tailWord_1934172) baseStart_1934172 baseEnd_1934172 := by
    simpa [prefixWord, tailWord_1934172, baseEnd_1934172] using wordTrace_append hprefix tailTrace_1934172
  have hstable : (prefixWord ++ tailWord_1934172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934172).length < 2 ^ (prefixWord ++ tailWord_1934172).sum := by decide
  have hdescent : baseEnd_1934172 < baseStart_1934172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934175 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_1934175 : Nat := 118140960795 + 1934175 * 2 ^ 59
def prefixEnd_1934175 : Nat := 4983230072969 + 3 ^ 40 * 1934175 * 2
def baseEnd_1934175 : Nat := 993161444910075265117397

theorem tailTrace_1934175 : CollatzResearch.WordTrace tailWord_1934175 prefixEnd_1934175 993161444910075265117397 := by
  unfold tailWord_1934175
  simp only [CollatzResearch.WordTrace]
  refine ⟨70545157767821780636131979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47030105178547853757421319 70545157767821780636131979)
  ·
    refine ⟨105817736651732670954197969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70545157767821780636131979 105817736651732670954197969)
    ·
      refine ⟨79363302488799503215648477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105817736651732670954197969 79363302488799503215648477)
      ·
        refine ⟨29761238433299813705868179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79363302488799503215648477 29761238433299813705868179)
        ·
          refine ⟨44641857649949720558802269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29761238433299813705868179 44641857649949720558802269)
          ·
            refine ⟨16740696618731145209550851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44641857649949720558802269 16740696618731145209550851)
            ·
              refine ⟨25111044928096717814326277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16740696618731145209550851 25111044928096717814326277)
              ·
                refine ⟨4708320924018134590186177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25111044928096717814326277 4708320924018134590186177)
                ·
                  refine ⟨3531240693013600942639633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708320924018134590186177 3531240693013600942639633)
                  ·
                    refine ⟨2648430519760200706979725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3531240693013600942639633 2648430519760200706979725)
                    ·
                      refine ⟨993161444910075265117397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2648430519760200706979725 993161444910075265117397)
                      ·
                        rfl

theorem cell23_1934175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_1934175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934175 prefixEnd_1934175 := by exact prefixLift 1934175
  have htrace : WordTrace (prefixWord ++ tailWord_1934175) baseStart_1934175 baseEnd_1934175 := by
    simpa [prefixWord, tailWord_1934175, baseEnd_1934175] using wordTrace_append hprefix tailTrace_1934175
  have hstable : (prefixWord ++ tailWord_1934175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934175).length < 2 ^ (prefixWord ++ tailWord_1934175).sum := by decide
  have hdescent : baseEnd_1934175 < baseStart_1934175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934206 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1934206 : Nat := 118140960795 + 1934206 * 2 ^ 59
def prefixEnd_1934206 : Nat := 4983230072969 + 3 ^ 40 * 1934206 * 2
def baseEnd_1934206 : Nat := 993177362810364643829755

theorem tailTrace_1934206 : CollatzResearch.WordTrace tailWord_1934206 prefixEnd_1934206 993177362810364643829755 := by
  unfold tailWord_1934206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818286053838684116313809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47030858953806315287006981 8818286053838684116313809)
  ·
    refine ⟨6613714540379013087235357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8818286053838684116313809 6613714540379013087235357)
    ·
      refine ⟨2480142952642129907713259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6613714540379013087235357 2480142952642129907713259)
      ·
        refine ⟨3720214428963194861569889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480142952642129907713259 3720214428963194861569889)
        ·
          refine ⟨2790160821722396146177417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3720214428963194861569889 2790160821722396146177417)
          ·
            refine ⟨2092620616291797109633063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2790160821722396146177417 2092620616291797109633063)
            ·
              refine ⟨3138930924437695664449595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092620616291797109633063 3138930924437695664449595)
              ·
                refine ⟨4708396386656543496674393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138930924437695664449595 4708396386656543496674393)
                ·
                  refine ⟨3531297289992407622505795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4708396386656543496674393 3531297289992407622505795)
                  ·
                    refine ⟨5296945934988611433758693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3531297289992407622505795 5296945934988611433758693)
                    ·
                      refine ⟨993177362810364643829755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5296945934988611433758693 993177362810364643829755)
                      ·
                        rfl

theorem cell23_1934206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1934206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934206 prefixEnd_1934206 := by exact prefixLift 1934206
  have htrace : WordTrace (prefixWord ++ tailWord_1934206) baseStart_1934206 baseEnd_1934206 := by
    simpa [prefixWord, tailWord_1934206, baseEnd_1934206] using wordTrace_append hprefix tailTrace_1934206
  have hstable : (prefixWord ++ tailWord_1934206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934206).length < 2 ^ (prefixWord ++ tailWord_1934206).sum := by decide
  have hdescent : baseEnd_1934206 < baseStart_1934206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934239 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1934239 : Nat := 118140960795 + 1934239 * 2 ^ 59
def prefixEnd_1934239 : Nat := 4983230072969 + 3 ^ 40 * 1934239 * 2
def baseEnd_1934239 : Nat := 993194307671963014717103

theorem tailTrace_1934239 : CollatzResearch.WordTrace tailWord_1934239 prefixEnd_1934239 993194307671963014717103 := by
  unfold tailWord_1934239
  simp only [CollatzResearch.WordTrace]
  refine ⟨70547492039589919566461771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47031661359726613044307847 70547492039589919566461771)
  ·
    refine ⟨105821238059384879349692657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70547492039589919566461771 105821238059384879349692657)
    ·
      refine ⟨79365928544538659512269493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105821238059384879349692657 79365928544538659512269493)
      ·
        refine ⟨7440555801050499329275265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79365928544538659512269493 7440555801050499329275265)
        ·
          refine ⟨5580416850787874496956449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7440555801050499329275265 5580416850787874496956449)
          ·
            refine ⟨4185312638090905872717337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580416850787874496956449 4185312638090905872717337)
            ·
              refine ⟨3138984478568179404538003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185312638090905872717337 3138984478568179404538003)
              ·
                refine ⟨4708476717852269106807005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3138984478568179404538003 4708476717852269106807005)
                ·
                  refine ⟨1765678769194600915052627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4708476717852269106807005 1765678769194600915052627)
                  ·
                    refine ⟨2648518153791901372578941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1765678769194600915052627 2648518153791901372578941)
                    ·
                      refine ⟨993194307671963014717103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2648518153791901372578941 993194307671963014717103)
                      ·
                        rfl

theorem cell23_1934239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1934239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934239 prefixEnd_1934239 := by exact prefixLift 1934239
  have htrace : WordTrace (prefixWord ++ tailWord_1934239) baseStart_1934239 baseEnd_1934239 := by
    simpa [prefixWord, tailWord_1934239, baseEnd_1934239] using wordTrace_append hprefix tailTrace_1934239
  have hstable : (prefixWord ++ tailWord_1934239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934239).length < 2 ^ (prefixWord ++ tailWord_1934239).sum := by decide
  have hdescent : baseEnd_1934239 < baseStart_1934239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934295 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1934295 : Nat := 118140960795 + 1934295 * 2 ^ 59
def prefixEnd_1934295 : Nat := 4983230072969 + 3 ^ 40 * 1934295 * 2
def baseEnd_1934295 : Nat := 993223062588614795616845

theorem tailTrace_1934295 : CollatzResearch.WordTrace tailWord_1934295 prefixEnd_1934295 993223062588614795616845 := by
  unfold tailWord_1934295
  simp only [CollatzResearch.WordTrace]
  refine ⟨70549534527387041130500339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47033023018258027420333559 70549534527387041130500339)
  ·
    refine ⟨105824301791080561695750509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70549534527387041130500339 105824301791080561695750509)
    ·
      refine ⟨39684113171655210635906441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105824301791080561695750509 39684113171655210635906441)
      ·
        refine ⟨29763084878741407976929831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39684113171655210635906441 29763084878741407976929831)
        ·
          refine ⟨44644627318112111965394747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29763084878741407976929831 44644627318112111965394747)
          ·
            refine ⟨66966940977168167948092121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44644627318112111965394747 66966940977168167948092121)
            ·
              refine ⟨50225205732876125961069091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66966940977168167948092121 50225205732876125961069091)
              ·
                refine ⟨75337808599314188941603637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50225205732876125961069091 75337808599314188941603637)
                ·
                  refine ⟨7062919556185705213275341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75337808599314188941603637 7062919556185705213275341)
                  ·
                    refine ⟨2648594833569639454978253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7062919556185705213275341 2648594833569639454978253)
                    ·
                      refine ⟨993223062588614795616845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2648594833569639454978253 993223062588614795616845)
                      ·
                        rfl

theorem cell23_1934295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1934295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934295 prefixEnd_1934295 := by exact prefixLift 1934295
  have htrace : WordTrace (prefixWord ++ tailWord_1934295) baseStart_1934295 baseEnd_1934295 := by
    simpa [prefixWord, tailWord_1934295, baseEnd_1934295] using wordTrace_append hprefix tailTrace_1934295
  have hstable : (prefixWord ++ tailWord_1934295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934295).length < 2 ^ (prefixWord ++ tailWord_1934295).sum := by decide
  have hdescent : baseEnd_1934295 < baseStart_1934295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934296 : List Nat := [2, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_1934296 : Nat := 118140960795 + 1934296 * 2 ^ 59
def prefixEnd_1934296 : Nat := 4983230072969 + 3 ^ 40 * 1934296 * 2
def baseEnd_1934296 : Nat := 993223576069269291704341

theorem tailTrace_1934296 : CollatzResearch.WordTrace tailWord_1934296 prefixEnd_1934296 993223576069269291704341 := by
  unfold tailWord_1934296
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274785500191709150643371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47033047333588945534191161 35274785500191709150643371)
  ·
    refine ⟨52912178250287563725965057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35274785500191709150643371 52912178250287563725965057)
    ·
      refine ⟨39684133687715672794473793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52912178250287563725965057 39684133687715672794473793)
      ·
        refine ⟨29763100265786754595855345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39684133687715672794473793 29763100265786754595855345)
        ·
          refine ⟨22322325199340065946891509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29763100265786754595855345 22322325199340065946891509)
          ·
            refine ⟨2092717987438131182521079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22322325199340065946891509 2092717987438131182521079)
            ·
              refine ⟨3139076981157196773781619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2092717987438131182521079 3139076981157196773781619)
              ·
                refine ⟨4708615471735795160672429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139076981157196773781619 4708615471735795160672429)
                ·
                  refine ⟨1765730801900923185252161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4708615471735795160672429 1765730801900923185252161)
                  ·
                    refine ⟨1324298101425692388939121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1765730801900923185252161 1324298101425692388939121)
                    ·
                      refine ⟨993223576069269291704341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324298101425692388939121 993223576069269291704341)
                      ·
                        rfl

theorem cell23_1934296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_1934296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934296 prefixEnd_1934296 := by exact prefixLift 1934296
  have htrace : WordTrace (prefixWord ++ tailWord_1934296) baseStart_1934296 baseEnd_1934296 := by
    simpa [prefixWord, tailWord_1934296, baseEnd_1934296] using wordTrace_append hprefix tailTrace_1934296
  have hstable : (prefixWord ++ tailWord_1934296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934296).length < 2 ^ (prefixWord ++ tailWord_1934296).sum := by decide
  have hdescent : baseEnd_1934296 < baseStart_1934296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934306 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_1934306 : Nat := 118140960795 + 1934306 * 2 ^ 59
def prefixEnd_1934306 : Nat := 4983230072969 + 3 ^ 40 * 1934306 * 2
def baseEnd_1934306 : Nat := 331076236958604750859765

theorem tailTrace_1934306 : CollatzResearch.WordTrace tailWord_1934306 prefixEnd_1934306 331076236958604750859765 := by
  unfold tailWord_1934306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637483932586797502287693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47033290486898126672767181 17637483932586797502287693)
  ·
    refine ⟨6614056474720049063357885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17637483932586797502287693 6614056474720049063357885)
    ·
      refine ⟨2480271178020018398759207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6614056474720049063357885 2480271178020018398759207)
      ·
        refine ⟨3720406767030027598138811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480271178020018398759207 3720406767030027598138811)
        ·
          refine ⟨5580610150545041397208217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3720406767030027598138811 5580610150545041397208217)
          ·
            refine ⟨4185457612908781047906163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580610150545041397208217 4185457612908781047906163)
            ·
              refine ⟨6278186419363171571859245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4185457612908781047906163 6278186419363171571859245)
              ·
                refine ⟨2354319907261189339447217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6278186419363171571859245 2354319907261189339447217)
                ·
                  refine ⟨1765739930445892004585413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354319907261189339447217 1765739930445892004585413)
                  ·
                    refine ⟨331076236958604750859765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1765739930445892004585413 331076236958604750859765)
                    ·
                      rfl

theorem cell23_1934306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_1934306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934306 prefixEnd_1934306 := by exact prefixLift 1934306
  have htrace : WordTrace (prefixWord ++ tailWord_1934306) baseStart_1934306 baseEnd_1934306 := by
    simpa [prefixWord, tailWord_1934306, baseEnd_1934306] using wordTrace_append hprefix tailTrace_1934306
  have hstable : (prefixWord ++ tailWord_1934306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934306).length < 2 ^ (prefixWord ++ tailWord_1934306).sum := by decide
  have hdescent : baseEnd_1934306 < baseStart_1934306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934346 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1934346 : Nat := 118140960795 + 1934346 * 2 ^ 59
def prefixEnd_1934346 : Nat := 4983230072969 + 3 ^ 40 * 1934346 * 2
def baseEnd_1934346 : Nat := 993249250101994096079111

theorem tailTrace_1934346 : CollatzResearch.WordTrace tailWord_1934346 prefixEnd_1934346 993249250101994096079111 := by
  unfold tailWord_1934346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637848662550569210151723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47034263100134851227071261 17637848662550569210151723)
  ·
    refine ⟨26456772993825853815227585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637848662550569210151723 26456772993825853815227585)
    ·
      refine ⟨19842579745369390361420689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26456772993825853815227585 19842579745369390361420689)
      ·
        refine ⟨14881934809027042771065517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19842579745369390361420689 14881934809027042771065517)
        ·
          refine ⟨5580725553385141039149569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14881934809027042771065517 5580725553385141039149569)
          ·
            refine ⟨4185544165038855779362177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5580725553385141039149569 4185544165038855779362177)
            ·
              refine ⟨3139158123779141834521633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4185544165038855779362177 3139158123779141834521633)
              ·
                refine ⟨2354368592834356375891225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139158123779141834521633 2354368592834356375891225)
                ·
                  refine ⟨1765776444625767281918419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354368592834356375891225 1765776444625767281918419)
                  ·
                    refine ⟨2648664666938650922877629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1765776444625767281918419 2648664666938650922877629)
                    ·
                      refine ⟨993249250101994096079111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2648664666938650922877629 993249250101994096079111)
                      ·
                        rfl

theorem cell23_1934346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1934346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934346 prefixEnd_1934346 := by exact prefixLift 1934346
  have htrace : WordTrace (prefixWord ++ tailWord_1934346) baseStart_1934346 baseEnd_1934346 := by
    simpa [prefixWord, tailWord_1934346, baseEnd_1934346] using wordTrace_append hprefix tailTrace_1934346
  have hstable : (prefixWord ++ tailWord_1934346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934346).length < 2 ^ (prefixWord ++ tailWord_1934346).sum := by decide
  have hdescent : baseEnd_1934346 < baseStart_1934346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934369 : List Nat := [1, 2, 3, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_1934369 : Nat := 118140960795 + 1934369 * 2 ^ 59
def prefixEnd_1934369 : Nat := 4983230072969 + 3 ^ 40 * 1934369 * 2
def baseEnd_1934369 : Nat := 993261060157047506091505

theorem tailTrace_1934369 : CollatzResearch.WordTrace tailWord_1934369 prefixEnd_1934369 993261060157047506091505 := by
  unfold tailWord_1934369
  simp only [CollatzResearch.WordTrace]
  refine ⟨70552233529118951768694161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47034822352745967845796107 70552233529118951768694161)
  ·
    refine ⟨52914175146839213826520621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70552233529118951768694161 52914175146839213826520621)
    ·
      refine ⟨19842815680064705184945233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52914175146839213826520621 19842815680064705184945233)
      ·
        refine ⟨14882111760048528888708925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19842815680064705184945233 14882111760048528888708925)
        ·
          refine ⟨5580791910018198333265847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14882111760048528888708925 5580791910018198333265847)
          ·
            refine ⟨8371187865027297499898771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580791910018198333265847 8371187865027297499898771)
            ·
              refine ⟨12556781797540946249848157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371187865027297499898771 12556781797540946249848157)
              ·
                refine ⟨4708793174077854843693059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12556781797540946249848157 4708793174077854843693059)
                ·
                  refine ⟨7063189761116782265539589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708793174077854843693059 7063189761116782265539589)
                  ·
                    refine ⟨1324348080209396674788673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7063189761116782265539589 1324348080209396674788673)
                    ·
                      refine ⟨993261060157047506091505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324348080209396674788673 993261060157047506091505)
                      ·
                        rfl

theorem cell23_1934369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_1934369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934369 prefixEnd_1934369 := by exact prefixLift 1934369
  have htrace : WordTrace (prefixWord ++ tailWord_1934369) baseStart_1934369 baseEnd_1934369 := by
    simpa [prefixWord, tailWord_1934369, baseEnd_1934369] using wordTrace_append hprefix tailTrace_1934369
  have hstable : (prefixWord ++ tailWord_1934369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934369).length < 2 ^ (prefixWord ++ tailWord_1934369).sum := by decide
  have hdescent : baseEnd_1934369 < baseStart_1934369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934382 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1934382 : Nat := 118140960795 + 1934382 * 2 ^ 59
def prefixEnd_1934382 : Nat := 4983230072969 + 3 ^ 40 * 1934382 * 2
def baseEnd_1934382 : Nat := 993267735405555955228945

theorem tailTrace_1934382 : CollatzResearch.WordTrace tailWord_1934382 prefixEnd_1934382 993267735405555955228945 := by
  unfold tailWord_1934382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8819088459758981873614675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47035138452047903325944933 8819088459758981873614675)
  ·
    refine ⟨13228632689638472810422013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8819088459758981873614675 13228632689638472810422013)
    ·
      refine ⟨4960737258614427303908255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13228632689638472810422013 4960737258614427303908255)
      ·
        refine ⟨7441105887921640955862383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960737258614427303908255 7441105887921640955862383)
        ·
          refine ⟨11161658831882461433793575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441105887921640955862383 11161658831882461433793575)
          ·
            refine ⟨16742488247823692150690363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161658831882461433793575 16742488247823692150690363)
            ·
              refine ⟨25113732371735538226035545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16742488247823692150690363 25113732371735538226035545)
              ·
                refine ⟨18835299278801653669526659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25113732371735538226035545 18835299278801653669526659)
                ·
                  refine ⟨28252948918202480504289989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18835299278801653669526659 28252948918202480504289989)
                  ·
                    refine ⟨5297427922162965094554373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28252948918202480504289989 5297427922162965094554373)
                    ·
                      refine ⟨993267735405555955228945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5297427922162965094554373 993267735405555955228945)
                      ·
                        rfl

theorem cell23_1934382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1934382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934382 prefixEnd_1934382 := by exact prefixLift 1934382
  have htrace : WordTrace (prefixWord ++ tailWord_1934382) baseStart_1934382 baseEnd_1934382 := by
    simpa [prefixWord, tailWord_1934382, baseEnd_1934382] using wordTrace_append hprefix tailTrace_1934382
  have hstable : (prefixWord ++ tailWord_1934382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934382).length < 2 ^ (prefixWord ++ tailWord_1934382).sum := by decide
  have hdescent : baseEnd_1934382 < baseStart_1934382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934390 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_1934390 : Nat := 118140960795 + 1934390 * 2 ^ 59
def prefixEnd_1934390 : Nat := 4983230072969 + 3 ^ 40 * 1934390 * 2
def baseEnd_1934390 : Nat := 993271843250791923928909

theorem tailTrace_1934390 : CollatzResearch.WordTrace tailWord_1934390 prefixEnd_1934390 993271843250791923928909 := by
  unfold tailWord_1934390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4409562466377679522200539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47035332974695248236805749 4409562466377679522200539)
  ·
    refine ⟨6614343699566519283300809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4409562466377679522200539 6614343699566519283300809)
    ·
      refine ⟨4960757774674889462475607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6614343699566519283300809 4960757774674889462475607)
      ·
        refine ⟨7441136662012334193713411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4960757774674889462475607 7441136662012334193713411)
        ·
          refine ⟨11161704993018501290570117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441136662012334193713411 11161704993018501290570117)
          ·
            refine ⟨2092819686190968991981897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11161704993018501290570117 2092819686190968991981897)
            ·
              refine ⟨1569614764643226743986423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2092819686190968991981897 1569614764643226743986423)
              ·
                refine ⟨2354422146964840115979635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569614764643226743986423 2354422146964840115979635)
                ·
                  refine ⟨3531633220447260173969453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354422146964840115979635 3531633220447260173969453)
                  ·
                    refine ⟨1324362457667722565238545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3531633220447260173969453 1324362457667722565238545)
                    ·
                      refine ⟨993271843250791923928909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324362457667722565238545 993271843250791923928909)
                      ·
                        rfl

theorem cell23_1934390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_1934390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934390 prefixEnd_1934390 := by exact prefixLift 1934390
  have htrace : WordTrace (prefixWord ++ tailWord_1934390) baseStart_1934390 baseEnd_1934390 := by
    simpa [prefixWord, tailWord_1934390, baseEnd_1934390] using wordTrace_append hprefix tailTrace_1934390
  have hstable : (prefixWord ++ tailWord_1934390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934390).length < 2 ^ (prefixWord ++ tailWord_1934390).sum := by decide
  have hdescent : baseEnd_1934390 < baseStart_1934390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934435 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 10]
def baseStart_1934435 : Nat := 118140960795 + 1934435 * 2 ^ 59
def prefixEnd_1934435 : Nat := 4983230072969 + 3 ^ 40 * 1934435 * 2
def baseEnd_1934435 : Nat := 331098316626748082622067

theorem tailTrace_1934435 : CollatzResearch.WordTrace tailWord_1934435 prefixEnd_1934435 331098316626748082622067 := by
  unfold tailWord_1934435
  simp only [CollatzResearch.WordTrace]
  refine ⟨70554640746879845040596759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47036427164586563360397839 70554640746879845040596759)
  ·
    refine ⟨105831961120319767560895139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70554640746879845040596759 105831961120319767560895139)
    ·
      refine ⟨158747941680479651341342709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105831961120319767560895139 158747941680479651341342709)
      ·
        refine ⟨14882619532544967313250879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158747941680479651341342709 14882619532544967313250879)
        ·
          refine ⟨22323929298817450969876319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14882619532544967313250879 22323929298817450969876319)
          ·
            refine ⟨33485893948226176454814479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22323929298817450969876319 33485893948226176454814479)
            ·
              refine ⟨50228840922339264682221719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33485893948226176454814479 50228840922339264682221719)
              ·
                refine ⟨75343261383508897023332579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50228840922339264682221719 75343261383508897023332579)
                ·
                  refine ⟨113014892075263345534998869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75343261383508897023332579 113014892075263345534998869)
                  ·
                    refine ⟨331098316626748082622067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 113014892075263345534998869 331098316626748082622067)
                    ·
                      rfl

theorem cell23_1934435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_1934435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934435 prefixEnd_1934435 := by exact prefixLift 1934435
  have htrace : WordTrace (prefixWord ++ tailWord_1934435) baseStart_1934435 baseEnd_1934435 := by
    simpa [prefixWord, tailWord_1934435, baseEnd_1934435] using wordTrace_append hprefix tailTrace_1934435
  have hstable : (prefixWord ++ tailWord_1934435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934435).length < 2 ^ (prefixWord ++ tailWord_1934435).sum := by decide
  have hdescent : baseEnd_1934435 < baseStart_1934435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934572 : List Nat := [2, 2, 1, 1, 2, 5, 10]
def baseStart_1934572 : Nat := 118140960795 + 1934572 * 2 ^ 59
def prefixEnd_1934572 : Nat := 4983230072969 + 3 ^ 40 * 1934572 * 2
def baseEnd_1934572 : Nat := 12263769095430990269791

theorem tailTrace_1934572 : CollatzResearch.WordTrace tailWord_1934572 prefixEnd_1934572 12263769095430990269791 := by
  unfold tailWord_1934572
  simp only [CollatzResearch.WordTrace]
  refine ⟨35279818773691758719166985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47039758364922344958889313 35279818773691758719166985)
  ·
    refine ⟨26459864080268819039375239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35279818773691758719166985 26459864080268819039375239)
    ·
      refine ⟨39689796120403228559062859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26459864080268819039375239 39689796120403228559062859)
      ·
        refine ⟨59534694180604842838594289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39689796120403228559062859 59534694180604842838594289)
        ·
          refine ⟨44651020635453632128945717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59534694180604842838594289 44651020635453632128945717)
          ·
            refine ⟨4186033184573778012088661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44651020635453632128945717 4186033184573778012088661)
            ·
              refine ⟨12263769095430990269791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4186033184573778012088661 12263769095430990269791)
              ·
                rfl

theorem cell23_1934572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 10].length) (baseStart_1934572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934572 prefixEnd_1934572 := by exact prefixLift 1934572
  have htrace : WordTrace (prefixWord ++ tailWord_1934572) baseStart_1934572 baseEnd_1934572 := by
    simpa [prefixWord, tailWord_1934572, baseEnd_1934572] using wordTrace_append hprefix tailTrace_1934572
  have hstable : (prefixWord ++ tailWord_1934572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934572).length < 2 ^ (prefixWord ++ tailWord_1934572).sum := by decide
  have hdescent : baseEnd_1934572 < baseStart_1934572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934593 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 2, 4]
def baseStart_1934593 : Nat := 118140960795 + 1934593 * 2 ^ 59
def prefixEnd_1934593 : Nat := 4983230072969 + 3 ^ 40 * 1934593 * 2
def baseEnd_1934593 : Nat := 331125359941218209896825

theorem tailTrace_1934593 : CollatzResearch.WordTrace tailWord_1934593 prefixEnd_1934593 331125359941218209896825 := by
  unfold tailWord_1934593
  simp only [CollatzResearch.WordTrace]
  refine ⟨70560403480307438024848433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47040268986871625349898955 70560403480307438024848433)
  ·
    refine ⟨52920302610230578518636325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70560403480307438024848433 52920302610230578518636325)
    ·
      refine ⟨9922556739418233472244311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52920302610230578518636325 9922556739418233472244311)
      ·
        refine ⟨14883835109127350208366467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9922556739418233472244311 14883835109127350208366467)
        ·
          refine ⟨22325752663691025312549701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883835109127350208366467 22325752663691025312549701)
          ·
            refine ⟨4186078624442067246103069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22325752663691025312549701 4186078624442067246103069)
            ·
              refine ⟨1569779484165775217288651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4186078624442067246103069 1569779484165775217288651)
              ·
                refine ⟨2354669226248662825932977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1569779484165775217288651 2354669226248662825932977)
                ·
                  refine ⟨1766001919686497119449733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2354669226248662825932977 1766001919686497119449733)
                  ·
                    refine ⟨331125359941218209896825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766001919686497119449733 331125359941218209896825)
                    ·
                      rfl

theorem cell23_1934593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_1934593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934593 prefixEnd_1934593 := by exact prefixLift 1934593
  have htrace : WordTrace (prefixWord ++ tailWord_1934593) baseStart_1934593 baseEnd_1934593 := by
    simpa [prefixWord, tailWord_1934593, baseEnd_1934593] using wordTrace_append hprefix tailTrace_1934593
  have hstable : (prefixWord ++ tailWord_1934593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934593).length < 2 ^ (prefixWord ++ tailWord_1934593).sum := by decide
  have hdescent : baseEnd_1934593 < baseStart_1934593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934596 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1934596 : Nat := 118140960795 + 1934596 * 2 ^ 59
def prefixEnd_1934596 : Nat := 4983230072969 + 3 ^ 40 * 1934596 * 2
def baseEnd_1934596 : Nat := 993377620265618117952961

theorem tailTrace_1934596 : CollatzResearch.WordTrace tailWord_1934596 prefixEnd_1934596 993377620265618117952961 := by
  unfold tailWord_1934596
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280256449648284768603821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47040341932864379691471761 35280256449648284768603821)
  ·
    refine ⟨13230096168618106788226433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35280256449648284768603821 13230096168618106788226433)
    ·
      refine ⟨9922572126463580091169825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13230096168618106788226433 9922572126463580091169825)
      ·
        refine ⟨7441929094847685068377369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9922572126463580091169825 7441929094847685068377369)
        ·
          refine ⟨5581446821135763801283027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441929094847685068377369 5581446821135763801283027)
          ·
            refine ⟨8372170231703645701924541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581446821135763801283027 8372170231703645701924541)
            ·
              refine ⟨3139563836888867138221703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8372170231703645701924541 3139563836888867138221703)
              ·
                refine ⟨4709345755333300707332555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139563836888867138221703 4709345755333300707332555)
                ·
                  refine ⟨7064018632999951060998833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709345755333300707332555 7064018632999951060998833)
                  ·
                    refine ⟨5298013974749963295749125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7064018632999951060998833 5298013974749963295749125)
                    ·
                      refine ⟨993377620265618117952961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5298013974749963295749125 993377620265618117952961)
                      ·
                        rfl

theorem cell23_1934596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1934596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934596 prefixEnd_1934596 := by exact prefixLift 1934596
  have htrace : WordTrace (prefixWord ++ tailWord_1934596) baseStart_1934596 baseEnd_1934596 := by
    simpa [prefixWord, tailWord_1934596, baseEnd_1934596] using wordTrace_append hprefix tailTrace_1934596
  have hstable : (prefixWord ++ tailWord_1934596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934596).length < 2 ^ (prefixWord ++ tailWord_1934596).sum := by decide
  have hdescent : baseEnd_1934596 < baseStart_1934596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934606 : List Nat := [4, 1, 1, 2, 1, 5, 2, 7]
def baseStart_1934606 : Nat := 118140960795 + 1934606 * 2 ^ 59
def prefixEnd_1934606 : Nat := 4983230072969 + 3 ^ 40 * 1934606 * 2
def baseEnd_1934606 : Nat := 36791953891561595512145

theorem tailTrace_1934606 : CollatzResearch.WordTrace tailWord_1934606 prefixEnd_1934606 36791953891561595512145 := by
  unfold tailWord_1934606
  simp only [CollatzResearch.WordTrace]
  refine ⟨8820109703657542655633959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47040585086173560830047781 8820109703657542655633959)
  ·
    refine ⟨13230164555486313983450939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8820109703657542655633959 13230164555486313983450939)
    ·
      refine ⟨19845246833229470975176409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230164555486313983450939 19845246833229470975176409)
      ·
        refine ⟨14883935124922103231382307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19845246833229470975176409 14883935124922103231382307)
        ·
          refine ⟨22325902687383154847073461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14883935124922103231382307 22325902687383154847073461)
          ·
            refine ⟨2093053376942170766913137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22325902687383154847073461 2093053376942170766913137)
            ·
              refine ⟨1569790032706628075184853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093053376942170766913137 1569790032706628075184853)
              ·
                refine ⟨36791953891561595512145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1569790032706628075184853 36791953891561595512145)
                ·
                  rfl

theorem cell23_1934606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_1934606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934606 prefixEnd_1934606 := by exact prefixLift 1934606
  have htrace : WordTrace (prefixWord ++ tailWord_1934606) baseStart_1934606 baseEnd_1934606 := by
    simpa [prefixWord, tailWord_1934606, baseEnd_1934606] using wordTrace_append hprefix tailTrace_1934606
  have hstable : (prefixWord ++ tailWord_1934606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934606).length < 2 ^ (prefixWord ++ tailWord_1934606).sum := by decide
  have hdescent : baseEnd_1934606 < baseStart_1934606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934616 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1934616 : Nat := 118140960795 + 1934616 * 2 ^ 59
def prefixEnd_1934616 : Nat := 4983230072969 + 3 ^ 40 * 1934616 * 2
def baseEnd_1934616 : Nat := 993387889878708039702869

theorem tailTrace_1934616 : CollatzResearch.WordTrace tailWord_1934616 prefixEnd_1934616 993387889878708039702869 := by
  unfold tailWord_1934616
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280621179612056476467851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47040828239482741968623801 35280621179612056476467851)
  ·
    refine ⟨52920931769418084714701777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35280621179612056476467851 52920931769418084714701777)
    ·
      refine ⟨39690698827063563536026333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52920931769418084714701777 39690698827063563536026333)
      ·
        refine ⟨14884012060148836326009875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39690698827063563536026333 14884012060148836326009875)
        ·
          refine ⟨22326018090223254489014813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14884012060148836326009875 22326018090223254489014813)
          ·
            refine ⟨8372256783833720433380555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22326018090223254489014813 8372256783833720433380555)
            ·
              refine ⟨12558385175750580650070833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372256783833720433380555 12558385175750580650070833)
              ·
                refine ⟨9418788881812935487553125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12558385175750580650070833 9418788881812935487553125)
                ·
                  refine ⟨1766022915339925403916211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9418788881812935487553125 1766022915339925403916211)
                  ·
                    refine ⟨2649034373009888105874317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1766022915339925403916211 2649034373009888105874317)
                    ·
                      refine ⟨993387889878708039702869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2649034373009888105874317 993387889878708039702869)
                      ·
                        rfl

theorem cell23_1934616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1934616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934616 prefixEnd_1934616 := by exact prefixLift 1934616
  have htrace : WordTrace (prefixWord ++ tailWord_1934616) baseStart_1934616 baseEnd_1934616 := by
    simpa [prefixWord, tailWord_1934616, baseEnd_1934616] using wordTrace_append hprefix tailTrace_1934616
  have hstable : (prefixWord ++ tailWord_1934616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934616).length < 2 ^ (prefixWord ++ tailWord_1934616).sum := by decide
  have hdescent : baseEnd_1934616 < baseStart_1934616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934634 : List Nat := [3, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1934634 : Nat := 118140960795 + 1934634 * 2 ^ 59
def prefixEnd_1934634 : Nat := 4983230072969 + 3 ^ 40 * 1934634 * 2
def baseEnd_1934634 : Nat := 993397132530488969277787

theorem tailTrace_1934634 : CollatzResearch.WordTrace tailWord_1934634 prefixEnd_1934634 993397132530488969277787 := by
  unfold tailWord_1934634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17640474718289725506772739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47041265915439268018060637 17640474718289725506772739)
  ·
    refine ⟨26460712077434588260159109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17640474718289725506772739 26460712077434588260159109)
    ·
      refine ⟨4961383514518985298779833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26460712077434588260159109 4961383514518985298779833)
      ·
        refine ⟨3721037635889238974084875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4961383514518985298779833 3721037635889238974084875)
        ·
          refine ⟨5581556453833858461127313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721037635889238974084875 5581556453833858461127313)
          ·
            refine ⟨4186167340375393845845485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5581556453833858461127313 4186167340375393845845485)
            ·
              refine ⟨1569812752640772692192057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4186167340375393845845485 1569812752640772692192057)
              ·
                refine ⟨1177359564480579519144043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569812752640772692192057 1177359564480579519144043)
                ·
                  refine ⟨1766039346720869278716065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177359564480579519144043 1766039346720869278716065)
                  ·
                    refine ⟨1324529510040651959037049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766039346720869278716065 1324529510040651959037049)
                    ·
                      refine ⟨993397132530488969277787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324529510040651959037049 993397132530488969277787)
                      ·
                        rfl

theorem cell23_1934634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1934634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934634 prefixEnd_1934634 := by exact prefixLift 1934634
  have htrace : WordTrace (prefixWord ++ tailWord_1934634) baseStart_1934634 baseEnd_1934634 := by
    simpa [prefixWord, tailWord_1934634, baseEnd_1934634] using wordTrace_append hprefix tailTrace_1934634
  have hstable : (prefixWord ++ tailWord_1934634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934634).length < 2 ^ (prefixWord ++ tailWord_1934634).sum := by decide
  have hdescent : baseEnd_1934634 < baseStart_1934634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934656 : List Nat := [2, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2]
def baseStart_1934656 : Nat := 118140960795 + 1934656 * 2 ^ 59
def prefixEnd_1934656 : Nat := 4983230072969 + 3 ^ 40 * 1934656 * 2
def baseEnd_1934656 : Nat := 993408429104887883202685

theorem tailTrace_1934656 : CollatzResearch.WordTrace tailWord_1934656 prefixEnd_1934656 993408429104887883202685 := by
  unfold tailWord_1934656
  simp only [CollatzResearch.WordTrace]
  refine ⟨35281350639539599892195911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47041800852719466522927881 35281350639539599892195911)
  ·
    refine ⟨52922025959309399838293867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35281350639539599892195911 52922025959309399838293867)
    ·
      refine ⟨79383038938964099757440801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52922025959309399838293867 79383038938964099757440801)
      ·
        refine ⟨59537279204223074818080601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79383038938964099757440801 59537279204223074818080601)
        ·
          refine ⟨44652959403167306113560451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59537279204223074818080601 44652959403167306113560451)
          ·
            refine ⟨66979439104750959170340677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44652959403167306113560451 66979439104750959170340677)
            ·
              refine ⟨12558644832140804844438877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66979439104750959170340677 12558644832140804844438877)
              ·
                refine ⟨4709491812052801816664579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12558644832140804844438877 4709491812052801816664579)
                ·
                  refine ⟨7064237718079202724996869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709491812052801816664579 7064237718079202724996869)
                  ·
                    refine ⟨1324544572139850510936913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7064237718079202724996869 1324544572139850510936913)
                    ·
                      refine ⟨993408429104887883202685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324544572139850510936913 993408429104887883202685)
                      ·
                        rfl

theorem cell23_1934656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_1934656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934656 prefixEnd_1934656 := by exact prefixLift 1934656
  have htrace : WordTrace (prefixWord ++ tailWord_1934656) baseStart_1934656 baseEnd_1934656 := by
    simpa [prefixWord, tailWord_1934656, baseEnd_1934656] using wordTrace_append hprefix tailTrace_1934656
  have hstable : (prefixWord ++ tailWord_1934656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934656).length < 2 ^ (prefixWord ++ tailWord_1934656).sum := by decide
  have hdescent : baseEnd_1934656 < baseStart_1934656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934660 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_1934660 : Nat := 118140960795 + 1934660 * 2 ^ 59
def prefixEnd_1934660 : Nat := 4983230072969 + 3 ^ 40 * 1934660 * 2
def baseEnd_1934660 : Nat := 993410483027505867552667

theorem tailTrace_1934660 : CollatzResearch.WordTrace tailWord_1934660 prefixEnd_1934660 993410483027505867552667 := by
  unfold tailWord_1934660
  simp only [CollatzResearch.WordTrace]
  refine ⟨35281423585532354233768717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47041898114043138978358289 35281423585532354233768717)
  ·
    refine ⟨13230533844574632837663269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35281423585532354233768717 13230533844574632837663269)
    ·
      refine ⟨2480725095857743657061863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13230533844574632837663269 2480725095857743657061863)
      ·
        refine ⟨3721087643786615485592795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480725095857743657061863 3721087643786615485592795)
        ·
          refine ⟨5581631465679923228389193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721087643786615485592795 5581631465679923228389193)
          ·
            refine ⟨4186223599259942421291895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5581631465679923228389193 4186223599259942421291895)
            ·
              refine ⟨6279335398889913631937843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4186223599259942421291895 6279335398889913631937843)
              ·
                refine ⟨9419003098334870447906765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279335398889913631937843 9419003098334870447906765)
                ·
                  refine ⟨3532126161875576417965037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9419003098334870447906765 3532126161875576417965037)
                  ·
                    refine ⟨1324547310703341156736889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532126161875576417965037 1324547310703341156736889)
                    ·
                      refine ⟨993410483027505867552667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324547310703341156736889 993410483027505867552667)
                      ·
                        rfl

theorem cell23_1934660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_1934660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934660 prefixEnd_1934660 := by exact prefixLift 1934660
  have htrace : WordTrace (prefixWord ++ tailWord_1934660) baseStart_1934660 baseEnd_1934660 := by
    simpa [prefixWord, tailWord_1934660, baseEnd_1934660] using wordTrace_append hprefix tailTrace_1934660
  have hstable : (prefixWord ++ tailWord_1934660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934660).length < 2 ^ (prefixWord ++ tailWord_1934660).sum := by decide
  have hdescent : baseEnd_1934660 < baseStart_1934660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934685 : List Nat := [1, 4, 5, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1934685 : Nat := 118140960795 + 1934685 * 2 ^ 59
def prefixEnd_1934685 : Nat := 4983230072969 + 3 ^ 40 * 1934685 * 2
def baseEnd_1934685 : Nat := 993423320043868269740053

theorem tailTrace_1934685 : CollatzResearch.WordTrace tailWord_1934685 prefixEnd_1934685 993423320043868269740053 := by
  unfold tailWord_1934685
  simp only [CollatzResearch.WordTrace]
  refine ⟨70563758995974137737197509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47042505997316091824798339 70563758995974137737197509)
  ·
    refine ⟨13230704811745150825724533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70563758995974137737197509 13230704811745150825724533)
    ·
      refine ⟨1240378576101107889911675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13230704811745150825724533 1240378576101107889911675)
      ·
        refine ⟨1860567864151661834867513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1240378576101107889911675 1860567864151661834867513)
        ·
          refine ⟨1395425898113746376150635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860567864151661834867513 1395425898113746376150635)
          ·
            refine ⟨2093138847170619564225953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395425898113746376150635 2093138847170619564225953)
            ·
              refine ⟨1569854135377964673169465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2093138847170619564225953 1569854135377964673169465)
              ·
                refine ⟨1177390601533473504877099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1569854135377964673169465 1177390601533473504877099)
                ·
                  refine ⟨1766085902300210257315649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177390601533473504877099 1766085902300210257315649)
                  ·
                    refine ⟨1324564426725157692986737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766085902300210257315649 1324564426725157692986737)
                    ·
                      refine ⟨993423320043868269740053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324564426725157692986737 993423320043868269740053)
                      ·
                        rfl

theorem cell23_1934685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1934685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934685 prefixEnd_1934685 := by exact prefixLift 1934685
  have htrace : WordTrace (prefixWord ++ tailWord_1934685) baseStart_1934685 baseEnd_1934685 := by
    simpa [prefixWord, tailWord_1934685, baseEnd_1934685] using wordTrace_append hprefix tailTrace_1934685
  have hstable : (prefixWord ++ tailWord_1934685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934685).length < 2 ^ (prefixWord ++ tailWord_1934685).sum := by decide
  have hdescent : baseEnd_1934685 < baseStart_1934685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934689 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1934689 : Nat := 118140960795 + 1934689 * 2 ^ 59
def prefixEnd_1934689 : Nat := 4983230072969 + 3 ^ 40 * 1934689 * 2
def baseEnd_1934689 : Nat := 993425373966486254090033

theorem tailTrace_1934689 : CollatzResearch.WordTrace tailWord_1934689 prefixEnd_1934689 993425373966486254090033 := by
  unfold tailWord_1934689
  simp only [CollatzResearch.WordTrace]
  refine ⟨70563904887959646420343121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47042603258639764280228747 70563904887959646420343121)
  ·
    refine ⟨52922928665969734815257341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70563904887959646420343121 52922928665969734815257341)
    ·
      refine ⟨19846098249738650555721503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52922928665969734815257341 19846098249738650555721503)
      ·
        refine ⟨29769147374607975833582255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19846098249738650555721503 29769147374607975833582255)
        ·
          refine ⟨44653721061911963750373383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29769147374607975833582255 44653721061911963750373383)
          ·
            refine ⟨66980581592867945625560075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44653721061911963750373383 66980581592867945625560075)
            ·
              refine ⟨100470872389301918438340113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66980581592867945625560075 100470872389301918438340113)
              ·
                refine ⟨75353154291976438828755085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100470872389301918438340113 75353154291976438828755085)
                ·
                  refine ⟨28257432859491164560783157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75353154291976438828755085 28257432859491164560783157)
                  ·
                    refine ⟨2649134330577296677573421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28257432859491164560783157 2649134330577296677573421)
                    ·
                      refine ⟨993425373966486254090033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2649134330577296677573421 993425373966486254090033)
                      ·
                        rfl

theorem cell23_1934689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1934689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934689 prefixEnd_1934689 := by exact prefixLift 1934689
  have htrace : WordTrace (prefixWord ++ tailWord_1934689) baseStart_1934689 baseEnd_1934689 := by
    simpa [prefixWord, tailWord_1934689, baseEnd_1934689] using wordTrace_append hprefix tailTrace_1934689
  have hstable : (prefixWord ++ tailWord_1934689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934689).length < 2 ^ (prefixWord ++ tailWord_1934689).sum := by decide
  have hdescent : baseEnd_1934689 < baseStart_1934689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934706 : List Nat := [3, 2, 1, 2, 1, 2, 3, 1, 2, 3, 3]
def baseStart_1934706 : Nat := 118140960795 + 1934706 * 2 ^ 59
def prefixEnd_1934706 : Nat := 4983230072969 + 3 ^ 40 * 1934706 * 2
def baseEnd_1934706 : Nat := 993434103137612687577455

theorem tailTrace_1934706 : CollatzResearch.WordTrace tailWord_1934706 prefixEnd_1934706 993434103137612687577455 := by
  unfold tailWord_1934706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641131232224514580927993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47043016619265372215807981 17641131232224514580927993)
  ·
    refine ⟨13230848424168385935695995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17641131232224514580927993 13230848424168385935695995)
    ·
      refine ⟨19846272636252578903543993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13230848424168385935695995 19846272636252578903543993)
      ·
        refine ⟨14884704477189434177657995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19846272636252578903543993 14884704477189434177657995)
        ·
          refine ⟨22327056715784151266486993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14884704477189434177657995 22327056715784151266486993)
          ·
            refine ⟨16745292536838113449865245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22327056715784151266486993 16745292536838113449865245)
            ·
              refine ⟨6279484701314292543699467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16745292536838113449865245 6279484701314292543699467)
              ·
                refine ⟨9419227051971438815549201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279484701314292543699467 9419227051971438815549201)
                ·
                  refine ⟨7064420288978579111661901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9419227051971438815549201 7064420288978579111661901)
                  ·
                    refine ⟨2649157608366967166873213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7064420288978579111661901 2649157608366967166873213)
                    ·
                      refine ⟨993434103137612687577455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2649157608366967166873213 993434103137612687577455)
                      ·
                        rfl

theorem cell23_1934706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_1934706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934706 prefixEnd_1934706 := by exact prefixLift 1934706
  have htrace : WordTrace (prefixWord ++ tailWord_1934706) baseStart_1934706 baseEnd_1934706 := by
    simpa [prefixWord, tailWord_1934706, baseEnd_1934706] using wordTrace_append hprefix tailTrace_1934706
  have hstable : (prefixWord ++ tailWord_1934706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934706).length < 2 ^ (prefixWord ++ tailWord_1934706).sum := by decide
  have hdescent : baseEnd_1934706 < baseStart_1934706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934716 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_1934716 : Nat := 118140960795 + 1934716 * 2 ^ 59
def prefixEnd_1934716 : Nat := 4983230072969 + 3 ^ 40 * 1934716 * 2
def baseEnd_1934716 : Nat := 993439237944157648452409

theorem tailTrace_1934716 : CollatzResearch.WordTrace tailWord_1934716 prefixEnd_1934716 993439237944157648452409 := by
  unfold tailWord_1934716
  simp only [CollatzResearch.WordTrace]
  refine ⟨35282444829430915015788001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47043259772574553354384001 35282444829430915015788001)
  ·
    refine ⟨26461833622073186261841001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35282444829430915015788001 26461833622073186261841001)
    ·
      refine ⟨19846375216554889696380751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26461833622073186261841001 19846375216554889696380751)
      ·
        refine ⟨29769562824832334544571127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19846375216554889696380751 29769562824832334544571127)
        ·
          refine ⟨44654344237248501816856691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29769562824832334544571127 44654344237248501816856691)
          ·
            refine ⟨66981516355872752725285037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44654344237248501816856691 66981516355872752725285037)
            ·
              refine ⟨25118068633452282271981889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66981516355872752725285037 25118068633452282271981889)
              ·
                refine ⟨18838551475089211703986417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25118068633452282271981889 18838551475089211703986417)
                ·
                  refine ⟨14128913606316908777989813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18838551475089211703986417 14128913606316908777989813)
                  ·
                    refine ⟨1324585650592210197936545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14128913606316908777989813 1324585650592210197936545)
                    ·
                      refine ⟨993439237944157648452409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324585650592210197936545 993439237944157648452409)
                      ·
                        rfl

theorem cell23_1934716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_1934716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934716 prefixEnd_1934716 := by exact prefixLift 1934716
  have htrace : WordTrace (prefixWord ++ tailWord_1934716) baseStart_1934716 baseEnd_1934716 := by
    simpa [prefixWord, tailWord_1934716, baseEnd_1934716] using wordTrace_append hprefix tailTrace_1934716
  have hstable : (prefixWord ++ tailWord_1934716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934716).length < 2 ^ (prefixWord ++ tailWord_1934716).sum := by decide
  have hdescent : baseEnd_1934716 < baseStart_1934716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934746 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_1934746 : Nat := 118140960795 + 1934746 * 2 ^ 59
def prefixEnd_1934746 : Nat := 4983230072969 + 3 ^ 40 * 1934746 * 2
def baseEnd_1934746 : Nat := 993454642363792531077271

theorem tailTrace_1934746 : CollatzResearch.WordTrace tailWord_1934746 prefixEnd_1934746 993454642363792531077271 := by
  unfold tailWord_1934746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17641495962188286288792023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47043989232502096770112061 17641495962188286288792023)
  ·
    refine ⟨26462243943282429433188035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17641495962188286288792023 26462243943282429433188035)
    ·
      refine ⟨39693365914923644149782053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26462243943282429433188035 39693365914923644149782053)
      ·
        refine ⟨7442506109048183278084135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39693365914923644149782053 7442506109048183278084135)
        ·
          refine ⟨11163759163572274917126203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7442506109048183278084135 11163759163572274917126203)
          ·
            refine ⟨16745638745358412375689305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11163759163572274917126203 16745638745358412375689305)
            ·
              refine ⟨12559229059018809281766979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16745638745358412375689305 12559229059018809281766979)
              ·
                refine ⟨18838843588528213922650469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559229059018809281766979 18838843588528213922650469)
                ·
                  refine ⟨3532283172849040110496963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18838843588528213922650469 3532283172849040110496963)
                  ·
                    refine ⟨5298424759273560165745445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3532283172849040110496963 5298424759273560165745445)
                    ·
                      refine ⟨993454642363792531077271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5298424759273560165745445 993454642363792531077271)
                      ·
                        rfl

theorem cell23_1934746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_1934746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934746 prefixEnd_1934746 := by exact prefixLift 1934746
  have htrace : WordTrace (prefixWord ++ tailWord_1934746) baseStart_1934746 baseEnd_1934746 := by
    simpa [prefixWord, tailWord_1934746, baseEnd_1934746] using wordTrace_append hprefix tailTrace_1934746
  have hstable : (prefixWord ++ tailWord_1934746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934746).length < 2 ^ (prefixWord ++ tailWord_1934746).sum := by decide
  have hdescent : baseEnd_1934746 < baseStart_1934746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934773 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_1934773 : Nat := 118140960795 + 1934773 * 2 ^ 59
def prefixEnd_1934773 : Nat := 4983230072969 + 3 ^ 40 * 1934773 * 2
def baseEnd_1934773 : Nat := 331156168780487975146549

theorem tailTrace_1934773 : CollatzResearch.WordTrace tailWord_1934773 prefixEnd_1934773 331156168780487975146549 := by
  unfold tailWord_1934773
  simp only [CollatzResearch.WordTrace]
  refine ⟨70566968619655328766400973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47044645746436885844267315 70566968619655328766400973)
  ·
    refine ⟨26462613232370748287400365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70566968619655328766400973 26462613232370748287400365)
    ·
      refine ⟨9923479962139030607775137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26462613232370748287400365 9923479962139030607775137)
      ·
        refine ⟨7442609971604272955831353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9923479962139030607775137 7442609971604272955831353)
        ·
          refine ⟨5581957478703204716873515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7442609971604272955831353 5581957478703204716873515)
          ·
            refine ⟨8372936218054807075310273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581957478703204716873515 8372936218054807075310273)
            ·
              refine ⟨6279702163541105306482705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372936218054807075310273 6279702163541105306482705)
              ·
                refine ⟨4709776622655828979862029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279702163541105306482705 4709776622655828979862029)
                ·
                  refine ⟨1766166233495935867448261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4709776622655828979862029 1766166233495935867448261)
                  ·
                    refine ⟨331156168780487975146549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766166233495935867448261 331156168780487975146549)
                    ·
                      rfl

theorem cell23_1934773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_1934773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934773 prefixEnd_1934773 := by exact prefixLift 1934773
  have htrace : WordTrace (prefixWord ++ tailWord_1934773) baseStart_1934773 baseEnd_1934773 := by
    simpa [prefixWord, tailWord_1934773, baseEnd_1934773] using wordTrace_append hprefix tailTrace_1934773
  have hstable : (prefixWord ++ tailWord_1934773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934773).length < 2 ^ (prefixWord ++ tailWord_1934773).sum := by decide
  have hdescent : baseEnd_1934773 < baseStart_1934773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934833 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_1934833 : Nat := 118140960795 + 1934833 * 2 ^ 59
def prefixEnd_1934833 : Nat := 4983230072969 + 3 ^ 40 * 1934833 * 2
def baseEnd_1934833 : Nat := 331166438393577896896457

theorem tailTrace_1934833 : CollatzResearch.WordTrace tailWord_1934833 prefixEnd_1934833 331166438393577896896457 := by
  unfold tailWord_1934833
  simp only [CollatzResearch.WordTrace]
  refine ⟨70569156999437959013585153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47046104666291972675723435 70569156999437959013585153)
  ·
    refine ⟨52926867749578469260188865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70569156999437959013585153 52926867749578469260188865)
    ·
      refine ⟨39695150812183851945141649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52926867749578469260188865 39695150812183851945141649)
      ·
        refine ⟨29771363109137888958856237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39695150812183851945141649 29771363109137888958856237)
        ·
          refine ⟨11164261165926708359571089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29771363109137888958856237 11164261165926708359571089)
          ·
            refine ⟨8373195874445031269678317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11164261165926708359571089 8373195874445031269678317)
            ·
              refine ⟨3139948452916886726129369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8373195874445031269678317 3139948452916886726129369)
              ·
                refine ⟨2354961339687665044597027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139948452916886726129369 2354961339687665044597027)
                ·
                  refine ⟨3532442009531497566895541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2354961339687665044597027 3532442009531497566895541)
                  ·
                    refine ⟨331166438393577896896457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3532442009531497566895541 331166438393577896896457)
                    ·
                      rfl

theorem cell23_1934833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_1934833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934833 prefixEnd_1934833 := by exact prefixLift 1934833
  have htrace : WordTrace (prefixWord ++ tailWord_1934833) baseStart_1934833 baseEnd_1934833 := by
    simpa [prefixWord, tailWord_1934833, baseEnd_1934833] using wordTrace_append hprefix tailTrace_1934833
  have hstable : (prefixWord ++ tailWord_1934833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934833).length < 2 ^ (prefixWord ++ tailWord_1934833).sum := by decide
  have hdescent : baseEnd_1934833 < baseStart_1934833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934840 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_1934840 : Nat := 118140960795 + 1934840 * 2 ^ 59
def prefixEnd_1934840 : Nat := 4983230072969 + 3 ^ 40 * 1934840 * 2
def baseEnd_1934840 : Nat := 993502909545315163301839

theorem tailTrace_1934840 : CollatzResearch.WordTrace tailWord_1934840 prefixEnd_1934840 993502909545315163301839 := by
  unfold tailWord_1934840
  simp only [CollatzResearch.WordTrace]
  refine ⟨35284706155206299604544987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47046274873608399472726649 35284706155206299604544987)
  ·
    refine ⟨52927059232809449406817481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35284706155206299604544987 52927059232809449406817481)
    ·
      refine ⟨39695294424607087055113111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52927059232809449406817481 39695294424607087055113111)
      ·
        refine ⟨59542941636910630582669667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39695294424607087055113111 59542941636910630582669667)
        ·
          refine ⟨89314412455365945874004501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59542941636910630582669667 89314412455365945874004501)
          ·
            refine ⟨4186613083845278712843961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89314412455365945874004501 4186613083845278712843961)
            ·
              refine ⟨3139959812883959034632971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186613083845278712843961 3139959812883959034632971)
              ·
                refine ⟨4709939719325938551949457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3139959812883959034632971 4709939719325938551949457)
                ·
                  refine ⟨3532454789494453913962093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4709939719325938551949457 3532454789494453913962093)
                  ·
                    refine ⟨1324670546060420217735785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532454789494453913962093 1324670546060420217735785)
                    ·
                      refine ⟨993502909545315163301839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324670546060420217735785 993502909545315163301839)
                      ·
                        rfl

theorem cell23_1934840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_1934840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934840 prefixEnd_1934840 := by exact prefixLift 1934840
  have htrace : WordTrace (prefixWord ++ tailWord_1934840) baseStart_1934840 baseEnd_1934840 := by
    simpa [prefixWord, tailWord_1934840, baseEnd_1934840] using wordTrace_append hprefix tailTrace_1934840
  have hstable : (prefixWord ++ tailWord_1934840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934840).length < 2 ^ (prefixWord ++ tailWord_1934840).sum := by decide
  have hdescent : baseEnd_1934840 < baseStart_1934840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934854 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_1934854 : Nat := 118140960795 + 1934854 * 2 ^ 59
def prefixEnd_1934854 : Nat := 4983230072969 + 3 ^ 40 * 1934854 * 2
def baseEnd_1934854 : Nat := 110390010919386456502975

theorem tailTrace_1934854 : CollatzResearch.WordTrace tailWord_1934854 prefixEnd_1934854 110390010919386456502975 := by
  unfold tailWord_1934854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2205310091636308737503113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47046615288241253066733077 2205310091636308737503113)
  ·
    refine ⟨1653982568727231553127335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2205310091636308737503113 1653982568727231553127335)
    ·
      refine ⟨2480973853090847329691003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653982568727231553127335 2480973853090847329691003)
      ·
        refine ⟨3721460779636270994536505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480973853090847329691003 3721460779636270994536505)
        ·
          refine ⟨2791095584727203245902379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721460779636270994536505 2791095584727203245902379)
          ·
            refine ⟨4186643377090804868853569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791095584727203245902379 4186643377090804868853569)
            ·
              refine ⟨3139982532818103651640177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186643377090804868853569 3139982532818103651640177)
              ·
                refine ⟨2354986899613577738730133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3139982532818103651640177 2354986899613577738730133)
                ·
                  refine ⟨110390010919386456502975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2354986899613577738730133 110390010919386456502975)
                  ·
                    rfl

theorem cell23_1934854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_1934854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934854 prefixEnd_1934854 := by exact prefixLift 1934854
  have htrace : WordTrace (prefixWord ++ tailWord_1934854) baseStart_1934854 baseEnd_1934854 := by
    simpa [prefixWord, tailWord_1934854, baseEnd_1934854] using wordTrace_append hprefix tailTrace_1934854
  have hstable : (prefixWord ++ tailWord_1934854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934854).length < 2 ^ (prefixWord ++ tailWord_1934854).sum := by decide
  have hdescent : baseEnd_1934854 < baseStart_1934854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934859 : List Nat := [1, 1, 1, 1, 19]
def baseStart_1934859 : Nat := 118140960795 + 1934859 * 2 ^ 59
def prefixEnd_1934859 : Nat := 4983230072969 + 3 ^ 40 * 1934859 * 2
def baseEnd_1934859 : Nat := 1362843162795268297619

theorem tailTrace_1934859 : CollatzResearch.WordTrace tailWord_1934859 prefixEnd_1934859 1362843162795268297619 := by
  unfold tailWord_1934859
  simp only [CollatzResearch.WordTrace]
  refine ⟨70570105297343765454031631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47046736864895843636021087 70570105297343765454031631)
  ·
    refine ⟨105855157946015648181047447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70570105297343765454031631 105855157946015648181047447)
    ·
      refine ⟨158782736919023472271571171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105855157946015648181047447 158782736919023472271571171)
      ·
        refine ⟨238174105378535208407356757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158782736919023472271571171 238174105378535208407356757)
        ·
          refine ⟨1362843162795268297619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 19 238174105378535208407356757 1362843162795268297619)
          ·
            rfl

theorem cell23_1934859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 19].length) (baseStart_1934859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934859 prefixEnd_1934859 := by exact prefixLift 1934859
  have htrace : WordTrace (prefixWord ++ tailWord_1934859) baseStart_1934859 baseEnd_1934859 := by
    simpa [prefixWord, tailWord_1934859, baseEnd_1934859] using wordTrace_append hprefix tailTrace_1934859
  have hstable : (prefixWord ++ tailWord_1934859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934859).length < 2 ^ (prefixWord ++ tailWord_1934859).sum := by decide
  have hdescent : baseEnd_1934859 < baseStart_1934859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934880 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_1934880 : Nat := 118140960795 + 1934880 * 2 ^ 59
def prefixEnd_1934880 : Nat := 4983230072969 + 3 ^ 40 * 1934880 * 2
def baseEnd_1934880 : Nat := 331174482923831668933885

theorem tailTrace_1934880 : CollatzResearch.WordTrace tailWord_1934880 prefixEnd_1934880 331174482923831668933885 := by
  unfold tailWord_1934880
  simp only [CollatzResearch.WordTrace]
  refine ⟨35285435615133843020273047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47047247486845124027030729 35285435615133843020273047)
  ·
    refine ⟨52928153422700764530409571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35285435615133843020273047 52928153422700764530409571)
    ·
      refine ⟨79392230134051146795614357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52928153422700764530409571 79392230134051146795614357)
      ·
        refine ⟨3721510787533647506044423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79392230134051146795614357 3721510787533647506044423)
        ·
          refine ⟨5582266181300471259066635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3721510787533647506044423 5582266181300471259066635)
          ·
            refine ⟨8373399271950706888599953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582266181300471259066635 8373399271950706888599953)
            ·
              refine ⟨6280049453963030166449965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373399271950706888599953 6280049453963030166449965)
              ·
                refine ⟨2355018545236136312418737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6280049453963030166449965 2355018545236136312418737)
                ·
                  refine ⟨1766263908927102234314053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2355018545236136312418737 1766263908927102234314053)
                  ·
                    refine ⟨331174482923831668933885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766263908927102234314053 331174482923831668933885)
                    ·
                      rfl

theorem cell23_1934880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_1934880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934880 prefixEnd_1934880 := by exact prefixLift 1934880
  have htrace : WordTrace (prefixWord ++ tailWord_1934880) baseStart_1934880 baseEnd_1934880 := by
    simpa [prefixWord, tailWord_1934880, baseEnd_1934880] using wordTrace_append hprefix tailTrace_1934880
  have hstable : (prefixWord ++ tailWord_1934880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934880).length < 2 ^ (prefixWord ++ tailWord_1934880).sum := by decide
  have hdescent : baseEnd_1934880 < baseStart_1934880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934890 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1934890 : Nat := 118140960795 + 1934890 * 2 ^ 59
def prefixEnd_1934890 : Nat := 4983230072969 + 3 ^ 40 * 1934890 * 2
def baseEnd_1934890 : Nat := 993528583578039967676609

theorem tailTrace_1934890 : CollatzResearch.WordTrace tailWord_1934890 prefixEnd_1934890 993528583578039967676609 := by
  unfold tailWord_1934890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642808990057864437102531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47047490640154305165606749 17642808990057864437102531)
  ·
    refine ⟨26464213485086796655653797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17642808990057864437102531 26464213485086796655653797)
    ·
      refine ⟨4962040028453774372935087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26464213485086796655653797 4962040028453774372935087)
      ·
        refine ⟨7443060042680661559402631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962040028453774372935087 7443060042680661559402631)
        ·
          refine ⟨11164590064020992339103947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443060042680661559402631 11164590064020992339103947)
          ·
            refine ⟨16746885096031488508655921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164590064020992339103947 16746885096031488508655921)
            ·
              refine ⟨12560163822023616381491941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16746885096031488508655921 12560163822023616381491941)
              ·
                refine ⟨2355030716629428071529739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12560163822023616381491941 2355030716629428071529739)
                ·
                  refine ⟨3532546074944142107294609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355030716629428071529739 3532546074944142107294609)
                  ·
                    refine ⟨2649409556208106580470957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3532546074944142107294609 2649409556208106580470957)
                    ·
                      refine ⟨993528583578039967676609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2649409556208106580470957 993528583578039967676609)
                      ·
                        rfl

theorem cell23_1934890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1934890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934890 prefixEnd_1934890 := by exact prefixLift 1934890
  have htrace : WordTrace (prefixWord ++ tailWord_1934890) baseStart_1934890 baseEnd_1934890 := by
    simpa [prefixWord, tailWord_1934890, baseEnd_1934890] using wordTrace_append hprefix tailTrace_1934890
  have hstable : (prefixWord ++ tailWord_1934890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934890).length < 2 ^ (prefixWord ++ tailWord_1934890).sum := by decide
  have hdescent : baseEnd_1934890 < baseStart_1934890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934903 : List Nat := [1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1934903 : Nat := 118140960795 + 1934903 * 2 ^ 59
def prefixEnd_1934903 : Nat := 4983230072969 + 3 ^ 40 * 1934903 * 2
def baseEnd_1934903 : Nat := 993535258826548416814049

theorem tailTrace_1934903 : CollatzResearch.WordTrace tailWord_1934903 prefixEnd_1934903 993535258826548416814049 := by
  unfold tailWord_1934903
  simp only [CollatzResearch.WordTrace]
  refine ⟨70571710109184360968633363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47047806739456240645755575 70571710109184360968633363)
  ·
    refine ⟨105857565163776541452950045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70571710109184360968633363 105857565163776541452950045)
    ·
      refine ⟨39696586936416203044856267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105857565163776541452950045 39696586936416203044856267)
      ·
        refine ⟨59544880404624304567284401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39696586936416203044856267 59544880404624304567284401)
        ·
          refine ⟨44658660303468228425463301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59544880404624304567284401 44658660303468228425463301)
          ·
            refine ⟨8373498806900292829774369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44658660303468228425463301 8373498806900292829774369)
            ·
              refine ⟨6280124105175219622330777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373498806900292829774369 6280124105175219622330777)
              ·
                refine ⟨4710093078881414716748083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280124105175219622330777 4710093078881414716748083)
                ·
                  refine ⟨7065139618322122075122125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710093078881414716748083 7065139618322122075122125)
                  ·
                    refine ⟨2649427356870795778170797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7065139618322122075122125 2649427356870795778170797)
                    ·
                      refine ⟨993535258826548416814049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2649427356870795778170797 993535258826548416814049)
                      ·
                        rfl

theorem cell23_1934903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1934903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934903 prefixEnd_1934903 := by exact prefixLift 1934903
  have htrace : WordTrace (prefixWord ++ tailWord_1934903) baseStart_1934903 baseEnd_1934903 := by
    simpa [prefixWord, tailWord_1934903, baseEnd_1934903] using wordTrace_append hprefix tailTrace_1934903
  have hstable : (prefixWord ++ tailWord_1934903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934903).length < 2 ^ (prefixWord ++ tailWord_1934903).sum := by decide
  have hdescent : baseEnd_1934903 < baseStart_1934903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934904 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 1, 2, 2]
def baseStart_1934904 : Nat := 118140960795 + 1934904 * 2 ^ 59
def prefixEnd_1934904 : Nat := 4983230072969 + 3 ^ 40 * 1934904 * 2
def baseEnd_1934904 : Nat := 993535772307202912901545

theorem tailTrace_1934904 : CollatzResearch.WordTrace tailWord_1934904 prefixEnd_1934904 993535772307202912901545 := by
  unfold tailWord_1934904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35285873291090369069709883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47047831054787158759613177 35285873291090369069709883)
  ·
    refine ⟨52928809936635553604564825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35285873291090369069709883 52928809936635553604564825)
    ·
      refine ⟨39696607452476665203423619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52928809936635553604564825 39696607452476665203423619)
      ·
        refine ⟨59544911178714997805135429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39696607452476665203423619 59544911178714997805135429)
        ·
          refine ⟨11164670846009062088462893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59544911178714997805135429 11164670846009062088462893)
          ·
            refine ⟨4186751567253398283173585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11164670846009062088462893 4186751567253398283173585)
            ·
              refine ⟨3140063675440048712380189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186751567253398283173585 3140063675440048712380189)
              ·
                refine ⟨1177523878290018267142571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3140063675440048712380189 1177523878290018267142571)
                ·
                  refine ⟨1766285817435027400713857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177523878290018267142571 1766285817435027400713857)
                  ·
                    refine ⟨1324714363076270550535393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766285817435027400713857 1324714363076270550535393)
                    ·
                      refine ⟨993535772307202912901545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324714363076270550535393 993535772307202912901545)
                      ·
                        rfl

theorem cell23_1934904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_1934904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934904 prefixEnd_1934904 := by exact prefixLift 1934904
  have htrace : WordTrace (prefixWord ++ tailWord_1934904) baseStart_1934904 baseEnd_1934904 := by
    simpa [prefixWord, tailWord_1934904, baseEnd_1934904] using wordTrace_append hprefix tailTrace_1934904
  have hstable : (prefixWord ++ tailWord_1934904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934904).length < 2 ^ (prefixWord ++ tailWord_1934904).sum := by decide
  have hdescent : baseEnd_1934904 < baseStart_1934904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934947 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 1, 3, 2]
def baseStart_1934947 : Nat := 118140960795 + 1934947 * 2 ^ 59
def prefixEnd_1934947 : Nat := 4983230072969 + 3 ^ 40 * 1934947 * 2
def baseEnd_1934947 : Nat := 993557851975346244663847

theorem tailTrace_1934947 : CollatzResearch.WordTrace tailWord_1934947 prefixEnd_1934947 993557851975346244663847 := by
  unfold tailWord_1934947
  simp only [CollatzResearch.WordTrace]
  refine ⟨70573314921024956483235095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47048876614016637655490063 70573314921024956483235095)
  ·
    refine ⟨105859972381537434724852643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70573314921024956483235095 105859972381537434724852643)
    ·
      refine ⟨158789958572306152087278965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105859972381537434724852643 158789958572306152087278965)
      ·
        refine ⟨14886558616153701758182403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158789958572306152087278965 14886558616153701758182403)
        ·
          refine ⟨22329837924230552637273605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14886558616153701758182403 22329837924230552637273605)
          ·
            refine ⟨4186844610793228619488801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22329837924230552637273605 4186844610793228619488801)
            ·
              refine ⟨3140133458094921464616601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4186844610793228619488801 3140133458094921464616601)
              ·
                refine ⟨2355100093571191098462451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140133458094921464616601 2355100093571191098462451)
                ·
                  refine ⟨3532650140356786647693677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355100093571191098462451 3532650140356786647693677)
                  ·
                    refine ⟨1324743802633794992885129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3532650140356786647693677 1324743802633794992885129)
                    ·
                      refine ⟨993557851975346244663847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324743802633794992885129 993557851975346244663847)
                      ·
                        rfl

theorem cell23_1934947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_1934947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934947 prefixEnd_1934947 := by exact prefixLift 1934947
  have htrace : WordTrace (prefixWord ++ tailWord_1934947) baseStart_1934947 baseEnd_1934947 := by
    simpa [prefixWord, tailWord_1934947, baseEnd_1934947] using wordTrace_append hprefix tailTrace_1934947
  have hstable : (prefixWord ++ tailWord_1934947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934947).length < 2 ^ (prefixWord ++ tailWord_1934947).sum := by decide
  have hdescent : baseEnd_1934947 < baseStart_1934947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934976 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1934976 : Nat := 118140960795 + 1934976 * 2 ^ 59
def prefixEnd_1934976 : Nat := 4983230072969 + 3 ^ 40 * 1934976 * 2
def baseEnd_1934976 : Nat := 993572742914326631201213

theorem tailTrace_1934976 : CollatzResearch.WordTrace tailWord_1934976 prefixEnd_1934976 993572742914326631201213 := by
  unfold tailWord_1934976
  simp only [CollatzResearch.WordTrace]
  refine ⟨35287186318959947218020391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47049581758613262957360521 35287186318959947218020391)
  ·
    refine ⟨52930779478439920827030587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35287186318959947218020391 52930779478439920827030587)
    ·
      refine ⟨79396169217659881240545881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52930779478439920827030587 79396169217659881240545881)
      ·
        refine ⟨59547126913244910930409411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79396169217659881240545881 59547126913244910930409411)
        ·
          refine ⟨89320690369867366395614117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59547126913244910930409411 89320690369867366395614117)
          ·
            refine ⟨16747629444350131199177647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89320690369867366395614117 16747629444350131199177647)
            ·
              refine ⟨25121444166525196798766471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747629444350131199177647 25121444166525196798766471)
              ·
                refine ⟨37682166249787795198149707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25121444166525196798766471 37682166249787795198149707)
                ·
                  refine ⟨56523249374681692797224561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37682166249787795198149707 56523249374681692797224561)
                  ·
                    refine ⟨42392437031011269597918421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56523249374681692797224561 42392437031011269597918421)
                    ·
                      refine ⟨993572742914326631201213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42392437031011269597918421 993572742914326631201213)
                      ·
                        rfl

theorem cell23_1934976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1934976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934976 prefixEnd_1934976 := by exact prefixLift 1934976
  have htrace : WordTrace (prefixWord ++ tailWord_1934976) baseStart_1934976 baseEnd_1934976 := by
    simpa [prefixWord, tailWord_1934976, baseEnd_1934976] using wordTrace_append hprefix tailTrace_1934976
  have hstable : (prefixWord ++ tailWord_1934976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934976).length < 2 ^ (prefixWord ++ tailWord_1934976).sum := by decide
  have hdescent : baseEnd_1934976 < baseStart_1934976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934977 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_1934977 : Nat := 118140960795 + 1934977 * 2 ^ 59
def prefixEnd_1934977 : Nat := 4983230072969 + 3 ^ 40 * 1934977 * 2
def baseEnd_1934977 : Nat := 993573256394981127288709

theorem tailTrace_1934977 : CollatzResearch.WordTrace tailWord_1934977 prefixEnd_1934977 993573256394981127288709 := by
  unfold tailWord_1934977
  simp only [CollatzResearch.WordTrace]
  refine ⟨70574409110916271606827185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47049606073944181071218123 70574409110916271606827185)
  ·
    refine ⟨52930806833187203705120389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70574409110916271606827185 52930806833187203705120389)
    ·
      refine ⟨9924526281222600694710073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52930806833187203705120389 9924526281222600694710073)
      ·
        refine ⟨7443394710916950521032555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9924526281222600694710073 7443394710916950521032555)
        ·
          refine ⟨11165092066375425781548833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443394710916950521032555 11165092066375425781548833)
          ·
            refine ⟨8373819049781569336161625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165092066375425781548833 8373819049781569336161625)
            ·
              refine ⟨6280364287336177002121219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373819049781569336161625 6280364287336177002121219)
              ·
                refine ⟨9420546431004265503181829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280364287336177002121219 9420546431004265503181829)
                ·
                  refine ⟨1766352455813299781846593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9420546431004265503181829 1766352455813299781846593)
                  ·
                    refine ⟨1324764341859974836384945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766352455813299781846593 1324764341859974836384945)
                    ·
                      refine ⟨993573256394981127288709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324764341859974836384945 993573256394981127288709)
                      ·
                        rfl

theorem cell23_1934977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_1934977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934977 prefixEnd_1934977 := by exact prefixLift 1934977
  have htrace : WordTrace (prefixWord ++ tailWord_1934977) baseStart_1934977 baseEnd_1934977 := by
    simpa [prefixWord, tailWord_1934977, baseEnd_1934977] using wordTrace_append hprefix tailTrace_1934977
  have hstable : (prefixWord ++ tailWord_1934977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934977).length < 2 ^ (prefixWord ++ tailWord_1934977).sum := by decide
  have hdescent : baseEnd_1934977 < baseStart_1934977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1934983 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 7]
def baseStart_1934983 : Nat := 118140960795 + 1934983 * 2 ^ 59
def prefixEnd_1934983 : Nat := 4983230072969 + 3 ^ 40 * 1934983 * 2
def baseEnd_1934983 : Nat := 110397370808767567090409

theorem tailTrace_1934983 : CollatzResearch.WordTrace tailWord_1934983 prefixEnd_1934983 110397370808767567090409 := by
  unfold tailWord_1934983
  simp only [CollatzResearch.WordTrace]
  refine ⟨70574627948894534631545603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47049751965929689754363735 70574627948894534631545603)
  ·
    refine ⟨105861941923341801947318405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70574627948894534631545603 105861941923341801947318405)
    ·
      refine ⟨19849114110626587865122201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105861941923341801947318405 19849114110626587865122201)
      ·
        refine ⟨14886835582969940898841651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19849114110626587865122201 14886835582969940898841651)
        ·
          refine ⟨22330253374454911348262477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14886835582969940898841651 22330253374454911348262477)
          ·
            refine ⟨8373845015420591755598429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22330253374454911348262477 8373845015420591755598429)
            ·
              refine ⟨3140191880782721908349411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8373845015420591755598429 3140191880782721908349411)
              ·
                refine ⟨4710287821174082862524117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140191880782721908349411 4710287821174082862524117)
                ·
                  refine ⟨110397370808767567090409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4710287821174082862524117 110397370808767567090409)
                  ·
                    rfl

theorem cell23_1934983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 7].length) (baseStart_1934983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1934983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1934983 prefixEnd_1934983 := by exact prefixLift 1934983
  have htrace : WordTrace (prefixWord ++ tailWord_1934983) baseStart_1934983 baseEnd_1934983 := by
    simpa [prefixWord, tailWord_1934983, baseEnd_1934983] using wordTrace_append hprefix tailTrace_1934983
  have hstable : (prefixWord ++ tailWord_1934983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1934983).length < 2 ^ (prefixWord ++ tailWord_1934983).sum := by decide
  have hdescent : baseEnd_1934983 < baseStart_1934983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1934983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935013 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_1935013 : Nat := 118140960795 + 1935013 * 2 ^ 59
def prefixEnd_1935013 : Nat := 4983230072969 + 3 ^ 40 * 1935013 * 2
def baseEnd_1935013 : Nat := 331197247232847662146181

theorem tailTrace_1935013 : CollatzResearch.WordTrace tailWord_1935013 prefixEnd_1935013 331197247232847662146181 := by
  unfold tailWord_1935013
  simp only [CollatzResearch.WordTrace]
  refine ⟨70575722138785849755137693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47050481425857233170091795 70575722138785849755137693)
  ·
    refine ⟨26465895802044693658176635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70575722138785849755137693 26465895802044693658176635)
    ·
      refine ⟨39698843703067040487264953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26465895802044693658176635 39698843703067040487264953)
      ·
        refine ⟨29774132777300280365448715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39698843703067040487264953 29774132777300280365448715)
        ·
          refine ⟨44661199165950420548173073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29774132777300280365448715 44661199165950420548173073)
          ·
            refine ⟨33495899374462815411129805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44661199165950420548173073 33495899374462815411129805)
            ·
              refine ⟨12560962265423555779173677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33495899374462815411129805 12560962265423555779173677)
              ·
                refine ⟨4710360849533833417190129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560962265423555779173677 4710360849533833417190129)
                ·
                  refine ⟨3532770637150375062892597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710360849533833417190129 3532770637150375062892597)
                  ·
                    refine ⟨331197247232847662146181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3532770637150375062892597 331197247232847662146181)
                    ·
                      rfl

theorem cell23_1935013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_1935013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935013 prefixEnd_1935013 := by exact prefixLift 1935013
  have htrace : WordTrace (prefixWord ++ tailWord_1935013) baseStart_1935013 baseEnd_1935013 := by
    simpa [prefixWord, tailWord_1935013, baseEnd_1935013] using wordTrace_append hprefix tailTrace_1935013
  have hstable : (prefixWord ++ tailWord_1935013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935013).length < 2 ^ (prefixWord ++ tailWord_1935013).sum := by decide
  have hdescent : baseEnd_1935013 < baseStart_1935013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935043 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 9, 4]
def baseStart_1935043 : Nat := 118140960795 + 1935043 * 2 ^ 59
def prefixEnd_1935043 : Nat := 4983230072969 + 3 ^ 40 * 1935043 * 2
def baseEnd_1935043 : Nat := 331202382039392623021135

theorem tailTrace_1935043 : CollatzResearch.WordTrace tailWord_1935043 prefixEnd_1935043 331202382039392623021135 := by
  unfold tailWord_1935043
  simp only [CollatzResearch.WordTrace]
  refine ⟨70576816328677164878729783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47051210885784776585819855 70576816328677164878729783)
  ·
    refine ⟨105865224493015747318094675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70576816328677164878729783 105865224493015747318094675)
    ·
      refine ⟨158797836739523620977142013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105865224493015747318094675 158797836739523620977142013)
      ·
        refine ⟨59549188777321357866428255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158797836739523620977142013 59549188777321357866428255)
        ·
          refine ⟨89323783165982036799642383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59549188777321357866428255 89323783165982036799642383)
          ·
            refine ⟨133985674748973055199463575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89323783165982036799642383 133985674748973055199463575)
            ·
              refine ⟨200978512123459582799195363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133985674748973055199463575 200978512123459582799195363)
              ·
                refine ⟨301467768185189374198793045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200978512123459582799195363 301467768185189374198793045)
                ·
                  refine ⟨1766412704210093989446053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 301467768185189374198793045 1766412704210093989446053)
                  ·
                    refine ⟨331202382039392623021135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766412704210093989446053 331202382039392623021135)
                    ·
                      rfl

theorem cell23_1935043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 4].length) (baseStart_1935043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935043 prefixEnd_1935043 := by exact prefixLift 1935043
  have htrace : WordTrace (prefixWord ++ tailWord_1935043) baseStart_1935043 baseEnd_1935043 := by
    simpa [prefixWord, tailWord_1935043, baseEnd_1935043] using wordTrace_append hprefix tailTrace_1935043
  have hstable : (prefixWord ++ tailWord_1935043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935043).length < 2 ^ (prefixWord ++ tailWord_1935043).sum := by decide
  have hdescent : baseEnd_1935043 < baseStart_1935043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935094 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1935094 : Nat := 118140960795 + 1935094 * 2 ^ 59
def prefixEnd_1935094 : Nat := 4983230072969 + 3 ^ 40 * 1935094 * 2
def baseEnd_1935094 : Nat := 331211111210519056508557

theorem tailTrace_1935094 : CollatzResearch.WordTrace tailWord_1935094 prefixEnd_1935094 331211111210519056508557 := by
  unfold tailWord_1935094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4411167278218275036802271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47052450967661600392557557 4411167278218275036802271)
  ·
    refine ⟨6616750917327412555203407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4411167278218275036802271 6616750917327412555203407)
    ·
      refine ⟨9925126375991118832805111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6616750917327412555203407 9925126375991118832805111)
      ·
        refine ⟨14887689563986678249207667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9925126375991118832805111 14887689563986678249207667)
        ·
          refine ⟨22331534345980017373811501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14887689563986678249207667 22331534345980017373811501)
          ·
            refine ⟨8374325379742506515179313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22331534345980017373811501 8374325379742506515179313)
            ·
              refine ⟨6280744034806879886384485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374325379742506515179313 6280744034806879886384485)
              ·
                refine ⟨1177639506526289978697091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6280744034806879886384485 1177639506526289978697091)
                ·
                  refine ⟨1766459259789434968045637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177639506526289978697091 1766459259789434968045637)
                  ·
                    refine ⟨331211111210519056508557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766459259789434968045637 331211111210519056508557)
                    ·
                      rfl

theorem cell23_1935094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1935094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935094 prefixEnd_1935094 := by exact prefixLift 1935094
  have htrace : WordTrace (prefixWord ++ tailWord_1935094) baseStart_1935094 baseEnd_1935094 := by
    simpa [prefixWord, tailWord_1935094, baseEnd_1935094] using wordTrace_append hprefix tailTrace_1935094
  have hstable : (prefixWord ++ tailWord_1935094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935094).length < 2 ^ (prefixWord ++ tailWord_1935094).sum := by decide
  have hdescent : baseEnd_1935094 < baseStart_1935094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935103 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 5, 5]
def baseStart_1935103 : Nat := 118140960795 + 1935103 * 2 ^ 59
def prefixEnd_1935103 : Nat := 4983230072969 + 3 ^ 40 * 1935103 * 2
def baseEnd_1935103 : Nat := 331212651652482544771043

theorem tailTrace_1935103 : CollatzResearch.WordTrace tailWord_1935103 prefixEnd_1935103 331212651652482544771043 := by
  unfold tailWord_1935103
  simp only [CollatzResearch.WordTrace]
  refine ⟨70579004708459795125913963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47052669805639863417275975 70579004708459795125913963)
  ·
    refine ⟨105868507062689692688870945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70579004708459795125913963 105868507062689692688870945)
    ·
      refine ⟨79401380297017269516653209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105868507062689692688870945 79401380297017269516653209)
      ·
        refine ⟨59551035222762952137489907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79401380297017269516653209 59551035222762952137489907)
        ·
          refine ⟨89326552834144428206234861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59551035222762952137489907 89326552834144428206234861)
          ·
            refine ⟨33497457312804160577338073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89326552834144428206234861 33497457312804160577338073)
            ·
              refine ⟨25123092984603120433003555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33497457312804160577338073 25123092984603120433003555)
              ·
                refine ⟨37684639476904680649505333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25123092984603120433003555 37684639476904680649505333)
                ·
                  refine ⟨3532934950959813810891125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37684639476904680649505333 3532934950959813810891125)
                  ·
                    refine ⟨331212651652482544771043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3532934950959813810891125 331212651652482544771043)
                    ·
                      rfl

theorem cell23_1935103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_1935103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935103 prefixEnd_1935103 := by exact prefixLift 1935103
  have htrace : WordTrace (prefixWord ++ tailWord_1935103) baseStart_1935103 baseEnd_1935103 := by
    simpa [prefixWord, tailWord_1935103, baseEnd_1935103] using wordTrace_append hprefix tailTrace_1935103
  have hstable : (prefixWord ++ tailWord_1935103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935103).length < 2 ^ (prefixWord ++ tailWord_1935103).sum := by decide
  have hdescent : baseEnd_1935103 < baseStart_1935103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935127 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 5, 2]
def baseStart_1935127 : Nat := 118140960795 + 1935127 * 2 ^ 59
def prefixEnd_1935127 : Nat := 4983230072969 + 3 ^ 40 * 1935127 * 2
def baseEnd_1935127 : Nat := 993650278493155540413019

theorem tailTrace_1935127 : CollatzResearch.WordTrace tailWord_1935127 prefixEnd_1935127 993650278493155540413019 := by
  unfold tailWord_1935127
  simp only [CollatzResearch.WordTrace]
  refine ⟨70579880060372847224787635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47053253373581898149858423 70579880060372847224787635)
  ·
    refine ⟨105869820090559270837181453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70579880060372847224787635 105869820090559270837181453)
    ·
      refine ⟨39701182533959726563943045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105869820090559270837181453 39701182533959726563943045)
      ·
        refine ⟨7443971725117448730739321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39701182533959726563943045 7443971725117448730739321)
        ·
          refine ⟨5582978793838086548054491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7443971725117448730739321 5582978793838086548054491)
          ·
            refine ⟨8374468190757129822081737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582978793838086548054491 8374468190757129822081737)
            ·
              refine ⟨6280851143067847366561303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374468190757129822081737 6280851143067847366561303)
              ·
                refine ⟨9421276714601771049841955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280851143067847366561303 9421276714601771049841955)
                ·
                  refine ⟨14131915071902656574762933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421276714601771049841955 14131915071902656574762933)
                  ·
                    refine ⟨1324867037990874053884025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14131915071902656574762933 1324867037990874053884025)
                    ·
                      refine ⟨993650278493155540413019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324867037990874053884025 993650278493155540413019)
                      ·
                        rfl

theorem cell23_1935127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_1935127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935127 prefixEnd_1935127 := by exact prefixLift 1935127
  have htrace : WordTrace (prefixWord ++ tailWord_1935127) baseStart_1935127 baseEnd_1935127 := by
    simpa [prefixWord, tailWord_1935127, baseEnd_1935127] using wordTrace_append hprefix tailTrace_1935127
  have hstable : (prefixWord ++ tailWord_1935127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935127).length < 2 ^ (prefixWord ++ tailWord_1935127).sum := by decide
  have hdescent : baseEnd_1935127 < baseStart_1935127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935144 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_1935144 : Nat := 118140960795 + 1935144 * 2 ^ 59
def prefixEnd_1935144 : Nat := 4983230072969 + 3 ^ 40 * 1935144 * 2
def baseEnd_1935144 : Nat := 993659007664281973900441

theorem tailTrace_1935144 : CollatzResearch.WordTrace tailWord_1935144 prefixEnd_1935144 993659007664281973900441 := by
  unfold tailWord_1935144
  simp only [CollatzResearch.WordTrace]
  refine ⟨35290250050655629564078243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47053666734207506085437657 35290250050655629564078243)
  ·
    refine ⟨52935375075983444346117365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35290250050655629564078243 52935375075983444346117365)
    ·
      refine ⟨4962691413373447907448503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52935375075983444346117365 4962691413373447907448503)
      ·
        refine ⟨7444037120060171861172755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962691413373447907448503 7444037120060171861172755)
        ·
          refine ⟨11166055680090257791759133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7444037120060171861172755 11166055680090257791759133)
          ·
            refine ⟨4187270880033846671909675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11166055680090257791759133 4187270880033846671909675)
            ·
              refine ⟨6280906320050770007864513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187270880033846671909675 6280906320050770007864513)
              ·
                refine ⟨4710679740038077505898385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280906320050770007864513 4710679740038077505898385)
                ·
                  refine ⟨3533009805028558129423789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4710679740038077505898385 3533009805028558129423789)
                  ·
                    refine ⟨1324878676885709298533921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533009805028558129423789 1324878676885709298533921)
                    ·
                      refine ⟨993659007664281973900441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324878676885709298533921 993659007664281973900441)
                      ·
                        rfl

theorem cell23_1935144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_1935144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935144 prefixEnd_1935144 := by exact prefixLift 1935144
  have htrace : WordTrace (prefixWord ++ tailWord_1935144) baseStart_1935144 baseEnd_1935144 := by
    simpa [prefixWord, tailWord_1935144, baseEnd_1935144] using wordTrace_append hprefix tailTrace_1935144
  have hstable : (prefixWord ++ tailWord_1935144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935144).length < 2 ^ (prefixWord ++ tailWord_1935144).sum := by decide
  have hdescent : baseEnd_1935144 < baseStart_1935144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935160 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_1935160 : Nat := 118140960795 + 1935160 * 2 ^ 59
def prefixEnd_1935160 : Nat := 4983230072969 + 3 ^ 40 * 1935160 * 2
def baseEnd_1935160 : Nat := 993667223354753911300367

theorem tailTrace_1935160 : CollatzResearch.WordTrace tailWord_1935160 prefixEnd_1935160 993667223354753911300367 := by
  unfold tailWord_1935160
  simp only [CollatzResearch.WordTrace]
  refine ⟨35290541834626646930369467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47054055779502195907159289 35290541834626646930369467)
  ·
    refine ⟨52935812751939970395554201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35290541834626646930369467 52935812751939970395554201)
    ·
      refine ⟨39701859563954977796665651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52935812751939970395554201 39701859563954977796665651)
      ·
        refine ⟨59552789345932466694998477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39701859563954977796665651 59552789345932466694998477)
        ·
          refine ⟨22332296004724675010624429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59552789345932466694998477 22332296004724675010624429)
          ·
            refine ⟨8374611001771753128984161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22332296004724675010624429 8374611001771753128984161)
            ·
              refine ⟨6280958251328814846738121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374611001771753128984161 6280958251328814846738121)
              ·
                refine ⟨4710718688496611135053591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6280958251328814846738121 4710718688496611135053591)
                ·
                  refine ⟨7066078032744916702580387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710718688496611135053591 7066078032744916702580387)
                  ·
                    refine ⟨10599117049117375053870581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066078032744916702580387 10599117049117375053870581)
                    ·
                      refine ⟨993667223354753911300367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10599117049117375053870581 993667223354753911300367)
                      ·
                        rfl

theorem cell23_1935160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_1935160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935160 prefixEnd_1935160 := by exact prefixLift 1935160
  have htrace : WordTrace (prefixWord ++ tailWord_1935160) baseStart_1935160 baseEnd_1935160 := by
    simpa [prefixWord, tailWord_1935160, baseEnd_1935160] using wordTrace_append hprefix tailTrace_1935160
  have hstable : (prefixWord ++ tailWord_1935160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935160).length < 2 ^ (prefixWord ++ tailWord_1935160).sum := by decide
  have hdescent : baseEnd_1935160 < baseStart_1935160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935194 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_1935194 : Nat := 118140960795 + 1935194 * 2 ^ 59
def prefixEnd_1935194 : Nat := 4983230072969 + 3 ^ 40 * 1935194 * 2
def baseEnd_1935194 : Nat := 993684681697006778275211

theorem tailTrace_1935194 : CollatzResearch.WordTrace tailWord_1935194 prefixEnd_1935194 993684681697006778275211 := by
  unfold tailWord_1935194
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645580937782529416869159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47054882500753411778317757 17645580937782529416869159)
  ·
    refine ⟨26468371406673794125303739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17645580937782529416869159 26468371406673794125303739)
    ·
      refine ⟨39702557110010691187955609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26468371406673794125303739 39702557110010691187955609)
      ·
        refine ⟨29776917832508018390966707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39702557110010691187955609 29776917832508018390966707)
        ·
          refine ⟨44665376748762027586450061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29776917832508018390966707 44665376748762027586450061)
          ·
            refine ⟨16749516280785760344918773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44665376748762027586450061 16749516280785760344918773)
            ·
              refine ⟨1570267151323665032336135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16749516280785760344918773 1570267151323665032336135)
              ·
                refine ⟨2355400726985497548504203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1570267151323665032336135 2355400726985497548504203)
                ·
                  refine ⟨3533101090478246322756305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355400726985497548504203 3533101090478246322756305)
                  ·
                    refine ⟨2649825817858684742067229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533101090478246322756305 2649825817858684742067229)
                    ·
                      refine ⟨993684681697006778275211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2649825817858684742067229 993684681697006778275211)
                      ·
                        rfl

theorem cell23_1935194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_1935194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935194 prefixEnd_1935194 := by exact prefixLift 1935194
  have htrace : WordTrace (prefixWord ++ tailWord_1935194) baseStart_1935194 baseEnd_1935194 := by
    simpa [prefixWord, tailWord_1935194, baseEnd_1935194] using wordTrace_append hprefix tailTrace_1935194
  have hstable : (prefixWord ++ tailWord_1935194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935194).length < 2 ^ (prefixWord ++ tailWord_1935194).sum := by decide
  have hdescent : baseEnd_1935194 < baseStart_1935194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935217 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_1935217 : Nat := 118140960795 + 1935217 * 2 ^ 59
def prefixEnd_1935217 : Nat := 4983230072969 + 3 ^ 40 * 1935217 * 2
def baseEnd_1935217 : Nat := 993696491752060188287605

theorem tailTrace_1935217 : CollatzResearch.WordTrace tailWord_1935217 prefixEnd_1935217 993696491752060188287605 := by
  unfold tailWord_1935217
  simp only [CollatzResearch.WordTrace]
  refine ⟨70583162630046792595563905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47055441753364528397042603 70583162630046792595563905)
  ·
    refine ⟨52937371972535094446672929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70583162630046792595563905 52937371972535094446672929)
    ·
      refine ⟨39703028979401320835004697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52937371972535094446672929 39703028979401320835004697)
      ·
        refine ⟨29777271734550990626253523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39703028979401320835004697 29777271734550990626253523)
        ·
          refine ⟨44665907601826485939380285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29777271734550990626253523 44665907601826485939380285)
          ·
            refine ⟨16749715350684932227267607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44665907601826485939380285 16749715350684932227267607)
            ·
              refine ⟨25124573026027398340901411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16749715350684932227267607 25124573026027398340901411)
              ·
                refine ⟨37686859539041097511352117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25124573026027398340901411 37686859539041097511352117)
                ·
                  refine ⟨3533143081785102891689261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37686859539041097511352117 3533143081785102891689261)
                  ·
                    refine ⟨1324928655669413584383473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3533143081785102891689261 1324928655669413584383473)
                    ·
                      refine ⟨993696491752060188287605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324928655669413584383473 993696491752060188287605)
                      ·
                        rfl

theorem cell23_1935217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_1935217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935217 prefixEnd_1935217 := by exact prefixLift 1935217
  have htrace : WordTrace (prefixWord ++ tailWord_1935217) baseStart_1935217 baseEnd_1935217 := by
    simpa [prefixWord, tailWord_1935217, baseEnd_1935217] using wordTrace_append hprefix tailTrace_1935217
  have hstable : (prefixWord ++ tailWord_1935217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935217).length < 2 ^ (prefixWord ++ tailWord_1935217).sum := by decide
  have hdescent : baseEnd_1935217 < baseStart_1935217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935281 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_1935281 : Nat := 118140960795 + 1935281 * 2 ^ 59
def prefixEnd_1935281 : Nat := 4983230072969 + 3 ^ 40 * 1935281 * 2
def baseEnd_1935281 : Nat := 993729354513947937887311

theorem tailTrace_1935281 : CollatzResearch.WordTrace tailWord_1935281 prefixEnd_1935281 993729354513947937887311 := by
  unfold tailWord_1935281
  simp only [CollatzResearch.WordTrace]
  refine ⟨70585496901814931525893697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47056997934543287683929131 70585496901814931525893697)
  ·
    refine ⟨52939122676361198644420273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70585496901814931525893697 52939122676361198644420273)
    ·
      refine ⟨39704342007270898983315205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52939122676361198644420273 39704342007270898983315205)
      ·
        refine ⟨7444564126363293559371601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39704342007270898983315205 7444564126363293559371601)
        ·
          refine ⟨5583423094772470169528701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444564126363293559371601 5583423094772470169528701)
          ·
            refine ⟨2093783660539676313573263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5583423094772470169528701 2093783660539676313573263)
            ·
              refine ⟨3140675490809514470359895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2093783660539676313573263 3140675490809514470359895)
              ·
                refine ⟨4711013236214271705539843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3140675490809514470359895 4711013236214271705539843)
                ·
                  refine ⟨7066519854321407558309765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711013236214271705539843 7066519854321407558309765)
                  ·
                    refine ⟨1324972472685263917183081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066519854321407558309765 1324972472685263917183081)
                    ·
                      refine ⟨993729354513947937887311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1324972472685263917183081 993729354513947937887311)
                      ·
                        rfl

theorem cell23_1935281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_1935281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935281 prefixEnd_1935281 := by exact prefixLift 1935281
  have htrace : WordTrace (prefixWord ++ tailWord_1935281) baseStart_1935281 baseEnd_1935281 := by
    simpa [prefixWord, tailWord_1935281, baseEnd_1935281] using wordTrace_append hprefix tailTrace_1935281
  have hstable : (prefixWord ++ tailWord_1935281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935281).length < 2 ^ (prefixWord ++ tailWord_1935281).sum := by decide
  have hdescent : baseEnd_1935281 < baseStart_1935281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935304 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 5]
def baseStart_1935304 : Nat := 118140960795 + 1935304 * 2 ^ 59
def prefixEnd_1935304 : Nat := 4983230072969 + 3 ^ 40 * 1935304 * 2
def baseEnd_1935304 : Nat := 110415684952111260877745

theorem tailTrace_1935304 : CollatzResearch.WordTrace tailWord_1935304 prefixEnd_1935304 110415684952111260877745 := by
  unfold tailWord_1935304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35293167890365803226990483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47057557187154404302653977 35293167890365803226990483)
  ·
    refine ⟨52939751835548704840485725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35293167890365803226990483 52939751835548704840485725)
    ·
      refine ⟨19852406938330764315182147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52939751835548704840485725 19852406938330764315182147)
      ·
        refine ⟨29778610407496146472773221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19852406938330764315182147 29778610407496146472773221)
        ·
          refine ⟨5583489451405527463644979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29778610407496146472773221 5583489451405527463644979)
          ·
            refine ⟨8375234177108291195467469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583489451405527463644979 8375234177108291195467469)
            ·
              refine ⟨3140712816415609198300301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8375234177108291195467469 3140712816415609198300301)
              ·
                refine ⟨1177767306155853449362613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3140712816415609198300301 1177767306155853449362613)
                ·
                  refine ⟨110415684952111260877745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1177767306155853449362613 110415684952111260877745)
                  ·
                    rfl

theorem cell23_1935304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 5].length) (baseStart_1935304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935304 prefixEnd_1935304 := by exact prefixLift 1935304
  have htrace : WordTrace (prefixWord ++ tailWord_1935304) baseStart_1935304 baseEnd_1935304 := by
    simpa [prefixWord, tailWord_1935304, baseEnd_1935304] using wordTrace_append hprefix tailTrace_1935304
  have hstable : (prefixWord ++ tailWord_1935304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935304).length < 2 ^ (prefixWord ++ tailWord_1935304).sum := by decide
  have hdescent : baseEnd_1935304 < baseStart_1935304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935317 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_1935317 : Nat := 118140960795 + 1935317 * 2 ^ 59
def prefixEnd_1935317 : Nat := 4983230072969 + 3 ^ 40 * 1935317 * 2
def baseEnd_1935317 : Nat := 331249279939169932345715

theorem tailTrace_1935317 : CollatzResearch.WordTrace tailWord_1935317 prefixEnd_1935317 331249279939169932345715 := by
  unfold tailWord_1935317
  simp only [CollatzResearch.WordTrace]
  refine ⟨70586809929684509674204205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47057873286456339782802803 70586809929684509674204205)
  ·
    refine ⟨26470053723631691127826577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70586809929684509674204205 26470053723631691127826577)
    ·
      refine ⟨19852540292723768345869933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26470053723631691127826577 19852540292723768345869933)
      ·
        refine ⟨7444702609771413129701225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19852540292723768345869933 7444702609771413129701225)
        ·
          refine ⟨5583526957328559847275919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444702609771413129701225 5583526957328559847275919)
          ·
            refine ⟨8375290435992839770913879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583526957328559847275919 8375290435992839770913879)
            ·
              refine ⟨12562935653989259656370819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375290435992839770913879 12562935653989259656370819)
              ·
                refine ⟨18844403480983889484556229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12562935653989259656370819 18844403480983889484556229)
                ·
                  refine ⟨3533325652684479278354293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18844403480983889484556229 3533325652684479278354293)
                  ·
                    refine ⟨331249279939169932345715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3533325652684479278354293 331249279939169932345715)
                    ·
                      rfl

theorem cell23_1935317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_1935317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935317 prefixEnd_1935317 := by exact prefixLift 1935317
  have htrace : WordTrace (prefixWord ++ tailWord_1935317) baseStart_1935317 baseEnd_1935317 := by
    simpa [prefixWord, tailWord_1935317, baseEnd_1935317] using wordTrace_append hprefix tailTrace_1935317
  have hstable : (prefixWord ++ tailWord_1935317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935317).length < 2 ^ (prefixWord ++ tailWord_1935317).sum := by decide
  have hdescent : baseEnd_1935317 < baseStart_1935317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935321 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 5]
def baseStart_1935321 : Nat := 118140960795 + 1935321 * 2 ^ 59
def prefixEnd_1935321 : Nat := 4983230072969 + 3 ^ 40 * 1935321 * 2
def baseEnd_1935321 : Nat := 110416654860014197931903

theorem tailTrace_1935321 : CollatzResearch.WordTrace tailWord_1935321 prefixEnd_1935321 110416654860014197931903 := by
  unfold tailWord_1935321
  simp only [CollatzResearch.WordTrace]
  refine ⟨70586955821670018357349817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47057970547780012238233211 70586955821670018357349817)
  ·
    refine ⟨52940216866252513768012363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70586955821670018357349817 52940216866252513768012363)
    ·
      refine ⟨79410325299378770652018545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52940216866252513768012363 79410325299378770652018545)
      ·
        refine ⟨59557743974534077989013909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79410325299378770652018545 59557743974534077989013909)
        ·
          refine ⟨2791769248806284905735027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59557743974534077989013909 2791769248806284905735027)
          ·
            refine ⟨4187653873209427358602541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791769248806284905735027 4187653873209427358602541)
            ·
              refine ⟨1570370202453535259475953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4187653873209427358602541 1570370202453535259475953)
              ·
                refine ⟨1177777651840151444606965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1570370202453535259475953 1177777651840151444606965)
                ·
                  refine ⟨110416654860014197931903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1177777651840151444606965 110416654860014197931903)
                  ·
                    rfl

theorem cell23_1935321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 5].length) (baseStart_1935321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935321 prefixEnd_1935321 := by exact prefixLift 1935321
  have htrace : WordTrace (prefixWord ++ tailWord_1935321) baseStart_1935321 baseEnd_1935321 := by
    simpa [prefixWord, tailWord_1935321, baseEnd_1935321] using wordTrace_append hprefix tailTrace_1935321
  have hstable : (prefixWord ++ tailWord_1935321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935321).length < 2 ^ (prefixWord ++ tailWord_1935321).sum := by decide
  have hdescent : baseEnd_1935321 < baseStart_1935321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935327 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_1935327 : Nat := 118140960795 + 1935327 * 2 ^ 59
def prefixEnd_1935327 : Nat := 4983230072969 + 3 ^ 40 * 1935327 * 2
def baseEnd_1935327 : Nat := 993752974624054757912099

theorem tailTrace_1935327 : CollatzResearch.WordTrace tailWord_1935327 prefixEnd_1935327 993752974624054757912099 := by
  unfold tailWord_1935327
  simp only [CollatzResearch.WordTrace]
  refine ⟨70587174659648281382068235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47058116439765520921378823 70587174659648281382068235)
  ·
    refine ⟨105880761989472422073102353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70587174659648281382068235 105880761989472422073102353)
    ·
      refine ⟨79410571492104316554826765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105880761989472422073102353 79410571492104316554826765)
      ·
        refine ⟨29778964309539118708060037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79410571492104316554826765 29778964309539118708060037)
        ·
          refine ⟨5583555808038584757761257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29778964309539118708060037 5583555808038584757761257)
          ·
            refine ⟨4187666856028938568320943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5583555808038584757761257 4187666856028938568320943)
            ·
              refine ⟨6281500284043407852481415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187666856028938568320943 6281500284043407852481415)
              ·
                refine ⟨9422250426065111778722123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281500284043407852481415 9422250426065111778722123)
                ·
                  refine ⟨14133375639097667668083185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422250426065111778722123 14133375639097667668083185)
                  ·
                    refine ⟨10600031729323250751062389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14133375639097667668083185 10600031729323250751062389)
                    ·
                      refine ⟨993752974624054757912099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10600031729323250751062389 993752974624054757912099)
                      ·
                        rfl

theorem cell23_1935327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_1935327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935327 prefixEnd_1935327 := by exact prefixLift 1935327
  have htrace : WordTrace (prefixWord ++ tailWord_1935327) baseStart_1935327 baseEnd_1935327 := by
    simpa [prefixWord, tailWord_1935327, baseEnd_1935327] using wordTrace_append hprefix tailTrace_1935327
  have hstable : (prefixWord ++ tailWord_1935327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935327).length < 2 ^ (prefixWord ++ tailWord_1935327).sum := by decide
  have hdescent : baseEnd_1935327 < baseStart_1935327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935340 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1935340 : Nat := 118140960795 + 1935340 * 2 ^ 59
def prefixEnd_1935340 : Nat := 4983230072969 + 3 ^ 40 * 1935340 * 2
def baseEnd_1935340 : Nat := 993759649872563207049539

theorem tailTrace_1935340 : CollatzResearch.WordTrace tailWord_1935340 prefixEnd_1935340 993759649872563207049539 := by
  unfold tailWord_1935340
  simp only [CollatzResearch.WordTrace]
  refine ⟨35293824404300592301145737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47058432539067456401527649 35293824404300592301145737)
  ·
    refine ⟨26470368303225444225859303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35293824404300592301145737 26470368303225444225859303)
    ·
      refine ⟨39705552454838166338788955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26470368303225444225859303 39705552454838166338788955)
      ·
        refine ⟨59558328682257249508183433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39705552454838166338788955 59558328682257249508183433)
        ·
          refine ⟨44668746511692937131137575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59558328682257249508183433 44668746511692937131137575)
          ·
            refine ⟨67003119767539405696706363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44668746511692937131137575 67003119767539405696706363)
            ·
              refine ⟨100504679651309108545059545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67003119767539405696706363 100504679651309108545059545)
              ·
                refine ⟨75378509738481831408794659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100504679651309108545059545 75378509738481831408794659)
                ·
                  refine ⟨113067764607722747113191989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75378509738481831408794659 113067764607722747113191989)
                  ·
                    refine ⟨10600102931974007541861749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113067764607722747113191989 10600102931974007541861749)
                    ·
                      refine ⟨993759649872563207049539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10600102931974007541861749 993759649872563207049539)
                      ·
                        rfl

theorem cell23_1935340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1935340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935340 prefixEnd_1935340 := by exact prefixLift 1935340
  have htrace : WordTrace (prefixWord ++ tailWord_1935340) baseStart_1935340 baseEnd_1935340 := by
    simpa [prefixWord, tailWord_1935340, baseEnd_1935340] using wordTrace_append hprefix tailTrace_1935340
  have hstable : (prefixWord ++ tailWord_1935340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935340).length < 2 ^ (prefixWord ++ tailWord_1935340).sum := by decide
  have hdescent : baseEnd_1935340 < baseStart_1935340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935347 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 3, 4]
def baseStart_1935347 : Nat := 118140960795 + 1935347 * 2 ^ 59
def prefixEnd_1935347 : Nat := 4983230072969 + 3 ^ 40 * 1935347 * 2
def baseEnd_1935347 : Nat := 331254414745714893220669

theorem tailTrace_1935347 : CollatzResearch.WordTrace tailWord_1935347 prefixEnd_1935347 331254414745714893220669 := by
  unfold tailWord_1935347
  simp only [CollatzResearch.WordTrace]
  refine ⟨70587904119575824797796295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47058602746383883198530863 70587904119575824797796295)
  ·
    refine ⟨105881856179363737196694443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70587904119575824797796295 105881856179363737196694443)
    ·
      refine ⟨158822784269045605795041665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105881856179363737196694443 158822784269045605795041665)
      ·
        refine ⟨119117088201784204346281249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158822784269045605795041665 119117088201784204346281249)
        ·
          refine ⟨89337816151338153259710937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119117088201784204346281249 89337816151338153259710937)
          ·
            refine ⟨67003362113503614944783203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89337816151338153259710937 67003362113503614944783203)
            ·
              refine ⟨100505043170255422417174805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67003362113503614944783203 100505043170255422417174805)
              ·
                refine ⟨4711173898605722925805069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100505043170255422417174805 4711173898605722925805069)
                ·
                  refine ⟨1766690211977146097176901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4711173898605722925805069 1766690211977146097176901)
                  ·
                    refine ⟨331254414745714893220669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1766690211977146097176901 331254414745714893220669)
                    ·
                      rfl

theorem cell23_1935347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 4].length) (baseStart_1935347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935347 prefixEnd_1935347 := by exact prefixLift 1935347
  have htrace : WordTrace (prefixWord ++ tailWord_1935347) baseStart_1935347 baseEnd_1935347 := by
    simpa [prefixWord, tailWord_1935347, baseEnd_1935347] using wordTrace_append hprefix tailTrace_1935347
  have hstable : (prefixWord ++ tailWord_1935347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935347).length < 2 ^ (prefixWord ++ tailWord_1935347).sum := by decide
  have hdescent : baseEnd_1935347 < baseStart_1935347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935357 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_1935357 : Nat := 118140960795 + 1935357 * 2 ^ 59
def prefixEnd_1935357 : Nat := 4983230072969 + 3 ^ 40 * 1935357 * 2
def baseEnd_1935357 : Nat := 993768379043689640536961

theorem tailTrace_1935357 : CollatzResearch.WordTrace tailWord_1935357 prefixEnd_1935357 993768379043689640536961 := by
  unfold tailWord_1935357
  simp only [CollatzResearch.WordTrace]
  refine ⟨70588268849539596505660325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47058845899693064337106883 70588268849539596505660325)
  ·
    refine ⟨13235300409288674344811311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70588268849539596505660325 13235300409288674344811311)
    ·
      refine ⟨19852950613933011517216967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13235300409288674344811311 19852950613933011517216967)
      ·
        refine ⟨29779425920899517275825451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19852950613933011517216967 29779425920899517275825451)
        ·
          refine ⟨44669138881349275913738177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29779425920899517275825451 44669138881349275913738177)
          ·
            refine ⟨33501854161011956935303633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44669138881349275913738177 33501854161011956935303633)
            ·
              refine ⟨25126390620758967701477725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33501854161011956935303633 25126390620758967701477725)
              ·
                refine ⟨9422396482784612888054147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25126390620758967701477725 9422396482784612888054147)
                ·
                  refine ⟨14133594724176919332081221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422396482784612888054147 14133594724176919332081221)
                  ·
                    refine ⟨2650049010783172374765229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14133594724176919332081221 2650049010783172374765229)
                    ·
                      refine ⟨993768379043689640536961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2650049010783172374765229 993768379043689640536961)
                      ·
                        rfl

theorem cell23_1935357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_1935357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935357 prefixEnd_1935357 := by exact prefixLift 1935357
  have htrace : WordTrace (prefixWord ++ tailWord_1935357) baseStart_1935357 baseEnd_1935357 := by
    simpa [prefixWord, tailWord_1935357, baseEnd_1935357] using wordTrace_append hprefix tailTrace_1935357
  have hstable : (prefixWord ++ tailWord_1935357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935357).length < 2 ^ (prefixWord ++ tailWord_1935357).sum := by decide
  have hdescent : baseEnd_1935357 < baseStart_1935357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935360 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 8]
def baseStart_1935360 : Nat := 118140960795 + 1935360 * 2 ^ 59
def prefixEnd_1935360 : Nat := 4983230072969 + 3 ^ 40 * 1935360 * 2
def baseEnd_1935360 : Nat := 110418879942850347644383

theorem tailTrace_1935360 : CollatzResearch.WordTrace tailWord_1935360 prefixEnd_1935360 110418879942850347644383 := by
  unfold tailWord_1935360
  simp only [CollatzResearch.WordTrace]
  refine ⟨35294189134264364009009767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47058918845685818678679689 35294189134264364009009767)
  ·
    refine ⟨52941283701396546013514651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35294189134264364009009767 52941283701396546013514651)
    ·
      refine ⟨79411925552094819020271977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52941283701396546013514651 79411925552094819020271977)
      ·
        refine ⟨59558944164071114265203983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79411925552094819020271977 59558944164071114265203983)
        ·
          refine ⟨89338416246106671397805975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59558944164071114265203983 89338416246106671397805975)
          ·
            refine ⟨134007624369160007096708963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89338416246106671397805975 134007624369160007096708963)
            ·
              refine ⟨201011436553740010645063445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134007624369160007096708963 201011436553740010645063445)
              ·
                refine ⟨9422411088456562998987349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 201011436553740010645063445 9422411088456562998987349)
                ·
                  refine ⟨110418879942850347644383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9422411088456562998987349 110418879942850347644383)
                  ·
                    rfl

theorem cell23_1935360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_1935360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935360 prefixEnd_1935360 := by exact prefixLift 1935360
  have htrace : WordTrace (prefixWord ++ tailWord_1935360) baseStart_1935360 baseEnd_1935360 := by
    simpa [prefixWord, tailWord_1935360, baseEnd_1935360] using wordTrace_append hprefix tailTrace_1935360
  have hstable : (prefixWord ++ tailWord_1935360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935360).length < 2 ^ (prefixWord ++ tailWord_1935360).sum := by decide
  have hdescent : baseEnd_1935360 < baseStart_1935360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935374 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1935374 : Nat := 118140960795 + 1935374 * 2 ^ 59
def prefixEnd_1935374 : Nat := 4983230072969 + 3 ^ 40 * 1935374 * 2
def baseEnd_1935374 : Nat := 993777108214816074024383

theorem tailTrace_1935374 : CollatzResearch.WordTrace tailWord_1935374 prefixEnd_1935374 993777108214816074024383 := by
  unfold tailWord_1935374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823611111309751051128647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47059259260318672272686117 8823611111309751051128647)
  ·
    refine ⟨13235416666964626576692971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8823611111309751051128647 13235416666964626576692971)
    ·
      refine ⟨19853125000446939865039457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13235416666964626576692971 19853125000446939865039457)
      ·
        refine ⟨14889843750335204898779593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19853125000446939865039457 14889843750335204898779593)
        ·
          refine ⟨11167382812751403674084695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14889843750335204898779593 11167382812751403674084695)
          ·
            refine ⟨16751074219127105511127043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11167382812751403674084695 16751074219127105511127043)
            ·
              refine ⟨25126611328690658266690565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16751074219127105511127043 25126611328690658266690565)
              ·
                refine ⟨4711239624129498425004481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25126611328690658266690565 4711239624129498425004481)
                ·
                  refine ⟨3533429718097123818753361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4711239624129498425004481 3533429718097123818753361)
                  ·
                    refine ⟨2650072288572842864065021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533429718097123818753361 2650072288572842864065021)
                    ·
                      refine ⟨993777108214816074024383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2650072288572842864065021 993777108214816074024383)
                      ·
                        rfl

theorem cell23_1935374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1935374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935374 prefixEnd_1935374 := by exact prefixLift 1935374
  have htrace : WordTrace (prefixWord ++ tailWord_1935374) baseStart_1935374 baseEnd_1935374 := by
    simpa [prefixWord, tailWord_1935374, baseEnd_1935374] using wordTrace_append hprefix tailTrace_1935374
  have hstable : (prefixWord ++ tailWord_1935374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935374).length < 2 ^ (prefixWord ++ tailWord_1935374).sum := by decide
  have hdescent : baseEnd_1935374 < baseStart_1935374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935424 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_1935424 : Nat := 118140960795 + 1935424 * 2 ^ 59
def prefixEnd_1935424 : Nat := 4983230072969 + 3 ^ 40 * 1935424 * 2
def baseEnd_1935424 : Nat := 331267594082513626133051

theorem tailTrace_1935424 : CollatzResearch.WordTrace tailWord_1935424 prefixEnd_1935424 331267594082513626133051 := by
  unfold tailWord_1935424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35295356270148433474174663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47060475026864577965566217 35295356270148433474174663)
  ·
    refine ⟨52943034405222650211261995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35295356270148433474174663 52943034405222650211261995)
    ·
      refine ⟨79414551607833975316892993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52943034405222650211261995 79414551607833975316892993)
      ·
        refine ⟨59560913705875481487669745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79414551607833975316892993 59560913705875481487669745)
        ·
          refine ⟨44670685279406611115752309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59560913705875481487669745 44670685279406611115752309)
          ·
            refine ⟨4187876744944369792101779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44670685279406611115752309 4187876744944369792101779)
            ·
              refine ⟨6281815117416554688152669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4187876744944369792101779 6281815117416554688152669)
              ·
                refine ⟨2355680669031208008057251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6281815117416554688152669 2355680669031208008057251)
                ·
                  refine ⟨3533521003546812012085877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355680669031208008057251 3533521003546812012085877)
                  ·
                    refine ⟨331267594082513626133051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3533521003546812012085877 331267594082513626133051)
                    ·
                      rfl

theorem cell23_1935424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_1935424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935424 prefixEnd_1935424 := by exact prefixLift 1935424
  have htrace : WordTrace (prefixWord ++ tailWord_1935424) baseStart_1935424 baseEnd_1935424 := by
    simpa [prefixWord, tailWord_1935424, baseEnd_1935424] using wordTrace_append hprefix tailTrace_1935424
  have hstable : (prefixWord ++ tailWord_1935424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935424).length < 2 ^ (prefixWord ++ tailWord_1935424).sum := by decide
  have hdescent : baseEnd_1935424 < baseStart_1935424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935427 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4]
def baseStart_1935427 : Nat := 118140960795 + 1935427 * 2 ^ 59
def prefixEnd_1935427 : Nat := 4983230072969 + 3 ^ 40 * 1935427 * 2
def baseEnd_1935427 : Nat := 993804322689504366661639

theorem tailTrace_1935427 : CollatzResearch.WordTrace tailWord_1935427 prefixEnd_1935427 993804322689504366661639 := by
  unfold tailWord_1935427
  simp only [CollatzResearch.WordTrace]
  refine ⟨70590821959285998460708535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47060547972857332307139023 70590821959285998460708535)
  ·
    refine ⟨105886232938928997691062803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70590821959285998460708535 105886232938928997691062803)
    ·
      refine ⟨158829349408393496536594205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105886232938928997691062803 158829349408393496536594205)
      ·
        refine ⟨59561006028147561201222827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158829349408393496536594205 59561006028147561201222827)
        ·
          refine ⟨89341509042221341801834241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59561006028147561201222827 89341509042221341801834241)
          ·
            refine ⟨67006131781666006351375681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89341509042221341801834241 67006131781666006351375681)
            ·
              refine ⟨50254598836249504763531761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67006131781666006351375681 50254598836249504763531761)
              ·
                refine ⟨37690949127187128572648821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50254598836249504763531761 37690949127187128572648821)
                ·
                  refine ⟨3533526480673793303685827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37690949127187128572648821 3533526480673793303685827)
                  ·
                    refine ⟨5300289721010689955528741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3533526480673793303685827 5300289721010689955528741)
                    ·
                      refine ⟨993804322689504366661639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5300289721010689955528741 993804322689504366661639)
                      ·
                        rfl

theorem cell23_1935427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_1935427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935427 prefixEnd_1935427 := by exact prefixLift 1935427
  have htrace : WordTrace (prefixWord ++ tailWord_1935427) baseStart_1935427 baseEnd_1935427 := by
    simpa [prefixWord, tailWord_1935427, baseEnd_1935427] using wordTrace_append hprefix tailTrace_1935427
  have hstable : (prefixWord ++ tailWord_1935427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935427).length < 2 ^ (prefixWord ++ tailWord_1935427).sum := by decide
  have hdescent : baseEnd_1935427 < baseStart_1935427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935438 : List Nat := [4, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3]
def baseStart_1935438 : Nat := 118140960795 + 1935438 * 2 ^ 59
def prefixEnd_1935438 : Nat := 4983230072969 + 3 ^ 40 * 1935438 * 2
def baseEnd_1935438 : Nat := 993809970976703823624089

theorem tailTrace_1935438 : CollatzResearch.WordTrace tailWord_1935438 prefixEnd_1935438 993809970976703823624089 := by
  unfold tailWord_1935438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8823902895280768417419871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47060815441497431559572645 8823902895280768417419871)
  ·
    refine ⟨13235854342921152626129807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8823902895280768417419871 13235854342921152626129807)
    ·
      refine ⟨19853781514381728939194711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13235854342921152626129807 19853781514381728939194711)
      ·
        refine ⟨29780672271572593408792067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19853781514381728939194711 29780672271572593408792067)
        ·
          refine ⟨44671008407358890113188101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29780672271572593408792067 44671008407358890113188101)
          ·
            refine ⟨8375814076379791896222769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44671008407358890113188101 8375814076379791896222769)
            ·
              refine ⟨6281860557284843922167077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8375814076379791896222769 6281860557284843922167077)
              ·
                refine ⟨1177848854490908235406327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6281860557284843922167077 1177848854490908235406327)
                ·
                  refine ⟨1766773281736362353109491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1177848854490908235406327 1766773281736362353109491)
                  ·
                    refine ⟨2650159922604543529664237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1766773281736362353109491 2650159922604543529664237)
                    ·
                      refine ⟨993809970976703823624089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2650159922604543529664237 993809970976703823624089)
                      ·
                        rfl

theorem cell23_1935438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3].length) (baseStart_1935438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935438 prefixEnd_1935438 := by exact prefixLift 1935438
  have htrace : WordTrace (prefixWord ++ tailWord_1935438) baseStart_1935438 baseEnd_1935438 := by
    simpa [prefixWord, tailWord_1935438, baseEnd_1935438] using wordTrace_append hprefix tailTrace_1935438
  have hstable : (prefixWord ++ tailWord_1935438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935438).length < 2 ^ (prefixWord ++ tailWord_1935438).sum := by decide
  have hdescent : baseEnd_1935438 < baseStart_1935438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935447 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1935447 : Nat := 118140960795 + 1935447 * 2 ^ 59
def prefixEnd_1935447 : Nat := 4983230072969 + 3 ^ 40 * 1935447 * 2
def baseEnd_1935447 : Nat := 993814592302594288411547

theorem tailTrace_1935447 : CollatzResearch.WordTrace tailWord_1935447 prefixEnd_1935447 993814592302594288411547 := by
  unfold tailWord_1935447
  simp only [CollatzResearch.WordTrace]
  refine ⟨70591551419213541876436595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47061034279475694584291063 70591551419213541876436595)
  ·
    refine ⟨105887327128820312814654893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70591551419213541876436595 105887327128820312814654893)
    ·
      refine ⟨39707747673307617305495585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105887327128820312814654893 39707747673307617305495585)
      ·
        refine ⟨29780810754980712979121689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39707747673307617305495585 29780810754980712979121689)
        ·
          refine ⟨22335608066235534734341267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29780810754980712979121689 22335608066235534734341267)
          ·
            refine ⟨33503412099353302101511901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22335608066235534734341267 33503412099353302101511901)
            ·
              refine ⟨12563779537257488288066963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33503412099353302101511901 12563779537257488288066963)
              ·
                refine ⟨18845669305886232432100445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563779537257488288066963 18845669305886232432100445)
                ·
                  refine ⟨7067125989707337162037667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18845669305886232432100445 7067125989707337162037667)
                  ·
                    refine ⟨10600688984561005743056501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7067125989707337162037667 10600688984561005743056501)
                    ·
                      refine ⟨993814592302594288411547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10600688984561005743056501 993814592302594288411547)
                      ·
                        rfl

theorem cell23_1935447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1935447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935447 prefixEnd_1935447 := by exact prefixLift 1935447
  have htrace : WordTrace (prefixWord ++ tailWord_1935447) baseStart_1935447 baseEnd_1935447 := by
    simpa [prefixWord, tailWord_1935447, baseEnd_1935447] using wordTrace_append hprefix tailTrace_1935447
  have hstable : (prefixWord ++ tailWord_1935447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935447).length < 2 ^ (prefixWord ++ tailWord_1935447).sum := by decide
  have hdescent : baseEnd_1935447 < baseStart_1935447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935458 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1935458 : Nat := 118140960795 + 1935458 * 2 ^ 59
def prefixEnd_1935458 : Nat := 4983230072969 + 3 ^ 40 * 1935458 * 2
def baseEnd_1935458 : Nat := 331273413529931248457999

theorem tailTrace_1935458 : CollatzResearch.WordTrace tailWord_1935458 prefixEnd_1935458 331273413529931248457999 := by
  unfold tailWord_1935458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17647988155543422688771757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47061301748115793836724685 17647988155543422688771757)
  ·
    refine ⟨6617995558328783508289409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17647988155543422688771757 6617995558328783508289409)
    ·
      refine ⟨4963496668746587631217057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6617995558328783508289409 4963496668746587631217057)
      ·
        refine ⟨3722622501559940723412793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4963496668746587631217057 3722622501559940723412793)
        ·
          refine ⟨2791966876169955542559595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3722622501559940723412793 2791966876169955542559595)
          ·
            refine ⟨4187950314254933313839393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2791966876169955542559595 4187950314254933313839393)
            ·
              refine ⟨3140962735691199985379545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4187950314254933313839393 3140962735691199985379545)
              ·
                refine ⟨2355722051768399989034659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140962735691199985379545 2355722051768399989034659)
                ·
                  refine ⟨3533583077652599983551989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355722051768399989034659 3533583077652599983551989)
                  ·
                    refine ⟨331273413529931248457999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3533583077652599983551989 331273413529931248457999)
                    ·
                      rfl

theorem cell23_1935458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1935458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935458 prefixEnd_1935458 := by exact prefixLift 1935458
  have htrace : WordTrace (prefixWord ++ tailWord_1935458) baseStart_1935458 baseEnd_1935458 := by
    simpa [prefixWord, tailWord_1935458, baseEnd_1935458] using wordTrace_append hprefix tailTrace_1935458
  have hstable : (prefixWord ++ tailWord_1935458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935458).length < 2 ^ (prefixWord ++ tailWord_1935458).sum := by decide
  have hdescent : baseEnd_1935458 < baseStart_1935458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935461 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1935461 : Nat := 118140960795 + 1935461 * 2 ^ 59
def prefixEnd_1935461 : Nat := 4983230072969 + 3 ^ 40 * 1935461 * 2
def baseEnd_1935461 : Nat := 993821781031757233636483

theorem tailTrace_1935461 : CollatzResearch.WordTrace tailWord_1935461 prefixEnd_1935461 993821781031757233636483 := by
  unfold tailWord_1935461
  simp only [CollatzResearch.WordTrace]
  refine ⟨70592062041162822267446237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47061374694108548178297491 70592062041162822267446237)
  ·
    refine ⟨26472023265436058350292339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70592062041162822267446237 26472023265436058350292339)
    ·
      refine ⟨39708034898154087525438509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26472023265436058350292339 39708034898154087525438509)
      ·
        refine ⟨14890513086807782822039441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39708034898154087525438509 14890513086807782822039441)
        ·
          refine ⟨11167884815105837116529581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14890513086807782822039441 11167884815105837116529581)
          ·
            refine ⟨4187956805664688918698593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11167884815105837116529581 4187956805664688918698593)
            ·
              refine ⟨3140967604248516689023945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4187956805664688918698593 3140967604248516689023945)
              ·
                refine ⟨2355725703186387516767959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3140967604248516689023945 2355725703186387516767959)
                ·
                  refine ⟨3533588554779581275151939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355725703186387516767959 3533588554779581275151939)
                  ·
                    refine ⟨5300382832169371912727909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3533588554779581275151939 5300382832169371912727909)
                    ·
                      refine ⟨993821781031757233636483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5300382832169371912727909 993821781031757233636483)
                      ·
                        rfl

theorem cell23_1935461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1935461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935461 prefixEnd_1935461 := by exact prefixLift 1935461
  have htrace : WordTrace (prefixWord ++ tailWord_1935461) baseStart_1935461 baseEnd_1935461 := by
    simpa [prefixWord, tailWord_1935461, baseEnd_1935461] using wordTrace_append hprefix tailTrace_1935461
  have hstable : (prefixWord ++ tailWord_1935461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935461).length < 2 ^ (prefixWord ++ tailWord_1935461).sum := by decide
  have hdescent : baseEnd_1935461 < baseStart_1935461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935481 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_1935481 : Nat := 118140960795 + 1935481 * 2 ^ 59
def prefixEnd_1935481 : Nat := 4983230072969 + 3 ^ 40 * 1935481 * 2
def baseEnd_1935481 : Nat := 993832050644847155386391

theorem tailTrace_1935481 : CollatzResearch.WordTrace tailWord_1935481 prefixEnd_1935481 993832050644847155386391 := by
  unfold tailWord_1935481
  simp only [CollatzResearch.WordTrace]
  refine ⟨70592791501090365683174297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47061861000726910455449531 70592791501090365683174297)
  ·
    refine ⟨52944593625817774262380723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70592791501090365683174297 52944593625817774262380723)
    ·
      refine ⟨79416890438726661393571085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52944593625817774262380723 79416890438726661393571085)
      ·
        refine ⟨29781333914522498022589157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79416890438726661393571085 29781333914522498022589157)
        ·
          refine ⟨5584000108972968379235467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29781333914522498022589157 5584000108972968379235467)
          ·
            refine ⟨8376000163459452568853201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584000108972968379235467 8376000163459452568853201)
            ·
              refine ⟨6282000122594589426639901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8376000163459452568853201 6282000122594589426639901)
              ·
                refine ⟨2355750045972971034989963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6282000122594589426639901 2355750045972971034989963)
                ·
                  refine ⟨3533625068959456552484945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2355750045972971034989963 3533625068959456552484945)
                  ·
                    refine ⟨2650218801719592414363709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3533625068959456552484945 2650218801719592414363709)
                    ·
                      refine ⟨993832050644847155386391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2650218801719592414363709 993832050644847155386391)
                      ·
                        rfl

theorem cell23_1935481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_1935481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935481 prefixEnd_1935481 := by exact prefixLift 1935481
  have htrace : WordTrace (prefixWord ++ tailWord_1935481) baseStart_1935481 baseEnd_1935481 := by
    simpa [prefixWord, tailWord_1935481, baseEnd_1935481] using wordTrace_append hprefix tailTrace_1935481
  have hstable : (prefixWord ++ tailWord_1935481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935481).length < 2 ^ (prefixWord ++ tailWord_1935481).sum := by decide
  have hdescent : baseEnd_1935481 < baseStart_1935481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935497 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_1935497 : Nat := 118140960795 + 1935497 * 2 ^ 59
def prefixEnd_1935497 : Nat := 4983230072969 + 3 ^ 40 * 1935497 * 2
def baseEnd_1935497 : Nat := 331280088778439697595439

theorem tailTrace_1935497 : CollatzResearch.WordTrace tailWord_1935497 prefixEnd_1935497 331280088778439697595439 := by
  unfold tailWord_1935497
  simp only [CollatzResearch.WordTrace]
  refine ⟨70593375069032400415756745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47062250046021600277171163 70593375069032400415756745)
  ·
    refine ⟨52945031301774300311817559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70593375069032400415756745 52945031301774300311817559)
    ·
      refine ⟨79417546952661450467726339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52945031301774300311817559 79417546952661450467726339)
      ·
        refine ⟨119126320428992175701589509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79417546952661450467726339 119126320428992175701589509)
        ·
          refine ⟨22336185080436032944048033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119126320428992175701589509 22336185080436032944048033)
          ·
            refine ⟨16752138810327024708036025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22336185080436032944048033 16752138810327024708036025)
            ·
              refine ⟨12564104107745268531027019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16752138810327024708036025 12564104107745268531027019)
              ·
                refine ⟨18846156161617902796540529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12564104107745268531027019 18846156161617902796540529)
                ·
                  refine ⟨14134617121213427097405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18846156161617902796540529 14134617121213427097405397)
                  ·
                    refine ⟨331280088778439697595439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14134617121213427097405397 331280088778439697595439)
                    ·
                      rfl

theorem cell23_1935497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_1935497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935497 prefixEnd_1935497 := by exact prefixLift 1935497
  have htrace : WordTrace (prefixWord ++ tailWord_1935497) baseStart_1935497 baseEnd_1935497 := by
    simpa [prefixWord, tailWord_1935497, baseEnd_1935497] using wordTrace_append hprefix tailTrace_1935497
  have hstable : (prefixWord ++ tailWord_1935497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935497).length < 2 ^ (prefixWord ++ tailWord_1935497).sum := by decide
  have hdescent : baseEnd_1935497 < baseStart_1935497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935584 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1935584 : Nat := 118140960795 + 1935584 * 2 ^ 59
def prefixEnd_1935584 : Nat := 4983230072969 + 3 ^ 40 * 1935584 * 2
def baseEnd_1935584 : Nat := 993884939152260252398417

theorem tailTrace_1935584 : CollatzResearch.WordTrace tailWord_1935584 prefixEnd_1935584 993884939152260252398417 := by
  unfold tailWord_1935584
  simp only [CollatzResearch.WordTrace]
  refine ⟨35298274109858607137086903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47064365479811476182782537 35298274109858607137086903)
  ·
    refine ⟨52947411164787910705630355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35298274109858607137086903 52947411164787910705630355)
    ·
      refine ⟨79421116747181866058445533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52947411164787910705630355 79421116747181866058445533)
      ·
        refine ⟨29782918780193199771917075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79421116747181866058445533 29782918780193199771917075)
        ·
          refine ⟨44674378170289799657875613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29782918780193199771917075 44674378170289799657875613)
          ·
            refine ⟨16752891813858674871703355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44674378170289799657875613 16752891813858674871703355)
            ·
              refine ⟨25129337720788012307555033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16752891813858674871703355 25129337720788012307555033)
              ·
                refine ⟨18847003290591009230666275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25129337720788012307555033 18847003290591009230666275)
                ·
                  refine ⟨28270504935886513845999413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18847003290591009230666275 28270504935886513845999413)
                  ·
                    refine ⟨2650359837739360673062445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28270504935886513845999413 2650359837739360673062445)
                    ·
                      refine ⟨993884939152260252398417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2650359837739360673062445 993884939152260252398417)
                      ·
                        rfl

theorem cell23_1935584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1935584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935584 prefixEnd_1935584 := by exact prefixLift 1935584
  have htrace : WordTrace (prefixWord ++ tailWord_1935584) baseStart_1935584 baseEnd_1935584 := by
    simpa [prefixWord, tailWord_1935584, baseEnd_1935584] using wordTrace_append hprefix tailTrace_1935584
  have hstable : (prefixWord ++ tailWord_1935584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935584).length < 2 ^ (prefixWord ++ tailWord_1935584).sum := by decide
  have hdescent : baseEnd_1935584 < baseStart_1935584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935602 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 2, 2, 2]
def baseStart_1935602 : Nat := 118140960795 + 1935602 * 2 ^ 59
def prefixEnd_1935602 : Nat := 4983230072969 + 3 ^ 40 * 1935602 * 2
def baseEnd_1935602 : Nat := 993894181804041181973335

theorem tailTrace_1935602 : CollatzResearch.WordTrace tailWord_1935602 prefixEnd_1935602 993894181804041181973335 := by
  unfold tailWord_1935602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649301183413000837082265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47064803155768002232219373 17649301183413000837082265)
  ·
    refine ⟨13236975887559750627811699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17649301183413000837082265 13236975887559750627811699)
    ·
      refine ⟨19855463831339625941717549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13236975887559750627811699 19855463831339625941717549)
      ·
        refine ⟨7445798936752359728144081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19855463831339625941717549 7445798936752359728144081)
        ·
          refine ⟨5584349202564269796108061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445798936752359728144081 5584349202564269796108061)
          ·
            refine ⟨2094130950961601173540523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5584349202564269796108061 2094130950961601173540523)
            ·
              refine ⟨3141196426442401760310785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094130950961601173540523 3141196426442401760310785)
              ·
                refine ⟨2355897319831801320233089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141196426442401760310785 2355897319831801320233089)
                ·
                  refine ⟨1766922989873850990174817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2355897319831801320233089 1766922989873850990174817)
                  ·
                    refine ⟨1325192242405388242631113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1766922989873850990174817 1325192242405388242631113)
                    ·
                      refine ⟨993894181804041181973335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325192242405388242631113 993894181804041181973335)
                      ·
                        rfl

theorem cell23_1935602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_1935602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935602 prefixEnd_1935602 := by exact prefixLift 1935602
  have htrace : WordTrace (prefixWord ++ tailWord_1935602) baseStart_1935602 baseEnd_1935602 := by
    simpa [prefixWord, tailWord_1935602, baseEnd_1935602] using wordTrace_append hprefix tailTrace_1935602
  have hstable : (prefixWord ++ tailWord_1935602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935602).length < 2 ^ (prefixWord ++ tailWord_1935602).sum := by decide
  have hdescent : baseEnd_1935602 < baseStart_1935602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935618 : List Nat := [3, 4, 1, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1935618 : Nat := 118140960795 + 1935618 * 2 ^ 59
def prefixEnd_1935618 : Nat := 4983230072969 + 3 ^ 40 * 1935618 * 2
def baseEnd_1935618 : Nat := 993902397494513119373261

theorem tailTrace_1935618 : CollatzResearch.WordTrace tailWord_1935618 prefixEnd_1935618 993902397494513119373261 := by
  unfold tailWord_1935618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17649447075398509520227877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47065192201062692053941005 17649447075398509520227877)
  ·
    refine ⟨3309271326637220535042727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17649447075398509520227877 3309271326637220535042727)
    ·
      refine ⟨4963906989955830802564091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3309271326637220535042727 4963906989955830802564091)
      ·
        refine ⟨7445860484933746203846137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4963906989955830802564091 7445860484933746203846137)
        ·
          refine ⟨5584395363700309652884603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7445860484933746203846137 5584395363700309652884603)
          ·
            refine ⟨8376593045550464479326905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584395363700309652884603 8376593045550464479326905)
            ·
              refine ⟨6282444784162848359495179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8376593045550464479326905 6282444784162848359495179)
              ·
                refine ⟨9423667176244272539242769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6282444784162848359495179 9423667176244272539242769)
                ·
                  refine ⟨7067750382183204404432077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9423667176244272539242769 7067750382183204404432077)
                  ·
                    refine ⟨2650406393318701651662029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7067750382183204404432077 2650406393318701651662029)
                    ·
                      refine ⟨993902397494513119373261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2650406393318701651662029 993902397494513119373261)
                      ·
                        rfl

theorem cell23_1935618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1935618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935618 prefixEnd_1935618 := by exact prefixLift 1935618
  have htrace : WordTrace (prefixWord ++ tailWord_1935618) baseStart_1935618 baseEnd_1935618 := by
    simpa [prefixWord, tailWord_1935618, baseEnd_1935618] using wordTrace_append hprefix tailTrace_1935618
  have hstable : (prefixWord ++ tailWord_1935618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935618).length < 2 ^ (prefixWord ++ tailWord_1935618).sum := by decide
  have hdescent : baseEnd_1935618 < baseStart_1935618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935644 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1935644 : Nat := 118140960795 + 1935644 * 2 ^ 59
def prefixEnd_1935644 : Nat := 4983230072969 + 3 ^ 40 * 1935644 * 2
def baseEnd_1935644 : Nat := 993915747991530017648141

theorem tailTrace_1935644 : CollatzResearch.WordTrace tailWord_1935644 prefixEnd_1935644 993915747991530017648141 := by
  unfold tailWord_1935644
  simp only [CollatzResearch.WordTrace]
  refine ⟨35299368299749922260678993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47065824399666563014238657 35299368299749922260678993)
  ·
    refine ⟨26474526224812441695509245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35299368299749922260678993 26474526224812441695509245)
    ·
      refine ⟨9927947334304665635815967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26474526224812441695509245 9927947334304665635815967)
      ·
        refine ⟨14891921001456998453723951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9927947334304665635815967 14891921001456998453723951)
        ·
          refine ⟨22337881502185497680585927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14891921001456998453723951 22337881502185497680585927)
          ·
            refine ⟨33506822253278246520878891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22337881502185497680585927 33506822253278246520878891)
            ·
              refine ⟨50260233379917369781318337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33506822253278246520878891 50260233379917369781318337)
              ·
                refine ⟨37695175034938027335988753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50260233379917369781318337 37695175034938027335988753)
                ·
                  refine ⟨28271381276203520501991565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37695175034938027335988753 28271381276203520501991565)
                  ·
                    refine ⟨10601767978576320188246837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28271381276203520501991565 10601767978576320188246837)
                    ·
                      refine ⟨993915747991530017648141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10601767978576320188246837 993915747991530017648141)
                      ·
                        rfl

theorem cell23_1935644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1935644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935644 prefixEnd_1935644 := by exact prefixLift 1935644
  have htrace : WordTrace (prefixWord ++ tailWord_1935644) baseStart_1935644 baseEnd_1935644 := by
    simpa [prefixWord, tailWord_1935644, baseEnd_1935644] using wordTrace_append hprefix tailTrace_1935644
  have hstable : (prefixWord ++ tailWord_1935644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935644).length < 2 ^ (prefixWord ++ tailWord_1935644).sum := by decide
  have hdescent : baseEnd_1935644 < baseStart_1935644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935704 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1935704 : Nat := 118140960795 + 1935704 * 2 ^ 59
def prefixEnd_1935704 : Nat := 4983230072969 + 3 ^ 40 * 1935704 * 2
def baseEnd_1935704 : Nat := 993946556830799782897865

theorem tailTrace_1935704 : CollatzResearch.WordTrace tailWord_1935704 prefixEnd_1935704 993946556830799782897865 := by
  unfold tailWord_1935704
  simp only [CollatzResearch.WordTrace]
  refine ⟨35300462489641237384271083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47067283319521649845694777 35300462489641237384271083)
  ·
    refine ⟨52950693734461856076406625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35300462489641237384271083 52950693734461856076406625)
    ·
      refine ⟨39713020300846392057304969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52950693734461856076406625 39713020300846392057304969)
      ·
        refine ⟨29784765225634794042978727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39713020300846392057304969 29784765225634794042978727)
        ·
          refine ⟨44677147838452191064468091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29784765225634794042978727 44677147838452191064468091)
          ·
            refine ⟨67015721757678286596702137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44677147838452191064468091 67015721757678286596702137)
            ·
              refine ⟨50261791318258714947526603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67015721757678286596702137 50261791318258714947526603)
              ·
                refine ⟨75392686977388072421289905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50261791318258714947526603 75392686977388072421289905)
                ·
                  refine ⟨56544515233041054315967429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75392686977388072421289905 56544515233041054315967429)
                  ·
                    refine ⟨10602096606195197684243893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56544515233041054315967429 10602096606195197684243893)
                    ·
                      refine ⟨993946556830799782897865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10602096606195197684243893 993946556830799782897865)
                      ·
                        rfl

theorem cell23_1935704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1935704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935704 prefixEnd_1935704 := by exact prefixLift 1935704
  have htrace : WordTrace (prefixWord ++ tailWord_1935704) baseStart_1935704 baseEnd_1935704 := by
    simpa [prefixWord, tailWord_1935704, baseEnd_1935704] using wordTrace_append hprefix tailTrace_1935704
  have hstable : (prefixWord ++ tailWord_1935704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935704).length < 2 ^ (prefixWord ++ tailWord_1935704).sum := by decide
  have hdescent : baseEnd_1935704 < baseStart_1935704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935711 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 1, 5]
def baseStart_1935711 : Nat := 118140960795 + 1935711 * 2 ^ 59
def prefixEnd_1935711 : Nat := 4983230072969 + 3 ^ 40 * 1935711 * 2
def baseEnd_1935711 : Nat := 331316717065127085170111

theorem tailTrace_1935711 : CollatzResearch.WordTrace tailWord_1935711 prefixEnd_1935711 331316717065127085170111 := by
  unfold tailWord_1935711
  simp only [CollatzResearch.WordTrace]
  refine ⟨70601180290257114964046987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47067453526838076642697991 70601180290257114964046987)
  ·
    refine ⟨105901770435385672446070481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70601180290257114964046987 105901770435385672446070481)
    ·
      refine ⟨79426327826539254334552861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105901770435385672446070481 79426327826539254334552861)
      ·
        refine ⟨29784872934952220375457323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79426327826539254334552861 29784872934952220375457323)
        ·
          refine ⟨44677309402428330563185985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29784872934952220375457323 44677309402428330563185985)
          ·
            refine ⟨33507982051821247922389489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44677309402428330563185985 33507982051821247922389489)
            ·
              refine ⟨25130986538865935941792117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33507982051821247922389489 25130986538865935941792117)
              ·
                refine ⟨2356029988018681494543011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25130986538865935941792117 2356029988018681494543011)
                ·
                  refine ⟨3534044982028022241814517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356029988018681494543011 3534044982028022241814517)
                  ·
                    refine ⟨331316717065127085170111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3534044982028022241814517 331316717065127085170111)
                    ·
                      rfl

theorem cell23_1935711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_1935711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935711 prefixEnd_1935711 := by exact prefixLift 1935711
  have htrace : WordTrace (prefixWord ++ tailWord_1935711) baseStart_1935711 baseEnd_1935711 := by
    simpa [prefixWord, tailWord_1935711, baseEnd_1935711] using wordTrace_append hprefix tailTrace_1935711
  have hstable : (prefixWord ++ tailWord_1935711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935711).length < 2 ^ (prefixWord ++ tailWord_1935711).sum := by decide
  have hdescent : baseEnd_1935711 < baseStart_1935711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935741 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1935741 : Nat := 118140960795 + 1935741 * 2 ^ 59
def prefixEnd_1935741 : Nat := 4983230072969 + 3 ^ 40 * 1935741 * 2
def baseEnd_1935741 : Nat := 331321851871672046045065

theorem tailTrace_1935741 : CollatzResearch.WordTrace tailWord_1935741 prefixEnd_1935741 331321851871672046045065 := by
  unfold tailWord_1935741
  simp only [CollatzResearch.WordTrace]
  refine ⟨70602274480148430087639077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47068182986765620058426051 70602274480148430087639077)
  ·
    refine ⟨13237926465027830641432327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70602274480148430087639077 13237926465027830641432327)
    ·
      refine ⟨19856889697541745962148491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13237926465027830641432327 19856889697541745962148491)
      ·
        refine ⟨29785334546312618943222737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19856889697541745962148491 29785334546312618943222737)
        ·
          refine ⟨22339000909734464207417053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29785334546312618943222737 22339000909734464207417053)
          ·
            refine ⟨8377125341150424077781395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22339000909734464207417053 8377125341150424077781395)
            ·
              refine ⟨12565688011725636116672093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8377125341150424077781395 12565688011725636116672093)
              ·
                refine ⟨4712133004397113543752035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12565688011725636116672093 4712133004397113543752035)
                ·
                  refine ⟨7068199506595670315628053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712133004397113543752035 7068199506595670315628053)
                  ·
                    refine ⟨331321851871672046045065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7068199506595670315628053 331321851871672046045065)
                    ·
                      rfl

theorem cell23_1935741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1935741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935741 prefixEnd_1935741 := by exact prefixLift 1935741
  have htrace : WordTrace (prefixWord ++ tailWord_1935741) baseStart_1935741 baseEnd_1935741 := by
    simpa [prefixWord, tailWord_1935741, baseEnd_1935741] using wordTrace_append hprefix tailTrace_1935741
  have hstable : (prefixWord ++ tailWord_1935741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935741).length < 2 ^ (prefixWord ++ tailWord_1935741).sum := by decide
  have hdescent : baseEnd_1935741 < baseStart_1935741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935748 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1935748 : Nat := 118140960795 + 1935748 * 2 ^ 59
def prefixEnd_1935748 : Nat := 4983230072969 + 3 ^ 40 * 1935748 * 2
def baseEnd_1935748 : Nat := 993969149979597610747663

theorem tailTrace_1935748 : CollatzResearch.WordTrace tailWord_1935748 prefixEnd_1935748 993969149979597610747663 := by
  unfold tailWord_1935748
  simp only [CollatzResearch.WordTrace]
  refine ⟨35301264895561535141571949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47068353194082046855429265 35301264895561535141571949)
  ·
    refine ⟨13237974335835575678089481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35301264895561535141571949 13237974335835575678089481)
    ·
      refine ⟨9928480751876681758567111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13237974335835575678089481 9928480751876681758567111)
      ·
        refine ⟨14892721127815022637850667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9928480751876681758567111 14892721127815022637850667)
        ·
          refine ⟨22339081691722533956776001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14892721127815022637850667 22339081691722533956776001)
          ·
            refine ⟨16754311268791900467582001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22339081691722533956776001 16754311268791900467582001)
            ·
              refine ⟨12565733451593925350686501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16754311268791900467582001 12565733451593925350686501)
              ·
                refine ⟨2356075022173861003253719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12565733451593925350686501 2356075022173861003253719)
                ·
                  refine ⟨3534112533260791504880579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356075022173861003253719 3534112533260791504880579)
                  ·
                    refine ⟨5301168799891187257320869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3534112533260791504880579 5301168799891187257320869)
                    ·
                      refine ⟨993969149979597610747663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5301168799891187257320869 993969149979597610747663)
                      ·
                        rfl

theorem cell23_1935748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1935748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935748 prefixEnd_1935748 := by exact prefixLift 1935748
  have htrace : WordTrace (prefixWord ++ tailWord_1935748) baseStart_1935748 baseEnd_1935748 := by
    simpa [prefixWord, tailWord_1935748, baseEnd_1935748] using wordTrace_append hprefix tailTrace_1935748
  have hstable : (prefixWord ++ tailWord_1935748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935748).length < 2 ^ (prefixWord ++ tailWord_1935748).sum := by decide
  have hdescent : baseEnd_1935748 < baseStart_1935748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935758 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1935758 : Nat := 118140960795 + 1935758 * 2 ^ 59
def prefixEnd_1935758 : Nat := 4983230072969 + 3 ^ 40 * 1935758 * 2
def baseEnd_1935758 : Nat := 331324761595380857207539

theorem tailTrace_1935758 : CollatzResearch.WordTrace tailWord_1935758 prefixEnd_1935758 331324761595380857207539 := by
  unfold tailWord_1935758
  simp only [CollatzResearch.WordTrace]
  refine ⟨8825361815135855248875991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47068596347391227994005285 8825361815135855248875991)
  ·
    refine ⟨13238042722703782873313987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8825361815135855248875991 13238042722703782873313987)
    ·
      refine ⟨19857064084055674309970981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13238042722703782873313987 19857064084055674309970981)
      ·
        refine ⟨3723199515760438933119559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19857064084055674309970981 3723199515760438933119559)
        ·
          refine ⟨5584799273640658399679339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3723199515760438933119559 5584799273640658399679339)
          ·
            refine ⟨8377198910460987599519009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5584799273640658399679339 8377198910460987599519009)
            ·
              refine ⟨6282899182845740699639257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8377198910460987599519009 6282899182845740699639257)
              ·
                refine ⟨4712174387134305524729443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6282899182845740699639257 4712174387134305524729443)
                ·
                  refine ⟨7068261580701458287094165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4712174387134305524729443 7068261580701458287094165)
                  ·
                    refine ⟨331324761595380857207539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7068261580701458287094165 331324761595380857207539)
                    ·
                      rfl

theorem cell23_1935758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1935758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935758 prefixEnd_1935758 := by exact prefixLift 1935758
  have htrace : WordTrace (prefixWord ++ tailWord_1935758) baseStart_1935758 baseEnd_1935758 := by
    simpa [prefixWord, tailWord_1935758, baseEnd_1935758] using wordTrace_append hprefix tailTrace_1935758
  have hstable : (prefixWord ++ tailWord_1935758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935758).length < 2 ^ (prefixWord ++ tailWord_1935758).sum := by decide
  have hdescent : baseEnd_1935758 < baseStart_1935758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935766 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1935766 : Nat := 118140960795 + 1935766 * 2 ^ 59
def prefixEnd_1935766 : Nat := 4983230072969 + 3 ^ 40 * 1935766 * 2
def baseEnd_1935766 : Nat := 110442043625708726702509

theorem tailTrace_1935766 : CollatzResearch.WordTrace tailWord_1935766 prefixEnd_1935766 110442043625708726702509 := by
  unfold tailWord_1935766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4412699144066116209831197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47068790870038572904866101 4412699144066116209831197)
  ·
    refine ⟨1654762179024793578686699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4412699144066116209831197 1654762179024793578686699)
    ·
      refine ⟨2482143268537190368030049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1654762179024793578686699 2482143268537190368030049)
      ·
        refine ⟨1861607451402892776022537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2482143268537190368030049 1861607451402892776022537)
        ·
          refine ⟨1396205588552169582016903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1861607451402892776022537 1396205588552169582016903)
          ·
            refine ⟨2094308382828254373025355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396205588552169582016903 2094308382828254373025355)
            ·
              refine ⟨3141462574242381559538033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094308382828254373025355 3141462574242381559538033)
              ·
                refine ⟨2356096930681786169653525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141462574242381559538033 2356096930681786169653525)
                ·
                  refine ⟨110442043625708726702509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2356096930681786169653525 110442043625708726702509)
                  ·
                    rfl

theorem cell23_1935766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1935766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935766 prefixEnd_1935766 := by exact prefixLift 1935766
  have htrace : WordTrace (prefixWord ++ tailWord_1935766) baseStart_1935766 baseEnd_1935766 := by
    simpa [prefixWord, tailWord_1935766, baseEnd_1935766] using wordTrace_append hprefix tailTrace_1935766
  have hstable : (prefixWord ++ tailWord_1935766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935766).length < 2 ^ (prefixWord ++ tailWord_1935766).sum := by decide
  have hdescent : baseEnd_1935766 < baseStart_1935766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935841 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_1935841 : Nat := 118140960795 + 1935841 * 2 ^ 59
def prefixEnd_1935841 : Nat := 4983230072969 + 3 ^ 40 * 1935841 * 2
def baseEnd_1935841 : Nat := 994016903680465746884735

theorem tailTrace_1935841 : CollatzResearch.WordTrace tailWord_1935841 prefixEnd_1935841 994016903680465746884735 := by
  unfold tailWord_1935841
  simp only [CollatzResearch.WordTrace]
  refine ⟨70605921779786147166279377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47070614519857431444186251 70605921779786147166279377)
  ·
    refine ⟨52954441334839610374709533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70605921779786147166279377 52954441334839610374709533)
    ·
      refine ⟨19857915500564853890516075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52954441334839610374709533 19857915500564853890516075)
      ·
        refine ⟨29786873250847280835774113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19857915500564853890516075 29786873250847280835774113)
        ·
          refine ⟨22340154938135460626830585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29786873250847280835774113 22340154938135460626830585)
          ·
            refine ⟨16755116203601595470122939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22340154938135460626830585 16755116203601595470122939)
            ·
              refine ⟨25132674305402393205184409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16755116203601595470122939 25132674305402393205184409)
              ·
                refine ⟨18849505729051794903888307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25132674305402393205184409 18849505729051794903888307)
                ·
                  refine ⟨28274258593577692355832461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18849505729051794903888307 28274258593577692355832461)
                  ·
                    refine ⟨10602846972591634633437173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28274258593577692355832461 10602846972591634633437173)
                    ·
                      refine ⟨994016903680465746884735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10602846972591634633437173 994016903680465746884735)
                      ·
                        rfl

theorem cell23_1935841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_1935841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935841 prefixEnd_1935841 := by exact prefixLift 1935841
  have htrace : WordTrace (prefixWord ++ tailWord_1935841) baseStart_1935841 baseEnd_1935841 := by
    simpa [prefixWord, tailWord_1935841, baseEnd_1935841] using wordTrace_append hprefix tailTrace_1935841
  have hstable : (prefixWord ++ tailWord_1935841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935841).length < 2 ^ (prefixWord ++ tailWord_1935841).sum := by decide
  have hdescent : baseEnd_1935841 < baseStart_1935841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935851 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_1935851 : Nat := 118140960795 + 1935851 * 2 ^ 59
def prefixEnd_1935851 : Nat := 4983230072969 + 3 ^ 40 * 1935851 * 2
def baseEnd_1935851 : Nat := 994022038487010707759689

theorem tailTrace_1935851 : CollatzResearch.WordTrace tailWord_1935851 prefixEnd_1935851 994022038487010707759689 := by
  unfold tailWord_1935851
  simp only [CollatzResearch.WordTrace]
  refine ⟨70606286509749918874143407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47070857673166612582762271 70606286509749918874143407)
  ·
    refine ⟨105909429764624878311215111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70606286509749918874143407 105909429764624878311215111)
    ·
      refine ⟨158864144646937317466822667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105909429764624878311215111 158864144646937317466822667)
      ·
        refine ⟨238296216970405976200234001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158864144646937317466822667 238296216970405976200234001)
        ·
          refine ⟨178722162727804482150175501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238296216970405976200234001 178722162727804482150175501)
          ·
            refine ⟨67020811022926680806315813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178722162727804482150175501 67020811022926680806315813)
            ·
              refine ⟨12566402066798752651184215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67020811022926680806315813 12566402066798752651184215)
              ·
                refine ⟨18849603100198128976776323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12566402066798752651184215 18849603100198128976776323)
                ·
                  refine ⟨28274404650297193465164485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18849603100198128976776323 28274404650297193465164485)
                  ·
                    refine ⟨5301450871930723774718341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28274404650297193465164485 5301450871930723774718341)
                    ·
                      refine ⟨994022038487010707759689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5301450871930723774718341 994022038487010707759689)
                      ·
                        rfl

theorem cell23_1935851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_1935851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935851 prefixEnd_1935851 := by exact prefixLift 1935851
  have htrace : WordTrace (prefixWord ++ tailWord_1935851) baseStart_1935851 baseEnd_1935851 := by
    simpa [prefixWord, tailWord_1935851, baseEnd_1935851] using wordTrace_append hprefix tailTrace_1935851
  have hstable : (prefixWord ++ tailWord_1935851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935851).length < 2 ^ (prefixWord ++ tailWord_1935851).sum := by decide
  have hdescent : baseEnd_1935851 < baseStart_1935851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935928 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_1935928 : Nat := 118140960795 + 1935928 * 2 ^ 59
def prefixEnd_1935928 : Nat := 4983230072969 + 3 ^ 40 * 1935928 * 2
def baseEnd_1935928 : Nat := 994061576497406906496835

theorem tailTrace_1935928 : CollatzResearch.WordTrace tailWord_1935928 prefixEnd_1935928 994061576497406906496835 := by
  unfold tailWord_1935928
  simp only [CollatzResearch.WordTrace]
  refine ⟨35304547465235480512348219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47072729953647307349797625 35304547465235480512348219)
  ·
    refine ⟨52956821197853220768522329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35304547465235480512348219 52956821197853220768522329)
    ·
      refine ⟨39717615898389915576391747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52956821197853220768522329 39717615898389915576391747)
      ·
        refine ⟨59576423847584873364587621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39717615898389915576391747 59576423847584873364587621)
        ·
          refine ⟨11170579471422163755860179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59576423847584873364587621 11170579471422163755860179)
          ·
            refine ⟨16755869207133245633790269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11170579471422163755860179 16755869207133245633790269)
            ·
              refine ⟨6283450952674967112671351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16755869207133245633790269 6283450952674967112671351)
              ·
                refine ⟨9425176429012450669007027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6283450952674967112671351 9425176429012450669007027)
                ·
                  refine ⟨14137764643518676003510541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9425176429012450669007027 14137764643518676003510541)
                  ·
                    refine ⟨5301661741319503501316453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14137764643518676003510541 5301661741319503501316453)
                    ·
                      refine ⟨994061576497406906496835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5301661741319503501316453 994061576497406906496835)
                      ·
                        rfl

theorem cell23_1935928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_1935928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935928 prefixEnd_1935928 := by exact prefixLift 1935928
  have htrace : WordTrace (prefixWord ++ tailWord_1935928) baseStart_1935928 baseEnd_1935928 := by
    simpa [prefixWord, tailWord_1935928, baseEnd_1935928] using wordTrace_append hprefix tailTrace_1935928
  have hstable : (prefixWord ++ tailWord_1935928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935928).length < 2 ^ (prefixWord ++ tailWord_1935928).sum := by decide
  have hdescent : baseEnd_1935928 < baseStart_1935928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935931 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_1935931 : Nat := 118140960795 + 1935931 * 2 ^ 59
def prefixEnd_1935931 : Nat := 4983230072969 + 3 ^ 40 * 1935931 * 2
def baseEnd_1935931 : Nat := 994063116939370394759321

theorem tailTrace_1935931 : CollatzResearch.WordTrace tailWord_1935931 prefixEnd_1935931 994063116939370394759321 := by
  unfold tailWord_1935931
  simp only [CollatzResearch.WordTrace]
  refine ⟨70609204349460092537055647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47072802899640061691370431 70609204349460092537055647)
  ·
    refine ⟨105913806524190138805583471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70609204349460092537055647 105913806524190138805583471)
    ·
      refine ⟨158870709786285208208375207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105913806524190138805583471 158870709786285208208375207)
      ·
        refine ⟨238306064679427812312562811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158870709786285208208375207 238306064679427812312562811)
        ·
          refine ⟨357459097019141718468844217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238306064679427812312562811 357459097019141718468844217)
          ·
            refine ⟨268094322764356288851633163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357459097019141718468844217 268094322764356288851633163)
            ·
              refine ⟨402141484146534433277449745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268094322764356288851633163 402141484146534433277449745)
              ·
                refine ⟨301606113109900824958087309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402141484146534433277449745 301606113109900824958087309)
                ·
                  refine ⟨113102292416212809359282741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301606113109900824958087309 113102292416212809359282741)
                  ·
                    refine ⟨10603339914019950877432757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113102292416212809359282741 10603339914019950877432757)
                    ·
                      refine ⟨994063116939370394759321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10603339914019950877432757 994063116939370394759321)
                      ·
                        rfl

theorem cell23_1935931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_1935931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935931 prefixEnd_1935931 := by exact prefixLift 1935931
  have htrace : WordTrace (prefixWord ++ tailWord_1935931) baseStart_1935931 baseEnd_1935931 := by
    simpa [prefixWord, tailWord_1935931, baseEnd_1935931] using wordTrace_append hprefix tailTrace_1935931
  have hstable : (prefixWord ++ tailWord_1935931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935931).length < 2 ^ (prefixWord ++ tailWord_1935931).sum := by decide
  have hdescent : baseEnd_1935931 < baseStart_1935931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935940 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_1935940 : Nat := 118140960795 + 1935940 * 2 ^ 59
def prefixEnd_1935940 : Nat := 4983230072969 + 3 ^ 40 * 1935940 * 2
def baseEnd_1935940 : Nat := 994067738265260859546781

theorem tailTrace_1935940 : CollatzResearch.WordTrace tailWord_1935940 prefixEnd_1935940 994067738265260859546781 := by
  unfold tailWord_1935940
  simp only [CollatzResearch.WordTrace]
  refine ⟨35304766303213743537066637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47073021737618324716088849 35304766303213743537066637)
  ·
    refine ⟨13239287363705153826399989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35304766303213743537066637 13239287363705153826399989)
    ·
      refine ⟨1241183190347358171224999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13239287363705153826399989 1241183190347358171224999)
      ·
        refine ⟨1861774785521037256837499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1241183190347358171224999 1861774785521037256837499)
        ·
          refine ⟨2792662178281555885256249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1861774785521037256837499 2792662178281555885256249)
          ·
            refine ⟨2094496633711166913942187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2792662178281555885256249 2094496633711166913942187)
            ·
              refine ⟨3141744950566750370913281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094496633711166913942187 3141744950566750370913281)
              ·
                refine ⟨2356308712925062778184961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3141744950566750370913281 2356308712925062778184961)
                ·
                  refine ⟨1767231534693797083638721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356308712925062778184961 1767231534693797083638721)
                  ·
                    refine ⟨1325423651020347812729041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1767231534693797083638721 1325423651020347812729041)
                    ·
                      refine ⟨994067738265260859546781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325423651020347812729041 994067738265260859546781)
                      ·
                        rfl

theorem cell23_1935940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_1935940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935940 prefixEnd_1935940 := by exact prefixLift 1935940
  have htrace : WordTrace (prefixWord ++ tailWord_1935940) baseStart_1935940 baseEnd_1935940 := by
    simpa [prefixWord, tailWord_1935940, baseEnd_1935940] using wordTrace_append hprefix tailTrace_1935940
  have hstable : (prefixWord ++ tailWord_1935940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935940).length < 2 ^ (prefixWord ++ tailWord_1935940).sum := by decide
  have hdescent : baseEnd_1935940 < baseStart_1935940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1935968 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 6]
def baseStart_1935968 : Nat := 118140960795 + 1935968 * 2 ^ 59
def prefixEnd_1935968 : Nat := 4983230072969 + 3 ^ 40 * 1935968 * 2
def baseEnd_1935968 : Nat := 110453568413731861110739

theorem tailTrace_1935968 : CollatzResearch.WordTrace tailWord_1935968 prefixEnd_1935968 110453568413731861110739 := by
  unfold tailWord_1935968
  simp only [CollatzResearch.WordTrace]
  refine ⟨35305276925163023928076279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47073702566884031904101705 35305276925163023928076279)
  ·
    refine ⟨52957915387744535892114419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35305276925163023928076279 52957915387744535892114419)
    ·
      refine ⟨79436873081616803838171629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52957915387744535892114419 79436873081616803838171629)
      ·
        refine ⟨29788827405606301439314361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79436873081616803838171629 29788827405606301439314361)
        ·
          refine ⟨22341620554204726079485771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29788827405606301439314361 22341620554204726079485771)
          ·
            refine ⟨33512430831307089119228657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22341620554204726079485771 33512430831307089119228657)
            ·
              refine ⟨25134323123480316839421493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33512430831307089119228657 25134323123480316839421493)
              ·
                refine ⟨2356342792826279703695765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25134323123480316839421493 2356342792826279703695765)
                ·
                  refine ⟨110453568413731861110739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2356342792826279703695765 110453568413731861110739)
                  ·
                    rfl

theorem cell23_1935968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_1935968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1935968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1935968 prefixEnd_1935968 := by exact prefixLift 1935968
  have htrace : WordTrace (prefixWord ++ tailWord_1935968) baseStart_1935968 baseEnd_1935968 := by
    simpa [prefixWord, tailWord_1935968, baseEnd_1935968] using wordTrace_append hprefix tailTrace_1935968
  have hstable : (prefixWord ++ tailWord_1935968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1935968).length < 2 ^ (prefixWord ++ tailWord_1935968).sum := by decide
  have hdescent : baseEnd_1935968 < baseStart_1935968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1935968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936035 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 4]
def baseStart_1936035 : Nat := 118140960795 + 1936035 * 2 ^ 59
def prefixEnd_1936035 : Nat := 4983230072969 + 3 ^ 40 * 1936035 * 2
def baseEnd_1936035 : Nat := 994116518927437987858843

theorem tailTrace_1936035 : CollatzResearch.WordTrace tailWord_1936035 prefixEnd_1936035 994116518927437987858843 := by
  unfold tailWord_1936035
  simp only [CollatzResearch.WordTrace]
  refine ⟨70612997541083318298841559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47075331694055545532561039 70612997541083318298841559)
  ·
    refine ⟨105919496311624977448262339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70612997541083318298841559 105919496311624977448262339)
    ·
      refine ⟨158879244467437466172393509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105919496311624977448262339 158879244467437466172393509)
      ·
        refine ⟨29789858337644524907323783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158879244467437466172393509 29789858337644524907323783)
        ·
          refine ⟨44684787506466787360985675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29789858337644524907323783 44684787506466787360985675)
          ·
            refine ⟨67027181259700181041478513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44684787506466787360985675 67027181259700181041478513)
            ·
              refine ⟨50270385944775135781108885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67027181259700181041478513 50270385944775135781108885)
              ·
                refine ⟨2356424341161334489739479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50270385944775135781108885 2356424341161334489739479)
                ·
                  refine ⟨3534636511742001734609219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356424341161334489739479 3534636511742001734609219)
                  ·
                    refine ⟨5301954767613002601913829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3534636511742001734609219 5301954767613002601913829)
                    ·
                      refine ⟨994116518927437987858843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5301954767613002601913829 994116518927437987858843)
                      ·
                        rfl

theorem cell23_1936035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_1936035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936035 prefixEnd_1936035 := by exact prefixLift 1936035
  have htrace : WordTrace (prefixWord ++ tailWord_1936035) baseStart_1936035 baseEnd_1936035 := by
    simpa [prefixWord, tailWord_1936035, baseEnd_1936035] using wordTrace_append hprefix tailTrace_1936035
  have hstable : (prefixWord ++ tailWord_1936035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936035).length < 2 ^ (prefixWord ++ tailWord_1936035).sum := by decide
  have hdescent : baseEnd_1936035 < baseStart_1936035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936045 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1936045 : Nat := 118140960795 + 1936045 * 2 ^ 59
def prefixEnd_1936045 : Nat := 4983230072969 + 3 ^ 40 * 1936045 * 2
def baseEnd_1936045 : Nat := 331373884577994316244599

theorem tailTrace_1936045 : CollatzResearch.WordTrace tailWord_1936045 prefixEnd_1936045 331373884577994316244599 := by
  unfold tailWord_1936045
  simp only [CollatzResearch.WordTrace]
  refine ⟨70613362271047090006705589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47075574847364726671137059 70613362271047090006705589)
  ·
    refine ⟨6620002712910664688128649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70613362271047090006705589 6620002712910664688128649)
    ·
      refine ⟨4965002034682998516096487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6620002712910664688128649 4965002034682998516096487)
      ·
        refine ⟨7447503052024497774144731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4965002034682998516096487 7447503052024497774144731)
        ·
          refine ⟨11171254578036746661217097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7447503052024497774144731 11171254578036746661217097)
          ·
            refine ⟨8378440933527559995912823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171254578036746661217097 8378440933527559995912823)
            ·
              refine ⟨12567661400291339993869235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378440933527559995912823 12567661400291339993869235)
              ·
                refine ⟨18851492100437009990803853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12567661400291339993869235 18851492100437009990803853)
                ·
                  refine ⟨7069309537663878746551445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18851492100437009990803853 7069309537663878746551445)
                  ·
                    refine ⟨331373884577994316244599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7069309537663878746551445 331373884577994316244599)
                    ·
                      rfl

theorem cell23_1936045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1936045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936045 prefixEnd_1936045 := by exact prefixLift 1936045
  have htrace : WordTrace (prefixWord ++ tailWord_1936045) baseStart_1936045 baseEnd_1936045 := by
    simpa [prefixWord, tailWord_1936045, baseEnd_1936045] using wordTrace_append hprefix tailTrace_1936045
  have hstable : (prefixWord ++ tailWord_1936045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936045).length < 2 ^ (prefixWord ++ tailWord_1936045).sum := by decide
  have hdescent : baseEnd_1936045 < baseStart_1936045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936136 : List Nat := [2, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_1936136 : Nat := 118140960795 + 1936136 * 2 ^ 59
def prefixEnd_1936136 : Nat := 4983230072969 + 3 ^ 40 * 1936136 * 2
def baseEnd_1936136 : Nat := 994168380473542092695879

theorem tailTrace_1936136 : CollatzResearch.WordTrace tailWord_1936136 prefixEnd_1936136 994168380473542092695879 := by
  unfold tailWord_1936136
  simp only [CollatzResearch.WordTrace]
  refine ⟨35308340656858706274134131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47077787542478275032178841 35308340656858706274134131)
  ·
    refine ⟨52962510985288059411201197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35308340656858706274134131 52962510985288059411201197)
    ·
      refine ⟨19860941619483022279200449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52962510985288059411201197 19860941619483022279200449)
      ·
        refine ⟨14895706214612266709400337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19860941619483022279200449 14895706214612266709400337)
        ·
          refine ⟨11171779660959200032050253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14895706214612266709400337 11171779660959200032050253)
          ·
            refine ⟨4189417372859700012018845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11171779660959200032050253 4189417372859700012018845)
            ·
              refine ⟨1571031514822387504507067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4189417372859700012018845 1571031514822387504507067)
              ·
                refine ⟨2356547272233581256760601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571031514822387504507067 2356547272233581256760601)
                ·
                  refine ⟨1767410454175185942570451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356547272233581256760601 1767410454175185942570451)
                  ·
                    refine ⟨2651115681262778913855677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1767410454175185942570451 2651115681262778913855677)
                    ·
                      refine ⟨994168380473542092695879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651115681262778913855677 994168380473542092695879)
                      ·
                        rfl

theorem cell23_1936136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_1936136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936136 prefixEnd_1936136 := by exact prefixLift 1936136
  have htrace : WordTrace (prefixWord ++ tailWord_1936136) baseStart_1936136 baseEnd_1936136 := by
    simpa [prefixWord, tailWord_1936136, baseEnd_1936136] using wordTrace_append hprefix tailTrace_1936136
  have hstable : (prefixWord ++ tailWord_1936136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936136).length < 2 ^ (prefixWord ++ tailWord_1936136).sum := by decide
  have hdescent : baseEnd_1936136 < baseStart_1936136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936145 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_1936145 : Nat := 118140960795 + 1936145 * 2 ^ 59
def prefixEnd_1936145 : Nat := 4983230072969 + 3 ^ 40 * 1936145 * 2
def baseEnd_1936145 : Nat := 994173001799432557483337

theorem tailTrace_1936145 : CollatzResearch.WordTrace tailWord_1936145 prefixEnd_1936145 994173001799432557483337 := by
  unfold tailWord_1936145
  simp only [CollatzResearch.WordTrace]
  refine ⟨70617009570684807085345889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47078006380456538056897259 70617009570684807085345889)
  ·
    refine ⟨52962757178013605314009417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70617009570684807085345889 52962757178013605314009417)
    ·
      refine ⟨39722067883510203985507063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52962757178013605314009417 39722067883510203985507063)
      ·
        refine ⟨59583101825265305978260595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39722067883510203985507063 59583101825265305978260595)
        ·
          refine ⟨89374652737897958967390893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59583101825265305978260595 89374652737897958967390893)
          ·
            refine ⟨33515494776711734612771585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89374652737897958967390893 33515494776711734612771585)
            ·
              refine ⟨25136621082533800959578689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33515494776711734612771585 25136621082533800959578689)
              ·
                refine ⟨18852465811900350719684017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25136621082533800959578689 18852465811900350719684017)
                ·
                  refine ⟨14139349358925263039763013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18852465811900350719684017 14139349358925263039763013)
                  ·
                    refine ⟨2651128004798486819955565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14139349358925263039763013 2651128004798486819955565)
                    ·
                      refine ⟨994173001799432557483337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651128004798486819955565 994173001799432557483337)
                      ·
                        rfl

theorem cell23_1936145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_1936145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936145 prefixEnd_1936145 := by exact prefixLift 1936145
  have htrace : WordTrace (prefixWord ++ tailWord_1936145) baseStart_1936145 baseEnd_1936145 := by
    simpa [prefixWord, tailWord_1936145, baseEnd_1936145] using wordTrace_append hprefix tailTrace_1936145
  have hstable : (prefixWord ++ tailWord_1936145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936145).length < 2 ^ (prefixWord ++ tailWord_1936145).sum := by decide
  have hdescent : baseEnd_1936145 < baseStart_1936145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936159 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 4, 2, 2]
def baseStart_1936159 : Nat := 118140960795 + 1936159 * 2 ^ 59
def prefixEnd_1936159 : Nat := 4983230072969 + 3 ^ 40 * 1936159 * 2
def baseEnd_1936159 : Nat := 994180190528595502708273

theorem tailTrace_1936159 : CollatzResearch.WordTrace tailWord_1936159 prefixEnd_1936159 994180190528595502708273 := by
  unfold tailWord_1936159
  simp only [CollatzResearch.WordTrace]
  refine ⟨70617520192634087476355531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47078346795089391650903687 70617520192634087476355531)
  ·
    refine ⟨105926280288951131214533297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70617520192634087476355531 105926280288951131214533297)
    ·
      refine ⟨79444710216713348410899973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105926280288951131214533297 79444710216713348410899973)
      ·
        refine ⟨14895883165633752827043745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79444710216713348410899973 14895883165633752827043745)
        ·
          refine ⟨11171912374225314620282809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14895883165633752827043745 11171912374225314620282809)
          ·
            refine ⟨8378934280668985965212107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11171912374225314620282809 8378934280668985965212107)
            ·
              refine ⟨12568401421003478947818161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8378934280668985965212107 12568401421003478947818161)
              ·
                refine ⟨9426301065752609210863621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12568401421003478947818161 9426301065752609210863621)
                ·
                  refine ⟨1767431449828614227036929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9426301065752609210863621 1767431449828614227036929)
                  ·
                    refine ⟨1325573587371460670277697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1767431449828614227036929 1325573587371460670277697)
                    ·
                      refine ⟨994180190528595502708273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325573587371460670277697 994180190528595502708273)
                      ·
                        rfl

theorem cell23_1936159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_1936159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936159 prefixEnd_1936159 := by exact prefixLift 1936159
  have htrace : WordTrace (prefixWord ++ tailWord_1936159) baseStart_1936159 baseEnd_1936159 := by
    simpa [prefixWord, tailWord_1936159, baseEnd_1936159] using wordTrace_append hprefix tailTrace_1936159
  have hstable : (prefixWord ++ tailWord_1936159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936159).length < 2 ^ (prefixWord ++ tailWord_1936159).sum := by decide
  have hdescent : baseEnd_1936159 < baseStart_1936159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936162 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_1936162 : Nat := 118140960795 + 1936162 * 2 ^ 59
def prefixEnd_1936162 : Nat := 4983230072969 + 3 ^ 40 * 1936162 * 2
def baseEnd_1936162 : Nat := 994181730970558990970759

theorem tailTrace_1936162 : CollatzResearch.WordTrace tailWord_1936162 prefixEnd_1936162 994181730970558990970759 := by
  unfold tailWord_1936162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654407402905804747178685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47078419741082145992476493 17654407402905804747178685)
  ·
    refine ⟨6620402776089676780192007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17654407402905804747178685 6620402776089676780192007)
    ·
      refine ⟨9930604164134515170288011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6620402776089676780192007 9930604164134515170288011)
      ·
        refine ⟨14895906246201772755432017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9930604164134515170288011 14895906246201772755432017)
        ·
          refine ⟨11171929684651329566574013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14895906246201772755432017 11171929684651329566574013)
          ·
            refine ⟨4189473631744248587465255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11171929684651329566574013 4189473631744248587465255)
            ·
              refine ⟨6284210447616372881197883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189473631744248587465255 6284210447616372881197883)
              ·
                refine ⟨9426315671424559321796825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284210447616372881197883 9426315671424559321796825)
                ·
                  refine ⟨7069736753568419491347619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426315671424559321796825 7069736753568419491347619)
                  ·
                    refine ⟨10604605130352629237021429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7069736753568419491347619 10604605130352629237021429)
                    ·
                      refine ⟨994181730970558990970759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10604605130352629237021429 994181730970558990970759)
                      ·
                        rfl

theorem cell23_1936162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_1936162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936162 prefixEnd_1936162 := by exact prefixLift 1936162
  have htrace : WordTrace (prefixWord ++ tailWord_1936162) baseStart_1936162 baseEnd_1936162 := by
    simpa [prefixWord, tailWord_1936162, baseEnd_1936162] using wordTrace_append hprefix tailTrace_1936162
  have hstable : (prefixWord ++ tailWord_1936162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936162).length < 2 ^ (prefixWord ++ tailWord_1936162).sum := by decide
  have hdescent : baseEnd_1936162 < baseStart_1936162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936195 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 4, 5]
def baseStart_1936195 : Nat := 118140960795 + 1936195 * 2 ^ 59
def prefixEnd_1936195 : Nat := 4983230072969 + 3 ^ 40 * 1936195 * 2
def baseEnd_1936195 : Nat := 331399558610719120619369

theorem tailTrace_1936195 : CollatzResearch.WordTrace tailWord_1936195 prefixEnd_1936195 331399558610719120619369 := by
  unfold tailWord_1936195
  simp only [CollatzResearch.WordTrace]
  refine ⟨70618833220503665624666039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47079222147002443749777359 70618833220503665624666039)
  ·
    refine ⟨105928249830755498436999059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70618833220503665624666039 105928249830755498436999059)
    ·
      refine ⟨158892374746133247655498589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105928249830755498436999059 158892374746133247655498589)
      ·
        refine ⟨59584640529799967870811971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158892374746133247655498589 59584640529799967870811971)
        ·
          refine ⟨89376960794699951806217957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59584640529799967870811971 89376960794699951806217957)
          ·
            refine ⟨16758180149006240963665867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89376960794699951806217957 16758180149006240963665867)
            ·
              refine ⟨25137270223509361445498801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16758180149006240963665867 25137270223509361445498801)
              ·
                refine ⟨18852952667632021084124101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25137270223509361445498801 18852952667632021084124101)
                ·
                  refine ⟨3534928625181003953273269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18852952667632021084124101 3534928625181003953273269)
                  ·
                    refine ⟨331399558610719120619369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3534928625181003953273269 331399558610719120619369)
                    ·
                      rfl

theorem cell23_1936195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 5].length) (baseStart_1936195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936195 prefixEnd_1936195 := by exact prefixLift 1936195
  have htrace : WordTrace (prefixWord ++ tailWord_1936195) baseStart_1936195 baseEnd_1936195 := by
    simpa [prefixWord, tailWord_1936195, baseEnd_1936195] using wordTrace_append hprefix tailTrace_1936195
  have hstable : (prefixWord ++ tailWord_1936195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936195).length < 2 ^ (prefixWord ++ tailWord_1936195).sum := by decide
  have hdescent : baseEnd_1936195 < baseStart_1936195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936202 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_1936202 : Nat := 118140960795 + 1936202 * 2 ^ 59
def prefixEnd_1936202 : Nat := 4983230072969 + 3 ^ 40 * 1936202 * 2
def baseEnd_1936202 : Nat := 994202270196738834470575

theorem tailTrace_1936202 : CollatzResearch.WordTrace tailWord_1936202 prefixEnd_1936202 994202270196738834470575 := by
  unfold tailWord_1936202
  simp only [CollatzResearch.WordTrace]
  refine ⟨17654772132869576455042715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47079392354318870546780573 17654772132869576455042715)
  ·
    refine ⟨26482158199304364682564073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17654772132869576455042715 26482158199304364682564073)
    ·
      refine ⟨19861618649478273511923055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26482158199304364682564073 19861618649478273511923055)
      ·
        refine ⟨29792427974217410267884583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19861618649478273511923055 29792427974217410267884583)
        ·
          refine ⟨44688641961326115401826875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29792427974217410267884583 44688641961326115401826875)
          ·
            refine ⟨67032962941989173102740313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44688641961326115401826875 67032962941989173102740313)
            ·
              refine ⟨50274722206491879827055235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67032962941989173102740313 50274722206491879827055235)
              ·
                refine ⟨75412083309737819740582853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50274722206491879827055235 75412083309737819740582853)
                ·
                  refine ⟨14139765620575841201359285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75412083309737819740582853 14139765620575841201359285)
                  ·
                    refine ⟨1325603026928985112627433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14139765620575841201359285 1325603026928985112627433)
                    ·
                      refine ⟨994202270196738834470575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325603026928985112627433 994202270196738834470575)
                      ·
                        rfl

theorem cell23_1936202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_1936202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936202 prefixEnd_1936202 := by exact prefixLift 1936202
  have htrace : WordTrace (prefixWord ++ tailWord_1936202) baseStart_1936202 baseEnd_1936202 := by
    simpa [prefixWord, tailWord_1936202, baseEnd_1936202] using wordTrace_append hprefix tailTrace_1936202
  have hstable : (prefixWord ++ tailWord_1936202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936202).length < 2 ^ (prefixWord ++ tailWord_1936202).sum := by decide
  have hdescent : baseEnd_1936202 < baseStart_1936202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936249 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 2, 4, 2]
def baseStart_1936249 : Nat := 118140960795 + 1936249 * 2 ^ 59
def prefixEnd_1936249 : Nat := 4983230072969 + 3 ^ 40 * 1936249 * 2
def baseEnd_1936249 : Nat := 994226403787500150582859

theorem tailTrace_1936249 : CollatzResearch.WordTrace tailWord_1936249 prefixEnd_1936249 994226403787500150582859 := by
  unfold tailWord_1936249
  simp only [CollatzResearch.WordTrace]
  refine ⟨70620802762308032847131801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47080535174872021898087867 70620802762308032847131801)
  ·
    refine ⟨52965602071731024635348851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70620802762308032847131801 52965602071731024635348851)
    ·
      refine ⟨79448403107596536953023277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52965602071731024635348851 79448403107596536953023277)
      ·
        refine ⟨29793151165348701357383729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79448403107596536953023277 29793151165348701357383729)
        ·
          refine ⟨22344863374011526018037797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29793151165348701357383729 22344863374011526018037797)
          ·
            refine ⟨4189661882627161128382087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22344863374011526018037797 4189661882627161128382087)
            ·
              refine ⟨6284492823940741692573131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189661882627161128382087 6284492823940741692573131)
              ·
                refine ⟨9426739235911112538859697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284492823940741692573131 9426739235911112538859697)
                ·
                  refine ⟨7070054426933334404144773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9426739235911112538859697 7070054426933334404144773)
                  ·
                    refine ⟨1325635205050000200777145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7070054426933334404144773 1325635205050000200777145)
                    ·
                      refine ⟨994226403787500150582859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325635205050000200777145 994226403787500150582859)
                      ·
                        rfl

theorem cell23_1936249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_1936249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936249 prefixEnd_1936249 := by exact prefixLift 1936249
  have htrace : WordTrace (prefixWord ++ tailWord_1936249) baseStart_1936249 baseEnd_1936249 := by
    simpa [prefixWord, tailWord_1936249, baseEnd_1936249] using wordTrace_append hprefix tailTrace_1936249
  have hstable : (prefixWord ++ tailWord_1936249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936249).length < 2 ^ (prefixWord ++ tailWord_1936249).sum := by decide
  have hdescent : baseEnd_1936249 < baseStart_1936249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936252 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1936252 : Nat := 118140960795 + 1936252 * 2 ^ 59
def prefixEnd_1936252 : Nat := 4983230072969 + 3 ^ 40 * 1936252 * 2
def baseEnd_1936252 : Nat := 994227944229463638845345

theorem tailTrace_1936252 : CollatzResearch.WordTrace tailWord_1936252 prefixEnd_1936252 994227944229463638845345 := by
  unfold tailWord_1936252
  simp only [CollatzResearch.WordTrace]
  refine ⟨35310456090648582179745505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47080608120864776239660673 35310456090648582179745505)
  ·
    refine ⟨26482842067986436634809129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35310456090648582179745505 26482842067986436634809129)
    ·
      refine ⟨19862131550989827476106847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26482842067986436634809129 19862131550989827476106847)
      ·
        refine ⟨29793197326484741214160271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19862131550989827476106847 29793197326484741214160271)
        ·
          refine ⟨44689795989727111821240407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29793197326484741214160271 44689795989727111821240407)
          ·
            refine ⟨67034693984590667731860611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44689795989727111821240407 67034693984590667731860611)
            ·
              refine ⟨100552040976886001597790917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67034693984590667731860611 100552040976886001597790917)
              ·
                refine ⟨18853507683166125299585797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100552040976886001597790917 18853507683166125299585797)
                ·
                  refine ⟨3535032690593648493672337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18853507683166125299585797 3535032690593648493672337)
                  ·
                    refine ⟨2651274517945236370254253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3535032690593648493672337 2651274517945236370254253)
                    ·
                      refine ⟨994227944229463638845345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651274517945236370254253 994227944229463638845345)
                      ·
                        rfl

theorem cell23_1936252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1936252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936252 prefixEnd_1936252 := by exact prefixLift 1936252
  have htrace : WordTrace (prefixWord ++ tailWord_1936252) baseStart_1936252 baseEnd_1936252 := by
    simpa [prefixWord, tailWord_1936252, baseEnd_1936252] using wordTrace_append hprefix tailTrace_1936252
  have hstable : (prefixWord ++ tailWord_1936252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936252).length < 2 ^ (prefixWord ++ tailWord_1936252).sum := by decide
  have hdescent : baseEnd_1936252 < baseStart_1936252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936266 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1936266 : Nat := 118140960795 + 1936266 * 2 ^ 59
def prefixEnd_1936266 : Nat := 4983230072969 + 3 ^ 40 * 1936266 * 2
def baseEnd_1936266 : Nat := 994235132958626584070281

theorem tailTrace_1936266 : CollatzResearch.WordTrace tailWord_1936266 prefixEnd_1936266 994235132958626584070281 := by
  unfold tailWord_1936266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17655355700811611187625163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47080948535497629833667101 17655355700811611187625163)
  ·
    refine ⟨26483033551217416781437745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17655355700811611187625163 26483033551217416781437745)
    ·
      refine ⟨19862275163413062586078309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26483033551217416781437745 19862275163413062586078309)
      ·
        refine ⟨3724176593139949234889683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19862275163413062586078309 3724176593139949234889683)
        ·
          refine ⟨5586264889709923852334525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724176593139949234889683 5586264889709923852334525)
          ·
            refine ⟨2094849333641221444625447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5586264889709923852334525 2094849333641221444625447)
            ·
              refine ⟨3142274000461832166938171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094849333641221444625447 3142274000461832166938171)
              ·
                refine ⟨4713411000692748250407257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142274000461832166938171 4713411000692748250407257)
                ·
                  refine ⟨3535058250519561187805443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4713411000692748250407257 3535058250519561187805443)
                  ·
                    refine ⟨5302587375779341781708165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535058250519561187805443 5302587375779341781708165)
                    ·
                      refine ⟨994235132958626584070281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5302587375779341781708165 994235132958626584070281)
                      ·
                        rfl

theorem cell23_1936266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1936266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936266 prefixEnd_1936266 := by exact prefixLift 1936266
  have htrace : WordTrace (prefixWord ++ tailWord_1936266) baseStart_1936266 baseEnd_1936266 := by
    simpa [prefixWord, tailWord_1936266, baseEnd_1936266] using wordTrace_append hprefix tailTrace_1936266
  have hstable : (prefixWord ++ tailWord_1936266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936266).length < 2 ^ (prefixWord ++ tailWord_1936266).sum := by decide
  have hdescent : baseEnd_1936266 < baseStart_1936266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936289 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 6]
def baseStart_1936289 : Nat := 118140960795 + 1936289 * 2 ^ 59
def prefixEnd_1936289 : Nat := 4983230072969 + 3 ^ 40 * 1936289 * 2
def baseEnd_1936289 : Nat := 110471882557075554898075

theorem tailTrace_1936289 : CollatzResearch.WordTrace tailWord_1936289 prefixEnd_1936289 110471882557075554898075 := by
  unfold tailWord_1936289
  simp only [CollatzResearch.WordTrace]
  refine ⟨70622261682163119678587921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47081507788108746452391947 70622261682163119678587921)
  ·
    refine ⟨52966696261622339758940941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70622261682163119678587921 52966696261622339758940941)
    ·
      refine ⟨19862511098108377409602853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52966696261622339758940941 19862511098108377409602853)
      ·
        refine ⟨3724220830895320764300535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19862511098108377409602853 3724220830895320764300535)
        ·
          refine ⟨5586331246342981146450803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724220830895320764300535 5586331246342981146450803)
          ·
            refine ⟨8379496869514471719676205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586331246342981146450803 8379496869514471719676205)
            ·
              refine ⟨3142311326067926894878577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8379496869514471719676205 3142311326067926894878577)
              ·
                refine ⟨2356733494550945171158933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3142311326067926894878577 2356733494550945171158933)
                ·
                  refine ⟨110471882557075554898075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2356733494550945171158933 110471882557075554898075)
                  ·
                    rfl

theorem cell23_1936289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_1936289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936289 prefixEnd_1936289 := by exact prefixLift 1936289
  have htrace : WordTrace (prefixWord ++ tailWord_1936289) baseStart_1936289 baseEnd_1936289 := by
    simpa [prefixWord, tailWord_1936289, baseEnd_1936289] using wordTrace_append hprefix tailTrace_1936289
  have hstable : (prefixWord ++ tailWord_1936289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936289).length < 2 ^ (prefixWord ++ tailWord_1936289).sum := by decide
  have hdescent : baseEnd_1936289 < baseStart_1936289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936309 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_1936309 : Nat := 118140960795 + 1936309 * 2 ^ 59
def prefixEnd_1936309 : Nat := 4983230072969 + 3 ^ 40 * 1936309 * 2
def baseEnd_1936309 : Nat := 994257212626769915832583

theorem tailTrace_1936309 : CollatzResearch.WordTrace tailWord_1936309 prefixEnd_1936309 994257212626769915832583 := by
  unfold tailWord_1936309
  simp only [CollatzResearch.WordTrace]
  refine ⟨70622991142090663094315981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47081994094727108729543987 70622991142090663094315981)
  ·
    refine ⟨26483621678283998660368493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70622991142090663094315981 26483621678283998660368493)
    ·
      refine ⟨9931358129356499497638185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26483621678283998660368493 9931358129356499497638185)
      ·
        refine ⟨7448518597017374623228639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9931358129356499497638185 7448518597017374623228639)
        ·
          refine ⟨11172777895526061934842959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448518597017374623228639 11172777895526061934842959)
          ·
            refine ⟨16759166843289092902264439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11172777895526061934842959 16759166843289092902264439)
            ·
              refine ⟨25138750264933639353396659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16759166843289092902264439 25138750264933639353396659)
              ·
                refine ⟨37708125397400459030094989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25138750264933639353396659 37708125397400459030094989)
                ·
                  refine ⟨14140547024025172136285621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37708125397400459030094989 14140547024025172136285621)
                  ·
                    refine ⟨1325676283502359887776777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14140547024025172136285621 1325676283502359887776777)
                    ·
                      refine ⟨994257212626769915832583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325676283502359887776777 994257212626769915832583)
                      ·
                        rfl

theorem cell23_1936309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_1936309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936309 prefixEnd_1936309 := by exact prefixLift 1936309
  have htrace : WordTrace (prefixWord ++ tailWord_1936309) baseStart_1936309 baseEnd_1936309 := by
    simpa [prefixWord, tailWord_1936309, baseEnd_1936309] using wordTrace_append hprefix tailTrace_1936309
  have hstable : (prefixWord ++ tailWord_1936309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936309).length < 2 ^ (prefixWord ++ tailWord_1936309).sum := by decide
  have hdescent : baseEnd_1936309 < baseStart_1936309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936332 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1936332 : Nat := 118140960795 + 1936332 * 2 ^ 59
def prefixEnd_1936332 : Nat := 4983230072969 + 3 ^ 40 * 1936332 * 2
def baseEnd_1936332 : Nat := 331423007560607775281659

theorem tailTrace_1936332 : CollatzResearch.WordTrace tailWord_1936332 prefixEnd_1936332 331423007560607775281659 := by
  unfold tailWord_1936332
  simp only [CollatzResearch.WordTrace]
  refine ⟨35311915010503669011201625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47082553347338225348268833 35311915010503669011201625)
  ·
    refine ⟨26483936257877751758401219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35311915010503669011201625 26483936257877751758401219)
    ·
      refine ⟨39725904386816627637601829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26483936257877751758401219 39725904386816627637601829)
      ·
        refine ⟨7448607072528117682050343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39725904386816627637601829 7448607072528117682050343)
        ·
          refine ⟨11172910608792176523075515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7448607072528117682050343 11172910608792176523075515)
          ·
            refine ⟨16759365913188264784613273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11172910608792176523075515 16759365913188264784613273)
            ·
              refine ⟨12569524434891198588459955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16759365913188264784613273 12569524434891198588459955)
              ·
                refine ⟨18854286652336797882689933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12569524434891198588459955 18854286652336797882689933)
                ·
                  refine ⟨7070357494626299206008725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18854286652336797882689933 7070357494626299206008725)
                  ·
                    refine ⟨331423007560607775281659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7070357494626299206008725 331423007560607775281659)
                    ·
                      rfl

theorem cell23_1936332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1936332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936332 prefixEnd_1936332 := by exact prefixLift 1936332
  have htrace : WordTrace (prefixWord ++ tailWord_1936332) baseStart_1936332 baseEnd_1936332 := by
    simpa [prefixWord, tailWord_1936332, baseEnd_1936332] using wordTrace_append hprefix tailTrace_1936332
  have hstable : (prefixWord ++ tailWord_1936332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936332).length < 2 ^ (prefixWord ++ tailWord_1936332).sum := by decide
  have hdescent : baseEnd_1936332 < baseStart_1936332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936356 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_1936356 : Nat := 118140960795 + 1936356 * 2 ^ 59
def prefixEnd_1936356 : Nat := 4983230072969 + 3 ^ 40 * 1936356 * 2
def baseEnd_1936356 : Nat := 994281346217531231944867

theorem tailTrace_1936356 : CollatzResearch.WordTrace tailWord_1936356 prefixEnd_1936356 994281346217531231944867 := by
  unfold tailWord_1936356
  simp only [CollatzResearch.WordTrace]
  refine ⟨35312352686460195060638461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47083136915280260080851281 35312352686460195060638461)
  ·
    refine ⟨13242132257422573147739423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35312352686460195060638461 13242132257422573147739423)
    ·
      refine ⟨19863198386133859721609135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13242132257422573147739423 19863198386133859721609135)
      ·
        refine ⟨29794797579200789582413703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19863198386133859721609135 29794797579200789582413703)
        ·
          refine ⟨44692196368801184373620555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29794797579200789582413703 44692196368801184373620555)
          ·
            refine ⟨67038294553201776560430833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44692196368801184373620555 67038294553201776560430833)
            ·
              refine ⟨50278720914901332420323125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67038294553201776560430833 50278720914901332420323125)
              ·
                refine ⟨4713630085771999914405293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50278720914901332420323125 4713630085771999914405293)
                ·
                  refine ⟨1767611282164499967901985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4713630085771999914405293 1767611282164499967901985)
                  ·
                    refine ⟨1325708461623374975926489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1767611282164499967901985 1325708461623374975926489)
                    ·
                      refine ⟨994281346217531231944867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325708461623374975926489 994281346217531231944867)
                      ·
                        rfl

theorem cell23_1936356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_1936356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936356 prefixEnd_1936356 := by exact prefixLift 1936356
  have htrace : WordTrace (prefixWord ++ tailWord_1936356) baseStart_1936356 baseEnd_1936356 := by
    simpa [prefixWord, tailWord_1936356, baseEnd_1936356] using wordTrace_append hprefix tailTrace_1936356
  have hstable : (prefixWord ++ tailWord_1936356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936356).length < 2 ^ (prefixWord ++ tailWord_1936356).sum := by decide
  have hdescent : baseEnd_1936356 < baseStart_1936356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936359 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1936359 : Nat := 118140960795 + 1936359 * 2 ^ 59
def prefixEnd_1936359 : Nat := 4983230072969 + 3 ^ 40 * 1936359 * 2
def baseEnd_1936359 : Nat := 994282886659494720207353

theorem tailTrace_1936359 : CollatzResearch.WordTrace tailWord_1936359 prefixEnd_1936359 994282886659494720207353 := by
  unfold tailWord_1936359
  simp only [CollatzResearch.WordTrace]
  refine ⟨70624814791909521633636131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47083209861273014422424087 70624814791909521633636131)
  ·
    refine ⟨105937222187864282450454197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70624814791909521633636131 105937222187864282450454197)
    ·
      refine ⟨9931614580112276479730081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105937222187864282450454197 9931614580112276479730081)
      ·
        refine ⟨7448710935084207359797561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9931614580112276479730081 7448710935084207359797561)
        ·
          refine ⟨5586533201313155519848171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7448710935084207359797561 5586533201313155519848171)
          ·
            refine ⟨8379799801969733279772257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586533201313155519848171 8379799801969733279772257)
            ·
              refine ⟨6284849851477299959829193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8379799801969733279772257 6284849851477299959829193)
              ·
                refine ⟨4713637388607974969871895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284849851477299959829193 4713637388607974969871895)
                ·
                  refine ⟨7070456082911962454807843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713637388607974969871895 7070456082911962454807843)
                  ·
                    refine ⟨10605684124367943682211765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7070456082911962454807843 10605684124367943682211765)
                    ·
                      refine ⟨994282886659494720207353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10605684124367943682211765 994282886659494720207353)
                      ·
                        rfl

theorem cell23_1936359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1936359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936359 prefixEnd_1936359 := by exact prefixLift 1936359
  have htrace : WordTrace (prefixWord ++ tailWord_1936359) baseStart_1936359 baseEnd_1936359 := by
    simpa [prefixWord, tailWord_1936359, baseEnd_1936359] using wordTrace_append hprefix tailTrace_1936359
  have hstable : (prefixWord ++ tailWord_1936359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936359).length < 2 ^ (prefixWord ++ tailWord_1936359).sum := by decide
  have hdescent : baseEnd_1936359 < baseStart_1936359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936362 : List Nat := [3, 1, 3, 1, 2, 2, 1, 10]
def baseStart_1936362 : Nat := 118140960795 + 1936362 * 2 ^ 59
def prefixEnd_1936362 : Nat := 4983230072969 + 3 ^ 40 * 1936362 * 2
def baseEnd_1936362 : Nat := 36825349151905859572957

theorem tailTrace_1936362 : CollatzResearch.WordTrace tailWord_1936362 prefixEnd_1936362 36825349151905859572957 := by
  unfold tailWord_1936362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656231052724663286498835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47083282807265768763996893 17656231052724663286498835)
  ·
    refine ⟨26484346579086994929748253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17656231052724663286498835 26484346579086994929748253)
    ·
      refine ⟨9931629967157623098655595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26484346579086994929748253 9931629967157623098655595)
      ·
        refine ⟨14897444950736434647983393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9931629967157623098655595 14897444950736434647983393)
        ·
          refine ⟨11173083713052325985987545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14897444950736434647983393 11173083713052325985987545)
          ·
            refine ⟨8379812784789244489490659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11173083713052325985987545 8379812784789244489490659)
            ·
              refine ⟨12569719177183866734235989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8379812784789244489490659 12569719177183866734235989)
              ·
                refine ⟨36825349151905859572957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12569719177183866734235989 36825349151905859572957)
                ·
                  rfl

theorem cell23_1936362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_1936362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936362 prefixEnd_1936362 := by exact prefixLift 1936362
  have htrace : WordTrace (prefixWord ++ tailWord_1936362) baseStart_1936362 baseEnd_1936362 := by
    simpa [prefixWord, tailWord_1936362, baseEnd_1936362] using wordTrace_append hprefix tailTrace_1936362
  have hstable : (prefixWord ++ tailWord_1936362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936362).length < 2 ^ (prefixWord ++ tailWord_1936362).sum := by decide
  have hdescent : baseEnd_1936362 < baseStart_1936362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936370 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1936370 : Nat := 118140960795 + 1936370 * 2 ^ 59
def prefixEnd_1936370 : Nat := 4983230072969 + 3 ^ 40 * 1936370 * 2
def baseEnd_1936370 : Nat := 331429511648898059056601

theorem tailTrace_1936370 : CollatzResearch.WordTrace tailWord_1936370 prefixEnd_1936370 331429511648898059056601 := by
  unfold tailWord_1936370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17656303998717417628071641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47083477329913113674857709 17656303998717417628071641)
  ·
    refine ⟨13242227999038063221053731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17656303998717417628071641 13242227999038063221053731)
    ·
      refine ⟨19863341998557094831580597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13242227999038063221053731 19863341998557094831580597)
      ·
        refine ⟨1862188312364727640460681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19863341998557094831580597 1862188312364727640460681)
        ·
          refine ⟨1396641234273545730345511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1862188312364727640460681 1396641234273545730345511)
          ·
            refine ⟨2094961851410318595518267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396641234273545730345511 2094961851410318595518267)
            ·
              refine ⟨3142442777115477893277401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2094961851410318595518267 3142442777115477893277401)
              ·
                refine ⟨2356832082836608419958051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3142442777115477893277401 2356832082836608419958051)
                ·
                  refine ⟨3535248124254912629937077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2356832082836608419958051 3535248124254912629937077)
                  ·
                    refine ⟨331429511648898059056601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3535248124254912629937077 331429511648898059056601)
                    ·
                      rfl

theorem cell23_1936370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1936370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936370 prefixEnd_1936370 := by exact prefixLift 1936370
  have htrace : WordTrace (prefixWord ++ tailWord_1936370) baseStart_1936370 baseEnd_1936370 := by
    simpa [prefixWord, tailWord_1936370, baseEnd_1936370] using wordTrace_append hprefix tailTrace_1936370
  have hstable : (prefixWord ++ tailWord_1936370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936370).length < 2 ^ (prefixWord ++ tailWord_1936370).sum := by decide
  have hdescent : baseEnd_1936370 < baseStart_1936370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936373 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1936373 : Nat := 118140960795 + 1936373 * 2 ^ 59
def prefixEnd_1936373 : Nat := 4983230072969 + 3 ^ 40 * 1936373 * 2
def baseEnd_1936373 : Nat := 994290075388657665432289

theorem tailTrace_1936373 : CollatzResearch.WordTrace tailWord_1936373 prefixEnd_1936373 994290075388657665432289 := by
  unfold tailWord_1936373
  simp only [CollatzResearch.WordTrace]
  refine ⟨70625325413858802024645773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47083550275905868016430515 70625325413858802024645773)
  ·
    refine ⟨26484497030197050759242165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70625325413858802024645773 26484497030197050759242165)
    ·
      refine ⟨2482921596580973508678953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 26484497030197050759242165 2482921596580973508678953)
      ·
        refine ⟨1862191197435730131509215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2482921596580973508678953 1862191197435730131509215)
        ·
          refine ⟨2793286796153595197263823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1862191197435730131509215 2793286796153595197263823)
          ·
            refine ⟨4189930194230392795895735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793286796153595197263823 4189930194230392795895735)
            ·
              refine ⟨6284895291345589193843603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4189930194230392795895735 6284895291345589193843603)
              ·
                refine ⟨9427342937018383790765405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6284895291345589193843603 9427342937018383790765405)
                ·
                  refine ⟨3535253601381893921537027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9427342937018383790765405 3535253601381893921537027)
                  ·
                    refine ⟨5302880402072840882305541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535253601381893921537027 5302880402072840882305541)
                    ·
                      refine ⟨994290075388657665432289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5302880402072840882305541 994290075388657665432289)
                      ·
                        rfl

theorem cell23_1936373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1936373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936373 prefixEnd_1936373 := by exact prefixLift 1936373
  have htrace : WordTrace (prefixWord ++ tailWord_1936373) baseStart_1936373 baseEnd_1936373 := by
    simpa [prefixWord, tailWord_1936373, baseEnd_1936373] using wordTrace_append hprefix tailTrace_1936373
  have hstable : (prefixWord ++ tailWord_1936373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936373).length < 2 ^ (prefixWord ++ tailWord_1936373).sum := by decide
  have hdescent : baseEnd_1936373 < baseStart_1936373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936389 : List Nat := [1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_1936389 : Nat := 118140960795 + 1936389 * 2 ^ 59
def prefixEnd_1936389 : Nat := 4983230072969 + 3 ^ 40 * 1936389 * 2
def baseEnd_1936389 : Nat := 994298291079129602832215

theorem tailTrace_1936389 : CollatzResearch.WordTrace tailWord_1936389 prefixEnd_1936389 994298291079129602832215 := by
  unfold tailWord_1936389
  simp only [CollatzResearch.WordTrace]
  refine ⟨70625908981800836757228221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47083939321200557838152147 70625908981800836757228221)
  ·
    refine ⟨26484715868175313783960583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70625908981800836757228221 26484715868175313783960583)
    ·
      refine ⟨39727073802262970675940875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26484715868175313783960583 39727073802262970675940875)
      ·
        refine ⟨59590610703394456013911313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39727073802262970675940875 59590610703394456013911313)
        ·
          refine ⟨44692958027545842010433485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59590610703394456013911313 44692958027545842010433485)
          ·
            refine ⟨16759859260329690753912557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44692958027545842010433485 16759859260329690753912557)
            ·
              refine ⟨6284947222623634032717209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16759859260329690753912557 6284947222623634032717209)
              ·
                refine ⟨4713710416967725524537907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6284947222623634032717209 4713710416967725524537907)
                ·
                  refine ⟨7070565625451588286806861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713710416967725524537907 7070565625451588286806861)
                  ·
                    refine ⟨2651462109544345607552573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7070565625451588286806861 2651462109544345607552573)
                    ·
                      refine ⟨994298291079129602832215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651462109544345607552573 994298291079129602832215)
                      ·
                        rfl

theorem cell23_1936389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_1936389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936389 prefixEnd_1936389 := by exact prefixLift 1936389
  have htrace : WordTrace (prefixWord ++ tailWord_1936389) baseStart_1936389 baseEnd_1936389 := by
    simpa [prefixWord, tailWord_1936389, baseEnd_1936389] using wordTrace_append hprefix tailTrace_1936389
  have hstable : (prefixWord ++ tailWord_1936389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936389).length < 2 ^ (prefixWord ++ tailWord_1936389).sum := by decide
  have hdescent : baseEnd_1936389 < baseStart_1936389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936407 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1936407 : Nat := 118140960795 + 1936407 * 2 ^ 59
def prefixEnd_1936407 : Nat := 4983230072969 + 3 ^ 40 * 1936407 * 2
def baseEnd_1936407 : Nat := 994307533730910532407133

theorem tailTrace_1936407 : CollatzResearch.WordTrace tailWord_1936407 prefixEnd_1936407 994307533730910532407133 := by
  unfold tailWord_1936407
  simp only [CollatzResearch.WordTrace]
  refine ⟨70626565495735625831383475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47084376997157083887588983 70626565495735625831383475)
  ·
    refine ⟨105939848243603438747075213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70626565495735625831383475 105939848243603438747075213)
    ·
      refine ⟨39727443091351289530153205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105939848243603438747075213 39727443091351289530153205)
      ·
        refine ⟨3724447789814183393451863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39727443091351289530153205 3724447789814183393451863)
        ·
          refine ⟨5586671684721275090177795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724447789814183393451863 5586671684721275090177795)
          ·
            refine ⟨8380007527081912635266693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5586671684721275090177795 8380007527081912635266693)
            ·
              refine ⟨1571251411327858619112505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8380007527081912635266693 1571251411327858619112505)
              ·
                refine ⟨1178438558495893964334379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571251411327858619112505 1178438558495893964334379)
                ·
                  refine ⟨1767657837743840946501569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178438558495893964334379 1767657837743840946501569)
                  ·
                    refine ⟨1325743378307880709876177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1767657837743840946501569 1325743378307880709876177)
                    ·
                      refine ⟨994307533730910532407133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325743378307880709876177 994307533730910532407133)
                      ·
                        rfl

theorem cell23_1936407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1936407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936407 prefixEnd_1936407 := by exact prefixLift 1936407
  have htrace : WordTrace (prefixWord ++ tailWord_1936407) baseStart_1936407 baseEnd_1936407 := by
    simpa [prefixWord, tailWord_1936407, baseEnd_1936407] using wordTrace_append hprefix tailTrace_1936407
  have hstable : (prefixWord ++ tailWord_1936407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936407).length < 2 ^ (prefixWord ++ tailWord_1936407).sum := by decide
  have hdescent : baseEnd_1936407 < baseStart_1936407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936423 : List Nat := [1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1936423 : Nat := 118140960795 + 1936423 * 2 ^ 59
def prefixEnd_1936423 : Nat := 4983230072969 + 3 ^ 40 * 1936423 * 2
def baseEnd_1936423 : Nat := 994315749421382469807059

theorem tailTrace_1936423 : CollatzResearch.WordTrace tailWord_1936423 prefixEnd_1936423 994315749421382469807059 := by
  unfold tailWord_1936423
  simp only [CollatzResearch.WordTrace]
  refine ⟨70627149063677660563965923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47084766042451773709310615 70627149063677660563965923)
  ·
    refine ⟨105940723595516490845948885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70627149063677660563965923 105940723595516490845948885)
    ·
      refine ⟨2482985709269917754201927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 105940723595516490845948885 2482985709269917754201927)
      ·
        refine ⟨3724478563904876631302891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2482985709269917754201927 3724478563904876631302891)
        ·
          refine ⟨5586717845857314946954337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3724478563904876631302891 5586717845857314946954337)
          ·
            refine ⟨4190038384392986210215753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586717845857314946954337 4190038384392986210215753)
            ·
              refine ⟨3142528788294739657661815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4190038384392986210215753 3142528788294739657661815)
              ·
                refine ⟨4713793182442109486492723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142528788294739657661815 4713793182442109486492723)
                ·
                  refine ⟨7070689773663164229739085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4713793182442109486492723 7070689773663164229739085)
                  ·
                    refine ⟨2651508665123686586152157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7070689773663164229739085 2651508665123686586152157)
                    ·
                      refine ⟨994315749421382469807059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651508665123686586152157 994315749421382469807059)
                      ·
                        rfl

theorem cell23_1936423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1936423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936423 prefixEnd_1936423 := by exact prefixLift 1936423
  have htrace : WordTrace (prefixWord ++ tailWord_1936423) baseStart_1936423 baseEnd_1936423 := by
    simpa [prefixWord, tailWord_1936423, baseEnd_1936423] using wordTrace_append hprefix tailTrace_1936423
  have hstable : (prefixWord ++ tailWord_1936423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936423).length < 2 ^ (prefixWord ++ tailWord_1936423).sum := by decide
  have hdescent : baseEnd_1936423 < baseStart_1936423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936469 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 7]
def baseStart_1936469 : Nat := 118140960795 + 1936469 * 2 ^ 59
def prefixEnd_1936469 : Nat := 4983230072969 + 3 ^ 40 * 1936469 * 2
def baseEnd_1936469 : Nat := 110482152170165476647983

theorem tailTrace_1936469 : CollatzResearch.WordTrace tailWord_1936469 prefixEnd_1936469 110482152170165476647983 := by
  unfold tailWord_1936469
  simp only [CollatzResearch.WordTrace]
  refine ⟨70628826821511010420140461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47085884547674006946760307 70628826821511010420140461)
  ·
    refine ⟨26485810058066628907552673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70628826821511010420140461 26485810058066628907552673)
    ·
      refine ⟨19864357543549971680664505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26485810058066628907552673 19864357543549971680664505)
      ·
        refine ⟨14898268157662478760498379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19864357543549971680664505 14898268157662478760498379)
        ·
          refine ⟨22347402236493718140747569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14898268157662478760498379 22347402236493718140747569)
          ·
            refine ⟨16760551677370288605560677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22347402236493718140747569 16760551677370288605560677)
            ·
              refine ⟨3142603439506929113542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16760551677370288605560677 3142603439506929113542627)
              ·
                refine ⟨4713905159260393670313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3142603439506929113542627 4713905159260393670313941)
                ·
                  refine ⟨110482152170165476647983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4713905159260393670313941 110482152170165476647983)
                  ·
                    rfl

theorem cell23_1936469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_1936469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936469 prefixEnd_1936469 := by exact prefixLift 1936469
  have htrace : WordTrace (prefixWord ++ tailWord_1936469) baseStart_1936469 baseEnd_1936469 := by
    simpa [prefixWord, tailWord_1936469, baseEnd_1936469] using wordTrace_append hprefix tailTrace_1936469
  have hstable : (prefixWord ++ tailWord_1936469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936469).length < 2 ^ (prefixWord ++ tailWord_1936469).sum := by decide
  have hdescent : baseEnd_1936469 < baseStart_1936469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936479 : List Nat := [1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_1936479 : Nat := 118140960795 + 1936479 * 2 ^ 59
def prefixEnd_1936479 : Nat := 4983230072969 + 3 ^ 40 * 1936479 * 2
def baseEnd_1936479 : Nat := 994344504338034250706801

theorem tailTrace_1936479 : CollatzResearch.WordTrace tailWord_1936479 prefixEnd_1936479 994344504338034250706801 := by
  unfold tailWord_1936479
  simp only [CollatzResearch.WordTrace]
  refine ⟨70629191551474782128004491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47086127700983188085336327 70629191551474782128004491)
  ·
    refine ⟨105943787327212173192006737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70629191551474782128004491 105943787327212173192006737)
    ·
      refine ⟨79457840495409129894005053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105943787327212173192006737 79457840495409129894005053)
      ·
        refine ⟨29796690185778423710251895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79457840495409129894005053 29796690185778423710251895)
        ·
          refine ⟨44695035278667635565377843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29796690185778423710251895 44695035278667635565377843)
          ·
            refine ⟨67042552918001453348066765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44695035278667635565377843 67042552918001453348066765)
            ·
              refine ⟨25140957344250545005525037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67042552918001453348066765 25140957344250545005525037)
              ·
                refine ⟨9427859004093954377071889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25140957344250545005525037 9427859004093954377071889)
                ·
                  refine ⟨7070894253070465782803917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9427859004093954377071889 7070894253070465782803917)
                  ·
                    refine ⟨2651585344901424668551469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7070894253070465782803917 2651585344901424668551469)
                    ·
                      refine ⟨994344504338034250706801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651585344901424668551469 994344504338034250706801)
                      ·
                        rfl

theorem cell23_1936479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_1936479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936479 prefixEnd_1936479 := by exact prefixLift 1936479
  have htrace : WordTrace (prefixWord ++ tailWord_1936479) baseStart_1936479 baseEnd_1936479 := by
    simpa [prefixWord, tailWord_1936479, baseEnd_1936479] using wordTrace_append hprefix tailTrace_1936479
  have hstable : (prefixWord ++ tailWord_1936479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936479).length < 2 ^ (prefixWord ++ tailWord_1936479).sum := by decide
  have hdescent : baseEnd_1936479 < baseStart_1936479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936480 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2]
def baseStart_1936480 : Nat := 118140960795 + 1936480 * 2 ^ 59
def prefixEnd_1936480 : Nat := 4983230072969 + 3 ^ 40 * 1936480 * 2
def baseEnd_1936480 : Nat := 994345017818688746794297

theorem tailTrace_1936480 : CollatzResearch.WordTrace tailWord_1936480 prefixEnd_1936480 994345017818688746794297 := by
  unfold tailWord_1936480
  simp only [CollatzResearch.WordTrace]
  refine ⟨35314614012235579649395447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47086152016314106199193929 35314614012235579649395447)
  ·
    refine ⟨52971921018353369474093171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35314614012235579649395447 52971921018353369474093171)
    ·
      refine ⟨79457881527530054211139757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52971921018353369474093171 79457881527530054211139757)
      ·
        refine ⟨29796705572823770329177409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79457881527530054211139757 29796705572823770329177409)
        ·
          refine ⟨22347529179617827746883057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29796705572823770329177409 22347529179617827746883057)
          ·
            refine ⟨16760646884713370810162293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22347529179617827746883057 16760646884713370810162293)
            ·
              refine ⟨1571310645441878513452715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16760646884713370810162293 1571310645441878513452715)
              ·
                refine ⟨2356965968162817770179073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571310645441878513452715 2356965968162817770179073)
                ·
                  refine ⟨1767724476122113327634305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2356965968162817770179073 1767724476122113327634305)
                  ·
                    refine ⟨1325793357091584995725729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1767724476122113327634305 1325793357091584995725729)
                    ·
                      refine ⟨994345017818688746794297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1325793357091584995725729 994345017818688746794297)
                      ·
                        rfl

theorem cell23_1936480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_1936480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936480 prefixEnd_1936480 := by exact prefixLift 1936480
  have htrace : WordTrace (prefixWord ++ tailWord_1936480) baseStart_1936480 baseEnd_1936480 := by
    simpa [prefixWord, tailWord_1936480, baseEnd_1936480] using wordTrace_append hprefix tailTrace_1936480
  have hstable : (prefixWord ++ tailWord_1936480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936480).length < 2 ^ (prefixWord ++ tailWord_1936480).sum := by decide
  have hdescent : baseEnd_1936480 < baseStart_1936480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936509 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_1936509 : Nat := 118140960795 + 1936509 * 2 ^ 59
def prefixEnd_1936509 : Nat := 4983230072969 + 3 ^ 40 * 1936509 * 2
def baseEnd_1936509 : Nat := 994359908757669133331663

theorem tailTrace_1936509 : CollatzResearch.WordTrace tailWord_1936509 prefixEnd_1936509 994359908757669133331663 := by
  unfold tailWord_1936509
  simp only [CollatzResearch.WordTrace]
  refine ⟨70630285741366097251596581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47086857160910731501064387 70630285741366097251596581)
  ·
    refine ⟨13243178576506143234674359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70630285741366097251596581 13243178576506143234674359)
    ·
      refine ⟨19864767864759214852011539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243178576506143234674359 19864767864759214852011539)
      ·
        refine ⟨29797151797138822278017309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19864767864759214852011539 29797151797138822278017309)
        ·
          refine ⟨11173931923927058354256491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29797151797138822278017309 11173931923927058354256491)
          ·
            refine ⟨16760897885890587531384737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11173931923927058354256491 16760897885890587531384737)
            ·
              refine ⟨12570673414417940648538553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16760897885890587531384737 12570673414417940648538553)
              ·
                refine ⟨9428005060813455486403915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12570673414417940648538553 9428005060813455486403915)
                ·
                  refine ⟨14142007591220183229605873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9428005060813455486403915 14142007591220183229605873)
                  ·
                    refine ⟨10606505693415137422204405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14142007591220183229605873 10606505693415137422204405)
                    ·
                      refine ⟨994359908757669133331663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10606505693415137422204405 994359908757669133331663)
                      ·
                        rfl

theorem cell23_1936509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_1936509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936509 prefixEnd_1936509 := by exact prefixLift 1936509
  have htrace : WordTrace (prefixWord ++ tailWord_1936509) baseStart_1936509 baseEnd_1936509 := by
    simpa [prefixWord, tailWord_1936509, baseEnd_1936509] using wordTrace_append hprefix tailTrace_1936509
  have hstable : (prefixWord ++ tailWord_1936509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936509).length < 2 ^ (prefixWord ++ tailWord_1936509).sum := by decide
  have hdescent : baseEnd_1936509 < baseStart_1936509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936516 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1936516 : Nat := 118140960795 + 1936516 * 2 ^ 59
def prefixEnd_1936516 : Nat := 4983230072969 + 3 ^ 40 * 1936516 * 2
def baseEnd_1936516 : Nat := 331454501040750201981377

theorem tailTrace_1936516 : CollatzResearch.WordTrace tailWord_1936516 prefixEnd_1936516 331454501040750201981377 := by
  unfold tailWord_1936516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35315270526170368723550701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47087027368227158298067601 35315270526170368723550701)
  ·
    refine ⟨13243226447313888271331513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35315270526170368723550701 13243226447313888271331513)
    ·
      refine ⟨9932419835485416203498635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13243226447313888271331513 9932419835485416203498635)
      ·
        refine ⟨14898629753228124305247953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9932419835485416203498635 14898629753228124305247953)
        ·
          refine ⟨11173972314921093228935965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14898629753228124305247953 11173972314921093228935965)
          ·
            refine ⟨4190239618095409960850987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11173972314921093228935965 4190239618095409960850987)
            ·
              refine ⟨6285359427143114941276481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190239618095409960850987 6285359427143114941276481)
              ·
                refine ⟨4714019570357336205957361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285359427143114941276481 4714019570357336205957361)
                ·
                  refine ⟨3535514677768002154468021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714019570357336205957361 3535514677768002154468021)
                  ·
                    refine ⟨331454501040750201981377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3535514677768002154468021 331454501040750201981377)
                    ·
                      rfl

theorem cell23_1936516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1936516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936516 prefixEnd_1936516 := by exact prefixLift 1936516
  have htrace : WordTrace (prefixWord ++ tailWord_1936516) baseStart_1936516 baseEnd_1936516 := by
    simpa [prefixWord, tailWord_1936516, baseEnd_1936516] using wordTrace_append hprefix tailTrace_1936516
  have hstable : (prefixWord ++ tailWord_1936516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936516).length < 2 ^ (prefixWord ++ tailWord_1936516).sum := by decide
  have hdescent : baseEnd_1936516 < baseStart_1936516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936520 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 5]
def baseStart_1936520 : Nat := 118140960795 + 1936520 * 2 ^ 59
def prefixEnd_1936520 : Nat := 4983230072969 + 3 ^ 40 * 1936520 * 2
def baseEnd_1936520 : Nat := 110485061893874287810457

theorem tailTrace_1936520 : CollatzResearch.WordTrace tailWord_1936520 prefixEnd_1936520 110485061893874287810457 := by
  unfold tailWord_1936520
  simp only [CollatzResearch.WordTrace]
  refine ⟨35315343472163123065123507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47087124629550830753498009 35315343472163123065123507)
  ·
    refine ⟨52973015208244684597685261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35315343472163123065123507 52973015208244684597685261)
    ·
      refine ⟨19864880703091756724131973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52973015208244684597685261 19864880703091756724131973)
      ·
        refine ⟨3724665131829704385774745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19864880703091756724131973 3724665131829704385774745)
        ·
          refine ⟨2793498848872278289331059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3724665131829704385774745 2793498848872278289331059)
          ·
            refine ⟨4190248273308417433996589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793498848872278289331059 4190248273308417433996589)
            ·
              refine ⟨1571343102490656537748721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4190248273308417433996589 1571343102490656537748721)
              ·
                refine ⟨1178507326867992403311541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571343102490656537748721 1178507326867992403311541)
                ·
                  refine ⟨110485061893874287810457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1178507326867992403311541 110485061893874287810457)
                  ·
                    rfl

theorem cell23_1936520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 5].length) (baseStart_1936520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936520 prefixEnd_1936520 := by exact prefixLift 1936520
  have htrace : WordTrace (prefixWord ++ tailWord_1936520) baseStart_1936520 baseEnd_1936520 := by
    simpa [prefixWord, tailWord_1936520, baseEnd_1936520] using wordTrace_append hprefix tailTrace_1936520
  have hstable : (prefixWord ++ tailWord_1936520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936520).length < 2 ^ (prefixWord ++ tailWord_1936520).sum := by decide
  have hdescent : baseEnd_1936520 < baseStart_1936520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936526 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1936526 : Nat := 118140960795 + 1936526 * 2 ^ 59
def prefixEnd_1936526 : Nat := 4983230072969 + 3 ^ 40 * 1936526 * 2
def baseEnd_1936526 : Nat := 994368637928795566819085

theorem tailTrace_1936526 : CollatzResearch.WordTrace tailWord_1936526 prefixEnd_1936526 994368637928795566819085 := by
  unfold tailWord_1936526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8828863222788063644370679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47087270521536339436643621 8828863222788063644370679)
  ·
    refine ⟨13243294834182095466556019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8828863222788063644370679 13243294834182095466556019)
    ·
      refine ⟨19864942251273143199834029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13243294834182095466556019 19864942251273143199834029)
      ·
        refine ⟨7449353344227428699937761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19864942251273143199834029 7449353344227428699937761)
        ·
          refine ⟨5587015008170571524953321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7449353344227428699937761 5587015008170571524953321)
          ·
            refine ⟨4190261256127928643714991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587015008170571524953321 4190261256127928643714991)
            ·
              refine ⟨6285391884191892965572487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190261256127928643714991 6285391884191892965572487)
              ·
                refine ⟨9428087826287839448358731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285391884191892965572487 9428087826287839448358731)
                ·
                  refine ⟨14142131739431759172538097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9428087826287839448358731 14142131739431759172538097)
                  ·
                    refine ⟨10606598804573819379403573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14142131739431759172538097 10606598804573819379403573)
                    ·
                      refine ⟨994368637928795566819085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10606598804573819379403573 994368637928795566819085)
                      ·
                        rfl

theorem cell23_1936526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1936526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936526 prefixEnd_1936526 := by exact prefixLift 1936526
  have htrace : WordTrace (prefixWord ++ tailWord_1936526) baseStart_1936526 baseEnd_1936526 := by
    simpa [prefixWord, tailWord_1936526, baseEnd_1936526] using wordTrace_append hprefix tailTrace_1936526
  have hstable : (prefixWord ++ tailWord_1936526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936526).length < 2 ^ (prefixWord ++ tailWord_1936526).sum := by decide
  have hdescent : baseEnd_1936526 < baseStart_1936526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936620 : List Nat := [2, 2, 1, 1, 2, 4, 1, 5, 1, 1, 3]
def baseStart_1936620 : Nat := 118140960795 + 1936620 * 2 ^ 59
def prefixEnd_1936620 : Nat := 4983230072969 + 3 ^ 40 * 1936620 * 2
def baseEnd_1936620 : Nat := 994416905110318199043653

theorem tailTrace_1936620 : CollatzResearch.WordTrace tailWord_1936620 prefixEnd_1936620 994416905110318199043653 := by
  unfold tailWord_1936620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35317167121981981604443657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47089556162642642139258209 35317167121981981604443657)
  ·
    refine ⟨26487875341486486203332743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35317167121981981604443657 26487875341486486203332743)
    ·
      refine ⟨39731813012229729304999115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26487875341486486203332743 39731813012229729304999115)
      ·
        refine ⟨59597719518344593957498673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39731813012229729304999115 59597719518344593957498673)
        ·
          refine ⟨44698289638758445468124005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59597719518344593957498673 44698289638758445468124005)
          ·
            refine ⟨8380929307267208525273251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44698289638758445468124005 8380929307267208525273251)
            ·
              refine ⟨12571393960900812787909877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8380929307267208525273251 12571393960900812787909877)
              ·
                refine ⟨1178568183834451198866551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12571393960900812787909877 1178568183834451198866551)
                ·
                  refine ⟨1767852275751676798299827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178568183834451198866551 1767852275751676798299827)
                  ·
                    refine ⟨2651778413627515197449741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1767852275751676798299827 2651778413627515197449741)
                    ·
                      refine ⟨994416905110318199043653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651778413627515197449741 994416905110318199043653)
                      ·
                        rfl

theorem cell23_1936620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_1936620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936620 prefixEnd_1936620 := by exact prefixLift 1936620
  have htrace : WordTrace (prefixWord ++ tailWord_1936620) baseStart_1936620 baseEnd_1936620 := by
    simpa [prefixWord, tailWord_1936620, baseEnd_1936620] using wordTrace_append hprefix tailTrace_1936620
  have hstable : (prefixWord ++ tailWord_1936620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936620).length < 2 ^ (prefixWord ++ tailWord_1936620).sum := by decide
  have hdescent : baseEnd_1936620 < baseStart_1936620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936623 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 1, 5]
def baseStart_1936623 : Nat := 118140960795 + 1936623 * 2 ^ 59
def prefixEnd_1936623 : Nat := 4983230072969 + 3 ^ 40 * 1936623 * 2
def baseEnd_1936623 : Nat := 331472815184093895768713

theorem tailTrace_1936623 : CollatzResearch.WordTrace tailWord_1936623 prefixEnd_1936623 331472815184093895768713 := by
  unfold tailWord_1936623
  simp only [CollatzResearch.WordTrace]
  refine ⟨70634443662953094721246523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47089629108635396480831015 70634443662953094721246523)
  ·
    refine ⟨105951665494429642081869785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70634443662953094721246523 105951665494429642081869785)
    ·
      refine ⟨79463749120822231561402339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105951665494429642081869785 79463749120822231561402339)
      ·
        refine ⟨119195623681233347342103509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79463749120822231561402339 119195623681233347342103509)
        ·
          refine ⟨2793647430028906578330551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 119195623681233347342103509 2793647430028906578330551)
          ·
            refine ⟨4190471145043359867495827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793647430028906578330551 4190471145043359867495827)
            ·
              refine ⟨6285706717565039801243741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190471145043359867495827 6285706717565039801243741)
              ·
                refine ⟨2357140019086889925466403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6285706717565039801243741 2357140019086889925466403)
                ·
                  refine ⟨3535710028630334888199605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357140019086889925466403 3535710028630334888199605)
                  ·
                    refine ⟨331472815184093895768713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3535710028630334888199605 331472815184093895768713)
                    ·
                      rfl

theorem cell23_1936623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_1936623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936623 prefixEnd_1936623 := by exact prefixLift 1936623
  have htrace : WordTrace (prefixWord ++ tailWord_1936623) baseStart_1936623 baseEnd_1936623 := by
    simpa [prefixWord, tailWord_1936623, baseEnd_1936623] using wordTrace_append hprefix tailTrace_1936623
  have hstable : (prefixWord ++ tailWord_1936623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936623).length < 2 ^ (prefixWord ++ tailWord_1936623).sum := by decide
  have hdescent : baseEnd_1936623 < baseStart_1936623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936649 : List Nat := [1, 2, 1, 1, 3, 3, 2, 10]
def baseStart_1936649 : Nat := 118140960795 + 1936649 * 2 ^ 59
def prefixEnd_1936649 : Nat := 4983230072969 + 3 ^ 40 * 1936649 * 2
def baseEnd_1936649 : Nat := 36830807261085132799297

theorem tailTrace_1936649 : CollatzResearch.WordTrace tailWord_1936649 prefixEnd_1936649 36830807261085132799297 := by
  unfold tailWord_1936649
  simp only [CollatzResearch.WordTrace]
  refine ⟨70635391960858901161693001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47090261307239267441128667 70635391960858901161693001)
  ·
    refine ⟨52976543970644175871269751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70635391960858901161693001 52976543970644175871269751)
    ·
      refine ⟨79464815955966263806904627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52976543970644175871269751 79464815955966263806904627)
      ·
        refine ⟨119197223933949395710356941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79464815955966263806904627 119197223933949395710356941)
        ·
          refine ⟨44698958975231023391383853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119197223933949395710356941 44698958975231023391383853)
          ·
            refine ⟨16762109615711633771768945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44698958975231023391383853 16762109615711633771768945)
            ·
              refine ⟨12571582211783725328826709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16762109615711633771768945 12571582211783725328826709)
              ·
                refine ⟨36830807261085132799297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12571582211783725328826709 36830807261085132799297)
                ·
                  rfl

theorem cell23_1936649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 10].length) (baseStart_1936649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936649 prefixEnd_1936649 := by exact prefixLift 1936649
  have htrace : WordTrace (prefixWord ++ tailWord_1936649) baseStart_1936649 baseEnd_1936649 := by
    simpa [prefixWord, tailWord_1936649, baseEnd_1936649] using wordTrace_append hprefix tailTrace_1936649
  have hstable : (prefixWord ++ tailWord_1936649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936649).length < 2 ^ (prefixWord ++ tailWord_1936649).sum := by decide
  have hdescent : baseEnd_1936649 < baseStart_1936649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936666 : List Nat := [3, 1, 1, 3, 3, 2, 1, 9]
def baseStart_1936666 : Nat := 118140960795 + 1936666 * 2 ^ 59
def prefixEnd_1936666 : Nat := 4983230072969 + 3 ^ 40 * 1936666 * 2
def baseEnd_1936666 : Nat := 36831130563719445150683

theorem tailTrace_1936666 : CollatzResearch.WordTrace tailWord_1936666 prefixEnd_1936666 36831130563719445150683 := by
  unfold tailWord_1936666
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659003000449328266265463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47090674667864875376707901 17659003000449328266265463)
  ·
    refine ⟨26488504500673992399398195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17659003000449328266265463 26488504500673992399398195)
    ·
      refine ⟨39732756751010988599097293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26488504500673992399398195 39732756751010988599097293)
      ·
        refine ⟨14899783781629120724661485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39732756751010988599097293 14899783781629120724661485)
        ·
          refine ⟨5587418918110920271748057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14899783781629120724661485 5587418918110920271748057)
          ·
            refine ⟨4190564188583190203811043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5587418918110920271748057 4190564188583190203811043)
            ·
              refine ⟨6285846282874785305716565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190564188583190203811043 6285846282874785305716565)
              ·
                refine ⟨36831130563719445150683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6285846282874785305716565 36831130563719445150683)
                ·
                  rfl

theorem cell23_1936666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_1936666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936666 prefixEnd_1936666 := by exact prefixLift 1936666
  have htrace : WordTrace (prefixWord ++ tailWord_1936666) baseStart_1936666 baseEnd_1936666 := by
    simpa [prefixWord, tailWord_1936666, baseEnd_1936666] using wordTrace_append hprefix tailTrace_1936666
  have hstable : (prefixWord ++ tailWord_1936666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936666).length < 2 ^ (prefixWord ++ tailWord_1936666).sum := by decide
  have hdescent : baseEnd_1936666 < baseStart_1936666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936680 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1936680 : Nat := 118140960795 + 1936680 * 2 ^ 59
def prefixEnd_1936680 : Nat := 4983230072969 + 3 ^ 40 * 1936680 * 2
def baseEnd_1936680 : Nat := 994447713949587964293377

theorem tailTrace_1936680 : CollatzResearch.WordTrace tailWord_1936680 prefixEnd_1936680 994447713949587964293377 := by
  unfold tailWord_1936680
  simp only [CollatzResearch.WordTrace]
  refine ⟨35318261311873296728035747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47091015082497728970714329 35318261311873296728035747)
  ·
    refine ⟨52977391967809945092053621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35318261311873296728035747 52977391967809945092053621)
    ·
      refine ⟨4966630496982182352380027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52977391967809945092053621 4966630496982182352380027)
      ·
        refine ⟨7449945745473273528570041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966630496982182352380027 7449945745473273528570041)
        ·
          refine ⟨5587459309104955146427531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7449945745473273528570041 5587459309104955146427531)
          ·
            refine ⟨8381188963657432719641297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587459309104955146427531 8381188963657432719641297)
            ·
              refine ⟨6285891722743074539730973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381188963657432719641297 6285891722743074539730973)
              ·
                refine ⟨2357209396028652952399115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6285891722743074539730973 2357209396028652952399115)
                ·
                  refine ⟨3535814094042979428598673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357209396028652952399115 3535814094042979428598673)
                  ·
                    refine ⟨2651860570532234571449005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3535814094042979428598673 2651860570532234571449005)
                    ·
                      refine ⟨994447713949587964293377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2651860570532234571449005 994447713949587964293377)
                      ·
                        rfl

theorem cell23_1936680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1936680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936680 prefixEnd_1936680 := by exact prefixLift 1936680
  have htrace : WordTrace (prefixWord ++ tailWord_1936680) baseStart_1936680 baseEnd_1936680 := by
    simpa [prefixWord, tailWord_1936680, baseEnd_1936680] using wordTrace_append hprefix tailTrace_1936680
  have hstable : (prefixWord ++ tailWord_1936680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936680).length < 2 ^ (prefixWord ++ tailWord_1936680).sum := by decide
  have hdescent : baseEnd_1936680 < baseStart_1936680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936699 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_1936699 : Nat := 118140960795 + 1936699 * 2 ^ 59
def prefixEnd_1936699 : Nat := 4983230072969 + 3 ^ 40 * 1936699 * 2
def baseEnd_1936699 : Nat := 994457470082023389955789

theorem tailTrace_1936699 : CollatzResearch.WordTrace tailWord_1936699 prefixEnd_1936699 994457470082023389955789 := by
  unfold tailWord_1936699
  simp only [CollatzResearch.WordTrace]
  refine ⟨70637215610677759701013151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47091477073785173134008767 70637215610677759701013151)
  ·
    refine ⟨105955823416016639551519727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70637215610677759701013151 105955823416016639551519727)
    ·
      refine ⟨158933735124024959327279591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105955823416016639551519727 158933735124024959327279591)
      ·
        refine ⟨238400602686037438990919387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158933735124024959327279591 238400602686037438990919387)
        ·
          refine ⟨357600904029056158486379081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238400602686037438990919387 357600904029056158486379081)
          ·
            refine ⟨268200678021792118864784311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357600904029056158486379081 268200678021792118864784311)
            ·
              refine ⟨402301017032688178297176467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268200678021792118864784311 402301017032688178297176467)
              ·
                refine ⟨603451525549032267445764701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402301017032688178297176467 603451525549032267445764701)
                ·
                  refine ⟨226294322080887100292161763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603451525549032267445764701 226294322080887100292161763)
                  ·
                    refine ⟨339441483121330650438242645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226294322080887100292161763 339441483121330650438242645)
                    ·
                      refine ⟨994457470082023389955789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 339441483121330650438242645 994457470082023389955789)
                      ·
                        rfl

theorem cell23_1936699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_1936699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936699 prefixEnd_1936699 := by exact prefixLift 1936699
  have htrace : WordTrace (prefixWord ++ tailWord_1936699) baseStart_1936699 baseEnd_1936699 := by
    simpa [prefixWord, tailWord_1936699, baseEnd_1936699] using wordTrace_append hprefix tailTrace_1936699
  have hstable : (prefixWord ++ tailWord_1936699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936699).length < 2 ^ (prefixWord ++ tailWord_1936699).sum := by decide
  have hdescent : baseEnd_1936699 < baseStart_1936699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936843 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3]
def baseStart_1936843 : Nat := 118140960795 + 1936843 * 2 ^ 59
def prefixEnd_1936843 : Nat := 4983230072969 + 3 ^ 40 * 1936843 * 2
def baseEnd_1936843 : Nat := 994531411296270826555127

theorem tailTrace_1936843 : CollatzResearch.WordTrace tailWord_1936843 prefixEnd_1936843 994531411296270826555127 := by
  unfold tailWord_1936843
  simp only [CollatzResearch.WordTrace]
  refine ⟨70642467722156072294255183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47094978481437381529503455 70642467722156072294255183)
  ·
    refine ⟨105963701583234108441382775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70642467722156072294255183 105963701583234108441382775)
    ·
      refine ⟨158945552374851162662074163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105963701583234108441382775 158945552374851162662074163)
      ·
        refine ⟨238418328562276743993111245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158945552374851162662074163 238418328562276743993111245)
        ·
          refine ⟨89406873210853778997416717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238418328562276743993111245 89406873210853778997416717)
          ·
            refine ⟨33527577454070167124031269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89406873210853778997416717 33527577454070167124031269)
            ·
              refine ⟨6286420772638156335755863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33527577454070167124031269 6286420772638156335755863)
              ·
                refine ⟨9429631158957234503633795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286420772638156335755863 9429631158957234503633795)
                ·
                  refine ⟨14144446738435851755450693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429631158957234503633795 14144446738435851755450693)
                  ·
                    refine ⟨2652083763456722204147005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14144446738435851755450693 2652083763456722204147005)
                    ·
                      refine ⟨994531411296270826555127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652083763456722204147005 994531411296270826555127)
                      ·
                        rfl

theorem cell23_1936843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3].length) (baseStart_1936843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936843 prefixEnd_1936843 := by exact prefixLift 1936843
  have htrace : WordTrace (prefixWord ++ tailWord_1936843) baseStart_1936843 baseEnd_1936843 := by
    simpa [prefixWord, tailWord_1936843, baseEnd_1936843] using wordTrace_append hprefix tailTrace_1936843
  have hstable : (prefixWord ++ tailWord_1936843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936843).length < 2 ^ (prefixWord ++ tailWord_1936843).sum := by decide
  have hdescent : baseEnd_1936843 < baseStart_1936843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936863 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 6]
def baseStart_1936863 : Nat := 118140960795 + 1936863 * 2 ^ 59
def prefixEnd_1936863 : Nat := 4983230072969 + 3 ^ 40 * 1936863 * 2
def baseEnd_1936863 : Nat := 110504631212151194256115

theorem tailTrace_1936863 : CollatzResearch.WordTrace tailWord_1936863 prefixEnd_1936863 110504631212151194256115 := by
  unfold tailWord_1936863
  simp only [CollatzResearch.WordTrace]
  refine ⟨70643197182083615709983243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47095464788055743806655495 70643197182083615709983243)
  ·
    refine ⟨105964795773125423564974865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70643197182083615709983243 105964795773125423564974865)
    ·
      refine ⟨79473596829844067673731149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105964795773125423564974865 79473596829844067673731149)
      ·
        refine ⟨29802598811191525377649181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79473596829844067673731149 29802598811191525377649181)
        ·
          refine ⟨11175974554196822016618443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29802598811191525377649181 11175974554196822016618443)
          ·
            refine ⟨16763961831295233024927665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11175974554196822016618443 16763961831295233024927665)
            ·
              refine ⟨12572971373471424768695749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16763961831295233024927665 12572971373471424768695749)
              ·
                refine ⟨2357432132525892144130453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12572971373471424768695749 2357432132525892144130453)
                ·
                  refine ⟨110504631212151194256115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2357432132525892144130453 110504631212151194256115)
                  ·
                    rfl

theorem cell23_1936863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 6].length) (baseStart_1936863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936863 prefixEnd_1936863 := by exact prefixLift 1936863
  have htrace : WordTrace (prefixWord ++ tailWord_1936863) baseStart_1936863 baseEnd_1936863 := by
    simpa [prefixWord, tailWord_1936863, baseEnd_1936863] using wordTrace_append hprefix tailTrace_1936863
  have hstable : (prefixWord ++ tailWord_1936863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936863).length < 2 ^ (prefixWord ++ tailWord_1936863).sum := by decide
  have hdescent : baseEnd_1936863 < baseStart_1936863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936867 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 3, 4]
def baseStart_1936867 : Nat := 118140960795 + 1936867 * 2 ^ 59
def prefixEnd_1936867 : Nat := 4983230072969 + 3 ^ 40 * 1936867 * 2
def baseEnd_1936867 : Nat := 331514578277326244218339

theorem tailTrace_1936867 : CollatzResearch.WordTrace tailWord_1936867 prefixEnd_1936867 331514578277326244218339 := by
  unfold tailWord_1936867
  simp only [CollatzResearch.WordTrace]
  refine ⟨70643343074069124393128855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47095562049379416262085903 70643343074069124393128855)
  ·
    refine ⟨105965014611103686589693283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70643343074069124393128855 105965014611103686589693283)
    ·
      refine ⟨158947521916655529884539925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105965014611103686589693283 158947521916655529884539925)
      ·
        refine ⟨7450665089843227963337809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158947521916655529884539925 7450665089843227963337809)
        ·
          refine ⟨5587998817382420972503357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7450665089843227963337809 5587998817382420972503357)
          ·
            refine ⟨2095499556518407864688759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5587998817382420972503357 2095499556518407864688759)
            ·
              refine ⟨3143249334777611797033139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095499556518407864688759 3143249334777611797033139)
              ·
                refine ⟨4714874002166417695549709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143249334777611797033139 4714874002166417695549709)
                ·
                  refine ⟨1768077750812406635831141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4714874002166417695549709 1768077750812406635831141)
                  ·
                    refine ⟨331514578277326244218339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768077750812406635831141 331514578277326244218339)
                    ·
                      rfl

theorem cell23_1936867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 4].length) (baseStart_1936867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936867 prefixEnd_1936867 := by exact prefixLift 1936867
  have htrace : WordTrace (prefixWord ++ tailWord_1936867) baseStart_1936867 baseEnd_1936867 := by
    simpa [prefixWord, tailWord_1936867, baseEnd_1936867] using wordTrace_append hprefix tailTrace_1936867
  have hstable : (prefixWord ++ tailWord_1936867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936867).length < 2 ^ (prefixWord ++ tailWord_1936867).sum := by decide
  have hdescent : baseEnd_1936867 < baseStart_1936867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936880 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 6]
def baseStart_1936880 : Nat := 118140960795 + 1936880 * 2 ^ 59
def prefixEnd_1936880 : Nat := 4983230072969 + 3 ^ 40 * 1936880 * 2
def baseEnd_1936880 : Nat := 110505601120054131310273

theorem tailTrace_1936880 : CollatzResearch.WordTrace tailWord_1936880 prefixEnd_1936880 110505601120054131310273 := by
  unfold tailWord_1936880
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321908611511013806676047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47095878148681351742234729 35321908611511013806676047)
  ·
    refine ⟨52982862917266520710014071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35321908611511013806676047 52982862917266520710014071)
    ·
      refine ⟨79474294375899781065021107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52982862917266520710014071 79474294375899781065021107)
      ·
        refine ⟨119211441563849671597531661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79474294375899781065021107 119211441563849671597531661)
        ·
          refine ⟨44704290586443626849074373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119211441563849671597531661 44704290586443626849074373)
          ·
            refine ⟨8382054484958180034201445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44704290586443626849074373 8382054484958180034201445)
            ·
              refine ⟨1571635215929658756412771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8382054484958180034201445 1571635215929658756412771)
              ·
                refine ⟨2357452823894488134619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1571635215929658756412771 2357452823894488134619157)
                ·
                  refine ⟨110505601120054131310273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2357452823894488134619157 110505601120054131310273)
                  ·
                    rfl

theorem cell23_1936880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 6].length) (baseStart_1936880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936880 prefixEnd_1936880 := by exact prefixLift 1936880
  have htrace : WordTrace (prefixWord ++ tailWord_1936880) baseStart_1936880 baseEnd_1936880 := by
    simpa [prefixWord, tailWord_1936880, baseEnd_1936880] using wordTrace_append hprefix tailTrace_1936880
  have hstable : (prefixWord ++ tailWord_1936880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936880).length < 2 ^ (prefixWord ++ tailWord_1936880).sum := by decide
  have hdescent : baseEnd_1936880 < baseStart_1936880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936890 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_1936890 : Nat := 118140960795 + 1936890 * 2 ^ 59
def prefixEnd_1936890 : Nat := 4983230072969 + 3 ^ 40 * 1936890 * 2
def baseEnd_1936890 : Nat := 994555544887032142667411

theorem tailTrace_1936890 : CollatzResearch.WordTrace tailWord_1936890 prefixEnd_1936890 994555544887032142667411 := by
  unfold tailWord_1936890
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661045488246449830304031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47096121301990532880810749 17661045488246449830304031)
  ·
    refine ⟨26491568232369674745456047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17661045488246449830304031 26491568232369674745456047)
    ·
      refine ⟨39737352348554512118184071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26491568232369674745456047 39737352348554512118184071)
      ·
        refine ⟨59606028522831768177276107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39737352348554512118184071 59606028522831768177276107)
        ·
          refine ⟨89409042784247652265914161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59606028522831768177276107 89409042784247652265914161)
          ·
            refine ⟨67056782088185739199435621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89409042784247652265914161 67056782088185739199435621)
            ·
              refine ⟨12573146641534826099894179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67056782088185739199435621 12573146641534826099894179)
              ·
                refine ⟨18859719962302239149841269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573146641534826099894179 18859719962302239149841269)
                ·
                  refine ⟨1768098746465834920297619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18859719962302239149841269 1768098746465834920297619)
                  ·
                    refine ⟨2652148119698752380446429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768098746465834920297619 2652148119698752380446429)
                    ·
                      refine ⟨994555544887032142667411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652148119698752380446429 994555544887032142667411)
                      ·
                        rfl

theorem cell23_1936890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_1936890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936890 prefixEnd_1936890 := by exact prefixLift 1936890
  have htrace : WordTrace (prefixWord ++ tailWord_1936890) baseStart_1936890 baseEnd_1936890 := by
    simpa [prefixWord, tailWord_1936890, baseEnd_1936890] using wordTrace_append hprefix tailTrace_1936890
  have hstable : (prefixWord ++ tailWord_1936890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936890).length < 2 ^ (prefixWord ++ tailWord_1936890).sum := by decide
  have hdescent : baseEnd_1936890 < baseStart_1936890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936917 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_1936917 : Nat := 118140960795 + 1936917 * 2 ^ 59
def prefixEnd_1936917 : Nat := 4983230072969 + 3 ^ 40 * 1936917 * 2
def baseEnd_1936917 : Nat := 994569408864703537029787

theorem tailTrace_1936917 : CollatzResearch.WordTrace tailWord_1936917 prefixEnd_1936917 994569408864703537029787 := by
  unfold tailWord_1936917
  simp only [CollatzResearch.WordTrace]
  refine ⟨70645166723887982932449005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47096777815925321954966003 70645166723887982932449005)
  ·
    refine ⟨26491937521457993599668377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70645166723887982932449005 26491937521457993599668377)
    ·
      refine ⟨19868953141093495199751283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26491937521457993599668377 19868953141093495199751283)
      ·
        refine ⟨29803429711640242799626925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19868953141093495199751283 29803429711640242799626925)
        ·
          refine ⟨11176286141865091049860097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29803429711640242799626925 11176286141865091049860097)
          ·
            refine ⟨8382214606398818287395073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11176286141865091049860097 8382214606398818287395073)
            ·
              refine ⟨6286660954799113715546305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8382214606398818287395073 6286660954799113715546305)
              ·
                refine ⟨4714995716099335286659729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286660954799113715546305 4714995716099335286659729)
                ·
                  refine ⟨3536246787074501464994797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714995716099335286659729 3536246787074501464994797)
                  ·
                    refine ⟨1326092545152938049373049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3536246787074501464994797 1326092545152938049373049)
                    ·
                      refine ⟨994569408864703537029787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326092545152938049373049 994569408864703537029787)
                      ·
                        rfl

theorem cell23_1936917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_1936917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936917 prefixEnd_1936917 := by exact prefixLift 1936917
  have htrace : WordTrace (prefixWord ++ tailWord_1936917) baseStart_1936917 baseEnd_1936917 := by
    simpa [prefixWord, tailWord_1936917, baseEnd_1936917] using wordTrace_append hprefix tailTrace_1936917
  have hstable : (prefixWord ++ tailWord_1936917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936917).length < 2 ^ (prefixWord ++ tailWord_1936917).sum := by decide
  have hdescent : baseEnd_1936917 < baseStart_1936917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936924 : List Nat := [2, 2, 3, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1936924 : Nat := 118140960795 + 1936924 * 2 ^ 59
def prefixEnd_1936924 : Nat := 4983230072969 + 3 ^ 40 * 1936924 * 2
def baseEnd_1936924 : Nat := 994573003229285009642255

theorem tailTrace_1936924 : CollatzResearch.WordTrace tailWord_1936924 prefixEnd_1936924 994573003229285009642255 := by
  unfold tailWord_1936924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35322711017431311563976913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47096948023241748751969217 35322711017431311563976913)
  ·
    refine ⟨26492033263073483672982685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35322711017431311563976913 26492033263073483672982685)
    ·
      refine ⟨9934512473652556377368507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26492033263073483672982685 9934512473652556377368507)
      ·
        refine ⟨14901768710478834566052761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9934512473652556377368507 14901768710478834566052761)
        ·
          refine ⟨11176326532859125924539571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14901768710478834566052761 11176326532859125924539571)
          ·
            refine ⟨16764489799288688886809357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176326532859125924539571 16764489799288688886809357)
            ·
              refine ⟨6286683674733258332553509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16764489799288688886809357 6286683674733258332553509)
              ·
                refine ⟨1178753189012485937353783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6286683674733258332553509 1178753189012485937353783)
                ·
                  refine ⟨1768129783518728906030675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178753189012485937353783 1768129783518728906030675)
                  ·
                    refine ⟨2652194675278093359046013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768129783518728906030675 2652194675278093359046013)
                    ·
                      refine ⟨994573003229285009642255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652194675278093359046013 994573003229285009642255)
                      ·
                        rfl

theorem cell23_1936924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1936924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936924 prefixEnd_1936924 := by exact prefixLift 1936924
  have htrace : WordTrace (prefixWord ++ tailWord_1936924) baseStart_1936924 baseEnd_1936924 := by
    simpa [prefixWord, tailWord_1936924, baseEnd_1936924] using wordTrace_append hprefix tailTrace_1936924
  have hstable : (prefixWord ++ tailWord_1936924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936924).length < 2 ^ (prefixWord ++ tailWord_1936924).sum := by decide
  have hdescent : baseEnd_1936924 < baseStart_1936924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936930 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_1936930 : Nat := 118140960795 + 1936930 * 2 ^ 59
def prefixEnd_1936930 : Nat := 4983230072969 + 3 ^ 40 * 1936930 * 2
def baseEnd_1936930 : Nat := 994576084113211986167227

theorem tailTrace_1936930 : CollatzResearch.WordTrace tailWord_1936930 prefixEnd_1936930 994576084113211986167227 := by
  unfold tailWord_1936930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17661410218210221538168061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47097093915227257435114829 17661410218210221538168061)
  ·
    refine ⟨6623028831828833076813023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17661410218210221538168061 6623028831828833076813023)
    ·
      refine ⟨9934543247743249615219535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623028831828833076813023 9934543247743249615219535)
      ·
        refine ⟨14901814871614874422829303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9934543247743249615219535 14901814871614874422829303)
        ·
          refine ⟨22352722307422311634243955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14901814871614874422829303 22352722307422311634243955)
          ·
            refine ⟨33529083461133467451365933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22352722307422311634243955 33529083461133467451365933)
            ·
              refine ⟨12573406297925050294262225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33529083461133467451365933 12573406297925050294262225)
              ·
                refine ⟨9430054723443787720696669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573406297925050294262225 9430054723443787720696669)
                ·
                  refine ⟨3536270521291420395261251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9430054723443787720696669 3536270521291420395261251)
                  ·
                    refine ⟨5304405781937130592891877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3536270521291420395261251 5304405781937130592891877)
                    ·
                      refine ⟨994576084113211986167227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5304405781937130592891877 994576084113211986167227)
                      ·
                        rfl

theorem cell23_1936930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_1936930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936930 prefixEnd_1936930 := by exact prefixLift 1936930
  have htrace : WordTrace (prefixWord ++ tailWord_1936930) baseStart_1936930 baseEnd_1936930 := by
    simpa [prefixWord, tailWord_1936930, baseEnd_1936930] using wordTrace_append hprefix tailTrace_1936930
  have hstable : (prefixWord ++ tailWord_1936930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936930).length < 2 ^ (prefixWord ++ tailWord_1936930).sum := by decide
  have hdescent : baseEnd_1936930 < baseStart_1936930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936933 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1936933 : Nat := 118140960795 + 1936933 * 2 ^ 59
def prefixEnd_1936933 : Nat := 4983230072969 + 3 ^ 40 * 1936933 * 2
def baseEnd_1936933 : Nat := 994577624555175474429713

theorem tailTrace_1936933 : CollatzResearch.WordTrace tailWord_1936933 prefixEnd_1936933 994577624555175474429713 := by
  unfold tailWord_1936933
  simp only [CollatzResearch.WordTrace]
  refine ⟨70645750291830017665031453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47097166861220011776687635 70645750291830017665031453)
  ·
    refine ⟨26492156359436256624386795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70645750291830017665031453 26492156359436256624386795)
    ·
      refine ⟨39738234539154384936580193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26492156359436256624386795 39738234539154384936580193)
      ·
        refine ⟨29803675904365788702435145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39738234539154384936580193 29803675904365788702435145)
        ·
          refine ⟨22352756928274341526826359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29803675904365788702435145 22352756928274341526826359)
          ·
            refine ⟨33529135392411512290239539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22352756928274341526826359 33529135392411512290239539)
            ·
              refine ⟨50293703088617268435359309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33529135392411512290239539 50293703088617268435359309)
              ·
                refine ⟨18860138658231475663259741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50293703088617268435359309 18860138658231475663259741)
                ·
                  refine ⟨7072551996836803373722403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18860138658231475663259741 7072551996836803373722403)
                  ·
                    refine ⟨10608827995255205060583605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072551996836803373722403 10608827995255205060583605)
                    ·
                      refine ⟨994577624555175474429713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10608827995255205060583605 994577624555175474429713)
                      ·
                        rfl

theorem cell23_1936933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1936933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936933 prefixEnd_1936933 := by exact prefixLift 1936933
  have htrace : WordTrace (prefixWord ++ tailWord_1936933) baseStart_1936933 baseEnd_1936933 := by
    simpa [prefixWord, tailWord_1936933, baseEnd_1936933] using wordTrace_append hprefix tailTrace_1936933
  have hstable : (prefixWord ++ tailWord_1936933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936933).length < 2 ^ (prefixWord ++ tailWord_1936933).sum := by decide
  have hdescent : baseEnd_1936933 < baseStart_1936933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936947 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 5, 2, 2]
def baseStart_1936947 : Nat := 118140960795 + 1936947 * 2 ^ 59
def prefixEnd_1936947 : Nat := 4983230072969 + 3 ^ 40 * 1936947 * 2
def baseEnd_1936947 : Nat := 994584813284338419654649

theorem tailTrace_1936947 : CollatzResearch.WordTrace tailWord_1936947 prefixEnd_1936947 994584813284338419654649 := by
  unfold tailWord_1936947
  simp only [CollatzResearch.WordTrace]
  refine ⟨70646260913779298056041095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47097507275852865370694063 70646260913779298056041095)
  ·
    refine ⟨105969391370668947084061643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70646260913779298056041095 105969391370668947084061643)
    ·
      refine ⟨158954087056003420626092465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105969391370668947084061643 158954087056003420626092465)
      ·
        refine ⟨119215565292002565469569349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158954087056003420626092465 119215565292002565469569349)
        ·
          refine ⟨22352918492250481025544253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119215565292002565469569349 22352918492250481025544253)
          ·
            refine ⟨8382344434593930384579095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22352918492250481025544253 8382344434593930384579095)
            ·
              refine ⟨12573516651890895576868643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382344434593930384579095 12573516651890895576868643)
              ·
                refine ⟨18860274977836343365302965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573516651890895576868643 18860274977836343365302965)
                ·
                  refine ⟨1768150779172157190497153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18860274977836343365302965 1768150779172157190497153)
                  ·
                    refine ⟨1326113084379117892872865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1768150779172157190497153 1326113084379117892872865)
                    ·
                      refine ⟨994584813284338419654649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326113084379117892872865 994584813284338419654649)
                      ·
                        rfl

theorem cell23_1936947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 2, 2].length) (baseStart_1936947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936947 prefixEnd_1936947 := by exact prefixLift 1936947
  have htrace : WordTrace (prefixWord ++ tailWord_1936947) baseStart_1936947 baseEnd_1936947 := by
    simpa [prefixWord, tailWord_1936947, baseEnd_1936947] using wordTrace_append hprefix tailTrace_1936947
  have hstable : (prefixWord ++ tailWord_1936947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936947).length < 2 ^ (prefixWord ++ tailWord_1936947).sum := by decide
  have hdescent : baseEnd_1936947 < baseStart_1936947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1936997 : List Nat := [1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1936997 : Nat := 118140960795 + 1936997 * 2 ^ 59
def prefixEnd_1936997 : Nat := 4983230072969 + 3 ^ 40 * 1936997 * 2
def baseEnd_1936997 : Nat := 994610487317063224029419

theorem tailTrace_1936997 : CollatzResearch.WordTrace tailWord_1936997 prefixEnd_1936997 994610487317063224029419 := by
  unfold tailWord_1936997
  simp only [CollatzResearch.WordTrace]
  refine ⟨70648084563598156595361245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47098723042398771063574163 70648084563598156595361245)
  ·
    refine ⟨26493031711349308723260467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70648084563598156595361245 26493031711349308723260467)
    ·
      refine ⟨39739547567023963084890701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26493031711349308723260467 39739547567023963084890701)
      ·
        refine ⟨14902330337633986156834013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39739547567023963084890701 14902330337633986156834013)
        ·
          refine ⟨5588373876612744808812755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14902330337633986156834013 5588373876612744808812755)
          ·
            refine ⟨8382560814919117213219133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588373876612744808812755 8382560814919117213219133)
            ·
              refine ⟨3143460305594668954957175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8382560814919117213219133 3143460305594668954957175)
              ·
                refine ⟨4715190458392003432435763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143460305594668954957175 4715190458392003432435763)
                ·
                  refine ⟨7072785687588005148653645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715190458392003432435763 7072785687588005148653645)
                  ·
                    refine ⟨2652294632845501930745117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7072785687588005148653645 2652294632845501930745117)
                    ·
                      refine ⟨994610487317063224029419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652294632845501930745117 994610487317063224029419)
                      ·
                        rfl

theorem cell23_1936997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1936997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1936997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1936997 prefixEnd_1936997 := by exact prefixLift 1936997
  have htrace : WordTrace (prefixWord ++ tailWord_1936997) baseStart_1936997 baseEnd_1936997 := by
    simpa [prefixWord, tailWord_1936997, baseEnd_1936997] using wordTrace_append hprefix tailTrace_1936997
  have hstable : (prefixWord ++ tailWord_1936997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1936997).length < 2 ^ (prefixWord ++ tailWord_1936997).sum := by decide
  have hdescent : baseEnd_1936997 < baseStart_1936997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1936997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937003 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_1937003 : Nat := 118140960795 + 1937003 * 2 ^ 59
def prefixEnd_1937003 : Nat := 4983230072969 + 3 ^ 40 * 1937003 * 2
def baseEnd_1937003 : Nat := 994613568200990200554391

theorem tailTrace_1937003 : CollatzResearch.WordTrace tailWord_1937003 prefixEnd_1937003 994613568200990200554391 := by
  unfold tailWord_1937003
  simp only [CollatzResearch.WordTrace]
  refine ⟨70648303401576419620079663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47098868934384279746719775 70648303401576419620079663)
  ·
    refine ⟨105972455102364629430119495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70648303401576419620079663 105972455102364629430119495)
    ·
      refine ⟨158958682653546944145179243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105972455102364629430119495 158958682653546944145179243)
      ·
        refine ⟨238438023980320416217768865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158958682653546944145179243 238438023980320416217768865)
        ·
          refine ⟨178828517985240312163326649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238438023980320416217768865 178828517985240312163326649)
          ·
            refine ⟨134121388488930234122494987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178828517985240312163326649 134121388488930234122494987)
            ·
              refine ⟨201182082733395351183742481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134121388488930234122494987 201182082733395351183742481)
              ·
                refine ⟨150886562050046513387806861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201182082733395351183742481 150886562050046513387806861)
                ·
                  refine ⟨56582460768767442520427573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150886562050046513387806861 56582460768767442520427573)
                  ·
                    refine ⟨5304605697071947736290085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56582460768767442520427573 5304605697071947736290085)
                    ·
                      refine ⟨994613568200990200554391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5304605697071947736290085 994613568200990200554391)
                      ·
                        rfl

theorem cell23_1937003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_1937003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937003 prefixEnd_1937003 := by exact prefixLift 1937003
  have htrace : WordTrace (prefixWord ++ tailWord_1937003) baseStart_1937003 baseEnd_1937003 := by
    simpa [prefixWord, tailWord_1937003, baseEnd_1937003] using wordTrace_append hprefix tailTrace_1937003
  have hstable : (prefixWord ++ tailWord_1937003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937003).length < 2 ^ (prefixWord ++ tailWord_1937003).sum := by decide
  have hdescent : baseEnd_1937003 < baseStart_1937003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937010 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1937010 : Nat := 118140960795 + 1937010 * 2 ^ 59
def prefixEnd_1937010 : Nat := 4983230072969 + 3 ^ 40 * 1937010 * 2
def baseEnd_1937010 : Nat := 994617162565571673166859

theorem tailTrace_1937010 : CollatzResearch.WordTrace tailWord_1937010 prefixEnd_1937010 994617162565571673166859 := by
  unfold tailWord_1937010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17662139678137764953896121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47099039141700706543722989 17662139678137764953896121)
  ·
    refine ⟨13246604758603323715422091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17662139678137764953896121 13246604758603323715422091)
    ·
      refine ⟨19869907137904985573133137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13246604758603323715422091 19869907137904985573133137)
      ·
        refine ⟨14902430353428739179849853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19869907137904985573133137 14902430353428739179849853)
        ·
          refine ⟨5588411382535777192443695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14902430353428739179849853 5588411382535777192443695)
          ·
            refine ⟨8382617073803665788665543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588411382535777192443695 8382617073803665788665543)
            ·
              refine ⟨12573925610705498682998315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382617073803665788665543 12573925610705498682998315)
              ·
                refine ⟨18860888416058248024497473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573925610705498682998315 18860888416058248024497473)
                ·
                  refine ⟨14145666312043686018373105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18860888416058248024497473 14145666312043686018373105)
                  ·
                    refine ⟨10609249734032764513779829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14145666312043686018373105 10609249734032764513779829)
                    ·
                      refine ⟨994617162565571673166859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10609249734032764513779829 994617162565571673166859)
                      ·
                        rfl

theorem cell23_1937010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1937010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937010 prefixEnd_1937010 := by exact prefixLift 1937010
  have htrace : WordTrace (prefixWord ++ tailWord_1937010) baseStart_1937010 baseEnd_1937010 := by
    simpa [prefixWord, tailWord_1937010, baseEnd_1937010] using wordTrace_append hprefix tailTrace_1937010
  have hstable : (prefixWord ++ tailWord_1937010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937010).length < 2 ^ (prefixWord ++ tailWord_1937010).sum := by decide
  have hdescent : baseEnd_1937010 < baseStart_1937010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937014 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1937014 : Nat := 118140960795 + 1937014 * 2 ^ 59
def prefixEnd_1937014 : Nat := 4983230072969 + 3 ^ 40 * 1937014 * 2
def baseEnd_1937014 : Nat := 994619216488189657516841

theorem tailTrace_1937014 : CollatzResearch.WordTrace tailWord_1937014 prefixEnd_1937014 994619216488189657516841 := by
  unfold tailWord_1937014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415544037783535531170631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47099136403024378999153397 4415544037783535531170631)
  ·
    refine ⟨6623316056675303296755947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415544037783535531170631 6623316056675303296755947)
    ·
      refine ⟨9934974085012954945133921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623316056675303296755947 9934974085012954945133921)
      ·
        refine ⟨7451230563759716208850441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9934974085012954945133921 7451230563759716208850441)
        ·
          refine ⟨5588422922819787156637831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451230563759716208850441 5588422922819787156637831)
          ·
            refine ⟨8382634384229680734956747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588422922819787156637831 8382634384229680734956747)
            ·
              refine ⟨12573951576344521102435121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382634384229680734956747 12573951576344521102435121)
              ·
                refine ⟨9430463682258390826826341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573951576344521102435121 9430463682258390826826341)
                ·
                  refine ⟨1768211940423448280029939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9430463682258390826826341 1768211940423448280029939)
                  ·
                    refine ⟨2652317910635172420044909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768211940423448280029939 2652317910635172420044909)
                    ·
                      refine ⟨994619216488189657516841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652317910635172420044909 994619216488189657516841)
                      ·
                        rfl

theorem cell23_1937014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1937014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937014 prefixEnd_1937014 := by exact prefixLift 1937014
  have htrace : WordTrace (prefixWord ++ tailWord_1937014) baseStart_1937014 baseEnd_1937014 := by
    simpa [prefixWord, tailWord_1937014, baseEnd_1937014] using wordTrace_append hprefix tailTrace_1937014
  have hstable : (prefixWord ++ tailWord_1937014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937014).length < 2 ^ (prefixWord ++ tailWord_1937014).sum := by decide
  have hdescent : baseEnd_1937014 < baseStart_1937014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937188 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1937188 : Nat := 118140960795 + 1937188 * 2 ^ 59
def prefixEnd_1937188 : Nat := 4983230072969 + 3 ^ 40 * 1937188 * 2
def baseEnd_1937188 : Nat := 331569520707357325580347

theorem tailTrace_1937188 : CollatzResearch.WordTrace tailWord_1937188 prefixEnd_1937188 331569520707357325580347 := by
  unfold tailWord_1937188
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327525452953098107782109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47103367270604130810376145 35327525452953098107782109)
  ·
    refine ⟨13247822044857411790418291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35327525452953098107782109 13247822044857411790418291)
    ·
      refine ⟨19871733067286117685627437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13247822044857411790418291 19871733067286117685627437)
      ·
        refine ⟨7451899900232294132110289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19871733067286117685627437 7451899900232294132110289)
        ·
          refine ⟨5588924925174220599082717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451899900232294132110289 5588924925174220599082717)
          ·
            refine ⟨2095846846940332724656019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5588924925174220599082717 2095846846940332724656019)
            ·
              refine ⟨3143770270410499086984029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2095846846940332724656019 3143770270410499086984029)
              ·
                refine ⟨1178913851403937157619011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3143770270410499086984029 1178913851403937157619011)
                ·
                  refine ⟨1768370777105905736428517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178913851403937157619011 1768370777105905736428517)
                  ·
                    refine ⟨331569520707357325580347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768370777105905736428517 331569520707357325580347)
                    ·
                      rfl

theorem cell23_1937188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1937188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937188 prefixEnd_1937188 := by exact prefixLift 1937188
  have htrace : WordTrace (prefixWord ++ tailWord_1937188) baseStart_1937188 baseEnd_1937188 := by
    simpa [prefixWord, tailWord_1937188, baseEnd_1937188] using wordTrace_append hprefix tailTrace_1937188
  have hstable : (prefixWord ++ tailWord_1937188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937188).length < 2 ^ (prefixWord ++ tailWord_1937188).sum := by decide
  have hdescent : baseEnd_1937188 < baseStart_1937188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937234 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1937234 : Nat := 118140960795 + 1937234 * 2 ^ 59
def prefixEnd_1937234 : Nat := 4983230072969 + 3 ^ 40 * 1937234 * 2
def baseEnd_1937234 : Nat := 994732182232178796765829

theorem tailTrace_1937234 : CollatzResearch.WordTrace tailWord_1937234 prefixEnd_1937234 994732182232178796765829 := by
  unfold tailWord_1937234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17664182165934886517934689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47104485775826364047825837 17664182165934886517934689)
  ·
    refine ⟨13248136624451164888451017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17664182165934886517934689 13248136624451164888451017)
    ·
      refine ⟨9936102468338373666338263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13248136624451164888451017 9936102468338373666338263)
      ·
        refine ⟨14904153702507560499507395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936102468338373666338263 14904153702507560499507395)
        ·
          refine ⟨22356230553761340749261093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904153702507560499507395 22356230553761340749261093)
          ·
            refine ⟨4191793228830251390486455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22356230553761340749261093 4191793228830251390486455)
            ·
              refine ⟨6287689843245377085729683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191793228830251390486455 6287689843245377085729683)
              ·
                refine ⟨9431534764868065628594525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6287689843245377085729683 9431534764868065628594525)
                ·
                  refine ⟨3536825536825524610722947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9431534764868065628594525 3536825536825524610722947)
                  ·
                    refine ⟨5305238305238286916084421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3536825536825524610722947 5305238305238286916084421)
                    ·
                      refine ⟨994732182232178796765829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5305238305238286916084421 994732182232178796765829)
                      ·
                        rfl

theorem cell23_1937234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1937234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937234 prefixEnd_1937234 := by exact prefixLift 1937234
  have htrace : WordTrace (prefixWord ++ tailWord_1937234) baseStart_1937234 baseEnd_1937234 := by
    simpa [prefixWord, tailWord_1937234, baseEnd_1937234] using wordTrace_append hprefix tailTrace_1937234
  have hstable : (prefixWord ++ tailWord_1937234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937234).length < 2 ^ (prefixWord ++ tailWord_1937234).sum := by decide
  have hdescent : baseEnd_1937234 < baseStart_1937234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937247 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_1937247 : Nat := 118140960795 + 1937247 * 2 ^ 59
def prefixEnd_1937247 : Nat := 4983230072969 + 3 ^ 40 * 1937247 * 2
def baseEnd_1937247 : Nat := 994738857480687245903269

theorem tailTrace_1937247 : CollatzResearch.WordTrace tailWord_1937247 prefixEnd_1937247 994738857480687245903269 := by
  unfold tailWord_1937247
  simp only [CollatzResearch.WordTrace]
  refine ⟨70657202812692449291961995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47104801875128299527974663 70657202812692449291961995)
  ·
    refine ⟨105985804219038673937942993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70657202812692449291961995 105985804219038673937942993)
    ·
      refine ⟨79489353164279005453457245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105985804219038673937942993 79489353164279005453457245)
      ·
        refine ⟨29808507436604627045046467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79489353164279005453457245 29808507436604627045046467)
        ·
          refine ⟨44712761154906940567569701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29808507436604627045046467 44712761154906940567569701)
          ·
            refine ⟨8383642716545051356419319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44712761154906940567569701 8383642716545051356419319)
            ·
              refine ⟨12575464074817577034628979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383642716545051356419319 12575464074817577034628979)
              ·
                refine ⟨18863196112226365551943469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575464074817577034628979 18863196112226365551943469)
                ·
                  refine ⟨7073698542084887081978801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18863196112226365551943469 7073698542084887081978801)
                  ·
                    refine ⟨5305273906563665311484101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073698542084887081978801 5305273906563665311484101)
                    ·
                      refine ⟨994738857480687245903269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5305273906563665311484101 994738857480687245903269)
                      ·
                        rfl

theorem cell23_1937247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_1937247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937247 prefixEnd_1937247 := by exact prefixLift 1937247
  have htrace : WordTrace (prefixWord ++ tailWord_1937247) baseStart_1937247 baseEnd_1937247 := by
    simpa [prefixWord, tailWord_1937247, baseEnd_1937247] using wordTrace_append hprefix tailTrace_1937247
  have hstable : (prefixWord ++ tailWord_1937247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937247).length < 2 ^ (prefixWord ++ tailWord_1937247).sum := by decide
  have hdescent : baseEnd_1937247 < baseStart_1937247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937262 : List Nat := [4, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1937262 : Nat := 118140960795 + 1937262 * 2 ^ 59
def prefixEnd_1937262 : Nat := 4983230072969 + 3 ^ 40 * 1937262 * 2
def baseEnd_1937262 : Nat := 994746559690504687215701

theorem tailTrace_1937262 : CollatzResearch.WordTrace tailWord_1937262 prefixEnd_1937262 994746559690504687215701 := by
  unfold tailWord_1937262
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832218738454763356719755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47105166605092071235838693 8832218738454763356719755)
  ·
    refine ⟨13248328107682145035079633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8832218738454763356719755 13248328107682145035079633)
    ·
      refine ⟨9936246080761608776309725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13248328107682145035079633 9936246080761608776309725)
      ·
        refine ⟨3726092280285603291116147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9936246080761608776309725 3726092280285603291116147)
        ·
          refine ⟨5589138420428404936674221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726092280285603291116147 5589138420428404936674221)
          ·
            refine ⟨2095926907660651851252833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5589138420428404936674221 2095926907660651851252833)
            ·
              refine ⟨1571945180745488888439625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2095926907660651851252833 1571945180745488888439625)
              ·
                refine ⟨1178958885559116666329719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1571945180745488888439625 1178958885559116666329719)
                ·
                  refine ⟨1768438328338674999494579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1178958885559116666329719 1768438328338674999494579)
                  ·
                    refine ⟨2652657492508012499241869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768438328338674999494579 2652657492508012499241869)
                    ·
                      refine ⟨994746559690504687215701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652657492508012499241869 994746559690504687215701)
                      ·
                        rfl

theorem cell23_1937262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1937262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937262 prefixEnd_1937262 := by exact prefixLift 1937262
  have htrace : WordTrace (prefixWord ++ tailWord_1937262) baseStart_1937262 baseEnd_1937262 := by
    simpa [prefixWord, tailWord_1937262, baseEnd_1937262] using wordTrace_append hprefix tailTrace_1937262
  have hstable : (prefixWord ++ tailWord_1937262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937262).length < 2 ^ (prefixWord ++ tailWord_1937262).sum := by decide
  have hdescent : baseEnd_1937262 < baseStart_1937262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937267 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3]
def baseStart_1937267 : Nat := 118140960795 + 1937267 * 2 ^ 59
def prefixEnd_1937267 : Nat := 4983230072969 + 3 ^ 40 * 1937267 * 2
def baseEnd_1937267 : Nat := 994749127093777167653177

theorem tailTrace_1937267 : CollatzResearch.WordTrace tailWord_1937267 prefixEnd_1937267 994749127093777167653177 := by
  unfold tailWord_1937267
  simp only [CollatzResearch.WordTrace]
  refine ⟨70657932272619992707690055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47105288181746661805126703 70657932272619992707690055)
  ·
    refine ⟨105986898408929989061535083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70657932272619992707690055 105986898408929989061535083)
    ·
      refine ⟨158980347613394983592302625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105986898408929989061535083 158980347613394983592302625)
      ·
        refine ⟨119235260710046237694226969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158980347613394983592302625 119235260710046237694226969)
        ·
          refine ⟨89426445532534678270670227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119235260710046237694226969 89426445532534678270670227)
          ·
            refine ⟨134139668298802017406005341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89426445532534678270670227 134139668298802017406005341)
            ·
              refine ⟨50302375612050756527252003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134139668298802017406005341 50302375612050756527252003)
              ·
                refine ⟨75453563418076134790878005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50302375612050756527252003 75453563418076134790878005)
                ·
                  refine ⟨7073771570444637636644813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75453563418076134790878005 7073771570444637636644813)
                  ·
                    refine ⟨2652664338916739113741805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7073771570444637636644813 2652664338916739113741805)
                    ·
                      refine ⟨994749127093777167653177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652664338916739113741805 994749127093777167653177)
                      ·
                        rfl

theorem cell23_1937267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_1937267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937267 prefixEnd_1937267 := by exact prefixLift 1937267
  have htrace : WordTrace (prefixWord ++ tailWord_1937267) baseStart_1937267 baseEnd_1937267 := by
    simpa [prefixWord, tailWord_1937267, baseEnd_1937267] using wordTrace_append hprefix tailTrace_1937267
  have hstable : (prefixWord ++ tailWord_1937267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937267).length < 2 ^ (prefixWord ++ tailWord_1937267).sum := by decide
  have hdescent : baseEnd_1937267 < baseStart_1937267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937278 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1937278 : Nat := 118140960795 + 1937278 * 2 ^ 59
def prefixEnd_1937278 : Nat := 4983230072969 + 3 ^ 40 * 1937278 * 2
def baseEnd_1937278 : Nat := 331584925126992208205209

theorem tailTrace_1937278 : CollatzResearch.WordTrace tailWord_1937278 prefixEnd_1937278 331584925126992208205209 := by
  unfold tailWord_1937278
  simp only [CollatzResearch.WordTrace]
  refine ⟨8832291684447517698292561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47105555650386761057560325 8832291684447517698292561)
  ·
    refine ⟨6624218763335638273719421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8832291684447517698292561 6624218763335638273719421)
    ·
      refine ⟨2484082036250864352644783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6624218763335638273719421 2484082036250864352644783)
      ·
        refine ⟨3726123054376296528967175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484082036250864352644783 3726123054376296528967175)
        ·
          refine ⟨5589184581564444793450763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726123054376296528967175 5589184581564444793450763)
          ·
            refine ⟨8383776872346667190176145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589184581564444793450763 8383776872346667190176145)
            ·
              refine ⟨6287832654260000392632109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8383776872346667190176145 6287832654260000392632109)
              ·
                refine ⟨2357937245347500147237041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287832654260000392632109 2357937245347500147237041)
                ·
                  refine ⟨1768452934010625110427781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2357937245347500147237041 1768452934010625110427781)
                  ·
                    refine ⟨331584925126992208205209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768452934010625110427781 331584925126992208205209)
                    ·
                      rfl

theorem cell23_1937278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1937278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937278 prefixEnd_1937278 := by exact prefixLift 1937278
  have htrace : WordTrace (prefixWord ++ tailWord_1937278) baseStart_1937278 baseEnd_1937278 := by
    simpa [prefixWord, tailWord_1937278, baseEnd_1937278] using wordTrace_append hprefix tailTrace_1937278
  have hstable : (prefixWord ++ tailWord_1937278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937278).length < 2 ^ (prefixWord ++ tailWord_1937278).sum := by decide
  have hdescent : baseEnd_1937278 < baseStart_1937278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937284 : List Nat := [2, 3, 2, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1937284 : Nat := 118140960795 + 1937284 * 2 ^ 59
def prefixEnd_1937284 : Nat := 4983230072969 + 3 ^ 40 * 1937284 * 2
def baseEnd_1937284 : Nat := 994757856264903601140599

theorem tailTrace_1937284 : CollatzResearch.WordTrace tailWord_1937284 prefixEnd_1937284 994757856264903601140599 := by
  unfold tailWord_1937284
  simp only [CollatzResearch.WordTrace]
  refine ⟨35329276156779202305529453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47105701542372269740705937 35329276156779202305529453)
  ·
    refine ⟨13248478558792200864573545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35329276156779202305529453 13248478558792200864573545)
    ·
      refine ⟨9936358919094150648430159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13248478558792200864573545 9936358919094150648430159)
      ·
        refine ⟨14904538378641225972645239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936358919094150648430159 14904538378641225972645239)
        ·
          refine ⟨22356807567961838958967859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904538378641225972645239 22356807567961838958967859)
          ·
            refine ⟨33535211351942758438451789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22356807567961838958967859 33535211351942758438451789)
            ·
              refine ⟨12575704256978534414419421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33535211351942758438451789 12575704256978534414419421)
              ·
                refine ⟨4715889096366950405407283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12575704256978534414419421 4715889096366950405407283)
                ·
                  refine ⟨7073833644550425608110925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715889096366950405407283 7073833644550425608110925)
                  ·
                    refine ⟨2652687616706409603041597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7073833644550425608110925 2652687616706409603041597)
                    ·
                      refine ⟨994757856264903601140599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652687616706409603041597 994757856264903601140599)
                      ·
                        rfl

theorem cell23_1937284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1937284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937284 prefixEnd_1937284 := by exact prefixLift 1937284
  have htrace : WordTrace (prefixWord ++ tailWord_1937284) baseStart_1937284 baseEnd_1937284 := by
    simpa [prefixWord, tailWord_1937284, baseEnd_1937284] using wordTrace_append hprefix tailTrace_1937284
  have hstable : (prefixWord ++ tailWord_1937284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937284).length < 2 ^ (prefixWord ++ tailWord_1937284).sum := by decide
  have hdescent : baseEnd_1937284 < baseStart_1937284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937407 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 8]
def baseStart_1937407 : Nat := 118140960795 + 1937407 * 2 ^ 59
def prefixEnd_1937407 : Nat := 4983230072969 + 3 ^ 40 * 1937407 * 2
def baseEnd_1937407 : Nat := 331607004795135539967511

theorem tailTrace_1937407 : CollatzResearch.WordTrace tailWord_1937407 prefixEnd_1937407 331607004795135539967511 := by
  unfold tailWord_1937407
  simp only [CollatzResearch.WordTrace]
  refine ⟨70663038492112796617786475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47108692328075197745190983 70663038492112796617786475)
  ·
    refine ⟨105994557738169194926679713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70663038492112796617786475 105994557738169194926679713)
    ·
      refine ⟨79495918303626896195009785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105994557738169194926679713 79495918303626896195009785)
      ·
        refine ⟨59621938727720172146257339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79495918303626896195009785 59621938727720172146257339)
        ·
          refine ⟨89432908091580258219386009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59621938727720172146257339 89432908091580258219386009)
          ·
            refine ⟨67074681068685193664539507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89432908091580258219386009 67074681068685193664539507)
            ·
              refine ⟨100612021603027790496809261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67074681068685193664539507 100612021603027790496809261)
              ·
                refine ⟨37729508101135421436303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100612021603027790496809261 37729508101135421436303473)
                ·
                  refine ⟨28297131075851566077227605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37729508101135421436303473 28297131075851566077227605)
                  ·
                    refine ⟨331607004795135539967511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28297131075851566077227605 331607004795135539967511)
                    ·
                      rfl

theorem cell23_1937407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_1937407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937407 prefixEnd_1937407 := by exact prefixLift 1937407
  have htrace : WordTrace (prefixWord ++ tailWord_1937407) baseStart_1937407 baseEnd_1937407 := by
    simpa [prefixWord, tailWord_1937407, baseEnd_1937407] using wordTrace_append hprefix tailTrace_1937407
  have hstable : (prefixWord ++ tailWord_1937407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937407).length < 2 ^ (prefixWord ++ tailWord_1937407).sum := by decide
  have hdescent : baseEnd_1937407 < baseStart_1937407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937417 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_1937417 : Nat := 118140960795 + 1937417 * 2 ^ 59
def prefixEnd_1937417 : Nat := 4983230072969 + 3 ^ 40 * 1937417 * 2
def baseEnd_1937417 : Nat := 994826149191951580777487

theorem tailTrace_1937417 : CollatzResearch.WordTrace tailWord_1937417 prefixEnd_1937417 994826149191951580777487 := by
  unfold tailWord_1937417
  simp only [CollatzResearch.WordTrace]
  refine ⟨70663403222076568325650505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47108935481384378883767003 70663403222076568325650505)
  ·
    refine ⟨52997552416557426244237879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70663403222076568325650505 52997552416557426244237879)
    ·
      refine ⟨79496328624836139366356819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52997552416557426244237879 79496328624836139366356819)
      ·
        refine ⟨119244492937254209049535229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79496328624836139366356819 119244492937254209049535229)
        ·
          refine ⟨44716684851470328393575711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119244492937254209049535229 44716684851470328393575711)
          ·
            refine ⟨67075027277205492590363567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44716684851470328393575711 67075027277205492590363567)
            ·
              refine ⟨100612540915808238885545351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67075027277205492590363567 100612540915808238885545351)
              ·
                refine ⟨150918811373712358328318027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100612540915808238885545351 150918811373712358328318027)
                ·
                  refine ⟨226378217060568537492477041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150918811373712358328318027 226378217060568537492477041)
                  ·
                    refine ⟨169783662795426403119357781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226378217060568537492477041 169783662795426403119357781)
                    ·
                      refine ⟨994826149191951580777487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 169783662795426403119357781 994826149191951580777487)
                      ·
                        rfl

theorem cell23_1937417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_1937417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937417 prefixEnd_1937417 := by exact prefixLift 1937417
  have htrace : WordTrace (prefixWord ++ tailWord_1937417) baseStart_1937417 baseEnd_1937417 := by
    simpa [prefixWord, tailWord_1937417, baseEnd_1937417] using wordTrace_append hprefix tailTrace_1937417
  have hstable : (prefixWord ++ tailWord_1937417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937417).length < 2 ^ (prefixWord ++ tailWord_1937417).sum := by decide
  have hdescent : baseEnd_1937417 < baseStart_1937417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937424 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 5, 4]
def baseStart_1937424 : Nat := 118140960795 + 1937424 * 2 ^ 59
def prefixEnd_1937424 : Nat := 4983230072969 + 3 ^ 40 * 1937424 * 2
def baseEnd_1937424 : Nat := 331609914518844351129985

theorem tailTrace_1937424 : CollatzResearch.WordTrace tailWord_1937424 prefixEnd_1937424 331609914518844351129985 := by
  unfold tailWord_1937424
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331829266525604260577663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47109105688700805680770217 35331829266525604260577663)
  ·
    refine ⟨52997743899788406390866495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35331829266525604260577663 52997743899788406390866495)
    ·
      refine ⟨79496615849682609586299743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52997743899788406390866495 79496615849682609586299743)
      ·
        refine ⟨119244923774523914379449615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79496615849682609586299743 119244923774523914379449615)
        ·
          refine ⟨178867385661785871569174423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119244923774523914379449615 178867385661785871569174423)
          ·
            refine ⟨268301078492678807353761635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178867385661785871569174423 268301078492678807353761635)
            ·
              refine ⟨402451617739018211030642453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268301078492678807353761635 402451617739018211030642453)
              ·
                refine ⟨18864919581516478642061365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 402451617739018211030642453 18864919581516478642061365)
                ·
                  refine ⟨1768586210767169872693253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18864919581516478642061365 1768586210767169872693253)
                  ·
                    refine ⟨331609914518844351129985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768586210767169872693253 331609914518844351129985)
                    ·
                      rfl

theorem cell23_1937424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 4].length) (baseStart_1937424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937424 prefixEnd_1937424 := by exact prefixLift 1937424
  have htrace : WordTrace (prefixWord ++ tailWord_1937424) baseStart_1937424 baseEnd_1937424 := by
    simpa [prefixWord, tailWord_1937424, baseEnd_1937424] using wordTrace_append hprefix tailTrace_1937424
  have hstable : (prefixWord ++ tailWord_1937424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937424).length < 2 ^ (prefixWord ++ tailWord_1937424).sum := by decide
  have hdescent : baseEnd_1937424 < baseStart_1937424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937465 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 2, 1, 4]
def baseStart_1937465 : Nat := 118140960795 + 1937465 * 2 ^ 59
def prefixEnd_1937465 : Nat := 4983230072969 + 3 ^ 40 * 1937465 * 2
def baseEnd_1937465 : Nat := 994850796263367392977267

theorem tailTrace_1937465 : CollatzResearch.WordTrace tailWord_1937465 prefixEnd_1937465 994850796263367392977267 := by
  unfold tailWord_1937465
  simp only [CollatzResearch.WordTrace]
  refine ⟨70665153925902672523397849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47110102617268448348931899 70665153925902672523397849)
  ·
    refine ⟨52998865444427004392548387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70665153925902672523397849 52998865444427004392548387)
    ·
      refine ⟨79498298166640506588822581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52998865444427004392548387 79498298166640506588822581)
      ·
        refine ⟨7452965453122547492702117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79498298166640506588822581 7452965453122547492702117)
        ·
          refine ⟨1397431022460477654881647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7452965453122547492702117 1397431022460477654881647)
          ·
            refine ⟨2096146533690716482322471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397431022460477654881647 2096146533690716482322471)
            ·
              refine ⟨3144219800536074723483707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096146533690716482322471 3144219800536074723483707)
              ·
                refine ⟨4716329700804112085225561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144219800536074723483707 4716329700804112085225561)
                ·
                  refine ⟨3537247275603084063919171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716329700804112085225561 3537247275603084063919171)
                  ·
                    refine ⟨5305870913404626095878757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3537247275603084063919171 5305870913404626095878757)
                    ·
                      refine ⟨994850796263367392977267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5305870913404626095878757 994850796263367392977267)
                      ·
                        rfl

theorem cell23_1937465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_1937465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937465 prefixEnd_1937465 := by exact prefixLift 1937465
  have htrace : WordTrace (prefixWord ++ tailWord_1937465) baseStart_1937465 baseEnd_1937465 := by
    simpa [prefixWord, tailWord_1937465, baseEnd_1937465] using wordTrace_append hprefix tailTrace_1937465
  have hstable : (prefixWord ++ tailWord_1937465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937465).length < 2 ^ (prefixWord ++ tailWord_1937465).sum := by decide
  have hdescent : baseEnd_1937465 < baseStart_1937465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937481 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 3]
def baseStart_1937481 : Nat := 118140960795 + 1937481 * 2 ^ 59
def prefixEnd_1937481 : Nat := 4983230072969 + 3 ^ 40 * 1937481 * 2
def baseEnd_1937481 : Nat := 994859011953839330377193

theorem tailTrace_1937481 : CollatzResearch.WordTrace tailWord_1937481 prefixEnd_1937481 994859011953839330377193 := by
  unfold tailWord_1937481
  simp only [CollatzResearch.WordTrace]
  refine ⟨70665737493844707255980297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47110491662563138170653531 70665737493844707255980297)
  ·
    refine ⟨52999303120383530441985223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70665737493844707255980297 52999303120383530441985223)
    ·
      refine ⟨79498954680575295662977835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52999303120383530441985223 79498954680575295662977835)
      ·
        refine ⟨119248432020862943494466753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79498954680575295662977835 119248432020862943494466753)
        ·
          refine ⟨89436324015647207620850065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119248432020862943494466753 89436324015647207620850065)
          ·
            refine ⟨67077243011735405715637549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89436324015647207620850065 67077243011735405715637549)
            ·
              refine ⟨25153966129400777143364081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67077243011735405715637549 25153966129400777143364081)
              ·
                refine ⟨18865474597050582857523061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25153966129400777143364081 18865474597050582857523061)
                ·
                  refine ⟨1768638243473492142892787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18865474597050582857523061 1768638243473492142892787)
                  ·
                    refine ⟨2652957365210238214339181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768638243473492142892787 2652957365210238214339181)
                    ·
                      refine ⟨994859011953839330377193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652957365210238214339181 994859011953839330377193)
                      ·
                        rfl

theorem cell23_1937481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_1937481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937481 prefixEnd_1937481 := by exact prefixLift 1937481
  have htrace : WordTrace (prefixWord ++ tailWord_1937481) baseStart_1937481 baseEnd_1937481 := by
    simpa [prefixWord, tailWord_1937481, baseEnd_1937481] using wordTrace_append hprefix tailTrace_1937481
  have hstable : (prefixWord ++ tailWord_1937481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937481).length < 2 ^ (prefixWord ++ tailWord_1937481).sum := by decide
  have hdescent : baseEnd_1937481 < baseStart_1937481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937498 : List Nat := [3, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_1937498 : Nat := 118140960795 + 1937498 * 2 ^ 59
def prefixEnd_1937498 : Nat := 4983230072969 + 3 ^ 40 * 1937498 * 2
def baseEnd_1937498 : Nat := 994867741124965763864615

theorem tailTrace_1937498 : CollatzResearch.WordTrace tailWord_1937498 prefixEnd_1937498 994867741124965763864615 := by
  unfold tailWord_1937498
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666589383695779789837287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47110905023188746106232765 17666589383695779789837287)
  ·
    refine ⟨26499884075543669684755931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666589383695779789837287 26499884075543669684755931)
    ·
      refine ⟨39749826113315504527133897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26499884075543669684755931 39749826113315504527133897)
      ·
        refine ⟨29812369584986628395350423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39749826113315504527133897 29812369584986628395350423)
        ·
          refine ⟨44718554377479942593025635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29812369584986628395350423 44718554377479942593025635)
          ·
            refine ⟨67077831566219913889538453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44718554377479942593025635 67077831566219913889538453)
            ·
              refine ⟨3144273354666558463572115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67077831566219913889538453 3144273354666558463572115)
              ·
                refine ⟨4716410031999837695358173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144273354666558463572115 4716410031999837695358173)
                ·
                  refine ⟨1768653761999939135759315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4716410031999837695358173 1768653761999939135759315)
                  ·
                    refine ⟨2652980642999908703638973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768653761999939135759315 2652980642999908703638973)
                    ·
                      refine ⟨994867741124965763864615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2652980642999908703638973 994867741124965763864615)
                      ·
                        rfl

theorem cell23_1937498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_1937498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937498 prefixEnd_1937498 := by exact prefixLift 1937498
  have htrace : WordTrace (prefixWord ++ tailWord_1937498) baseStart_1937498 baseEnd_1937498 := by
    simpa [prefixWord, tailWord_1937498, baseEnd_1937498] using wordTrace_append hprefix tailTrace_1937498
  have hstable : (prefixWord ++ tailWord_1937498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937498).length < 2 ^ (prefixWord ++ tailWord_1937498).sum := by decide
  have hdescent : baseEnd_1937498 < baseStart_1937498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937518 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1937518 : Nat := 118140960795 + 1937518 * 2 ^ 59
def prefixEnd_1937518 : Nat := 4983230072969 + 3 ^ 40 * 1937518 * 2
def baseEnd_1937518 : Nat := 331626003579351895204841

theorem tailTrace_1937518 : CollatzResearch.WordTrace tailWord_1937518 prefixEnd_1937518 331626003579351895204841 := by
  unfold tailWord_1937518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8833385874338832821884651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47111391329807108383384805 8833385874338832821884651)
  ·
    refine ⟨13250078811508249232826977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8833385874338832821884651 13250078811508249232826977)
    ·
      refine ⟨9937559108631186924620233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13250078811508249232826977 9937559108631186924620233)
      ·
        refine ⟨7453169331473390193465175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9937559108631186924620233 7453169331473390193465175)
        ·
          refine ⟨11179753997210085290197763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453169331473390193465175 11179753997210085290197763)
          ·
            refine ⟨16769630995815127935296645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11179753997210085290197763 16769630995815127935296645)
            ·
              refine ⟨3144305811715336487868121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16769630995815127935296645 3144305811715336487868121)
              ·
                refine ⟨2358229358786502365901091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144305811715336487868121 2358229358786502365901091)
                ·
                  refine ⟨3537344038179753548851637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358229358786502365901091 3537344038179753548851637)
                  ·
                    refine ⟨331626003579351895204841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3537344038179753548851637 331626003579351895204841)
                    ·
                      rfl

theorem cell23_1937518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1937518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937518 prefixEnd_1937518 := by exact prefixLift 1937518
  have htrace : WordTrace (prefixWord ++ tailWord_1937518) baseStart_1937518 baseEnd_1937518 := by
    simpa [prefixWord, tailWord_1937518, baseEnd_1937518] using wordTrace_append hprefix tailTrace_1937518
  have hstable : (prefixWord ++ tailWord_1937518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937518).length < 2 ^ (prefixWord ++ tailWord_1937518).sum := by decide
  have hdescent : baseEnd_1937518 < baseStart_1937518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937521 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_1937521 : Nat := 118140960795 + 1937521 * 2 ^ 59
def prefixEnd_1937521 : Nat := 4983230072969 + 3 ^ 40 * 1937521 * 2
def baseEnd_1937521 : Nat := 994879551180019173877009

theorem tailTrace_1937521 : CollatzResearch.WordTrace tailWord_1937521 prefixEnd_1937521 994879551180019173877009 := by
  unfold tailWord_1937521
  simp only [CollatzResearch.WordTrace]
  refine ⟨70667196413699794087436417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47111464275799862724957611 70667196413699794087436417)
  ·
    refine ⟨53000397310274845565577313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70667196413699794087436417 53000397310274845565577313)
    ·
      refine ⟨39750297982706134174182985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53000397310274845565577313 39750297982706134174182985)
      ·
        refine ⟨29812723487029600630637239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39750297982706134174182985 29812723487029600630637239)
        ·
          refine ⟨44719085230544400945955859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29812723487029600630637239 44719085230544400945955859)
          ·
            refine ⟨67078627845816601418933789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44719085230544400945955859 67078627845816601418933789)
            ·
              refine ⟨25154485442181225532100171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67078627845816601418933789 25154485442181225532100171)
              ·
                refine ⟨37731728163271838298150257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25154485442181225532100171 37731728163271838298150257)
                ·
                  refine ⟨28298796122453878723612693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37731728163271838298150257 28298796122453878723612693)
                  ·
                    refine ⟨1326506068240025565169345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28298796122453878723612693 1326506068240025565169345)
                    ·
                      refine ⟨994879551180019173877009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326506068240025565169345 994879551180019173877009)
                      ·
                        rfl

theorem cell23_1937521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_1937521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937521 prefixEnd_1937521 := by exact prefixLift 1937521
  have htrace : WordTrace (prefixWord ++ tailWord_1937521) baseStart_1937521 baseEnd_1937521 := by
    simpa [prefixWord, tailWord_1937521, baseEnd_1937521] using wordTrace_append hprefix tailTrace_1937521
  have hstable : (prefixWord ++ tailWord_1937521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937521).length < 2 ^ (prefixWord ++ tailWord_1937521).sum := by decide
  have hdescent : baseEnd_1937521 < baseStart_1937521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937532 : List Nat := [2, 2, 2, 1, 1, 6, 1, 3, 1, 1, 3]
def baseStart_1937532 : Nat := 118140960795 + 1937532 * 2 ^ 59
def prefixEnd_1937532 : Nat := 4983230072969 + 3 ^ 40 * 1937532 * 2
def baseEnd_1937532 : Nat := 994885199467218630839459

theorem tailTrace_1937532 : CollatzResearch.WordTrace tailWord_1937532 prefixEnd_1937532 994885199467218630839459 := by
  unfold tailWord_1937532
  simp only [CollatzResearch.WordTrace]
  refine ⟨35333798808329971483043425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47111731744439961977391233 35333798808329971483043425)
  ·
    refine ⟨26500349106247478612282569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35333798808329971483043425 26500349106247478612282569)
    ·
      refine ⟨19875261829685608959211927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26500349106247478612282569 19875261829685608959211927)
      ·
        refine ⟨29812892744528413438817891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19875261829685608959211927 29812892744528413438817891)
        ·
          refine ⟨44719339116792620158226837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29812892744528413438817891 44719339116792620158226837)
          ·
            refine ⟨2096219021099654069916883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44719339116792620158226837 2096219021099654069916883)
            ·
              refine ⟨3144328531649481104875325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096219021099654069916883 3144328531649481104875325)
              ·
                refine ⟨1179123199368555414328247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3144328531649481104875325 1179123199368555414328247)
                ·
                  refine ⟨1768684799052833121492371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179123199368555414328247 1768684799052833121492371)
                  ·
                    refine ⟨2653027198579249682238557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768684799052833121492371 2653027198579249682238557)
                    ·
                      refine ⟨994885199467218630839459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653027198579249682238557 994885199467218630839459)
                      ·
                        rfl

theorem cell23_1937532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3, 1, 1, 3].length) (baseStart_1937532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937532 prefixEnd_1937532 := by exact prefixLift 1937532
  have htrace : WordTrace (prefixWord ++ tailWord_1937532) baseStart_1937532 baseEnd_1937532 := by
    simpa [prefixWord, tailWord_1937532, baseEnd_1937532] using wordTrace_append hprefix tailTrace_1937532
  have hstable : (prefixWord ++ tailWord_1937532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937532).length < 2 ^ (prefixWord ++ tailWord_1937532).sum := by decide
  have hdescent : baseEnd_1937532 < baseStart_1937532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937541 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1937541 : Nat := 118140960795 + 1937541 * 2 ^ 59
def prefixEnd_1937541 : Nat := 4983230072969 + 3 ^ 40 * 1937541 * 2
def baseEnd_1937541 : Nat := 994889820793109095626917

theorem tailTrace_1937541 : CollatzResearch.WordTrace tailWord_1937541 prefixEnd_1937541 994889820793109095626917 := by
  unfold tailWord_1937541
  simp only [CollatzResearch.WordTrace]
  refine ⟨70667925873627337503164477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47111950582418225002109651 70667925873627337503164477)
  ·
    refine ⟨26500472202610251563686679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70667925873627337503164477 26500472202610251563686679)
    ·
      refine ⟨39750708303915377345530019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26500472202610251563686679 39750708303915377345530019)
      ·
        refine ⟨59626062455873066018295029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39750708303915377345530019 59626062455873066018295029)
        ·
          refine ⟨5589943355238099939215159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59626062455873066018295029 5589943355238099939215159)
          ·
            refine ⟨8384915032857149908822739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589943355238099939215159 8384915032857149908822739)
            ·
              refine ⟨12577372549285724863234109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384915032857149908822739 12577372549285724863234109)
              ·
                refine ⟨4716514705982146823712791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12577372549285724863234109 4716514705982146823712791)
                ·
                  refine ⟨7074772058973220235569187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716514705982146823712791 7074772058973220235569187)
                  ·
                    refine ⟨10612158088459830353353781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7074772058973220235569187 10612158088459830353353781)
                    ·
                      refine ⟨994889820793109095626917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10612158088459830353353781 994889820793109095626917)
                      ·
                        rfl

theorem cell23_1937541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1937541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937541 prefixEnd_1937541 := by exact prefixLift 1937541
  have htrace : WordTrace (prefixWord ++ tailWord_1937541) baseStart_1937541 baseEnd_1937541 := by
    simpa [prefixWord, tailWord_1937541, baseEnd_1937541] using wordTrace_append hprefix tailTrace_1937541
  have hstable : (prefixWord ++ tailWord_1937541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937541).length < 2 ^ (prefixWord ++ tailWord_1937541).sum := by decide
  have hdescent : baseEnd_1937541 < baseStart_1937541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937565 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_1937565 : Nat := 118140960795 + 1937565 * 2 ^ 59
def prefixEnd_1937565 : Nat := 4983230072969 + 3 ^ 40 * 1937565 * 2
def baseEnd_1937565 : Nat := 331634048109605667242269

theorem tailTrace_1937565 : CollatzResearch.WordTrace tailWord_1937565 prefixEnd_1937565 331634048109605667242269 := by
  unfold tailWord_1937565
  simp only [CollatzResearch.WordTrace]
  refine ⟨70668801225540389602038149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47112534150360259734692099 70668801225540389602038149)
  ·
    refine ⟨13250400229788823050382153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70668801225540389602038149 13250400229788823050382153)
    ·
      refine ⟨9937800172341617287786615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13250400229788823050382153 9937800172341617287786615)
      ·
        refine ⟨14906700258512425931679923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9937800172341617287786615 14906700258512425931679923)
        ·
          refine ⟨22360050387768638897519885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14906700258512425931679923 22360050387768638897519885)
          ·
            refine ⟨8385018895413239586569957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22360050387768638897519885 8385018895413239586569957)
            ·
              refine ⟨1572191042889982422481867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8385018895413239586569957 1572191042889982422481867)
              ·
                refine ⟨2358286564334973633722801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1572191042889982422481867 2358286564334973633722801)
                ·
                  refine ⟨1768714923251230225292101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2358286564334973633722801 1768714923251230225292101)
                  ·
                    refine ⟨331634048109605667242269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768714923251230225292101 331634048109605667242269)
                    ·
                      rfl

theorem cell23_1937565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_1937565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937565 prefixEnd_1937565 := by exact prefixLift 1937565
  have htrace : WordTrace (prefixWord ++ tailWord_1937565) baseStart_1937565 baseEnd_1937565 := by
    simpa [prefixWord, tailWord_1937565, baseEnd_1937565] using wordTrace_append hprefix tailTrace_1937565
  have hstable : (prefixWord ++ tailWord_1937565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937565).length < 2 ^ (prefixWord ++ tailWord_1937565).sum := by decide
  have hdescent : baseEnd_1937565 < baseStart_1937565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937572 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_1937572 : Nat := 118140960795 + 1937572 * 2 ^ 59
def prefixEnd_1937572 : Nat := 4983230072969 + 3 ^ 40 * 1937572 * 2
def baseEnd_1937572 : Nat := 994905738693398474339275

theorem tailTrace_1937572 : CollatzResearch.WordTrace tailWord_1937572 prefixEnd_1937572 994905738693398474339275 := by
  unfold tailWord_1937572
  simp only [CollatzResearch.WordTrace]
  refine ⟨35334528268257514898771485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47112704357676686531695313 35334528268257514898771485)
  ·
    refine ⟨13250448100596568087039307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35334528268257514898771485 13250448100596568087039307)
    ·
      refine ⟨19875672150894852130558961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13250448100596568087039307 19875672150894852130558961)
      ·
        refine ⟨14906754113171139097919221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19875672150894852130558961 14906754113171139097919221)
        ·
          refine ⟨1397508198109794290429927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14906754113171139097919221 1397508198109794290429927)
          ·
            refine ⟨2096262297164691435644891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397508198109794290429927 2096262297164691435644891)
            ·
              refine ⟨3144393445747037153467337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096262297164691435644891 3144393445747037153467337)
              ·
                refine ⟨2358295084310277865100503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3144393445747037153467337 2358295084310277865100503)
                ·
                  refine ⟨3537442626465416797650755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358295084310277865100503 3537442626465416797650755)
                  ·
                    refine ⟨5306163939698125196476133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3537442626465416797650755 5306163939698125196476133)
                    ·
                      refine ⟨994905738693398474339275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5306163939698125196476133 994905738693398474339275)
                      ·
                        rfl

theorem cell23_1937572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_1937572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937572 prefixEnd_1937572 := by exact prefixLift 1937572
  have htrace : WordTrace (prefixWord ++ tailWord_1937572) baseStart_1937572 baseEnd_1937572 := by
    simpa [prefixWord, tailWord_1937572, baseEnd_1937572] using wordTrace_append hprefix tailTrace_1937572
  have hstable : (prefixWord ++ tailWord_1937572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937572).length < 2 ^ (prefixWord ++ tailWord_1937572).sum := by decide
  have hdescent : baseEnd_1937572 < baseStart_1937572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937575 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1937575 : Nat := 118140960795 + 1937575 * 2 ^ 59
def prefixEnd_1937575 : Nat := 4983230072969 + 3 ^ 40 * 1937575 * 2
def baseEnd_1937575 : Nat := 994907279135361962601761

theorem tailTrace_1937575 : CollatzResearch.WordTrace tailWord_1937575 prefixEnd_1937575 994907279135361962601761 := by
  unfold tailWord_1937575
  simp only [CollatzResearch.WordTrace]
  refine ⟨70669165955504161309902179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47112777303669440873268119 70669165955504161309902179)
  ·
    refine ⟨106003748933256241964853269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70669165955504161309902179 106003748933256241964853269)
    ·
      refine ⟨4968925731246386342102497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 106003748933256241964853269 4968925731246386342102497)
      ·
        refine ⟨3726694298434789756576873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4968925731246386342102497 3726694298434789756576873)
        ·
          refine ⟨2795020723826092317432655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726694298434789756576873 2795020723826092317432655)
          ·
            refine ⟨4192531085739138476148983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795020723826092317432655 4192531085739138476148983)
            ·
              refine ⟨6288796628608707714223475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192531085739138476148983 6288796628608707714223475)
              ·
                refine ⟨9433194942913061571335213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288796628608707714223475 9433194942913061571335213)
                ·
                  refine ⟨3537448103592398089250705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9433194942913061571335213 3537448103592398089250705)
                  ·
                    refine ⟨2653086077694298566938029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537448103592398089250705 2653086077694298566938029)
                    ·
                      refine ⟨994907279135361962601761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653086077694298566938029 994907279135361962601761)
                      ·
                        rfl

theorem cell23_1937575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1937575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937575 prefixEnd_1937575 := by exact prefixLift 1937575
  have htrace : WordTrace (prefixWord ++ tailWord_1937575) baseStart_1937575 baseEnd_1937575 := by
    simpa [prefixWord, tailWord_1937575, baseEnd_1937575] using wordTrace_append hprefix tailTrace_1937575
  have hstable : (prefixWord ++ tailWord_1937575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937575).length < 2 ^ (prefixWord ++ tailWord_1937575).sum := by decide
  have hdescent : baseEnd_1937575 < baseStart_1937575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937622 : List Nat := [5, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1937622 : Nat := 118140960795 + 1937622 * 2 ^ 59
def prefixEnd_1937622 : Nat := 4983230072969 + 3 ^ 40 * 1937622 * 2
def baseEnd_1937622 : Nat := 994931412726123278714045

theorem tailTrace_1937622 : CollatzResearch.WordTrace tailWord_1937622 prefixEnd_1937622 994931412726123278714045 := by
  unfold tailWord_1937622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416930011645868021053945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47113920124222592224575413 4416930011645868021053945)
  ·
    refine ⟨3312697508734401015790459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4416930011645868021053945 3312697508734401015790459)
    ·
      refine ⟨4969046263101601523685689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312697508734401015790459 4969046263101601523685689)
      ·
        refine ⟨3726784697326201142764267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4969046263101601523685689 3726784697326201142764267)
        ·
          refine ⟨5590177045989301714146401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726784697326201142764267 5590177045989301714146401)
          ·
            refine ⟨4192632784491976285609801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590177045989301714146401 4192632784491976285609801)
            ·
              refine ⟨3144474588368982214207351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4192632784491976285609801 3144474588368982214207351)
              ·
                refine ⟨4716711882553473321311027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144474588368982214207351 4716711882553473321311027)
                ·
                  refine ⟨7075067823830209981966541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716711882553473321311027 7075067823830209981966541)
                  ·
                    refine ⟨2653150433936328743237453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7075067823830209981966541 2653150433936328743237453)
                    ·
                      refine ⟨994931412726123278714045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653150433936328743237453 994931412726123278714045)
                      ·
                        rfl

theorem cell23_1937622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1937622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937622 prefixEnd_1937622 := by exact prefixLift 1937622
  have htrace : WordTrace (prefixWord ++ tailWord_1937622) baseStart_1937622 baseEnd_1937622 := by
    simpa [prefixWord, tailWord_1937622, baseEnd_1937622] using wordTrace_append hprefix tailTrace_1937622
  have hstable : (prefixWord ++ tailWord_1937622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937622).length < 2 ^ (prefixWord ++ tailWord_1937622).sum := by decide
  have hdescent : baseEnd_1937622 < baseStart_1937622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937631 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_1937631 : Nat := 118140960795 + 1937631 * 2 ^ 59
def prefixEnd_1937631 : Nat := 4983230072969 + 3 ^ 40 * 1937631 * 2
def baseEnd_1937631 : Nat := 994936034052013743501503

theorem tailTrace_1937631 : CollatzResearch.WordTrace tailWord_1937631 prefixEnd_1937631 994936034052013743501503 := by
  unfold tailWord_1937631
  simp only [CollatzResearch.WordTrace]
  refine ⟨70671208443301282873940747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47114138962200855249293831 70671208443301282873940747)
  ·
    refine ⟨106006812664951924310911121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70671208443301282873940747 106006812664951924310911121)
    ·
      refine ⟨79505109498713943233183341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106006812664951924310911121 79505109498713943233183341)
      ·
        refine ⟨29814416062017728712443753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79505109498713943233183341 29814416062017728712443753)
        ·
          refine ⟨22360812046513296534332815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29814416062017728712443753 22360812046513296534332815)
          ·
            refine ⟨33541218069769944801499223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22360812046513296534332815 33541218069769944801499223)
            ·
              refine ⟨50311827104654917202248835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33541218069769944801499223 50311827104654917202248835)
              ·
                refine ⟨75467740656982375803373253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50311827104654917202248835 75467740656982375803373253)
                ·
                  refine ⟨14150201373184195463132485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75467740656982375803373253 14150201373184195463132485)
                  ·
                    refine ⟨2653162757472036649337341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14150201373184195463132485 2653162757472036649337341)
                    ·
                      refine ⟨994936034052013743501503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653162757472036649337341 994936034052013743501503)
                      ·
                        rfl

theorem cell23_1937631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_1937631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937631 prefixEnd_1937631 := by exact prefixLift 1937631
  have htrace : WordTrace (prefixWord ++ tailWord_1937631) baseStart_1937631 baseEnd_1937631 := by
    simpa [prefixWord, tailWord_1937631, baseEnd_1937631] using wordTrace_append hprefix tailTrace_1937631
  have hstable : (prefixWord ++ tailWord_1937631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937631).length < 2 ^ (prefixWord ++ tailWord_1937631).sum := by decide
  have hdescent : baseEnd_1937631 < baseStart_1937631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937662 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1937662 : Nat := 118140960795 + 1937662 * 2 ^ 59
def prefixEnd_1937662 : Nat := 4983230072969 + 3 ^ 40 * 1937662 * 2
def baseEnd_1937662 : Nat := 994951951952303122213861

theorem tailTrace_1937662 : CollatzResearch.WordTrace tailWord_1937662 prefixEnd_1937662 994951951952303122213861 := by
  unfold tailWord_1937662
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834042388273621896039905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47114892737459316778879493 8834042388273621896039905)
  ·
    refine ⟨6625531791205216422029929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8834042388273621896039905 6625531791205216422029929)
    ·
      refine ⟨4969148843403912316522447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625531791205216422029929 4969148843403912316522447)
      ·
        refine ⟨7453723265105868474783671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969148843403912316522447 7453723265105868474783671)
        ·
          refine ⟨11180584897658802712175507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453723265105868474783671 11180584897658802712175507)
          ·
            refine ⟨16770877346488204068263261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180584897658802712175507 16770877346488204068263261)
            ·
              refine ⟨6289079004933076525598723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16770877346488204068263261 6289079004933076525598723)
              ·
                refine ⟨9433618507399614788398085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289079004933076525598723 9433618507399614788398085)
                ·
                  refine ⟨1768803470137427772824641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9433618507399614788398085 1768803470137427772824641)
                  ·
                    refine ⟨1326602602603070829618481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1768803470137427772824641 1326602602603070829618481)
                    ·
                      refine ⟨994951951952303122213861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326602602603070829618481 994951951952303122213861)
                      ·
                        rfl

theorem cell23_1937662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1937662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937662 prefixEnd_1937662 := by exact prefixLift 1937662
  have htrace : WordTrace (prefixWord ++ tailWord_1937662) baseStart_1937662 baseEnd_1937662 := by
    simpa [prefixWord, tailWord_1937662, baseEnd_1937662] using wordTrace_append hprefix tailTrace_1937662
  have hstable : (prefixWord ++ tailWord_1937662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937662).length < 2 ^ (prefixWord ++ tailWord_1937662).sum := by decide
  have hdescent : baseEnd_1937662 < baseStart_1937662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937678 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1937678 : Nat := 118140960795 + 1937678 * 2 ^ 59
def prefixEnd_1937678 : Nat := 4983230072969 + 3 ^ 40 * 1937678 * 2
def baseEnd_1937678 : Nat := 994960167642775059613787

theorem tailTrace_1937678 : CollatzResearch.WordTrace tailWord_1937678 prefixEnd_1937678 994960167642775059613787 := by
  unfold tailWord_1937678
  simp only [CollatzResearch.WordTrace]
  refine ⟨8834115334266376237612711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47115281782754006600601125 8834115334266376237612711)
  ·
    refine ⟨13251173001399564356419067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8834115334266376237612711 13251173001399564356419067)
    ·
      refine ⟨19876759502099346534628601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251173001399564356419067 19876759502099346534628601)
      ·
        refine ⟨14907569626574509900971451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19876759502099346534628601 14907569626574509900971451)
        ·
          refine ⟨22361354439861764851457177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14907569626574509900971451 22361354439861764851457177)
          ·
            refine ⟨16771015829896323638592883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22361354439861764851457177 16771015829896323638592883)
            ·
              refine ⟨25156523744844485457889325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16771015829896323638592883 25156523744844485457889325)
              ·
                refine ⟨9433696404316682046708497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25156523744844485457889325 9433696404316682046708497)
                ·
                  refine ⟨7075272303237511535031373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9433696404316682046708497 7075272303237511535031373)
                  ·
                    refine ⟨2653227113714066825636765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7075272303237511535031373 2653227113714066825636765)
                    ·
                      refine ⟨994960167642775059613787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653227113714066825636765 994960167642775059613787)
                      ·
                        rfl

theorem cell23_1937678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1937678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937678 prefixEnd_1937678 := by exact prefixLift 1937678
  have htrace : WordTrace (prefixWord ++ tailWord_1937678) baseStart_1937678 baseEnd_1937678 := by
    simpa [prefixWord, tailWord_1937678, baseEnd_1937678] using wordTrace_append hprefix tailTrace_1937678
  have hstable : (prefixWord ++ tailWord_1937678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937678).length < 2 ^ (prefixWord ++ tailWord_1937678).sum := by decide
  have hdescent : baseEnd_1937678 < baseStart_1937678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937681 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_1937681 : Nat := 118140960795 + 1937681 * 2 ^ 59
def prefixEnd_1937681 : Nat := 4983230072969 + 3 ^ 40 * 1937681 * 2
def baseEnd_1937681 : Nat := 331653902694912849292091

theorem tailTrace_1937681 : CollatzResearch.WordTrace tailWord_1937681 prefixEnd_1937681 331653902694912849292091 := by
  unfold tailWord_1937681
  simp only [CollatzResearch.WordTrace]
  refine ⟨70673032093120141413260897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47115354728746760942173931 70673032093120141413260897)
  ·
    refine ⟨53004774069840106059945673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70673032093120141413260897 53004774069840106059945673)
    ·
      refine ⟨39753580552380079544959255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53004774069840106059945673 39753580552380079544959255)
      ·
        refine ⟨59630370828570119317438883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39753580552380079544959255 59630370828570119317438883)
        ·
          refine ⟨89445556242855178976158325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59630370828570119317438883 89445556242855178976158325)
          ·
            refine ⟨8385520897767673029014843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89445556242855178976158325 8385520897767673029014843)
            ·
              refine ⟨12578281346651509543522265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385520897767673029014843 12578281346651509543522265)
              ·
                refine ⟨9433711009988632157641699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12578281346651509543522265 9433711009988632157641699)
                ·
                  refine ⟨14150566514982948236462549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433711009988632157641699 14150566514982948236462549)
                  ·
                    refine ⟨331653902694912849292091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14150566514982948236462549 331653902694912849292091)
                    ·
                      rfl

theorem cell23_1937681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_1937681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937681 prefixEnd_1937681 := by exact prefixLift 1937681
  have htrace : WordTrace (prefixWord ++ tailWord_1937681) baseStart_1937681 baseEnd_1937681 := by
    simpa [prefixWord, tailWord_1937681, baseEnd_1937681] using wordTrace_append hprefix tailTrace_1937681
  have hstable : (prefixWord ++ tailWord_1937681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937681).length < 2 ^ (prefixWord ++ tailWord_1937681).sum := by decide
  have hdescent : baseEnd_1937681 < baseStart_1937681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937698 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1937698 : Nat := 118140960795 + 1937698 * 2 ^ 59
def prefixEnd_1937698 : Nat := 4983230072969 + 3 ^ 40 * 1937698 * 2
def baseEnd_1937698 : Nat := 331656812418621660454565

theorem tailTrace_1937698 : CollatzResearch.WordTrace tailWord_1937698 prefixEnd_1937698 331656812418621660454565 := by
  unfold tailWord_1937698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668413033514638329157437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47115768089372368877753165 17668413033514638329157437)
  ·
    refine ⟨6625654887567989373434039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17668413033514638329157437 6625654887567989373434039)
    ·
      refine ⟨9938482331351984060151059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6625654887567989373434039 9938482331351984060151059)
      ·
        refine ⟨14907723497027976090226589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9938482331351984060151059 14907723497027976090226589)
        ·
          refine ⟨5590396311385491033834971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14907723497027976090226589 5590396311385491033834971)
          ·
            refine ⟨8385594467078236550752457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590396311385491033834971 8385594467078236550752457)
            ·
              refine ⟨6289195850308677413064343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385594467078236550752457 6289195850308677413064343)
              ·
                refine ⟨9433793775463016119596515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289195850308677413064343 9433793775463016119596515)
                ·
                  refine ⟨14150690663194524179394773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433793775463016119596515 14150690663194524179394773)
                  ·
                    refine ⟨331656812418621660454565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14150690663194524179394773 331656812418621660454565)
                    ·
                      rfl

theorem cell23_1937698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1937698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937698 prefixEnd_1937698 := by exact prefixLift 1937698
  have htrace : WordTrace (prefixWord ++ tailWord_1937698) baseStart_1937698 baseEnd_1937698 := by
    simpa [prefixWord, tailWord_1937698, baseEnd_1937698] using wordTrace_append hprefix tailTrace_1937698
  have hstable : (prefixWord ++ tailWord_1937698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937698).length < 2 ^ (prefixWord ++ tailWord_1937698).sum := by decide
  have hdescent : baseEnd_1937698 < baseStart_1937698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937728 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_1937728 : Nat := 118140960795 + 1937728 * 2 ^ 59
def prefixEnd_1937728 : Nat := 4983230072969 + 3 ^ 40 * 1937728 * 2
def baseEnd_1937728 : Nat := 331661947225166621329519

theorem tailTrace_1937728 : CollatzResearch.WordTrace tailWord_1937728 prefixEnd_1937728 331661947225166621329519 := by
  unfold tailWord_1937728
  simp only [CollatzResearch.WordTrace]
  refine ⟨35337373161974934220110919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47116497549299912293481225 35337373161974934220110919)
  ·
    refine ⟨53006059742962401330166379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35337373161974934220110919 53006059742962401330166379)
    ·
      refine ⟨79509089614443601995249569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53006059742962401330166379 79509089614443601995249569)
      ·
        refine ⟨59631817210832701496437177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79509089614443601995249569 59631817210832701496437177)
        ·
          refine ⟨44723862908124526122327883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59631817210832701496437177 44723862908124526122327883)
          ·
            refine ⟨67085794362186789183491825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44723862908124526122327883 67085794362186789183491825)
            ·
              refine ⟨50314345771640091887618869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67085794362186789183491825 50314345771640091887618869)
              ·
                refine ⟨4716969916091258614464269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50314345771640091887618869 4716969916091258614464269)
                ·
                  refine ⟨1768863718534221980424101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4716969916091258614464269 1768863718534221980424101)
                  ·
                    refine ⟨331661947225166621329519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1768863718534221980424101 331661947225166621329519)
                    ·
                      rfl

theorem cell23_1937728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_1937728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937728 prefixEnd_1937728 := by exact prefixLift 1937728
  have htrace : WordTrace (prefixWord ++ tailWord_1937728) baseStart_1937728 baseEnd_1937728 := by
    simpa [prefixWord, tailWord_1937728, baseEnd_1937728] using wordTrace_append hprefix tailTrace_1937728
  have hstable : (prefixWord ++ tailWord_1937728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937728).length < 2 ^ (prefixWord ++ tailWord_1937728).sum := by decide
  have hdescent : baseEnd_1937728 < baseStart_1937728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937731 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1937731 : Nat := 118140960795 + 1937731 * 2 ^ 59
def prefixEnd_1937731 : Nat := 4983230072969 + 3 ^ 40 * 1937731 * 2
def baseEnd_1937731 : Nat := 994987382117463352251043

theorem tailTrace_1937731 : CollatzResearch.WordTrace tailWord_1937731 prefixEnd_1937731 994987382117463352251043 := by
  unfold tailWord_1937731
  simp only [CollatzResearch.WordTrace]
  refine ⟨70674855742938999952581047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47116570495292666635054031 70674855742938999952581047)
  ·
    refine ⟨106012283614408499928871571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70674855742938999952581047 106012283614408499928871571)
    ·
      refine ⟨159018425421612749893307357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106012283614408499928871571 159018425421612749893307357)
      ·
        refine ⟨59631909533104781209990259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159018425421612749893307357 59631909533104781209990259)
        ·
          refine ⟨89447864299657171814985389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59631909533104781209990259 89447864299657171814985389)
          ·
            refine ⟨33542949112371439430619521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89447864299657171814985389 33542949112371439430619521)
            ·
              refine ⟨25157211834278579572964641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33542949112371439430619521 25157211834278579572964641)
              ·
                refine ⟨18867908875708934679723481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25157211834278579572964641 18867908875708934679723481)
                ·
                  refine ⟨14150931656781701009792611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18867908875708934679723481 14150931656781701009792611)
                  ·
                    refine ⟨21226397485172551514688917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14150931656781701009792611 21226397485172551514688917)
                    ·
                      refine ⟨994987382117463352251043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21226397485172551514688917 994987382117463352251043)
                      ·
                        rfl

theorem cell23_1937731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1937731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937731 prefixEnd_1937731 := by exact prefixLift 1937731
  have htrace : WordTrace (prefixWord ++ tailWord_1937731) baseStart_1937731 baseEnd_1937731 := by
    simpa [prefixWord, tailWord_1937731, baseEnd_1937731] using wordTrace_append hprefix tailTrace_1937731
  have hstable : (prefixWord ++ tailWord_1937731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937731).length < 2 ^ (prefixWord ++ tailWord_1937731).sum := by decide
  have hdescent : baseEnd_1937731 < baseStart_1937731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937761 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1937761 : Nat := 118140960795 + 1937761 * 2 ^ 59
def prefixEnd_1937761 : Nat := 4983230072969 + 3 ^ 40 * 1937761 * 2
def baseEnd_1937761 : Nat := 995002786537098234875905

theorem tailTrace_1937761 : CollatzResearch.WordTrace tailWord_1937761 prefixEnd_1937761 995002786537098234875905 := by
  unfold tailWord_1937761
  simp only [CollatzResearch.WordTrace]
  refine ⟨70675949932830315076173137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47117299955220210050782091 70675949932830315076173137)
  ·
    refine ⟨53006962449622736307129853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70675949932830315076173137 53006962449622736307129853)
    ·
      refine ⟨19877610918608526115173695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53006962449622736307129853 19877610918608526115173695)
      ·
        refine ⟨29816416377912789172760543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19877610918608526115173695 29816416377912789172760543)
        ·
          refine ⟨44724624566869183759140815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29816416377912789172760543 44724624566869183759140815)
          ·
            refine ⟨67086936850303775638711223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44724624566869183759140815 67086936850303775638711223)
            ·
              refine ⟨100630405275455663458066835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67086936850303775638711223 100630405275455663458066835)
              ·
                refine ⟨150945607913183495187100253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100630405275455663458066835 150945607913183495187100253)
                ·
                  refine ⟨56604602967443810695162595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150945607913183495187100253 56604602967443810695162595)
                  ·
                    refine ⟨84906904451165716042743893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56604602967443810695162595 84906904451165716042743893)
                    ·
                      refine ⟨995002786537098234875905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84906904451165716042743893 995002786537098234875905)
                      ·
                        rfl

theorem cell23_1937761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1937761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937761 prefixEnd_1937761 := by exact prefixLift 1937761
  have htrace : WordTrace (prefixWord ++ tailWord_1937761) baseStart_1937761 baseEnd_1937761 := by
    simpa [prefixWord, tailWord_1937761, baseEnd_1937761] using wordTrace_append hprefix tailTrace_1937761
  have hstable : (prefixWord ++ tailWord_1937761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937761).length < 2 ^ (prefixWord ++ tailWord_1937761).sum := by decide
  have hdescent : baseEnd_1937761 < baseStart_1937761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937785 : List Nat := [1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 3]
def baseStart_1937785 : Nat := 118140960795 + 1937785 * 2 ^ 59
def prefixEnd_1937785 : Nat := 4983230072969 + 3 ^ 40 * 1937785 * 2
def baseEnd_1937785 : Nat := 995015110072806140975795

theorem tailTrace_1937785 : CollatzResearch.WordTrace tailWord_1937785 prefixEnd_1937785 995015110072806140975795 := by
  unfold tailWord_1937785
  simp only [CollatzResearch.WordTrace]
  refine ⟨70676825284743367175046809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47117883523162244783364539 70676825284743367175046809)
  ·
    refine ⟨53007618963557525381285107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70676825284743367175046809 53007618963557525381285107)
    ·
      refine ⟨79511428445336288071927661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53007618963557525381285107 79511428445336288071927661)
      ·
        refine ⟨29816785667001108026972873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79511428445336288071927661 29816785667001108026972873)
        ·
          refine ⟨22362589250250831020229655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29816785667001108026972873 22362589250250831020229655)
          ·
            refine ⟨33543883875376246530344483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22362589250250831020229655 33543883875376246530344483)
            ·
              refine ⟨50315825813064369795516725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33543883875376246530344483 50315825813064369795516725)
              ·
                refine ⟨4717108669974784668329693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50315825813064369795516725 4717108669974784668329693)
                ·
                  refine ⟨1768915751240544250623635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4717108669974784668329693 1768915751240544250623635)
                  ·
                    refine ⟨2653373626860816375935453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1768915751240544250623635 2653373626860816375935453)
                    ·
                      refine ⟨995015110072806140975795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653373626860816375935453 995015110072806140975795)
                      ·
                        rfl

theorem cell23_1937785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_1937785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937785 prefixEnd_1937785 := by exact prefixLift 1937785
  have htrace : WordTrace (prefixWord ++ tailWord_1937785) baseStart_1937785 baseEnd_1937785 := by
    simpa [prefixWord, tailWord_1937785, baseEnd_1937785] using wordTrace_append hprefix tailTrace_1937785
  have hstable : (prefixWord ++ tailWord_1937785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937785).length < 2 ^ (prefixWord ++ tailWord_1937785).sum := by decide
  have hdescent : baseEnd_1937785 < baseStart_1937785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937852 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1937852 : Nat := 118140960795 + 1937852 * 2 ^ 59
def prefixEnd_1937852 : Nat := 4983230072969 + 3 ^ 40 * 1937852 * 2
def baseEnd_1937852 : Nat := 331683171092219126279329

theorem tailTrace_1937852 : CollatzResearch.WordTrace tailWord_1937852 prefixEnd_1937852 331683171092219126279329 := by
  unfold tailWord_1937852
  simp only [CollatzResearch.WordTrace]
  refine ⟨35339634487750318808867905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47119512650333758411823873 35339634487750318808867905)
  ·
    refine ⟨26504725865812739106650929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35339634487750318808867905 26504725865812739106650929)
    ·
      refine ⟨19878544399359554329988197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26504725865812739106650929 19878544399359554329988197)
      ·
        refine ⟨3727227074879916436872787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19878544399359554329988197 3727227074879916436872787)
        ·
          refine ⟨5590840612319874655309181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727227074879916436872787 5590840612319874655309181)
          ·
            refine ⟨2096565229619952995740943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5590840612319874655309181 2096565229619952995740943)
            ·
              refine ⟨3144847844429929493611415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096565229619952995740943 3144847844429929493611415)
              ·
                refine ⟨4717271766644894240417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144847844429929493611415 4717271766644894240417123)
                ·
                  refine ⟨7075907649967341360625685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717271766644894240417123 7075907649967341360625685)
                  ·
                    refine ⟨331683171092219126279329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7075907649967341360625685 331683171092219126279329)
                    ·
                      rfl

theorem cell23_1937852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1937852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937852 prefixEnd_1937852 := by exact prefixLift 1937852
  have htrace : WordTrace (prefixWord ++ tailWord_1937852) baseStart_1937852 baseEnd_1937852 := by
    simpa [prefixWord, tailWord_1937852, baseEnd_1937852] using wordTrace_append hprefix tailTrace_1937852
  have hstable : (prefixWord ++ tailWord_1937852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937852).length < 2 ^ (prefixWord ++ tailWord_1937852).sum := by decide
  have hdescent : baseEnd_1937852 < baseStart_1937852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937888 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1937888 : Nat := 118140960795 + 1937888 * 2 ^ 59
def prefixEnd_1937888 : Nat := 4983230072969 + 3 ^ 40 * 1937888 * 2
def baseEnd_1937888 : Nat := 995067998580219237987821

theorem tailTrace_1937888 : CollatzResearch.WordTrace tailWord_1937888 prefixEnd_1937888 995067998580219237987821 := by
  unfold tailWord_1937888
  simp only [CollatzResearch.WordTrace]
  refine ⟨35340291001685107883023159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47120388002246810510697545 35340291001685107883023159)
  ·
    refine ⟨53010436502527661824534739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35340291001685107883023159 53010436502527661824534739)
    ·
      refine ⟨79515654753791492736802109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53010436502527661824534739 79515654753791492736802109)
      ·
        refine ⟨29818370532671809776300791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79515654753791492736802109 29818370532671809776300791)
        ·
          refine ⟨44727555799007714664451187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29818370532671809776300791 44727555799007714664451187)
          ·
            refine ⟨67091333698511571996676781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44727555799007714664451187 67091333698511571996676781)
            ·
              refine ⟨25159250136941839498753793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67091333698511571996676781 25159250136941839498753793)
              ·
                refine ⟨18869437602706379624065345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25159250136941839498753793 18869437602706379624065345)
                ·
                  refine ⟨14152078202029784718049009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18869437602706379624065345 14152078202029784718049009)
                  ·
                    refine ⟨10614058651522338538536757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14152078202029784718049009 10614058651522338538536757)
                    ·
                      refine ⟨995067998580219237987821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10614058651522338538536757 995067998580219237987821)
                      ·
                        rfl

theorem cell23_1937888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1937888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937888 prefixEnd_1937888 := by exact prefixLift 1937888
  have htrace : WordTrace (prefixWord ++ tailWord_1937888) baseStart_1937888 baseEnd_1937888 := by
    simpa [prefixWord, tailWord_1937888, baseEnd_1937888] using wordTrace_append hprefix tailTrace_1937888
  have hstable : (prefixWord ++ tailWord_1937888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937888).length < 2 ^ (prefixWord ++ tailWord_1937888).sum := by decide
  have hdescent : baseEnd_1937888 < baseStart_1937888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937893 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1937893 : Nat := 118140960795 + 1937893 * 2 ^ 59
def prefixEnd_1937893 : Nat := 4983230072969 + 3 ^ 40 * 1937893 * 2
def baseEnd_1937893 : Nat := 995070565983491718425299

theorem tailTrace_1937893 : CollatzResearch.WordTrace tailWord_1937893 prefixEnd_1937893 995070565983491718425299 := by
  unfold tailWord_1937893
  simp only [CollatzResearch.WordTrace]
  refine ⟨70680764368352101619978333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47120509578901401079985555 70680764368352101619978333)
  ·
    refine ⟨26505286638132038107491875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70680764368352101619978333 26505286638132038107491875)
    ·
      refine ⟨39757929957198057161237813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26505286638132038107491875 39757929957198057161237813)
      ·
        refine ⟨3727305933487317858866045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39757929957198057161237813 3727305933487317858866045)
        ·
          refine ⟨1397739725057744197074767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3727305933487317858866045 1397739725057744197074767)
          ·
            refine ⟨2096609587586616295612151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1397739725057744197074767 2096609587586616295612151)
            ·
              refine ⟨3144914381379924443418227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096609587586616295612151 3144914381379924443418227)
              ·
                refine ⟨4717371572069886665127341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144914381379924443418227 4717371572069886665127341)
                ·
                  refine ⟨1769014339526207499422753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4717371572069886665127341 1769014339526207499422753)
                  ·
                    refine ⟨1326760754644655624567065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769014339526207499422753 1326760754644655624567065)
                    ·
                      refine ⟨995070565983491718425299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326760754644655624567065 995070565983491718425299)
                      ·
                        rfl

theorem cell23_1937893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1937893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937893 prefixEnd_1937893 := by exact prefixLift 1937893
  have htrace : WordTrace (prefixWord ++ tailWord_1937893) baseStart_1937893 baseEnd_1937893 := by
    simpa [prefixWord, tailWord_1937893, baseEnd_1937893] using wordTrace_append hprefix tailTrace_1937893
  have hstable : (prefixWord ++ tailWord_1937893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937893).length < 2 ^ (prefixWord ++ tailWord_1937893).sum := by decide
  have hdescent : baseEnd_1937893 < baseStart_1937893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937926 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1937926 : Nat := 118140960795 + 1937926 * 2 ^ 59
def prefixEnd_1937926 : Nat := 4983230072969 + 3 ^ 40 * 1937926 * 2
def baseEnd_1937926 : Nat := 995087510845090089312647

theorem tailTrace_1937926 : CollatzResearch.WordTrace tailWord_1937926 prefixEnd_1937926 995087510845090089312647 := by
  unfold tailWord_1937926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2208811499288517132997801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47121311984821698837286421 2208811499288517132997801)
  ·
    refine ⟨1656608624466387849748351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2208811499288517132997801 1656608624466387849748351)
    ·
      refine ⟨2484912936699581774622527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1656608624466387849748351 2484912936699581774622527)
      ·
        refine ⟨3727369405049372661933791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484912936699581774622527 3727369405049372661933791)
        ·
          refine ⟨5591054107574058992900687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727369405049372661933791 5591054107574058992900687)
          ·
            refine ⟨8386581161361088489351031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591054107574058992900687 8386581161361088489351031)
            ·
              refine ⟨12579871742041632734026547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386581161361088489351031 12579871742041632734026547)
              ·
                refine ⟨18869807613062449101039821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579871742041632734026547 18869807613062449101039821)
                ·
                  refine ⟨7076177854898418412889933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18869807613062449101039821 7076177854898418412889933)
                  ·
                    refine ⟨2653566695586906904833725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7076177854898418412889933 2653566695586906904833725)
                    ·
                      refine ⟨995087510845090089312647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653566695586906904833725 995087510845090089312647)
                      ·
                        rfl

theorem cell23_1937926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1937926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937926 prefixEnd_1937926 := by exact prefixLift 1937926
  have htrace : WordTrace (prefixWord ++ tailWord_1937926) baseStart_1937926 baseEnd_1937926 := by
    simpa [prefixWord, tailWord_1937926, baseEnd_1937926] using wordTrace_append hprefix tailTrace_1937926
  have hstable : (prefixWord ++ tailWord_1937926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937926).length < 2 ^ (prefixWord ++ tailWord_1937926).sum := by decide
  have hdescent : baseEnd_1937926 < baseStart_1937926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937932 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 3, 4, 2]
def baseStart_1937932 : Nat := 118140960795 + 1937932 * 2 ^ 59
def prefixEnd_1937932 : Nat := 4983230072969 + 3 ^ 40 * 1937932 * 2
def baseEnd_1937932 : Nat := 995090591729017065837619

theorem tailTrace_1937932 : CollatzResearch.WordTrace tailWord_1937932 prefixEnd_1937932 995090591729017065837619 := by
  unfold tailWord_1937932
  simp only [CollatzResearch.WordTrace]
  refine ⟨35341093407605405640324025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47121457876807207520432033 35341093407605405640324025)
  ·
    refine ⟨26505820055704054230243019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35341093407605405640324025 26505820055704054230243019)
    ·
      refine ⟨39758730083556081345364529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26505820055704054230243019 39758730083556081345364529)
      ·
        refine ⟨29819047562667061009023397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39758730083556081345364529 29819047562667061009023397)
        ·
          refine ⟨5591071418000073939191887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29819047562667061009023397 5591071418000073939191887)
          ·
            refine ⟨8386607127000110908787831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591071418000073939191887 8386607127000110908787831)
            ·
              refine ⟨12579910690500166363181747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386607127000110908787831 12579910690500166363181747)
              ·
                refine ⟨18869866035750249544772621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579910690500166363181747 18869866035750249544772621)
                ·
                  refine ⟨7076199763406343579289733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18869866035750249544772621 7076199763406343579289733)
                  ·
                    refine ⟨1326787455638689421116825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076199763406343579289733 1326787455638689421116825)
                    ·
                      refine ⟨995090591729017065837619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326787455638689421116825 995090591729017065837619)
                      ·
                        rfl

theorem cell23_1937932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_1937932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937932 prefixEnd_1937932 := by exact prefixLift 1937932
  have htrace : WordTrace (prefixWord ++ tailWord_1937932) baseStart_1937932 baseEnd_1937932 := by
    simpa [prefixWord, tailWord_1937932, baseEnd_1937932] using wordTrace_append hprefix tailTrace_1937932
  have hstable : (prefixWord ++ tailWord_1937932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937932).length < 2 ^ (prefixWord ++ tailWord_1937932).sum := by decide
  have hdescent : baseEnd_1937932 < baseStart_1937932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937959 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 2, 6]
def baseStart_1937959 : Nat := 118140960795 + 1937959 * 2 ^ 59
def prefixEnd_1937959 : Nat := 4983230072969 + 3 ^ 40 * 1937959 * 2
def baseEnd_1937959 : Nat := 331701485235562820066665

theorem tailTrace_1937959 : CollatzResearch.WordTrace tailWord_1937959 prefixEnd_1937959 331701485235562820066665 := by
  unfold tailWord_1937959
  simp only [CollatzResearch.WordTrace]
  refine ⟨70683171586112994891880931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47122114390741996594587287 70683171586112994891880931)
  ·
    refine ⟨106024757379169492337821397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70683171586112994891880931 106024757379169492337821397)
    ·
      refine ⟨2484955251074284976667689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 106024757379169492337821397 2484955251074284976667689)
      ·
        refine ⟨1863716438305713732500767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2484955251074284976667689 1863716438305713732500767)
        ·
          refine ⟨2795574657458570598751151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1863716438305713732500767 2795574657458570598751151)
          ·
            refine ⟨4193361986187855898126727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795574657458570598751151 4193361986187855898126727)
            ·
              refine ⟨6290042979281783847190091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193361986187855898126727 6290042979281783847190091)
              ·
                refine ⟨9435064468922675770785137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290042979281783847190091 9435064468922675770785137)
                ·
                  refine ⟨7076298351692006828088853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9435064468922675770785137 7076298351692006828088853)
                  ·
                    refine ⟨331701485235562820066665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7076298351692006828088853 331701485235562820066665)
                    ·
                      rfl

theorem cell23_1937959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_1937959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937959 prefixEnd_1937959 := by exact prefixLift 1937959
  have htrace : WordTrace (prefixWord ++ tailWord_1937959) baseStart_1937959 baseEnd_1937959 := by
    simpa [prefixWord, tailWord_1937959, baseEnd_1937959] using wordTrace_append hprefix tailTrace_1937959
  have hstable : (prefixWord ++ tailWord_1937959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937959).length < 2 ^ (prefixWord ++ tailWord_1937959).sum := by decide
  have hdescent : baseEnd_1937959 < baseStart_1937959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937962 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1937962 : Nat := 118140960795 + 1937962 * 2 ^ 59
def prefixEnd_1937962 : Nat := 4983230072969 + 3 ^ 40 * 1937962 * 2
def baseEnd_1937962 : Nat := 995105996148651948462481

theorem tailTrace_1937962 : CollatzResearch.WordTrace tailWord_1937962 prefixEnd_1937962 995105996148651948462481 := by
  unfold tailWord_1937962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17670820251275531601060035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47122187336734750936160093 17670820251275531601060035)
  ·
    refine ⟨26506230376913297401590053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17670820251275531601060035 26506230376913297401590053)
    ·
      refine ⟨4969918195671243262798135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26506230376913297401590053 4969918195671243262798135)
      ·
        refine ⟨7454877293506864894197203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969918195671243262798135 7454877293506864894197203)
        ·
          refine ⟨11182315940260297341295805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7454877293506864894197203 11182315940260297341295805)
          ·
            refine ⟨4193368477597611502985927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11182315940260297341295805 4193368477597611502985927)
            ·
              refine ⟨6290052716396417254478891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193368477597611502985927 6290052716396417254478891)
              ·
                refine ⟨9435079074594625881718337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290052716396417254478891 9435079074594625881718337)
                ·
                  refine ⟨7076309305945969411288753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9435079074594625881718337 7076309305945969411288753)
                  ·
                    refine ⟨5307231979459477058466565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7076309305945969411288753 5307231979459477058466565)
                    ·
                      refine ⟨995105996148651948462481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5307231979459477058466565 995105996148651948462481)
                      ·
                        rfl

theorem cell23_1937962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1937962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937962 prefixEnd_1937962 := by exact prefixLift 1937962
  have htrace : WordTrace (prefixWord ++ tailWord_1937962) baseStart_1937962 baseEnd_1937962 := by
    simpa [prefixWord, tailWord_1937962, baseEnd_1937962] using wordTrace_append hprefix tailTrace_1937962
  have hstable : (prefixWord ++ tailWord_1937962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937962).length < 2 ^ (prefixWord ++ tailWord_1937962).sum := by decide
  have hdescent : baseEnd_1937962 < baseStart_1937962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1937966 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_1937966 : Nat := 118140960795 + 1937966 * 2 ^ 59
def prefixEnd_1937966 : Nat := 4983230072969 + 3 ^ 40 * 1937966 * 2
def baseEnd_1937966 : Nat := 995108050071269932812463

theorem tailTrace_1937966 : CollatzResearch.WordTrace tailWord_1937966 prefixEnd_1937966 995108050071269932812463 := by
  unfold tailWord_1937966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835428362135954385923219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47122284598058423391590501 8835428362135954385923219)
  ·
    refine ⟨13253142543203931578884829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8835428362135954385923219 13253142543203931578884829)
    ·
      refine ⟨4969928453701474342081811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13253142543203931578884829 4969928453701474342081811)
      ·
        refine ⟨7454892680552211513122717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969928453701474342081811 7454892680552211513122717)
        ·
          refine ⟨2795584755207079317421019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7454892680552211513122717 2795584755207079317421019)
          ·
            refine ⟨4193377132810618976131529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795584755207079317421019 4193377132810618976131529)
            ·
              refine ⟨3145032849607964232098647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193377132810618976131529 3145032849607964232098647)
              ·
                refine ⟨4717549274411946348147971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145032849607964232098647 4717549274411946348147971)
                ·
                  refine ⟨7076323911617919522221957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717549274411946348147971 7076323911617919522221957)
                  ·
                    refine ⟨1326810733428359910416617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7076323911617919522221957 1326810733428359910416617)
                    ·
                      refine ⟨995108050071269932812463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326810733428359910416617 995108050071269932812463)
                      ·
                        rfl

theorem cell23_1937966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_1937966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1937966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1937966 prefixEnd_1937966 := by exact prefixLift 1937966
  have htrace : WordTrace (prefixWord ++ tailWord_1937966) baseStart_1937966 baseEnd_1937966 := by
    simpa [prefixWord, tailWord_1937966, baseEnd_1937966] using wordTrace_append hprefix tailTrace_1937966
  have hstable : (prefixWord ++ tailWord_1937966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1937966).length < 2 ^ (prefixWord ++ tailWord_1937966).sum := by decide
  have hdescent : baseEnd_1937966 < baseStart_1937966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1937966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938062 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_1938062 : Nat := 118140960795 + 1938062 * 2 ^ 59
def prefixEnd_1938062 : Nat := 4983230072969 + 3 ^ 40 * 1938062 * 2
def baseEnd_1938062 : Nat := 110573038246011284134669

theorem tailTrace_1938062 : CollatzResearch.WordTrace tailWord_1938062 prefixEnd_1938062 110573038246011284134669 := by
  unfold tailWord_1938062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8835866038092480435360055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47124618869826562321920293 8835866038092480435360055)
  ·
    refine ⟨13253799057138720653040083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8835866038092480435360055 13253799057138720653040083)
    ·
      refine ⟨19880698585708080979560125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13253799057138720653040083 19880698585708080979560125)
      ·
        refine ⟨7455261969640530367335047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19880698585708080979560125 7455261969640530367335047)
        ·
          refine ⟨11182892954460795551002571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455261969640530367335047 11182892954460795551002571)
          ·
            refine ⟨16774339431691193326503857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182892954460795551002571 16774339431691193326503857)
            ·
              refine ⟨12580754573768394994877893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16774339431691193326503857 12580754573768394994877893)
              ·
                refine ⟨2358891482581574061539605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12580754573768394994877893 2358891482581574061539605)
                ·
                  refine ⟨110573038246011284134669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2358891482581574061539605 110573038246011284134669)
                  ·
                    rfl

theorem cell23_1938062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_1938062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938062 prefixEnd_1938062 := by exact prefixLift 1938062
  have htrace : WordTrace (prefixWord ++ tailWord_1938062) baseStart_1938062 baseEnd_1938062 := by
    simpa [prefixWord, tailWord_1938062, baseEnd_1938062] using wordTrace_append hprefix tailTrace_1938062
  have hstable : (prefixWord ++ tailWord_1938062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938062).length < 2 ^ (prefixWord ++ tailWord_1938062).sum := by decide
  have hdescent : baseEnd_1938062 < baseStart_1938062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938066 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1938066 : Nat := 118140960795 + 1938066 * 2 ^ 59
def prefixEnd_1938066 : Nat := 4983230072969 + 3 ^ 40 * 1938066 * 2
def baseEnd_1938066 : Nat := 331719799378906513854001

theorem tailTrace_1938066 : CollatzResearch.WordTrace tailWord_1938066 prefixEnd_1938066 331719799378906513854001 := by
  unfold tailWord_1938066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17671768549181338041506513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47124716131150234777350701 17671768549181338041506513)
  ·
    refine ⟨13253826411886003531129885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17671768549181338041506513 13253826411886003531129885)
    ·
      refine ⟨4970184904457251324173707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13253826411886003531129885 4970184904457251324173707)
      ·
        refine ⟨7455277356685876986260561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970184904457251324173707 7455277356685876986260561)
        ·
          refine ⟨5591458017514407739695421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7455277356685876986260561 5591458017514407739695421)
          ·
            refine ⟨2096796756567902902385783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5591458017514407739695421 2096796756567902902385783)
            ·
              refine ⟨3145195134851854353578675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2096796756567902902385783 3145195134851854353578675)
              ·
                refine ⟨4717792702277781530368013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145195134851854353578675 4717792702277781530368013)
                ·
                  refine ⟨1769172263354168073888005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4717792702277781530368013 1769172263354168073888005)
                  ·
                    refine ⟨331719799378906513854001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769172263354168073888005 331719799378906513854001)
                    ·
                      rfl

theorem cell23_1938066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1938066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938066 prefixEnd_1938066 := by exact prefixLift 1938066
  have htrace : WordTrace (prefixWord ++ tailWord_1938066) baseStart_1938066 baseEnd_1938066 := by
    simpa [prefixWord, tailWord_1938066, baseEnd_1938066] using wordTrace_append hprefix tailTrace_1938066
  have hstable : (prefixWord ++ tailWord_1938066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938066).length < 2 ^ (prefixWord ++ tailWord_1938066).sum := by decide
  have hdescent : baseEnd_1938066 < baseStart_1938066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938099 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 2, 3, 2]
def baseStart_1938099 : Nat := 118140960795 + 1938099 * 2 ^ 59
def prefixEnd_1938099 : Nat := 4983230072969 + 3 ^ 40 * 1938099 * 2
def baseEnd_1938099 : Nat := 995176342998317912449351

theorem tailTrace_1938099 : CollatzResearch.WordTrace tailWord_1938099 prefixEnd_1938099 995176342998317912449351 := by
  unfold tailWord_1938099
  simp only [CollatzResearch.WordTrace]
  refine ⟨70688277805605798801977351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47125518537070532534651567 70688277805605798801977351)
  ·
    refine ⟨106032416708408698202966027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70688277805605798801977351 106032416708408698202966027)
    ·
      refine ⟨159048625062613047304449041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106032416708408698202966027 159048625062613047304449041)
      ·
        refine ⟨119286468796959785478336781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159048625062613047304449041 119286468796959785478336781)
        ·
          refine ⟨44732425798859919554376293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119286468796959785478336781 44732425798859919554376293)
          ·
            refine ⟨8387329837286234916445555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44732425798859919554376293 8387329837286234916445555)
            ·
              refine ⟨12580994755929352374668333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387329837286234916445555 12580994755929352374668333)
              ·
                refine ⟨4717873033473507140500625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12580994755929352374668333 4717873033473507140500625)
                ·
                  refine ⟨3538404775105130355375469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717873033473507140500625 3538404775105130355375469)
                  ·
                    refine ⟨1326901790664423883265801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538404775105130355375469 1326901790664423883265801)
                    ·
                      refine ⟨995176342998317912449351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326901790664423883265801 995176342998317912449351)
                      ·
                        rfl

theorem cell23_1938099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 3, 2].length) (baseStart_1938099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938099 prefixEnd_1938099 := by exact prefixLift 1938099
  have htrace : WordTrace (prefixWord ++ tailWord_1938099) baseStart_1938099 baseEnd_1938099 := by
    simpa [prefixWord, tailWord_1938099, baseEnd_1938099] using wordTrace_append hprefix tailTrace_1938099
  have hstable : (prefixWord ++ tailWord_1938099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938099).length < 2 ^ (prefixWord ++ tailWord_1938099).sum := by decide
  have hdescent : baseEnd_1938099 < baseStart_1938099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938106 : List Nat := [3, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3]
def baseStart_1938106 : Nat := 118140960795 + 1938106 * 2 ^ 59
def prefixEnd_1938106 : Nat := 4983230072969 + 3 ^ 40 * 1938106 * 2
def baseEnd_1938106 : Nat := 995179937362899385061819

theorem tailTrace_1938106 : CollatzResearch.WordTrace tailWord_1938106 prefixEnd_1938106 995179937362899385061819 := by
  unfold tailWord_1938106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17672133279145109749370543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47125688744386959331654781 17672133279145109749370543)
  ·
    refine ⟨26508199918717664624055815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17672133279145109749370543 26508199918717664624055815)
    ·
      refine ⟨39762299878076496936083723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26508199918717664624055815 39762299878076496936083723)
      ·
        refine ⟨59643449817114745404125585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39762299878076496936083723 59643449817114745404125585)
        ·
          refine ⟨44732587362836059053094189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59643449817114745404125585 44732587362836059053094189)
          ·
            refine ⟨16774720261063522144910321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44732587362836059053094189 16774720261063522144910321)
            ·
              refine ⟨12581040195797641608682741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16774720261063522144910321 12581040195797641608682741)
              ·
                refine ⟨1179472518356028900814007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12581040195797641608682741 1179472518356028900814007)
                ·
                  refine ⟨1769208777534043351221011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179472518356028900814007 1769208777534043351221011)
                  ·
                    refine ⟨2653813166301065026831517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1769208777534043351221011 2653813166301065026831517)
                    ·
                      refine ⟨995179937362899385061819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653813166301065026831517 995179937362899385061819)
                      ·
                        rfl

theorem cell23_1938106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3].length) (baseStart_1938106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938106 prefixEnd_1938106 := by exact prefixLift 1938106
  have htrace : WordTrace (prefixWord ++ tailWord_1938106) baseStart_1938106 baseEnd_1938106 := by
    simpa [prefixWord, tailWord_1938106, baseEnd_1938106] using wordTrace_append hprefix tailTrace_1938106
  have hstable : (prefixWord ++ tailWord_1938106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938106).length < 2 ^ (prefixWord ++ tailWord_1938106).sum := by decide
  have hdescent : baseEnd_1938106 < baseStart_1938106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938116 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_1938116 : Nat := 118140960795 + 1938116 * 2 ^ 59
def prefixEnd_1938116 : Nat := 4983230072969 + 3 ^ 40 * 1938116 * 2
def baseEnd_1938116 : Nat := 995185072169444345936773

theorem tailTrace_1938116 : CollatzResearch.WordTrace tailWord_1938116 prefixEnd_1938116 995185072169444345936773 := by
  unfold tailWord_1938116
  simp only [CollatzResearch.WordTrace]
  refine ⟨35344448923272105352673101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47125931897696140470230801 35344448923272105352673101)
  ·
    refine ⟨13254168346227039507252413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35344448923272105352673101 13254168346227039507252413)
    ·
      refine ⟨4970313129835139815219655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13254168346227039507252413 4970313129835139815219655)
      ·
        refine ⟨7455469694752709722829483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970313129835139815219655 7455469694752709722829483)
        ·
          refine ⟨11183204542129064584244225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455469694752709722829483 11183204542129064584244225)
          ·
            refine ⟨8387403406596798438183169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183204542129064584244225 8387403406596798438183169)
            ·
              refine ⟨6290552554947598828637377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8387403406596798438183169 6290552554947598828637377)
              ·
                refine ⟨4717914416210699121478033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6290552554947598828637377 4717914416210699121478033)
                ·
                  refine ⟨3538435812158024341108525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717914416210699121478033 3538435812158024341108525)
                  ·
                    refine ⟨1326913429559259127915697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538435812158024341108525 1326913429559259127915697)
                    ·
                      refine ⟨995185072169444345936773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1326913429559259127915697 995185072169444345936773)
                      ·
                        rfl

theorem cell23_1938116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_1938116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938116 prefixEnd_1938116 := by exact prefixLift 1938116
  have htrace : WordTrace (prefixWord ++ tailWord_1938116) baseStart_1938116 baseEnd_1938116 := by
    simpa [prefixWord, tailWord_1938116, baseEnd_1938116] using wordTrace_append hprefix tailTrace_1938116
  have hstable : (prefixWord ++ tailWord_1938116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938116).length < 2 ^ (prefixWord ++ tailWord_1938116).sum := by decide
  have hdescent : baseEnd_1938116 < baseStart_1938116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938149 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_1938149 : Nat := 118140960795 + 1938149 * 2 ^ 59
def prefixEnd_1938149 : Nat := 4983230072969 + 3 ^ 40 * 1938149 * 2
def baseEnd_1938149 : Nat := 995202017031042716824121

theorem tailTrace_1938149 : CollatzResearch.WordTrace tailWord_1938149 prefixEnd_1938149 995202017031042716824121 := by
  unfold tailWord_1938149
  simp only [CollatzResearch.WordTrace]
  refine ⟨70690101455424657341297501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47126734303616438227531667 70690101455424657341297501)
  ·
    refine ⟨26508788045784246502986563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70690101455424657341297501 26508788045784246502986563)
    ·
      refine ⟨39763182068676369754479845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26508788045784246502986563 39763182068676369754479845)
      ·
        refine ⟨7455596637876819328964971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39763182068676369754479845 7455596637876819328964971)
        ·
          refine ⟨11183394956815228993447457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7455596637876819328964971 11183394956815228993447457)
          ·
            refine ⟨8387546217611421745085593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11183394956815228993447457 8387546217611421745085593)
            ·
              refine ⟨6290659663208566308814195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8387546217611421745085593 6290659663208566308814195)
              ·
                refine ⟨9435989494812849463221293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290659663208566308814195 9435989494812849463221293)
                ·
                  refine ⟨3538496060554818548707985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9435989494812849463221293 3538496060554818548707985)
                  ·
                    refine ⟨2653872045416113911530989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3538496060554818548707985 2653872045416113911530989)
                    ·
                      refine ⟨995202017031042716824121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653872045416113911530989 995202017031042716824121)
                      ·
                        rfl

theorem cell23_1938149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_1938149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938149 prefixEnd_1938149 := by exact prefixLift 1938149
  have htrace : WordTrace (prefixWord ++ tailWord_1938149) baseStart_1938149 baseEnd_1938149 := by
    simpa [prefixWord, tailWord_1938149, baseEnd_1938149] using wordTrace_append hprefix tailTrace_1938149
  have hstable : (prefixWord ++ tailWord_1938149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938149).length < 2 ^ (prefixWord ++ tailWord_1938149).sum := by decide
  have hdescent : baseEnd_1938149 < baseStart_1938149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938166 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1938166 : Nat := 118140960795 + 1938166 * 2 ^ 59
def prefixEnd_1938166 : Nat := 4983230072969 + 3 ^ 40 * 1938166 * 2
def baseEnd_1938166 : Nat := 995210746202169150311543

theorem tailTrace_1938166 : CollatzResearch.WordTrace tailWord_1938166 prefixEnd_1938166 995210746202169150311543 := by
  unfold tailWord_1938166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4418170093522691827791647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47127147664242046163110901 4418170093522691827791647)
  ·
    refine ⟨6627255140284037741687471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4418170093522691827791647 6627255140284037741687471)
    ·
      refine ⟨9940882710426056612531207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6627255140284037741687471 9940882710426056612531207)
      ·
        refine ⟨14911324065639084918796811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9940882710426056612531207 14911324065639084918796811)
        ·
          refine ⟨22366986098458627378195217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14911324065639084918796811 22366986098458627378195217)
          ·
            refine ⟨16775239573843970533646413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22366986098458627378195217 16775239573843970533646413)
            ·
              refine ⟨6290714840191488950117405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16775239573843970533646413 6290714840191488950117405)
              ·
                refine ⟨2359018065071808356294027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6290714840191488950117405 2359018065071808356294027)
                ·
                  refine ⟨3538527097607712534441041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359018065071808356294027 3538527097607712534441041)
                  ·
                    refine ⟨2653895323205784400830781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3538527097607712534441041 2653895323205784400830781)
                    ·
                      refine ⟨995210746202169150311543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2653895323205784400830781 995210746202169150311543)
                      ·
                        rfl

theorem cell23_1938166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1938166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938166 prefixEnd_1938166 := by exact prefixLift 1938166
  have htrace : WordTrace (prefixWord ++ tailWord_1938166) baseStart_1938166 baseEnd_1938166 := by
    simpa [prefixWord, tailWord_1938166, baseEnd_1938166] using wordTrace_append hprefix tailTrace_1938166
  have hstable : (prefixWord ++ tailWord_1938166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938166).length < 2 ^ (prefixWord ++ tailWord_1938166).sum := by decide
  have hdescent : baseEnd_1938166 < baseStart_1938166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938289 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_1938289 : Nat := 118140960795 + 1938289 * 2 ^ 59
def prefixEnd_1938289 : Nat := 4983230072969 + 3 ^ 40 * 1938289 * 2
def baseEnd_1938289 : Nat := 331757968107557389691159

theorem tailTrace_1938289 : CollatzResearch.WordTrace tailWord_1938289 prefixEnd_1938289 331757968107557389691159 := by
  unfold tailWord_1938289
  simp only [CollatzResearch.WordTrace]
  refine ⟨70695207674917461251393921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47130138449944974167595947 70695207674917461251393921)
  ·
    refine ⟨53021405756188095938545441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70695207674917461251393921 53021405756188095938545441)
    ·
      refine ⟨39766054317141071953909081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53021405756188095938545441 39766054317141071953909081)
      ·
        refine ⟨29824540737855803965431811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39766054317141071953909081 29824540737855803965431811)
        ·
          refine ⟨44736811106783705948147717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29824540737855803965431811 44736811106783705948147717)
          ·
            refine ⟨8388152082521944865277697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44736811106783705948147717 8388152082521944865277697)
            ·
              refine ⟨6291114061891458648958273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8388152082521944865277697 6291114061891458648958273)
              ·
                refine ⟨4718335546418593986718705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291114061891458648958273 4718335546418593986718705)
                ·
                  refine ⟨3538751659813945490039029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718335546418593986718705 3538751659813945490039029)
                  ·
                    refine ⟨331757968107557389691159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3538751659813945490039029 331757968107557389691159)
                    ·
                      rfl

theorem cell23_1938289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_1938289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938289 prefixEnd_1938289 := by exact prefixLift 1938289
  have htrace : WordTrace (prefixWord ++ tailWord_1938289) baseStart_1938289 baseEnd_1938289 := by
    simpa [prefixWord, tailWord_1938289, baseEnd_1938289] using wordTrace_append hprefix tailTrace_1938289
  have hstable : (prefixWord ++ tailWord_1938289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938289).length < 2 ^ (prefixWord ++ tailWord_1938289).sum := by decide
  have hdescent : baseEnd_1938289 < baseStart_1938289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938293 : List Nat := [1, 3, 4, 1, 1, 2, 4, 2, 5]
def baseStart_1938293 : Nat := 118140960795 + 1938293 * 2 ^ 59
def prefixEnd_1938293 : Nat := 4983230072969 + 3 ^ 40 * 1938293 * 2
def baseEnd_1938293 : Nat := 110586217582810017047051

theorem tailTrace_1938293 : CollatzResearch.WordTrace tailWord_1938293 prefixEnd_1938293 110586217582810017047051 := by
  unfold tailWord_1938293
  simp only [CollatzResearch.WordTrace]
  refine ⟨70695353566902969934539533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47130235711268646623026355 70695353566902969934539533)
  ·
    refine ⟨26510757587588613725452325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70695353566902969934539533 26510757587588613725452325)
    ·
      refine ⟨4970767047672865073522311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26510757587588613725452325 4970767047672865073522311)
      ·
        refine ⟨7456150571509297610283467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970767047672865073522311 7456150571509297610283467)
        ·
          refine ⟨11184225857263946415425201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456150571509297610283467 11184225857263946415425201)
          ·
            refine ⟨8388169392947959811568901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11184225857263946415425201 8388169392947959811568901)
            ·
              refine ⟨1572781761177742464669169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8388169392947959811568901 1572781761177742464669169)
              ·
                refine ⟨1179586320883306848501877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572781761177742464669169 1179586320883306848501877)
                ·
                  refine ⟨110586217582810017047051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1179586320883306848501877 110586217582810017047051)
                  ·
                    rfl

theorem cell23_1938293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_1938293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938293 prefixEnd_1938293 := by exact prefixLift 1938293
  have htrace : WordTrace (prefixWord ++ tailWord_1938293) baseStart_1938293 baseEnd_1938293 := by
    simpa [prefixWord, tailWord_1938293, baseEnd_1938293] using wordTrace_append hprefix tailTrace_1938293
  have hstable : (prefixWord ++ tailWord_1938293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938293).length < 2 ^ (prefixWord ++ tailWord_1938293).sum := by decide
  have hdescent : baseEnd_1938293 < baseStart_1938293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938353 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_1938353 : Nat := 118140960795 + 1938353 * 2 ^ 59
def prefixEnd_1938353 : Nat := 4983230072969 + 3 ^ 40 * 1938353 * 2
def baseEnd_1938353 : Nat := 331768922361519972891061

theorem tailTrace_1938353 : CollatzResearch.WordTrace tailWord_1938353 prefixEnd_1938353 331768922361519972891061 := by
  unfold tailWord_1938353
  simp only [CollatzResearch.WordTrace]
  refine ⟨70697541946685600181723713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47131694631123733454482475 70697541946685600181723713)
  ·
    refine ⟨53023156460014200136292785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70697541946685600181723713 53023156460014200136292785)
    ·
      refine ⟨39767367345010650102219589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53023156460014200136292785 39767367345010650102219589)
      ·
        refine ⟨7456381377189496894166173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39767367345010650102219589 7456381377189496894166173)
        ·
          refine ⟨2796143016446061335312315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7456381377189496894166173 2796143016446061335312315)
          ·
            refine ⟨4194214524669092002968473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796143016446061335312315 4194214524669092002968473)
            ·
              refine ⟨3145660893501819002226355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194214524669092002968473 3145660893501819002226355)
              ·
                refine ⟨4718491340252728503339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145660893501819002226355 4718491340252728503339533)
                ·
                  refine ⟨1769434252594773188752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4718491340252728503339533 1769434252594773188752325)
                  ·
                    refine ⟨331768922361519972891061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769434252594773188752325 331768922361519972891061)
                    ·
                      rfl

theorem cell23_1938353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_1938353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938353 prefixEnd_1938353 := by exact prefixLift 1938353
  have htrace : WordTrace (prefixWord ++ tailWord_1938353) baseStart_1938353 baseEnd_1938353 := by
    simpa [prefixWord, tailWord_1938353, baseEnd_1938353] using wordTrace_append hprefix tailTrace_1938353
  have hstable : (prefixWord ++ tailWord_1938353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938353).length < 2 ^ (prefixWord ++ tailWord_1938353).sum := by decide
  have hdescent : baseEnd_1938353 < baseStart_1938353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938403 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 2, 3, 2]
def baseStart_1938403 : Nat := 118140960795 + 1938403 * 2 ^ 59
def prefixEnd_1938403 : Nat := 4983230072969 + 3 ^ 40 * 1938403 * 2
def baseEnd_1938403 : Nat := 995332441117284723047953

theorem tailTrace_1938403 : CollatzResearch.WordTrace tailWord_1938403 prefixEnd_1938403 995332441117284723047953 := by
  unfold tailWord_1938403
  simp only [CollatzResearch.WordTrace]
  refine ⟨70699365596504458721043863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47132910397669639147362575 70699365596504458721043863)
  ·
    refine ⟨106049048394756688081565795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70699365596504458721043863 106049048394756688081565795)
    ·
      refine ⟨159073572592135032122348693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106049048394756688081565795 159073572592135032122348693)
      ·
        refine ⟨7456573715256329630735095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 159073572592135032122348693 7456573715256329630735095)
        ·
          refine ⟨11184860572884494446102643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456573715256329630735095 11184860572884494446102643)
          ·
            refine ⟨16777290859326741669153965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184860572884494446102643 16777290859326741669153965)
            ·
              refine ⟨6291484072247528125932737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16777290859326741669153965 6291484072247528125932737)
              ·
                refine ⟨4718613054185646094449553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6291484072247528125932737 4718613054185646094449553)
                ·
                  refine ⟨3538959790639234570837165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718613054185646094449553 3538959790639234570837165)
                  ·
                    refine ⟨1327109921489712964063937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3538959790639234570837165 1327109921489712964063937)
                    ·
                      refine ⟨995332441117284723047953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327109921489712964063937 995332441117284723047953)
                      ·
                        rfl

theorem cell23_1938403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_1938403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938403 prefixEnd_1938403 := by exact prefixLift 1938403
  have htrace : WordTrace (prefixWord ++ tailWord_1938403) baseStart_1938403 baseEnd_1938403 := by
    simpa [prefixWord, tailWord_1938403, baseEnd_1938403] using wordTrace_append hprefix tailTrace_1938403
  have hstable : (prefixWord ++ tailWord_1938403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938403).length < 2 ^ (prefixWord ++ tailWord_1938403).sum := by decide
  have hdescent : baseEnd_1938403 < baseStart_1938403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938410 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1938410 : Nat := 118140960795 + 1938410 * 2 ^ 59
def prefixEnd_1938410 : Nat := 4983230072969 + 3 ^ 40 * 1938410 * 2
def baseEnd_1938410 : Nat := 995336035481866195660421

theorem tailTrace_1938410 : CollatzResearch.WordTrace tailWord_1938410 prefixEnd_1938410 995336035481866195660421 := by
  unfold tailWord_1938410
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674905226869774729137171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47133080604986065944365789 17674905226869774729137171)
  ·
    refine ⟨26512357840304662093705757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17674905226869774729137171 26512357840304662093705757)
    ·
      refine ⟨9942134190114248285139659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26512357840304662093705757 9942134190114248285139659)
      ·
        refine ⟨14913201285171372427709489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942134190114248285139659 14913201285171372427709489)
        ·
          refine ⟨11184900963878529320782117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14913201285171372427709489 11184900963878529320782117)
          ·
            refine ⟨2097168930727224247646647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11184900963878529320782117 2097168930727224247646647)
            ·
              refine ⟨3145753396090836371469971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097168930727224247646647 3145753396090836371469971)
              ·
                refine ⟨4718630094136254557204957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145753396090836371469971 4718630094136254557204957)
                ·
                  refine ⟨1769486285301095458951859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4718630094136254557204957 1769486285301095458951859)
                  ·
                    refine ⟨2654229427951643188427789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1769486285301095458951859 2654229427951643188427789)
                    ·
                      refine ⟨995336035481866195660421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654229427951643188427789 995336035481866195660421)
                      ·
                        rfl

theorem cell23_1938410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1938410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938410 prefixEnd_1938410 := by exact prefixLift 1938410
  have htrace : WordTrace (prefixWord ++ tailWord_1938410) baseStart_1938410 baseEnd_1938410 := by
    simpa [prefixWord, tailWord_1938410, baseEnd_1938410] using wordTrace_append hprefix tailTrace_1938410
  have hstable : (prefixWord ++ tailWord_1938410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938410).length < 2 ^ (prefixWord ++ tailWord_1938410).sum := by decide
  have hdescent : baseEnd_1938410 < baseStart_1938410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938419 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3]
def baseStart_1938419 : Nat := 118140960795 + 1938419 * 2 ^ 59
def prefixEnd_1938419 : Nat := 4983230072969 + 3 ^ 40 * 1938419 * 2
def baseEnd_1938419 : Nat := 995340656807756660447879

theorem tailTrace_1938419 : CollatzResearch.WordTrace tailWord_1938419 prefixEnd_1938419 995340656807756660447879 := by
  unfold tailWord_1938419
  simp only [CollatzResearch.WordTrace]
  refine ⟨70699949164446493453626311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47133299442964328969084207 70699949164446493453626311)
  ·
    refine ⟨106049923746669740180439467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70699949164446493453626311 106049923746669740180439467)
    ·
      refine ⟨159074885620004610270659201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106049923746669740180439467 159074885620004610270659201)
      ·
        refine ⟨119306164215003457702994401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159074885620004610270659201 119306164215003457702994401)
        ·
          refine ⟨89479623161252593277245801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119306164215003457702994401 89479623161252593277245801)
          ·
            refine ⟨67109717370939444957934351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89479623161252593277245801 67109717370939444957934351)
            ·
              refine ⟨100664576056409167436901527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67109717370939444957934351 100664576056409167436901527)
              ·
                refine ⟨150996864084613751155352291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100664576056409167436901527 150996864084613751155352291)
                ·
                  refine ⟨226495296126920626733028437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150996864084613751155352291 226495296126920626733028437)
                  ·
                    refine ⟨2654241751487351094527677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 226495296126920626733028437 2654241751487351094527677)
                    ·
                      refine ⟨995340656807756660447879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654241751487351094527677 995340656807756660447879)
                      ·
                        rfl

theorem cell23_1938419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_1938419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938419 prefixEnd_1938419 := by exact prefixLift 1938419
  have htrace : WordTrace (prefixWord ++ tailWord_1938419) baseStart_1938419 baseEnd_1938419 := by
    simpa [prefixWord, tailWord_1938419, baseEnd_1938419] using wordTrace_append hprefix tailTrace_1938419
  have hstable : (prefixWord ++ tailWord_1938419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938419).length < 2 ^ (prefixWord ++ tailWord_1938419).sum := by decide
  have hdescent : baseEnd_1938419 < baseStart_1938419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938433 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_1938433 : Nat := 118140960795 + 1938433 * 2 ^ 59
def prefixEnd_1938433 : Nat := 4983230072969 + 3 ^ 40 * 1938433 * 2
def baseEnd_1938433 : Nat := 995347845536919605672815

theorem tailTrace_1938433 : CollatzResearch.WordTrace tailWord_1938433 prefixEnd_1938433 995347845536919605672815 := by
  unfold tailWord_1938433
  simp only [CollatzResearch.WordTrace]
  refine ⟨70700459786395773844635953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47133639857597182563090635 70700459786395773844635953)
  ·
    refine ⟨53025344839796830383476965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70700459786395773844635953 53025344839796830383476965)
    ·
      refine ⟨9942252157461905696901931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53025344839796830383476965 9942252157461905696901931)
      ·
        refine ⟨14913378236192858545352897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942252157461905696901931 14913378236192858545352897)
        ·
          refine ⟨11185033677144643909014673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14913378236192858545352897 11185033677144643909014673)
          ·
            refine ⟨8388775257858482931761005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11185033677144643909014673 8388775257858482931761005)
            ·
              refine ⟨3145790721696931099410377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8388775257858482931761005 3145790721696931099410377)
              ·
                refine ⟨2359343041272698324557783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145790721696931099410377 2359343041272698324557783)
                ·
                  refine ⟨3539014561909047486836675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359343041272698324557783 3539014561909047486836675)
                  ·
                    refine ⟨5308521842863571230255013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539014561909047486836675 5308521842863571230255013)
                    ·
                      refine ⟨995347845536919605672815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5308521842863571230255013 995347845536919605672815)
                      ·
                        rfl

theorem cell23_1938433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_1938433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938433 prefixEnd_1938433 := by exact prefixLift 1938433
  have htrace : WordTrace (prefixWord ++ tailWord_1938433) baseStart_1938433 baseEnd_1938433 := by
    simpa [prefixWord, tailWord_1938433, baseEnd_1938433] using wordTrace_append hprefix tailTrace_1938433
  have hstable : (prefixWord ++ tailWord_1938433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938433).length < 2 ^ (prefixWord ++ tailWord_1938433).sum := by decide
  have hdescent : baseEnd_1938433 < baseStart_1938433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938439 : List Nat := [1, 1, 4, 3, 1, 1, 1, 11]
def baseStart_1938439 : Nat := 118140960795 + 1938439 * 2 ^ 59
def prefixEnd_1938439 : Nat := 4983230072969 + 3 ^ 40 * 1938439 * 2
def baseEnd_1938439 : Nat := 36864849126698021562881

theorem tailTrace_1938439 : CollatzResearch.WordTrace tailWord_1938439 prefixEnd_1938439 36864849126698021562881 := by
  unfold tailWord_1938439
  simp only [CollatzResearch.WordTrace]
  refine ⟨70700678624374036869354371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47133785749582691246236247 70700678624374036869354371)
  ·
    refine ⟨106051017936561055304031557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70700678624374036869354371 106051017936561055304031557)
    ·
      refine ⟨19884565863105197869505917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106051017936561055304031557 19884565863105197869505917)
      ·
        refine ⟨7456712198664449201064719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19884565863105197869505917 7456712198664449201064719)
        ·
          refine ⟨11185068297996673801597079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456712198664449201064719 11185068297996673801597079)
          ·
            refine ⟨16777602446995010702395619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185068297996673801597079 16777602446995010702395619)
            ·
              refine ⟨25166403670492516053593429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16777602446995010702395619 25166403670492516053593429)
              ·
                refine ⟨36864849126698021562881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 25166403670492516053593429 36864849126698021562881)
                ·
                  rfl

theorem cell23_1938439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 11].length) (baseStart_1938439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938439 prefixEnd_1938439 := by exact prefixLift 1938439
  have htrace : WordTrace (prefixWord ++ tailWord_1938439) baseStart_1938439 baseEnd_1938439 := by
    simpa [prefixWord, tailWord_1938439, baseEnd_1938439] using wordTrace_append hprefix tailTrace_1938439
  have hstable : (prefixWord ++ tailWord_1938439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938439).length < 2 ^ (prefixWord ++ tailWord_1938439).sum := by decide
  have hdescent : baseEnd_1938439 < baseStart_1938439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938446 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1938446 : Nat := 118140960795 + 1938446 * 2 ^ 59
def prefixEnd_1938446 : Nat := 4983230072969 + 3 ^ 40 * 1938446 * 2
def baseEnd_1938446 : Nat := 995354520785428054810255

theorem tailTrace_1938446 : CollatzResearch.WordTrace tailWord_1938446 prefixEnd_1938446 995354520785428054810255 := by
  unfold tailWord_1938446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837616741918584633107399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47133955956899118043239461 8837616741918584633107399)
  ·
    refine ⟨13256425112877876949661099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8837616741918584633107399 13256425112877876949661099)
    ·
      refine ⟨19884637669316815424491649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256425112877876949661099 19884637669316815424491649)
      ·
        refine ⟨14913478251987611568368737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19884637669316815424491649 14913478251987611568368737)
        ·
          refine ⟨11185108688990708676276553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14913478251987611568368737 11185108688990708676276553)
          ·
            refine ⟨8388831516743031507207415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11185108688990708676276553 8388831516743031507207415)
            ·
              refine ⟨12583247275114547260811123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8388831516743031507207415 12583247275114547260811123)
              ·
                refine ⟨18874870912671820891216685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12583247275114547260811123 18874870912671820891216685)
                ·
                  refine ⟨7078076592251932834206257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18874870912671820891216685 7078076592251932834206257)
                  ·
                    refine ⟨5308557444188949625654693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078076592251932834206257 5308557444188949625654693)
                    ·
                      refine ⟨995354520785428054810255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5308557444188949625654693 995354520785428054810255)
                      ·
                        rfl

theorem cell23_1938446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1938446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938446 prefixEnd_1938446 := by exact prefixLift 1938446
  have htrace : WordTrace (prefixWord ++ tailWord_1938446) baseStart_1938446 baseEnd_1938446 := by
    simpa [prefixWord, tailWord_1938446, baseEnd_1938446] using wordTrace_append hprefix tailTrace_1938446
  have hstable : (prefixWord ++ tailWord_1938446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938446).length < 2 ^ (prefixWord ++ tailWord_1938446).sum := by decide
  have hdescent : baseEnd_1938446 < baseStart_1938446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938453 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_1938453 : Nat := 118140960795 + 1938453 * 2 ^ 59
def prefixEnd_1938453 : Nat := 4983230072969 + 3 ^ 40 * 1938453 * 2
def baseEnd_1938453 : Nat := 995358115150009527422723

theorem tailTrace_1938453 : CollatzResearch.WordTrace tailWord_1938453 prefixEnd_1938453 995358115150009527422723 := by
  unfold tailWord_1938453
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701189246323317260364013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47134126164215544840242675 70701189246323317260364013)
  ·
    refine ⟨26512945967371243972636505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70701189246323317260364013 26512945967371243972636505)
    ·
      refine ⟨19884709475528432979477379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26512945967371243972636505 19884709475528432979477379)
      ·
        refine ⟨29827064213292649469216069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19884709475528432979477379 29827064213292649469216069)
        ·
          refine ⟨5592574539992371775478013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29827064213292649469216069 5592574539992371775478013)
          ·
            refine ⟨2097215452497139415804255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5592574539992371775478013 2097215452497139415804255)
            ·
              refine ⟨3145823178745709123706383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2097215452497139415804255 3145823178745709123706383)
              ·
                refine ⟨4718734768118563685559575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145823178745709123706383 4718734768118563685559575)
                ·
                  refine ⟨7078102152177845528339363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718734768118563685559575 7078102152177845528339363)
                  ·
                    refine ⟨10617153228266768292509045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7078102152177845528339363 10617153228266768292509045)
                    ·
                      refine ⟨995358115150009527422723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10617153228266768292509045 995358115150009527422723)
                      ·
                        rfl

theorem cell23_1938453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_1938453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938453 prefixEnd_1938453 := by exact prefixLift 1938453
  have htrace : WordTrace (prefixWord ++ tailWord_1938453) baseStart_1938453 baseEnd_1938453 := by
    simpa [prefixWord, tailWord_1938453, baseEnd_1938453] using wordTrace_append hprefix tailTrace_1938453
  have hstable : (prefixWord ++ tailWord_1938453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938453).length < 2 ^ (prefixWord ++ tailWord_1938453).sum := by decide
  have hdescent : baseEnd_1938453 < baseStart_1938453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938460 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1938460 : Nat := 118140960795 + 1938460 * 2 ^ 59
def prefixEnd_1938460 : Nat := 4983230072969 + 3 ^ 40 * 1938460 * 2
def baseEnd_1938460 : Nat := 331787236504863666678397

theorem tailTrace_1938460 : CollatzResearch.WordTrace tailWord_1938460 prefixEnd_1938460 331787236504863666678397 := by
  unfold tailWord_1938460
  simp only [CollatzResearch.WordTrace]
  refine ⟨35350722278648978727934417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47134296371531971637245889 35350722278648978727934417)
  ·
    refine ⟨26513041708986734045950813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35350722278648978727934417 26513041708986734045950813)
    ·
      refine ⟨9942390640870025267231555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26513041708986734045950813 9942390640870025267231555)
      ·
        refine ⟨14913585961305037900847333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942390640870025267231555 14913585961305037900847333)
        ·
          refine ⟨2796297367744694606408875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14913585961305037900847333 2796297367744694606408875)
          ·
            refine ⟨4194446051617041909613313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796297367744694606408875 4194446051617041909613313)
            ·
              refine ⟨3145834538712781432209985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194446051617041909613313 3145834538712781432209985)
              ·
                refine ⟨2359375904034586074157489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145834538712781432209985 2359375904034586074157489)
                ·
                  refine ⟨1769531928025939555618117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2359375904034586074157489 1769531928025939555618117)
                  ·
                    refine ⟨331787236504863666678397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1769531928025939555618117 331787236504863666678397)
                    ·
                      rfl

theorem cell23_1938460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1938460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938460 prefixEnd_1938460 := by exact prefixLift 1938460
  have htrace : WordTrace (prefixWord ++ tailWord_1938460) baseStart_1938460 baseEnd_1938460 := by
    simpa [prefixWord, tailWord_1938460, baseEnd_1938460] using wordTrace_append hprefix tailTrace_1938460
  have hstable : (prefixWord ++ tailWord_1938460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938460).length < 2 ^ (prefixWord ++ tailWord_1938460).sum := by decide
  have hdescent : baseEnd_1938460 < baseStart_1938460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938461 : List Nat := [1, 4, 2, 2, 4, 1, 2, 2, 1, 1, 3]
def baseStart_1938461 : Nat := 118140960795 + 1938461 * 2 ^ 59
def prefixEnd_1938461 : Nat := 4983230072969 + 3 ^ 40 * 1938461 * 2
def baseEnd_1938461 : Nat := 995362222995245496122687

theorem tailTrace_1938461 : CollatzResearch.WordTrace tailWord_1938461 prefixEnd_1938461 995362222995245496122687 := by
  unfold tailWord_1938461
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701481030294334626655237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47134320686862889751103491 70701481030294334626655237)
  ·
    refine ⟨13256527693180187742497857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70701481030294334626655237 13256527693180187742497857)
    ·
      refine ⟨9942395769885140806873393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13256527693180187742497857 9942395769885140806873393)
      ·
        refine ⟨7456796827413855605155045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942395769885140806873393 7456796827413855605155045)
        ·
          refine ⟨1398149405140097925966571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7456796827413855605155045 1398149405140097925966571)
          ·
            refine ⟨2097224107710146888949857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1398149405140097925966571 2097224107710146888949857)
            ·
              refine ⟨1572918080782610166712393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2097224107710146888949857 1572918080782610166712393)
              ·
                refine ⟨1179688560586957625034295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1572918080782610166712393 1179688560586957625034295)
                ·
                  refine ⟨1769532840880436437551443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179688560586957625034295 1769532840880436437551443)
                  ·
                    refine ⟨2654299261320654656327165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1769532840880436437551443 2654299261320654656327165)
                    ·
                      refine ⟨995362222995245496122687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2654299261320654656327165 995362222995245496122687)
                      ·
                        rfl

theorem cell23_1938461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_1938461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938461 prefixEnd_1938461 := by exact prefixLift 1938461
  have htrace : WordTrace (prefixWord ++ tailWord_1938461) baseStart_1938461 baseEnd_1938461 := by
    simpa [prefixWord, tailWord_1938461, baseEnd_1938461] using wordTrace_append hprefix tailTrace_1938461
  have hstable : (prefixWord ++ tailWord_1938461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938461).length < 2 ^ (prefixWord ++ tailWord_1938461).sum := by decide
  have hdescent : baseEnd_1938461 < baseStart_1938461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938467 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 1, 2, 2]
def baseStart_1938467 : Nat := 118140960795 + 1938467 * 2 ^ 59
def prefixEnd_1938467 : Nat := 4983230072969 + 3 ^ 40 * 1938467 * 2
def baseEnd_1938467 : Nat := 995365303879172472647659

theorem tailTrace_1938467 : CollatzResearch.WordTrace tailWord_1938467 prefixEnd_1938467 995365303879172472647659 := by
  unfold tailWord_1938467
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701699868272597651373655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47134466578848398434249103 70701699868272597651373655)
  ·
    refine ⟨106052549802408896477060483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70701699868272597651373655 106052549802408896477060483)
    ·
      refine ⟨159078824703613344715590725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106052549802408896477060483 159078824703613344715590725)
      ·
        refine ⟨29827279631927502134173261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159078824703613344715590725 29827279631927502134173261)
        ·
          refine ⟨11185229861972813300314973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29827279631927502134173261 11185229861972813300314973)
          ·
            refine ⟨4194461198239804987618115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11185229861972813300314973 4194461198239804987618115)
            ·
              refine ⟨6291691797359707481427173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194461198239804987618115 6291691797359707481427173)
              ·
                refine ⟨1179692212004945152767595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6291691797359707481427173 1179692212004945152767595)
                ·
                  refine ⟨1769538318007417729151393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1179692212004945152767595 1769538318007417729151393)
                  ·
                    refine ⟨1327153738505563296863545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1769538318007417729151393 1327153738505563296863545)
                    ·
                      refine ⟨995365303879172472647659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327153738505563296863545 995365303879172472647659)
                      ·
                        rfl

theorem cell23_1938467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_1938467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938467 prefixEnd_1938467 := by exact prefixLift 1938467
  have htrace : WordTrace (prefixWord ++ tailWord_1938467) baseStart_1938467 baseEnd_1938467 := by
    simpa [prefixWord, tailWord_1938467, baseEnd_1938467] using wordTrace_append hprefix tailTrace_1938467
  have hstable : (prefixWord ++ tailWord_1938467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938467).length < 2 ^ (prefixWord ++ tailWord_1938467).sum := by decide
  have hdescent : baseEnd_1938467 < baseStart_1938467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938469 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_1938469 : Nat := 118140960795 + 1938469 * 2 ^ 59
def prefixEnd_1938469 : Nat := 4983230072969 + 3 ^ 40 * 1938469 * 2
def baseEnd_1938469 : Nat := 331788776946827154940883

theorem tailTrace_1938469 : CollatzResearch.WordTrace tailWord_1938469 prefixEnd_1938469 331788776946827154940883 := by
  unfold tailWord_1938469
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701772814265351992946461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47134515209510234661964307 70701772814265351992946461)
  ·
    refine ⟨26513164805349506997354923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70701772814265351992946461 26513164805349506997354923)
    ·
      refine ⟨39769747208024260496032385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26513164805349506997354923 39769747208024260496032385)
      ·
        refine ⟨29827310406018195372024289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39769747208024260496032385 29827310406018195372024289)
        ·
          refine ⟨22370482804513646529018217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29827310406018195372024289 22370482804513646529018217)
          ·
            refine ⟨16777862103385234896763663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22370482804513646529018217 16777862103385234896763663)
            ·
              refine ⟨25166793155077852345145495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16777862103385234896763663 25166793155077852345145495)
              ·
                refine ⟨37750189732616778517718243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25166793155077852345145495 37750189732616778517718243)
                ·
                  refine ⟨56625284598925167776577365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37750189732616778517718243 56625284598925167776577365)
                  ·
                    refine ⟨331788776946827154940883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 56625284598925167776577365 331788776946827154940883)
                    ·
                      rfl

theorem cell23_1938469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_1938469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938469 prefixEnd_1938469 := by exact prefixLift 1938469
  have htrace : WordTrace (prefixWord ++ tailWord_1938469) baseStart_1938469 baseEnd_1938469 := by
    simpa [prefixWord, tailWord_1938469, baseEnd_1938469] using wordTrace_append hprefix tailTrace_1938469
  have hstable : (prefixWord ++ tailWord_1938469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938469).length < 2 ^ (prefixWord ++ tailWord_1938469).sum := by decide
  have hdescent : baseEnd_1938469 < baseStart_1938469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938499 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 8]
def baseStart_1938499 : Nat := 118140960795 + 1938499 * 2 ^ 59
def prefixEnd_1938499 : Nat := 4983230072969 + 3 ^ 40 * 1938499 * 2
def baseEnd_1938499 : Nat := 331793911753372115815837

theorem tailTrace_1938499 : CollatzResearch.WordTrace tailWord_1938499 prefixEnd_1938499 331793911753372115815837 := by
  unfold tailWord_1938499
  simp only [CollatzResearch.WordTrace]
  refine ⟨70702867004156667116538551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47135244669437778077692367 70702867004156667116538551)
  ·
    refine ⟨106054300506235000674807827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70702867004156667116538551 106054300506235000674807827)
    ·
      refine ⟨159081450759352501012211741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106054300506235000674807827 159081450759352501012211741)
      ·
        refine ⟨59655544034757187879579403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159081450759352501012211741 59655544034757187879579403)
        ·
          refine ⟨89483316052135781819369105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59655544034757187879579403 89483316052135781819369105)
          ·
            refine ⟨67112487039101836364526829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89483316052135781819369105 67112487039101836364526829)
            ·
              refine ⟨25167182639663188636697561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67112487039101836364526829 25167182639663188636697561)
              ·
                refine ⟨18875386979747391477523171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25167182639663188636697561 18875386979747391477523171)
                ·
                  refine ⟨28313080469621087216284757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18875386979747391477523171 28313080469621087216284757)
                  ·
                    refine ⟨331793911753372115815837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28313080469621087216284757 331793911753372115815837)
                    ·
                      rfl

theorem cell23_1938499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_1938499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938499 prefixEnd_1938499 := by exact prefixLift 1938499
  have htrace : WordTrace (prefixWord ++ tailWord_1938499) baseStart_1938499 baseEnd_1938499 := by
    simpa [prefixWord, tailWord_1938499, baseEnd_1938499] using wordTrace_append hprefix tailTrace_1938499
  have hstable : (prefixWord ++ tailWord_1938499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938499).length < 2 ^ (prefixWord ++ tailWord_1938499).sum := by decide
  have hdescent : baseEnd_1938499 < baseStart_1938499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938510 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_1938510 : Nat := 118140960795 + 1938510 * 2 ^ 59
def prefixEnd_1938510 : Nat := 4983230072969 + 3 ^ 40 * 1938510 * 2
def baseEnd_1938510 : Nat := 995387383547315804409961

theorem tailTrace_1938510 : CollatzResearch.WordTrace tailWord_1938510 prefixEnd_1938510 995387383547315804409961 := by
  unfold tailWord_1938510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8837908525889601999398623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47135512138077877330125989 8837908525889601999398623)
  ·
    refine ⟨13256862788834402999097935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8837908525889601999398623 13256862788834402999097935)
    ·
      refine ⟨19885294183251604498646903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256862788834402999097935 19885294183251604498646903)
      ·
        refine ⟨29827941274877406747970355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19885294183251604498646903 29827941274877406747970355)
        ·
          refine ⟨44741911912316110121955533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29827941274877406747970355 44741911912316110121955533)
          ·
            refine ⟨16778216967118541295733325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44741911912316110121955533 16778216967118541295733325)
            ·
              refine ⟨6291831362669452985899997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16778216967118541295733325 6291831362669452985899997)
              ·
                refine ⟨2359436761001044869712499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6291831362669452985899997 2359436761001044869712499)
                ·
                  refine ⟨3539155141501567304568749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359436761001044869712499 3539155141501567304568749)
                  ·
                    refine ⟨1327183178063087739213281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3539155141501567304568749 1327183178063087739213281)
                    ·
                      refine ⟨995387383547315804409961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1327183178063087739213281 995387383547315804409961)
                      ·
                        rfl

theorem cell23_1938510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_1938510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938510 prefixEnd_1938510 := by exact prefixLift 1938510
  have htrace : WordTrace (prefixWord ++ tailWord_1938510) baseStart_1938510 baseEnd_1938510 := by
    simpa [prefixWord, tailWord_1938510, baseEnd_1938510] using wordTrace_append hprefix tailTrace_1938510
  have hstable : (prefixWord ++ tailWord_1938510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938510).length < 2 ^ (prefixWord ++ tailWord_1938510).sum := by decide
  have hdescent : baseEnd_1938510 < baseStart_1938510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938516 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1938516 : Nat := 118140960795 + 1938516 * 2 ^ 59
def prefixEnd_1938516 : Nat := 4983230072969 + 3 ^ 40 * 1938516 * 2
def baseEnd_1938516 : Nat := 331796821477080926978311

theorem tailTrace_1938516 : CollatzResearch.WordTrace tailWord_1938516 prefixEnd_1938516 331796821477080926978311 := by
  unfold tailWord_1938516
  simp only [CollatzResearch.WordTrace]
  refine ⟨35351743522547539509953701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47135658030063386013271601 35351743522547539509953701)
  ·
    refine ⟨6628451910477663658116319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35351743522547539509953701 6628451910477663658116319)
    ·
      refine ⟨9942677865716495487174479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6628451910477663658116319 9942677865716495487174479)
      ·
        refine ⟨14914016798574743230761719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942677865716495487174479 14914016798574743230761719)
        ·
          refine ⟨22371025197862114846142579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14914016798574743230761719 22371025197862114846142579)
          ·
            refine ⟨33556537796793172269213869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22371025197862114846142579 33556537796793172269213869)
            ·
              refine ⟨12583701673797439600955201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33556537796793172269213869 12583701673797439600955201)
              ·
                refine ⟨9437776255348079700716401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12583701673797439600955201 9437776255348079700716401)
                ·
                  refine ⟨7078332191511059775537301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9437776255348079700716401 7078332191511059775537301)
                  ·
                    refine ⟨331796821477080926978311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7078332191511059775537301 331796821477080926978311)
                    ·
                      rfl

theorem cell23_1938516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1938516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938516 prefixEnd_1938516 := by exact prefixLift 1938516
  have htrace : WordTrace (prefixWord ++ tailWord_1938516) baseStart_1938516 baseEnd_1938516 := by
    simpa [prefixWord, tailWord_1938516, baseEnd_1938516] using wordTrace_append hprefix tailTrace_1938516
  have hstable : (prefixWord ++ tailWord_1938516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938516).length < 2 ^ (prefixWord ++ tailWord_1938516).sum := by decide
  have hdescent : baseEnd_1938516 < baseStart_1938516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938539 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_1938539 : Nat := 118140960795 + 1938539 * 2 ^ 59
def prefixEnd_1938539 : Nat := 4983230072969 + 3 ^ 40 * 1938539 * 2
def baseEnd_1938539 : Nat := 995402274486296190947327

theorem tailTrace_1938539 : CollatzResearch.WordTrace tailWord_1938539 prefixEnd_1938539 995402274486296190947327 := by
  unfold tailWord_1938539
  simp only [CollatzResearch.WordTrace]
  refine ⟨70704325924011753947994671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47136217282674502631996447 70704325924011753947994671)
  ·
    refine ⟨106056488886017630921992007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70704325924011753947994671 106056488886017630921992007)
    ·
      refine ⟨159084733329026446382988011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106056488886017630921992007 159084733329026446382988011)
      ·
        refine ⟨238627099993539669574482017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159084733329026446382988011 238627099993539669574482017)
        ·
          refine ⟨178970324995154752180861513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238627099993539669574482017 178970324995154752180861513)
          ·
            refine ⟨134227743746366064135646135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178970324995154752180861513 134227743746366064135646135)
            ·
              refine ⟨201341615619549096203469203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134227743746366064135646135 201341615619549096203469203)
              ·
                refine ⟨302012423429323644305203805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201341615619549096203469203 302012423429323644305203805)
                ·
                  refine ⟨113254658785996366614451427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 302012423429323644305203805 113254658785996366614451427)
                  ·
                    refine ⟨169881988178994549921677141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113254658785996366614451427 169881988178994549921677141)
                    ·
                      refine ⟨995402274486296190947327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 169881988178994549921677141 995402274486296190947327)
                      ·
                        rfl

theorem cell23_1938539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_1938539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938539 prefixEnd_1938539 := by exact prefixLift 1938539
  have htrace : WordTrace (prefixWord ++ tailWord_1938539) baseStart_1938539 baseEnd_1938539 := by
    simpa [prefixWord, tailWord_1938539, baseEnd_1938539] using wordTrace_append hprefix tailTrace_1938539
  have hstable : (prefixWord ++ tailWord_1938539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938539).length < 2 ^ (prefixWord ++ tailWord_1938539).sum := by decide
  have hdescent : baseEnd_1938539 < baseStart_1938539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1938546 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 7]
def baseStart_1938546 : Nat := 118140960795 + 1938546 * 2 ^ 59
def prefixEnd_1938546 : Nat := 4983230072969 + 3 ^ 40 * 1938546 * 2
def baseEnd_1938546 : Nat := 110600652094541962617755

theorem tailTrace_1938546 : CollatzResearch.WordTrace tailWord_1938546 prefixEnd_1938546 110600652094541962617755 := by
  unfold tailWord_1938546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676145308746598535874873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47136387489990929428999661 17676145308746598535874873)
  ·
    refine ⟨13257108981559948901906155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17676145308746598535874873 13257108981559948901906155)
    ·
      refine ⟨19885663472339923352859233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13257108981559948901906155 19885663472339923352859233)
      ·
        refine ⟨14914247604254942514644425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19885663472339923352859233 14914247604254942514644425)
        ·
          refine ⟨11185685703191206885983319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14914247604254942514644425 11185685703191206885983319)
          ·
            refine ⟨16778528554786810328974979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185685703191206885983319 16778528554786810328974979)
            ·
              refine ⟨25167792832180215493462469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16778528554786810328974979 25167792832180215493462469)
              ·
                refine ⟨4718961156033790405024213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25167792832180215493462469 4718961156033790405024213)
                ·
                  refine ⟨110600652094541962617755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4718961156033790405024213 110600652094541962617755)
                  ·
                    rfl

theorem cell23_1938546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_1938546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1938546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1938546 prefixEnd_1938546 := by exact prefixLift 1938546
  have htrace : WordTrace (prefixWord ++ tailWord_1938546) baseStart_1938546 baseEnd_1938546 := by
    simpa [prefixWord, tailWord_1938546, baseEnd_1938546] using wordTrace_append hprefix tailTrace_1938546
  have hstable : (prefixWord ++ tailWord_1938546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1938546).length < 2 ^ (prefixWord ++ tailWord_1938546).sum := by decide
  have hdescent : baseEnd_1938546 < baseStart_1938546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1938546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
