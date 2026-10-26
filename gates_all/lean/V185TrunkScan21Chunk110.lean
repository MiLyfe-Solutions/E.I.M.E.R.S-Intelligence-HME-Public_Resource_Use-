import V185TrunkScan21Chunk109

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1336625 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 3]
def baseStart_1336625 : Nat := 118140960795 + 1336625 * 2 ^ 59
def prefixEnd_1336625 : Nat := 4983230072969 + 3 ^ 40 * 1336625 * 2
def baseEnd_1336625 : Nat := 305036035473750303217991

theorem tailTrace_1336625 : CollatzResearch.WordTrace tailWord_1336625 prefixEnd_1336625 305036035473750303217991 := by
  unfold tailWord_1336625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48750718782643377221019329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32500479188428918147346219 48750718782643377221019329)
  ·
    refine ⟨36563039086982532915764497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48750718782643377221019329 36563039086982532915764497)
    ·
      refine ⟨27422279315236899686823373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36563039086982532915764497 27422279315236899686823373)
      ·
        refine ⟨10283354743213837382558765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27422279315236899686823373 10283354743213837382558765)
        ·
          refine ⟨3856258028705189018459537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10283354743213837382558765 3856258028705189018459537)
          ·
            refine ⟨2892193521528891763844653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3856258028705189018459537 2892193521528891763844653)
            ·
              refine ⟨1084572570573334411441745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2892193521528891763844653 1084572570573334411441745)
              ·
                refine ⟨813429427930000808581309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084572570573334411441745 813429427930000808581309)
                ·
                  refine ⟨305036035473750303217991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813429427930000808581309 305036035473750303217991)
                  ·
                    rfl

theorem cell21_1336625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_1336625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336625 prefixEnd_1336625 := by exact prefixLift 1336625
  have htrace : WordTrace (prefixWord ++ tailWord_1336625) baseStart_1336625 baseEnd_1336625 := by
    simpa [prefixWord, tailWord_1336625, baseEnd_1336625] using wordTrace_append hprefix tailTrace_1336625
  have hstable : (prefixWord ++ tailWord_1336625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336625).length < 2 ^ (prefixWord ++ tailWord_1336625).sum := by decide
  have hdescent : baseEnd_1336625 < baseStart_1336625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336636 : List Nat := [2, 2, 2, 2, 1, 4, 2, 6]
def baseStart_1336636 : Nat := 118140960795 + 1336636 * 2 ^ 59
def prefixEnd_1336636 : Nat := 4983230072969 + 3 ^ 40 * 1336636 * 2
def baseEnd_1336636 : Nat := 101679515274538909511545

theorem tailTrace_1336636 : CollatzResearch.WordTrace tailWord_1336636 prefixEnd_1336636 101679515274538909511545 := by
  unfold tailWord_1336636
  simp only [CollatzResearch.WordTrace]
  refine ⟨24375559992801763049834881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32500746657069017399779841 24375559992801763049834881)
  ·
    refine ⟨18281669994601322287376161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24375559992801763049834881 18281669994601322287376161)
    ·
      refine ⟨13711252495950991715532121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18281669994601322287376161 13711252495950991715532121)
      ·
        refine ⟨10283439371963243786649091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13711252495950991715532121 10283439371963243786649091)
        ·
          refine ⟨15425159057944865679973637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10283439371963243786649091 15425159057944865679973637)
          ·
            refine ⟨2892217323364662314995057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15425159057944865679973637 2892217323364662314995057)
            ·
              refine ⟨2169162992523496736246293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2892217323364662314995057 2169162992523496736246293)
              ·
                refine ⟨101679515274538909511545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2169162992523496736246293 101679515274538909511545)
                ·
                  rfl

theorem cell21_1336636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_1336636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336636 prefixEnd_1336636 := by exact prefixLift 1336636
  have htrace : WordTrace (prefixWord ++ tailWord_1336636) baseStart_1336636 baseEnd_1336636 := by
    simpa [prefixWord, tailWord_1336636, baseEnd_1336636] using wordTrace_append hprefix tailTrace_1336636
  have hstable : (prefixWord ++ tailWord_1336636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336636).length < 2 ^ (prefixWord ++ tailWord_1336636).sum := by decide
  have hdescent : baseEnd_1336636 < baseStart_1336636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336639 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 4]
def baseStart_1336639 : Nat := 118140960795 + 1336639 * 2 ^ 59
def prefixEnd_1336639 : Nat := 4983230072969 + 3 ^ 40 * 1336639 * 2
def baseEnd_1336639 : Nat := 305039230464489389984629

theorem tailTrace_1336639 : CollatzResearch.WordTrace tailWord_1336639 prefixEnd_1336639 305039230464489389984629 := by
  unfold tailWord_1336639
  simp only [CollatzResearch.WordTrace]
  refine ⟨48751229404592657612028971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32500819603061771741352647 48751229404592657612028971)
  ·
    refine ⟨73126844106888986418043457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48751229404592657612028971 73126844106888986418043457)
    ·
      refine ⟨54845133080166739813532593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73126844106888986418043457 54845133080166739813532593)
      ·
        refine ⟨41133849810125054860149445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54845133080166739813532593 41133849810125054860149445)
        ·
          refine ⟨7712596839398447786278021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41133849810125054860149445 7712596839398447786278021)
          ·
            refine ⟨1446111907387208959927129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7712596839398447786278021 1446111907387208959927129)
            ·
              refine ⟨1084583930540406719945347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446111907387208959927129 1084583930540406719945347)
              ·
                refine ⟨1626875895810610079918021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084583930540406719945347 1626875895810610079918021)
                ·
                  refine ⟨305039230464489389984629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626875895810610079918021 305039230464489389984629)
                  ·
                    rfl

theorem cell21_1336639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 4].length) (baseStart_1336639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336639 prefixEnd_1336639 := by exact prefixLift 1336639
  have htrace : WordTrace (prefixWord ++ tailWord_1336639) baseStart_1336639 baseEnd_1336639 := by
    simpa [prefixWord, tailWord_1336639, baseEnd_1336639] using wordTrace_append hprefix tailTrace_1336639
  have hstable : (prefixWord ++ tailWord_1336639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336639).length < 2 ^ (prefixWord ++ tailWord_1336639).sum := by decide
  have hdescent : baseEnd_1336639 < baseStart_1336639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336650 : List Nat := [3, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1336650 : Nat := 118140960795 + 1336650 * 2 ^ 59
def prefixEnd_1336650 : Nat := 4983230072969 + 3 ^ 40 * 1336650 * 2
def baseEnd_1336650 : Nat := 305041740814355815301273

theorem tailTrace_1336650 : CollatzResearch.WordTrace tailWord_1336650 prefixEnd_1336650 305041740814355815301273 := by
  unfold tailWord_1336650
  simp only [CollatzResearch.WordTrace]
  refine ⟨12187907651888201622669851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32501087071701870993786269 12187907651888201622669851)
  ·
    refine ⟨18281861477832302434004777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12187907651888201622669851 18281861477832302434004777)
    ·
      refine ⟨13711396108374226825503583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18281861477832302434004777 13711396108374226825503583)
      ·
        refine ⟨20567094162561340238255375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13711396108374226825503583 20567094162561340238255375)
        ·
          refine ⟨30850641243842010357383063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20567094162561340238255375 30850641243842010357383063)
          ·
            refine ⟨46275961865763015536074595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30850641243842010357383063 46275961865763015536074595)
            ·
              refine ⟨69413942798644523304111893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46275961865763015536074595 69413942798644523304111893)
              ·
                refine ⟨3253778568686462029880245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69413942798644523304111893 3253778568686462029880245)
                ·
                  refine ⟨305041740814355815301273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3253778568686462029880245 305041740814355815301273)
                  ·
                    rfl

theorem cell21_1336650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1336650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336650 prefixEnd_1336650 := by exact prefixLift 1336650
  have htrace : WordTrace (prefixWord ++ tailWord_1336650) baseStart_1336650 baseEnd_1336650 := by
    simpa [prefixWord, tailWord_1336650, baseEnd_1336650] using wordTrace_append hprefix tailTrace_1336650
  have hstable : (prefixWord ++ tailWord_1336650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336650).length < 2 ^ (prefixWord ++ tailWord_1336650).sum := by decide
  have hdescent : baseEnd_1336650 < baseStart_1336650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336684 : List Nat := [2, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_1336684 : Nat := 118140960795 + 1336684 * 2 ^ 59
def prefixEnd_1336684 : Nat := 4983230072969 + 3 ^ 40 * 1336684 * 2
def baseEnd_1336684 : Nat := 305049500077579311734537

theorem tailTrace_1336684 : CollatzResearch.WordTrace tailWord_1336684 prefixEnd_1336684 305049500077579311734537 := by
  unfold tailWord_1336684
  simp only [CollatzResearch.WordTrace]
  refine ⟨24376435344714815148708553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32501913792953086864944737 24376435344714815148708553)
  ·
    refine ⟨18282326508536111361531415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24376435344714815148708553 18282326508536111361531415)
    ·
      refine ⟨27423489762804167042297123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18282326508536111361531415 27423489762804167042297123)
      ·
        refine ⟨41135234644206250563445685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27423489762804167042297123 41135234644206250563445685)
        ·
          refine ⟨3856428247894335990323033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41135234644206250563445685 3856428247894335990323033)
          ·
            refine ⟨2892321185920751992742275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3856428247894335990323033 2892321185920751992742275)
            ·
              refine ⟨4338481778881127989113413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2892321185920751992742275 4338481778881127989113413)
              ·
                refine ⟨813465333540211497958765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4338481778881127989113413 813465333540211497958765)
                ·
                  refine ⟨305049500077579311734537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813465333540211497958765 305049500077579311734537)
                  ·
                    rfl

theorem cell21_1336684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_1336684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336684 prefixEnd_1336684 := by exact prefixLift 1336684
  have htrace : WordTrace (prefixWord ++ tailWord_1336684) baseStart_1336684 baseEnd_1336684 := by
    simpa [prefixWord, tailWord_1336684, baseEnd_1336684] using wordTrace_append hprefix tailTrace_1336684
  have hstable : (prefixWord ++ tailWord_1336684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336684).length < 2 ^ (prefixWord ++ tailWord_1336684).sum := by decide
  have hdescent : baseEnd_1336684 < baseStart_1336684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336732 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1336732 : Nat := 118140960795 + 1336732 * 2 ^ 59
def prefixEnd_1336732 : Nat := 4983230072969 + 3 ^ 40 * 1336732 * 2
def baseEnd_1336732 : Nat := 305060454331541894934439

theorem tailTrace_1336732 : CollatzResearch.WordTrace tailWord_1336732 prefixEnd_1336732 305060454331541894934439 := by
  unfold tailWord_1336732
  simp only [CollatzResearch.WordTrace]
  refine ⟨24377310696627867247582225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32503080928837156330109633 24377310696627867247582225)
  ·
    refine ⟨18282983022470900435686669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24377310696627867247582225 18282983022470900435686669)
    ·
      refine ⟨6856118633426587663382501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18282983022470900435686669 6856118633426587663382501)
      ·
        refine ⟨1285522243767485186884219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6856118633426587663382501 1285522243767485186884219)
        ·
          refine ⟨1928283365651227780326329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285522243767485186884219 1928283365651227780326329)
          ·
            refine ⟨1446212524238420835244747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1928283365651227780326329 1446212524238420835244747)
            ·
              refine ⟨2169318786357631252867121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446212524238420835244747 2169318786357631252867121)
              ·
                refine ⟨1626989089768223439650341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169318786357631252867121 1626989089768223439650341)
                ·
                  refine ⟨305060454331541894934439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1626989089768223439650341 305060454331541894934439)
                  ·
                    rfl

theorem cell21_1336732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1336732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336732 prefixEnd_1336732 := by exact prefixLift 1336732
  have htrace : WordTrace (prefixWord ++ tailWord_1336732) baseStart_1336732 baseEnd_1336732 := by
    simpa [prefixWord, tailWord_1336732, baseEnd_1336732] using wordTrace_append hprefix tailTrace_1336732
  have hstable : (prefixWord ++ tailWord_1336732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336732).length < 2 ^ (prefixWord ++ tailWord_1336732).sum := by decide
  have hdescent : baseEnd_1336732 < baseStart_1336732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336743 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_1336743 : Nat := 118140960795 + 1336743 * 2 ^ 59
def prefixEnd_1336743 : Nat := 4983230072969 + 3 ^ 40 * 1336743 * 2
def baseEnd_1336743 : Nat := 305062964681408320251083

theorem tailTrace_1336743 : CollatzResearch.WordTrace tailWord_1336743 prefixEnd_1336743 305062964681408320251083 := by
  unfold tailWord_1336743
  simp only [CollatzResearch.WordTrace]
  refine ⟨48755022596215883373814883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32503348397477255582543255 48755022596215883373814883)
  ·
    refine ⟨73132533894323825060722325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48755022596215883373814883 73132533894323825060722325)
    ·
      refine ⟨3428087526296429299721359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73132533894323825060722325 3428087526296429299721359)
      ·
        refine ⟨5142131289444643949582039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3428087526296429299721359 5142131289444643949582039)
        ·
          refine ⟨7713196934166965924373059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142131289444643949582039 7713196934166965924373059)
          ·
            refine ⟨11569795401250448886559589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713196934166965924373059 11569795401250448886559589)
            ·
              refine ⟨2169336637734459166229923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11569795401250448886559589 2169336637734459166229923)
              ·
                refine ⟨3254004956601688749344885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169336637734459166229923 3254004956601688749344885)
                ·
                  refine ⟨305062964681408320251083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3254004956601688749344885 305062964681408320251083)
                  ·
                    rfl

theorem cell21_1336743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_1336743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336743 prefixEnd_1336743 := by exact prefixLift 1336743
  have htrace : WordTrace (prefixWord ++ tailWord_1336743) baseStart_1336743 baseEnd_1336743 := by
    simpa [prefixWord, tailWord_1336743, baseEnd_1336743] using wordTrace_append hprefix tailTrace_1336743
  have hstable : (prefixWord ++ tailWord_1336743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336743).length < 2 ^ (prefixWord ++ tailWord_1336743).sum := by decide
  have hdescent : baseEnd_1336743 < baseStart_1336743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336853 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 3]
def baseStart_1336853 : Nat := 118140960795 + 1336853 * 2 ^ 59
def prefixEnd_1336853 : Nat := 4983230072969 + 3 ^ 40 * 1336853 * 2
def baseEnd_1336853 : Nat := 305088068180072573417525

theorem tailTrace_1336853 : CollatzResearch.WordTrace tailWord_1336853 prefixEnd_1336853 305088068180072573417525 := by
  unfold tailWord_1336853
  simp only [CollatzResearch.WordTrace]
  refine ⟨48759034625817372160319213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32506023083878248106879475 48759034625817372160319213)
  ·
    refine ⟨18284637984681514560119705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48759034625817372160319213 18284637984681514560119705)
    ·
      refine ⟨13713478488511135920089779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18284637984681514560119705 13713478488511135920089779)
      ·
        refine ⟨20570217732766703880134669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13713478488511135920089779 20570217732766703880134669)
        ·
          refine ⟨7713831649787513955050501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20570217732766703880134669 7713831649787513955050501)
          ·
            refine ⟨1446343434335158866571969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7713831649787513955050501 1446343434335158866571969)
            ·
              refine ⟨1084757575751369149928977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446343434335158866571969 1084757575751369149928977)
              ·
                refine ⟨813568181813526862446733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1084757575751369149928977 813568181813526862446733)
                ·
                  refine ⟨305088068180072573417525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813568181813526862446733 305088068180072573417525)
                  ·
                    rfl

theorem cell21_1336853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_1336853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336853 prefixEnd_1336853 := by exact prefixLift 1336853
  have htrace : WordTrace (prefixWord ++ tailWord_1336853) baseStart_1336853 baseEnd_1336853 := by
    simpa [prefixWord, tailWord_1336853, baseEnd_1336853] using wordTrace_append hprefix tailTrace_1336853
  have hstable : (prefixWord ++ tailWord_1336853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336853).length < 2 ^ (prefixWord ++ tailWord_1336853).sum := by decide
  have hdescent : baseEnd_1336853 < baseStart_1336853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336864 : List Nat := [2, 1, 1, 6, 1, 1, 3, 6]
def baseStart_1336864 : Nat := 118140960795 + 1336864 * 2 ^ 59
def prefixEnd_1336864 : Nat := 4983230072969 + 3 ^ 40 * 1336864 * 2
def baseEnd_1336864 : Nat := 101696859509979666244723

theorem tailTrace_1336864 : CollatzResearch.WordTrace tailWord_1336864 prefixEnd_1336864 101696859509979666244723 := by
  unfold tailWord_1336864
  simp only [CollatzResearch.WordTrace]
  refine ⟨24379717914388760519484823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32506290552518347359313097 24379717914388760519484823)
  ·
    refine ⟨36569576871583140779227235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24379717914388760519484823 36569576871583140779227235)
    ·
      refine ⟨54854365307374711168840853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36569576871583140779227235 54854365307374711168840853)
      ·
        refine ⟨2571298373783189586039415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54854365307374711168840853 2571298373783189586039415)
        ·
          refine ⟨3856947560674784379059123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571298373783189586039415 3856947560674784379059123)
          ·
            refine ⟨5785421341012176568588685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856947560674784379059123 5785421341012176568588685)
            ·
              refine ⟨2169533002879566213220757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5785421341012176568588685 2169533002879566213220757)
              ·
                refine ⟨101696859509979666244723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2169533002879566213220757 101696859509979666244723)
                ·
                  rfl

theorem cell21_1336864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_1336864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336864 prefixEnd_1336864 := by exact prefixLift 1336864
  have htrace : WordTrace (prefixWord ++ tailWord_1336864) baseStart_1336864 baseEnd_1336864 := by
    simpa [prefixWord, tailWord_1336864, baseEnd_1336864] using wordTrace_append hprefix tailTrace_1336864
  have hstable : (prefixWord ++ tailWord_1336864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336864).length < 2 ^ (prefixWord ++ tailWord_1336864).sum := by decide
  have hdescent : baseEnd_1336864 < baseStart_1336864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1336895 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 3]
def baseStart_1336895 : Nat := 118140960795 + 1336895 * 2 ^ 59
def prefixEnd_1336895 : Nat := 4983230072969 + 3 ^ 40 * 1336895 * 2
def baseEnd_1336895 : Nat := 305097653152289833717439

theorem tailTrace_1336895 : CollatzResearch.WordTrace tailWord_1336895 prefixEnd_1336895 305097653152289833717439 := by
  unfold tailWord_1336895
  simp only [CollatzResearch.WordTrace]
  refine ⟨48760566491665213333348139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32507044327776808888898759 48760566491665213333348139)
  ·
    refine ⟨73140849737497820000022209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48760566491665213333348139 73140849737497820000022209)
    ·
      refine ⟨54855637303123365000016657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73140849737497820000022209 54855637303123365000016657)
      ·
        refine ⟨41141727977342523750012493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54855637303123365000016657 41141727977342523750012493)
        ·
          refine ⟨15428147991503446406254685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41141727977342523750012493 15428147991503446406254685)
          ·
            refine ⟨5785555496813792402345507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15428147991503446406254685 5785555496813792402345507)
            ·
              refine ⟨8678333245220688603518261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785555496813792402345507 8678333245220688603518261)
              ·
                refine ⟨813593741739439556579837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8678333245220688603518261 813593741739439556579837)
                ·
                  refine ⟨305097653152289833717439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813593741739439556579837 305097653152289833717439)
                  ·
                    rfl

theorem cell21_1336895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 3].length) (baseStart_1336895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1336895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1336895 prefixEnd_1336895 := by exact prefixLift 1336895
  have htrace : WordTrace (prefixWord ++ tailWord_1336895) baseStart_1336895 baseEnd_1336895 := by
    simpa [prefixWord, tailWord_1336895, baseEnd_1336895] using wordTrace_append hprefix tailTrace_1336895
  have hstable : (prefixWord ++ tailWord_1336895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1336895).length < 2 ^ (prefixWord ++ tailWord_1336895).sum := by decide
  have hdescent : baseEnd_1336895 < baseStart_1336895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1336895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337064 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_1337064 : Nat := 118140960795 + 1337064 * 2 ^ 59
def prefixEnd_1337064 : Nat := 4983230072969 + 3 ^ 40 * 1337064 * 2
def baseEnd_1337064 : Nat := 305136221254783095400427

theorem tailTrace_1337064 : CollatzResearch.WordTrace tailWord_1337064 prefixEnd_1337064 305136221254783095400427 := by
  unfold tailWord_1337064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24383365214026477598125123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32511153618701970130833497 24383365214026477598125123)
  ·
    refine ⟨36575047821039716397187685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24383365214026477598125123 36575047821039716397187685)
    ·
      refine ⟨6857821466444946824472691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36575047821039716397187685 6857821466444946824472691)
      ·
        refine ⟨10286732199667420236709037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857821466444946824472691 10286732199667420236709037)
        ·
          refine ⟨3857524574875282588765889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10286732199667420236709037 3857524574875282588765889)
          ·
            refine ⟨2893143431156461941574417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3857524574875282588765889 2893143431156461941574417)
            ·
              refine ⟨2169857573367346456180813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2893143431156461941574417 2169857573367346456180813)
              ·
                refine ⟨813696590012754921067805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2169857573367346456180813 813696590012754921067805)
                ·
                  refine ⟨305136221254783095400427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813696590012754921067805 305136221254783095400427)
                  ·
                    rfl

theorem cell21_1337064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_1337064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337064 prefixEnd_1337064 := by exact prefixLift 1337064
  have htrace : WordTrace (prefixWord ++ tailWord_1337064) baseStart_1337064 baseEnd_1337064 := by
    simpa [prefixWord, tailWord_1337064, baseEnd_1337064] using wordTrace_append hprefix tailTrace_1337064
  have hstable : (prefixWord ++ tailWord_1337064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337064).length < 2 ^ (prefixWord ++ tailWord_1337064).sum := by decide
  have hdescent : baseEnd_1337064 < baseStart_1337064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337078 : List Nat := [5, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1337078 : Nat := 118140960795 + 1337078 * 2 ^ 59
def prefixEnd_1337078 : Nat := 4983230072969 + 3 ^ 40 * 1337078 * 2
def baseEnd_1337078 : Nat := 305139416245522182167065

theorem tailTrace_1337078 : CollatzResearch.WordTrace tailWord_1337078 prefixEnd_1337078 305139416245522182167065 := by
  unfold tailWord_1337078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047952565625139724203743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32511494033334823724839925 3047952565625139724203743)
  ·
    refine ⟨4571928848437709586305615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3047952565625139724203743 4571928848437709586305615)
    ·
      refine ⟨6857893272656564379458423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4571928848437709586305615 6857893272656564379458423)
      ·
        refine ⟨10286839908984846569187635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857893272656564379458423 10286839908984846569187635)
        ·
          refine ⟨15430259863477269853781453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286839908984846569187635 15430259863477269853781453)
          ·
            refine ⟨5786347448803976195168045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15430259863477269853781453 5786347448803976195168045)
            ·
              refine ⟨2169880293301491073188017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5786347448803976195168045 2169880293301491073188017)
              ·
                refine ⟨1627410219976118304891013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2169880293301491073188017 1627410219976118304891013)
                ·
                  refine ⟨305139416245522182167065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627410219976118304891013 305139416245522182167065)
                  ·
                    rfl

theorem cell21_1337078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1337078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337078 prefixEnd_1337078 := by exact prefixLift 1337078
  have htrace : WordTrace (prefixWord ++ tailWord_1337078) baseStart_1337078 baseEnd_1337078 := by
    simpa [prefixWord, tailWord_1337078, baseEnd_1337078] using wordTrace_append hprefix tailTrace_1337078
  have hstable : (prefixWord ++ tailWord_1337078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337078).length < 2 ^ (prefixWord ++ tailWord_1337078).sum := by decide
  have hdescent : baseEnd_1337078 < baseStart_1337078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337095 : List Nat := [1, 1, 4, 4, 2, 1, 3, 1, 4]
def baseStart_1337095 : Nat := 118140960795 + 1337095 * 2 ^ 59
def prefixEnd_1337095 : Nat := 4983230072969 + 3 ^ 40 * 1337095 * 2
def baseEnd_1337095 : Nat := 305143295877133930383697

theorem tailTrace_1337095 : CollatzResearch.WordTrace tailWord_1337095 prefixEnd_1337095 305143295877133930383697 := by
  unfold tailWord_1337095
  simp only [CollatzResearch.WordTrace]
  refine ⟨48767861090940647490628739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32511907393960431660419159 48767861090940647490628739)
  ·
    refine ⟨73151791636410971235943109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48767861090940647490628739 73151791636410971235943109)
    ·
      refine ⟨13715960931827057106739333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73151791636410971235943109 13715960931827057106739333)
      ·
        refine ⟨2571742674717573207513625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13715960931827057106739333 2571742674717573207513625)
        ·
          refine ⟨1928807006038179905635219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2571742674717573207513625 1928807006038179905635219)
          ·
            refine ⟨2893210509057269858452829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928807006038179905635219 2893210509057269858452829)
            ·
              refine ⟨1084953940896476196919811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893210509057269858452829 1084953940896476196919811)
              ·
                refine ⟨1627430911344714295379717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084953940896476196919811 1627430911344714295379717)
                ·
                  refine ⟨305143295877133930383697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627430911344714295379717 305143295877133930383697)
                  ·
                    rfl

theorem cell21_1337095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 1, 4].length) (baseStart_1337095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337095 prefixEnd_1337095 := by exact prefixLift 1337095
  have htrace : WordTrace (prefixWord ++ tailWord_1337095) baseStart_1337095 baseEnd_1337095 := by
    simpa [prefixWord, tailWord_1337095, baseEnd_1337095] using wordTrace_append hprefix tailTrace_1337095
  have hstable : (prefixWord ++ tailWord_1337095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337095).length < 2 ^ (prefixWord ++ tailWord_1337095).sum := by decide
  have hdescent : baseEnd_1337095 < baseStart_1337095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337101 : List Nat := [1, 7, 2, 1, 2, 1, 2, 5]
def baseStart_1337101 : Nat := 118140960795 + 1337101 * 2 ^ 59
def prefixEnd_1337101 : Nat := 4983230072969 + 3 ^ 40 * 1337101 * 2
def baseEnd_1337101 : Nat := 101714888386293084427895

theorem tailTrace_1337101 : CollatzResearch.WordTrace tailWord_1337101 prefixEnd_1337101 101714888386293084427895 := by
  unfold tailWord_1337101
  simp only [CollatzResearch.WordTrace]
  refine ⟨48768079928918910515347157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32512053285945940343564771 48768079928918910515347157)
  ·
    refine ⟨1143001873334036965203449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 48768079928918910515347157 1143001873334036965203449)
    ·
      refine ⟨857251405000527723902587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1143001873334036965203449 857251405000527723902587)
      ·
        refine ⟨1285877107500791585853881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857251405000527723902587 1285877107500791585853881)
        ·
          refine ⟨964407830625593689390411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1285877107500791585853881 964407830625593689390411)
          ·
            refine ⟨1446611745938390534085617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964407830625593689390411 1446611745938390534085617)
            ·
              refine ⟨1084958809453792900564213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446611745938390534085617 1084958809453792900564213)
              ·
                refine ⟨101714888386293084427895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1084958809453792900564213 101714888386293084427895)
                ·
                  rfl

theorem cell21_1337101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 5].length) (baseStart_1337101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337101 prefixEnd_1337101 := by exact prefixLift 1337101
  have htrace : WordTrace (prefixWord ++ tailWord_1337101) baseStart_1337101 baseEnd_1337101 := by
    simpa [prefixWord, tailWord_1337101, baseEnd_1337101] using wordTrace_append hprefix tailTrace_1337101
  have hstable : (prefixWord ++ tailWord_1337101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337101).length < 2 ^ (prefixWord ++ tailWord_1337101).sum := by decide
  have hdescent : baseEnd_1337101 < baseStart_1337101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337120 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_1337120 : Nat := 118140960795 + 1337120 * 2 ^ 59
def prefixEnd_1337120 : Nat := 4983230072969 + 3 ^ 40 * 1337120 * 2
def baseEnd_1337120 : Nat := 305149001217739442466979

theorem tailTrace_1337120 : CollatzResearch.WordTrace tailWord_1337120 prefixEnd_1337120 305149001217739442466979 := by
  unfold tailWord_1337120
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384386457925038380144407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32512515277233384506859209 24384386457925038380144407)
  ·
    refine ⟨36576579686887557570216611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24384386457925038380144407 36576579686887557570216611)
    ·
      refine ⟨54864869530331336355324917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36576579686887557570216611 54864869530331336355324917)
      ·
        refine ⟨5143581518468562783311711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54864869530331336355324917 5143581518468562783311711)
        ·
          refine ⟨7715372277702844174967567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143581518468562783311711 7715372277702844174967567)
          ·
            refine ⟨11573058416554266262451351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715372277702844174967567 11573058416554266262451351)
            ·
              refine ⟨17359587624831399393677027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11573058416554266262451351 17359587624831399393677027)
              ·
                refine ⟨26039381437247099090515541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17359587624831399393677027 26039381437247099090515541)
                ·
                  refine ⟨305149001217739442466979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26039381437247099090515541 305149001217739442466979)
                  ·
                    rfl

theorem cell21_1337120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_1337120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337120 prefixEnd_1337120 := by exact prefixLift 1337120
  have htrace : WordTrace (prefixWord ++ tailWord_1337120) baseStart_1337120 baseEnd_1337120 := by
    simpa [prefixWord, tailWord_1337120, baseEnd_1337120] using wordTrace_append hprefix tailTrace_1337120
  have hstable : (prefixWord ++ tailWord_1337120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337120).length < 2 ^ (prefixWord ++ tailWord_1337120).sum := by decide
  have hdescent : baseEnd_1337120 < baseStart_1337120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337123 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 3]
def baseStart_1337123 : Nat := 118140960795 + 1337123 * 2 ^ 59
def prefixEnd_1337123 : Nat := 4983230072969 + 3 ^ 40 * 1337123 * 2
def baseEnd_1337123 : Nat := 305149685858612103916973

theorem tailTrace_1337123 : CollatzResearch.WordTrace tailWord_1337123 prefixEnd_1337123 305149685858612103916973 := by
  unfold tailWord_1337123
  simp only [CollatzResearch.WordTrace]
  refine ⟨48768882334839208272648023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32512588223226138848432015 48768882334839208272648023)
  ·
    refine ⟨73153323502258812408972035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48768882334839208272648023 73153323502258812408972035)
    ·
      refine ⟨109729985253388218613458053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73153323502258812408972035 109729985253388218613458053)
      ·
        refine ⟨20574372235010290990023385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109729985253388218613458053 20574372235010290990023385)
        ·
          refine ⟨15430779176257718242517539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20574372235010290990023385 15430779176257718242517539)
          ·
            refine ⟨23146168764386577363776309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430779176257718242517539 23146168764386577363776309)
            ·
              refine ⟨2169953321661241627854029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23146168764386577363776309 2169953321661241627854029)
              ·
                refine ⟨813732495622965610445261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2169953321661241627854029 813732495622965610445261)
                ·
                  refine ⟨305149685858612103916973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813732495622965610445261 305149685858612103916973)
                  ·
                    rfl

theorem cell21_1337123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 3].length) (baseStart_1337123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337123 prefixEnd_1337123 := by exact prefixLift 1337123
  have htrace : WordTrace (prefixWord ++ tailWord_1337123) baseStart_1337123 baseEnd_1337123 := by
    simpa [prefixWord, tailWord_1337123, baseEnd_1337123] using wordTrace_append hprefix tailTrace_1337123
  have hstable : (prefixWord ++ tailWord_1337123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337123).length < 2 ^ (prefixWord ++ tailWord_1337123).sum := by decide
  have hdescent : baseEnd_1337123 < baseStart_1337123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337140 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_1337140 : Nat := 118140960795 + 1337140 * 2 ^ 59
def prefixEnd_1337140 : Nat := 4983230072969 + 3 ^ 40 * 1337140 * 2
def baseEnd_1337140 : Nat := 305153565490223852133605

theorem tailTrace_1337140 : CollatzResearch.WordTrace tailWord_1337140 prefixEnd_1337140 305153565490223852133605 := by
  unfold tailWord_1337140
  simp only [CollatzResearch.WordTrace]
  refine ⟨24384751187888810088008437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32513001583851746784011249 24384751187888810088008437)
  ·
    refine ⟨2286070423864575945750791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24384751187888810088008437 2286070423864575945750791)
    ·
      refine ⟨3429105635796863918626187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286070423864575945750791 3429105635796863918626187)
      ·
        refine ⟨5143658453695295877939281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429105635796863918626187 5143658453695295877939281)
        ·
          refine ⟨3857743840271471908454461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5143658453695295877939281 3857743840271471908454461)
          ·
            refine ⟨1446653940101801965670423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3857743840271471908454461 1446653940101801965670423)
            ·
              refine ⟨2169980910152702948505635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446653940101801965670423 2169980910152702948505635)
              ·
                refine ⟨3254971365229054422758453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2169980910152702948505635 3254971365229054422758453)
                ·
                  refine ⟨305153565490223852133605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3254971365229054422758453 305153565490223852133605)
                  ·
                    rfl

theorem cell21_1337140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_1337140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337140 prefixEnd_1337140 := by exact prefixLift 1337140
  have htrace : WordTrace (prefixWord ++ tailWord_1337140) baseStart_1337140 baseEnd_1337140 := by
    simpa [prefixWord, tailWord_1337140, baseEnd_1337140] using wordTrace_append hprefix tailTrace_1337140
  have hstable : (prefixWord ++ tailWord_1337140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337140).length < 2 ^ (prefixWord ++ tailWord_1337140).sum := by decide
  have hdescent : baseEnd_1337140 < baseStart_1337140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337247 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 4]
def baseStart_1337247 : Nat := 118140960795 + 1337247 * 2 ^ 59
def prefixEnd_1337247 : Nat := 4983230072969 + 3 ^ 40 * 1337247 * 2
def baseEnd_1337247 : Nat := 305177984348015443850053

theorem tailTrace_1337247 : CollatzResearch.WordTrace tailWord_1337247 prefixEnd_1337247 305177984348015443850053 := by
  unfold tailWord_1337247
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773404986389977450161995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32515603324259984966774663 48773404986389977450161995)
  ·
    refine ⟨73160107479584966175242993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48773404986389977450161995 73160107479584966175242993)
    ·
      refine ⟨54870080609688724631432245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73160107479584966175242993 54870080609688724631432245)
      ·
        refine ⟨5144070057158317934196773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54870080609688724631432245 5144070057158317934196773)
        ·
          refine ⟨964513135717184612661895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5144070057158317934196773 964513135717184612661895)
          ·
            refine ⟨1446769703575776918992843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964513135717184612661895 1446769703575776918992843)
            ·
              refine ⟨2170154555363665378489265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446769703575776918992843 2170154555363665378489265)
              ·
                refine ⟨1627615916522749033866949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170154555363665378489265 1627615916522749033866949)
                ·
                  refine ⟨305177984348015443850053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627615916522749033866949 305177984348015443850053)
                  ·
                    rfl

theorem cell21_1337247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4].length) (baseStart_1337247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337247 prefixEnd_1337247 := by exact prefixLift 1337247
  have htrace : WordTrace (prefixWord ++ tailWord_1337247) baseStart_1337247 baseEnd_1337247 := by
    simpa [prefixWord, tailWord_1337247, baseEnd_1337247] using wordTrace_append hprefix tailTrace_1337247
  have hstable : (prefixWord ++ tailWord_1337247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337247).length < 2 ^ (prefixWord ++ tailWord_1337247).sum := by decide
  have hdescent : baseEnd_1337247 < baseStart_1337247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337292 : List Nat := [2, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_1337292 : Nat := 118140960795 + 1337292 * 2 ^ 59
def prefixEnd_1337292 : Nat := 4983230072969 + 3 ^ 40 * 1337292 * 2
def baseEnd_1337292 : Nat := 305188253961105365599961

theorem tailTrace_1337292 : CollatzResearch.WordTrace tailWord_1337292 prefixEnd_1337292 305188253961105365599961 := by
  unfold tailWord_1337292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24387523135613475067775065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32516697514151300090366753 24387523135613475067775065)
  ·
    refine ⟨18290642351710106300831299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24387523135613475067775065 18290642351710106300831299)
    ·
      refine ⟨27435963527565159451246949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18290642351710106300831299 27435963527565159451246949)
      ·
        refine ⟨5144243161418467397108803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27435963527565159451246949 5144243161418467397108803)
        ·
          refine ⟨7716364742127701095663205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144243161418467397108803 7716364742127701095663205)
          ·
            refine ⟨1446818389148943955436851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7716364742127701095663205 1446818389148943955436851)
            ·
              refine ⟨2170227583723415933155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446818389148943955436851 2170227583723415933155277)
              ·
                refine ⟨813835343896280974933229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170227583723415933155277 813835343896280974933229)
                ·
                  refine ⟨305188253961105365599961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813835343896280974933229 305188253961105365599961)
                  ·
                    rfl

theorem cell21_1337292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_1337292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337292 prefixEnd_1337292 := by exact prefixLift 1337292
  have htrace : WordTrace (prefixWord ++ tailWord_1337292) baseStart_1337292 baseEnd_1337292 := by
    simpa [prefixWord, tailWord_1337292, baseEnd_1337292] using wordTrace_append hprefix tailTrace_1337292
  have hstable : (prefixWord ++ tailWord_1337292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337292).length < 2 ^ (prefixWord ++ tailWord_1337292).sum := by decide
  have hdescent : baseEnd_1337292 < baseStart_1337292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337309 : List Nat := [1, 4, 3, 1, 3, 1, 3, 2, 3]
def baseStart_1337309 : Nat := 118140960795 + 1337309 * 2 ^ 59
def prefixEnd_1337309 : Nat := 4983230072969 + 3 ^ 40 * 1337309 * 2
def baseEnd_1337309 : Nat := 305192133592717113816593

theorem tailTrace_1337309 : CollatzResearch.WordTrace tailWord_1337309 prefixEnd_1337309 305192133592717113816593 := by
  unfold tailWord_1337309
  simp only [CollatzResearch.WordTrace]
  refine ⟨48775666312165362038918981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32517110874776908025945987 48775666312165362038918981)
  ·
    refine ⟨9145437433531005382297309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48775666312165362038918981 9145437433531005382297309)
    ·
      refine ⟨3429539037574127018361491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9145437433531005382297309 3429539037574127018361491)
      ·
        refine ⟨5144308556361190527542237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429539037574127018361491 5144308556361190527542237)
        ·
          refine ⟨1929115708635446447828339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5144308556361190527542237 1929115708635446447828339)
          ·
            refine ⟨2893673562953169671742509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929115708635446447828339 2893673562953169671742509)
            ·
              refine ⟨1085127586107438626903441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893673562953169671742509 1085127586107438626903441)
              ·
                refine ⟨813845689580578970177581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085127586107438626903441 813845689580578970177581)
                ·
                  refine ⟨305192133592717113816593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 813845689580578970177581 305192133592717113816593)
                  ·
                    rfl

theorem cell21_1337309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_1337309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337309 prefixEnd_1337309 := by exact prefixLift 1337309
  have htrace : WordTrace (prefixWord ++ tailWord_1337309) baseStart_1337309 baseEnd_1337309 := by
    simpa [prefixWord, tailWord_1337309, baseEnd_1337309] using wordTrace_append hprefix tailTrace_1337309
  have hstable : (prefixWord ++ tailWord_1337309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337309).length < 2 ^ (prefixWord ++ tailWord_1337309).sum := by decide
  have hdescent : baseEnd_1337309 < baseStart_1337309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337393 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 7]
def baseStart_1337393 : Nat := 118140960795 + 1337393 * 2 ^ 59
def prefixEnd_1337393 : Nat := 4983230072969 + 3 ^ 40 * 1337393 * 2
def baseEnd_1337393 : Nat := 305211303537151634416421

theorem tailTrace_1337393 : CollatzResearch.WordTrace tailWord_1337393 prefixEnd_1337393 305211303537151634416421 := by
  unfold tailWord_1337393
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778730043861044384976833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32519153362574029589984555 48778730043861044384976833)
  ·
    refine ⟨36584047532895783288732625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48778730043861044384976833 36584047532895783288732625)
    ·
      refine ⟨27438035649671837466549469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36584047532895783288732625 27438035649671837466549469)
      ·
        refine ⟨10289263368626939049956051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27438035649671837466549469 10289263368626939049956051)
        ·
          refine ⟨15433895052940408574934077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10289263368626939049956051 15433895052940408574934077)
          ·
            refine ⟨5787710644852653215600279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15433895052940408574934077 5787710644852653215600279)
            ·
              refine ⟨8681565967278979823400419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787710644852653215600279 8681565967278979823400419)
              ·
                refine ⟨13022348950918469735100629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681565967278979823400419 13022348950918469735100629)
                ·
                  refine ⟨305211303537151634416421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13022348950918469735100629 305211303537151634416421)
                  ·
                    rfl

theorem cell21_1337393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_1337393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337393 prefixEnd_1337393 := by exact prefixLift 1337393
  have htrace : WordTrace (prefixWord ++ tailWord_1337393) baseStart_1337393 baseEnd_1337393 := by
    simpa [prefixWord, tailWord_1337393, baseEnd_1337393] using wordTrace_append hprefix tailTrace_1337393
  have hstable : (prefixWord ++ tailWord_1337393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337393).length < 2 ^ (prefixWord ++ tailWord_1337393).sum := by decide
  have hdescent : baseEnd_1337393 < baseStart_1337393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337455 : List Nat := [1, 1, 2, 1, 3, 4, 4, 5]
def baseStart_1337455 : Nat := 118140960795 + 1337455 * 2 ^ 59
def prefixEnd_1337455 : Nat := 4983230072969 + 3 ^ 40 * 1337455 * 2
def baseEnd_1337455 : Nat := 101741817593951101460987

theorem tailTrace_1337455 : CollatzResearch.WordTrace tailWord_1337455 prefixEnd_1337455 101741817593951101460987 := by
  unfold tailWord_1337455
  simp only [CollatzResearch.WordTrace]
  refine ⟨48780991369636428973733819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32520660913090952649155879 48780991369636428973733819)
  ·
    refine ⟨73171487054454643460600729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48780991369636428973733819 73171487054454643460600729)
    ·
      refine ⟨54878615290840982595450547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73171487054454643460600729 54878615290840982595450547)
      ·
        refine ⟨82317922936261473893175821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54878615290840982595450547 82317922936261473893175821)
        ·
          refine ⟨30869221101098052709940933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82317922936261473893175821 30869221101098052709940933)
          ·
            refine ⟨5787978956455884883113925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30869221101098052709940933 5787978956455884883113925)
            ·
              refine ⟨1085246054335478415583861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5787978956455884883113925 1085246054335478415583861)
              ·
                refine ⟨101741817593951101460987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1085246054335478415583861 101741817593951101460987)
                ·
                  rfl

theorem cell21_1337455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 5].length) (baseStart_1337455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337455 prefixEnd_1337455 := by exact prefixLift 1337455
  have htrace : WordTrace (prefixWord ++ tailWord_1337455) baseStart_1337455 baseEnd_1337455 := by
    simpa [prefixWord, tailWord_1337455, baseEnd_1337455] using wordTrace_append hprefix tailTrace_1337455
  have hstable : (prefixWord ++ tailWord_1337455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337455).length < 2 ^ (prefixWord ++ tailWord_1337455).sum := by decide
  have hdescent : baseEnd_1337455 < baseStart_1337455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337492 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_1337492 : Nat := 118140960795 + 1337492 * 2 ^ 59
def prefixEnd_1337492 : Nat := 4983230072969 + 3 ^ 40 * 1337492 * 2
def baseEnd_1337492 : Nat := 305233896685949462266219

theorem tailTrace_1337492 : CollatzResearch.WordTrace tailWord_1337492 prefixEnd_1337492 305233896685949462266219 := by
  unfold tailWord_1337492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24391170435251192146415365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32521560580334922861887153 24391170435251192146415365)
  ·
    refine ⟨4573344456609598527452881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24391170435251192146415365 4573344456609598527452881)
    ·
      refine ⟨3430008342457198895589661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4573344456609598527452881 3430008342457198895589661)
      ·
        refine ⟨1286253128421449585846123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3430008342457198895589661 1286253128421449585846123)
        ·
          refine ⟨1929379692632174378769185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286253128421449585846123 1929379692632174378769185)
          ·
            refine ⟨1447034769474130784076889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1929379692632174378769185 1447034769474130784076889)
            ·
              refine ⟨1085276077105598088057667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447034769474130784076889 1085276077105598088057667)
              ·
                refine ⟨1627914115658397132086501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085276077105598088057667 1627914115658397132086501)
                ·
                  refine ⟨305233896685949462266219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627914115658397132086501 305233896685949462266219)
                  ·
                    rfl

theorem cell21_1337492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_1337492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337492 prefixEnd_1337492 := by exact prefixLift 1337492
  have htrace : WordTrace (prefixWord ++ tailWord_1337492) baseStart_1337492 baseEnd_1337492 := by
    simpa [prefixWord, tailWord_1337492, baseEnd_1337492] using wordTrace_append hprefix tailTrace_1337492
  have hstable : (prefixWord ++ tailWord_1337492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337492).length < 2 ^ (prefixWord ++ tailWord_1337492).sum := by decide
  have hdescent : baseEnd_1337492 < baseStart_1337492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337534 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_1337534 : Nat := 118140960795 + 1337534 * 2 ^ 59
def prefixEnd_1337534 : Nat := 4983230072969 + 3 ^ 40 * 1337534 * 2
def baseEnd_1337534 : Nat := 305243481658166722566133

theorem tailTrace_1337534 : CollatzResearch.WordTrace tailWord_1337534 prefixEnd_1337534 305243481658166722566133 := by
  unfold tailWord_1337534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097984092043778183232457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32522581824233483643906437 6097984092043778183232457)
  ·
    refine ⟨4573488069032833637424343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6097984092043778183232457 4573488069032833637424343)
    ·
      refine ⟨6860232103549250456136515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573488069032833637424343 6860232103549250456136515)
      ·
        refine ⟨10290348155323875684204773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860232103549250456136515 10290348155323875684204773)
        ·
          refine ⟨1929440279123226690788395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10290348155323875684204773 1929440279123226690788395)
          ·
            refine ⟨2894160418684840036182593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929440279123226690788395 2894160418684840036182593)
            ·
              refine ⟨2170620314013630027136945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894160418684840036182593 2170620314013630027136945)
              ·
                refine ⟨1627965235510222520352709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2170620314013630027136945 1627965235510222520352709)
                ·
                  refine ⟨305243481658166722566133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1627965235510222520352709 305243481658166722566133)
                  ·
                    rfl

theorem cell21_1337534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_1337534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337534 prefixEnd_1337534 := by exact prefixLift 1337534
  have htrace : WordTrace (prefixWord ++ tailWord_1337534) baseStart_1337534 baseEnd_1337534 := by
    simpa [prefixWord, tailWord_1337534, baseEnd_1337534] using wordTrace_append hprefix tailTrace_1337534
  have hstable : (prefixWord ++ tailWord_1337534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337534).length < 2 ^ (prefixWord ++ tailWord_1337534).sum := by decide
  have hdescent : baseEnd_1337534 < baseStart_1337534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337559 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_1337559 : Nat := 118140960795 + 1337559 * 2 ^ 59
def prefixEnd_1337559 : Nat := 4983230072969 + 3 ^ 40 * 1337559 * 2
def baseEnd_1337559 : Nat := 305249186998772234649415

theorem tailTrace_1337559 : CollatzResearch.WordTrace tailWord_1337559 prefixEnd_1337559 305249186998772234649415 := by
  unfold tailWord_1337559
  simp only [CollatzResearch.WordTrace]
  refine ⟨48784784561259654735519731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32523189707506436490346487 48784784561259654735519731)
  ·
    refine ⟨73177176841889482103279597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48784784561259654735519731 73177176841889482103279597)
    ·
      refine ⟨27441441315708555788729849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73177176841889482103279597 27441441315708555788729849)
      ·
        refine ⟨20581080986781416841547387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27441441315708555788729849 20581080986781416841547387)
        ·
          refine ⟨30871621480172125262321081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20581080986781416841547387 30871621480172125262321081)
          ·
            refine ⟨23153716110129093946740811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30871621480172125262321081 23153716110129093946740811)
            ·
              refine ⟨34730574165193640920111217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23153716110129093946740811 34730574165193640920111217)
              ·
                refine ⟨26047930623895230690083413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34730574165193640920111217 26047930623895230690083413)
                ·
                  refine ⟨305249186998772234649415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26047930623895230690083413 305249186998772234649415)
                  ·
                    rfl

theorem cell21_1337559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_1337559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337559 prefixEnd_1337559 := by exact prefixLift 1337559
  have htrace : WordTrace (prefixWord ++ tailWord_1337559) baseStart_1337559 baseEnd_1337559 := by
    simpa [prefixWord, tailWord_1337559, baseEnd_1337559] using wordTrace_append hprefix tailTrace_1337559
  have hstable : (prefixWord ++ tailWord_1337559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337559).length < 2 ^ (prefixWord ++ tailWord_1337559).sum := by decide
  have hdescent : baseEnd_1337559 < baseStart_1337559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337621 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1337621 : Nat := 118140960795 + 1337621 * 2 ^ 59
def prefixEnd_1337621 : Nat := 4983230072969 + 3 ^ 40 * 1337621 * 2
def baseEnd_1337621 : Nat := 305263336243473904615955

theorem tailTrace_1337621 : CollatzResearch.WordTrace tailWord_1337621 prefixEnd_1337621 305263336243473904615955 := by
  unfold tailWord_1337621
  simp only [CollatzResearch.WordTrace]
  refine ⟨48787045887035039324276717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32524697258023359549517811 48787045887035039324276717)
  ·
    refine ⟨18295142207638139746603769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48787045887035039324276717 18295142207638139746603769)
    ·
      refine ⟨13721356655728604809952827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18295142207638139746603769 13721356655728604809952827)
      ·
        refine ⟨20582034983592907214929241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13721356655728604809952827 20582034983592907214929241)
        ·
          refine ⟨15436526237694680411196931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20582034983592907214929241 15436526237694680411196931)
          ·
            refine ⟨23154789356542020616795397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15436526237694680411196931 23154789356542020616795397)
            ·
              refine ⟨4341523004351628865649137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23154789356542020616795397 4341523004351628865649137)
              ·
                refine ⟨3256142253263721649236853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4341523004351628865649137 3256142253263721649236853)
                ·
                  refine ⟨305263336243473904615955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3256142253263721649236853 305263336243473904615955)
                  ·
                    rfl

theorem cell21_1337621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1337621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337621 prefixEnd_1337621 := by exact prefixLift 1337621
  have htrace : WordTrace (prefixWord ++ tailWord_1337621) baseStart_1337621 baseEnd_1337621 := by
    simpa [prefixWord, tailWord_1337621, baseEnd_1337621] using wordTrace_append hprefix tailTrace_1337621
  have hstable : (prefixWord ++ tailWord_1337621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337621).length < 2 ^ (prefixWord ++ tailWord_1337621).sum := by decide
  have hdescent : baseEnd_1337621 < baseStart_1337621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337635 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 8]
def baseStart_1337635 : Nat := 118140960795 + 1337635 * 2 ^ 59
def prefixEnd_1337635 : Nat := 4983230072969 + 3 ^ 40 * 1337635 * 2
def baseEnd_1337635 : Nat := 305266531234212991382593

theorem tailTrace_1337635 : CollatzResearch.WordTrace tailWord_1337635 prefixEnd_1337635 305266531234212991382593 := by
  unfold tailWord_1337635
  simp only [CollatzResearch.WordTrace]
  refine ⟨48787556508984319715286359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32525037672656213143524239 48787556508984319715286359)
  ·
    refine ⟨73181334763476479572929539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48787556508984319715286359 73181334763476479572929539)
    ·
      refine ⟨109772002145214719359394309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73181334763476479572929539 109772002145214719359394309)
      ·
        refine ⟨20582250402227759879886433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109772002145214719359394309 20582250402227759879886433)
        ·
          refine ⟨15436687801670819909914825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20582250402227759879886433 15436687801670819909914825)
          ·
            refine ⟨11577515851253114932436119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15436687801670819909914825 11577515851253114932436119)
            ·
              refine ⟨17366273776879672398654179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577515851253114932436119 17366273776879672398654179)
              ·
                refine ⟨26049410665319508597981269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17366273776879672398654179 26049410665319508597981269)
                ·
                  refine ⟨305266531234212991382593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26049410665319508597981269 305266531234212991382593)
                  ·
                    rfl

theorem cell21_1337635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 8].length) (baseStart_1337635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337635 prefixEnd_1337635 := by exact prefixLift 1337635
  have htrace : WordTrace (prefixWord ++ tailWord_1337635) baseStart_1337635 baseEnd_1337635 := by
    simpa [prefixWord, tailWord_1337635, baseEnd_1337635] using wordTrace_append hprefix tailTrace_1337635
  have hstable : (prefixWord ++ tailWord_1337635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337635).length < 2 ^ (prefixWord ++ tailWord_1337635).sum := by decide
  have hdescent : baseEnd_1337635 < baseStart_1337635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337748 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 3]
def baseStart_1337748 : Nat := 118140960795 + 1337748 * 2 ^ 59
def prefixEnd_1337748 : Nat := 4983230072969 + 3 ^ 40 * 1337748 * 2
def baseEnd_1337748 : Nat := 305292319373749905999029

theorem tailTrace_1337748 : CollatzResearch.WordTrace tailWord_1337748 prefixEnd_1337748 305292319373749905999029 := by
  unfold tailWord_1337748
  simp only [CollatzResearch.WordTrace]
  refine ⟨24395838978787470007074949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32527785305049960009433265 24395838978787470007074949)
  ·
    refine ⟨4574219808522650626326553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24395838978787470007074949 4574219808522650626326553)
    ·
      refine ⟨3430664856391987969744915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4574219808522650626326553 3430664856391987969744915)
      ·
        refine ⟨5145997284587981954617373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430664856391987969744915 5145997284587981954617373)
        ·
          refine ⟨1929748981720493232981515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5145997284587981954617373 1929748981720493232981515)
          ·
            refine ⟨2894623472580739849472273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929748981720493232981515 2894623472580739849472273)
            ·
              refine ⟨2170967604435554887104205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894623472580739849472273 2170967604435554887104205)
              ·
                refine ⟨814112851663333082664077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170967604435554887104205 814112851663333082664077)
                ·
                  refine ⟨305292319373749905999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814112851663333082664077 305292319373749905999029)
                  ·
                    rfl

theorem cell21_1337748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_1337748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337748 prefixEnd_1337748 := by exact prefixLift 1337748
  have htrace : WordTrace (prefixWord ++ tailWord_1337748) baseStart_1337748 baseEnd_1337748 := by
    simpa [prefixWord, tailWord_1337748, baseEnd_1337748] using wordTrace_append hprefix tailTrace_1337748
  have hstable : (prefixWord ++ tailWord_1337748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337748).length < 2 ^ (prefixWord ++ tailWord_1337748).sum := by decide
  have hdescent : baseEnd_1337748 < baseStart_1337748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337793 : List Nat := [1, 2, 7, 1, 1, 1, 1, 7]
def baseStart_1337793 : Nat := 118140960795 + 1337793 * 2 ^ 59
def prefixEnd_1337793 : Nat := 4983230072969 + 3 ^ 40 * 1337793 * 2
def baseEnd_1337793 : Nat := 101767529662279942582979

theorem tailTrace_1337793 : CollatzResearch.WordTrace tailWord_1337793 prefixEnd_1337793 101767529662279942582979 := by
  unfold tailWord_1337793
  simp only [CollatzResearch.WordTrace]
  refine ⟨48793319242411912699538033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32528879494941275133025355 48793319242411912699538033)
  ·
    refine ⟨36594989431808934524653525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48793319242411912699538033 36594989431808934524653525)
    ·
      refine ⟨857695064808021902921567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 36594989431808934524653525 857695064808021902921567)
      ·
        refine ⟨1286542597212032854382351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857695064808021902921567 1286542597212032854382351)
        ·
          refine ⟨1929813895818049281573527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286542597212032854382351 1929813895818049281573527)
          ·
            refine ⟨2894720843727073922360291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929813895818049281573527 2894720843727073922360291)
            ·
              refine ⟨4342081265590610883540437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2894720843727073922360291 4342081265590610883540437)
              ·
                refine ⟨101767529662279942582979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4342081265590610883540437 101767529662279942582979)
                ·
                  rfl

theorem cell21_1337793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 7].length) (baseStart_1337793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337793 prefixEnd_1337793 := by exact prefixLift 1337793
  have htrace : WordTrace (prefixWord ++ tailWord_1337793) baseStart_1337793 baseEnd_1337793 := by
    simpa [prefixWord, tailWord_1337793, baseEnd_1337793] using wordTrace_append hprefix tailTrace_1337793
  have hstable : (prefixWord ++ tailWord_1337793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337793).length < 2 ^ (prefixWord ++ tailWord_1337793).sum := by decide
  have hdescent : baseEnd_1337793 < baseStart_1337793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337838 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1337838 : Nat := 118140960795 + 1337838 * 2 ^ 59
def prefixEnd_1337838 : Nat := 4983230072969 + 3 ^ 40 * 1337838 * 2
def baseEnd_1337838 : Nat := 305312858599929749498845

theorem tailTrace_1337838 : CollatzResearch.WordTrace tailWord_1337838 prefixEnd_1337838 305312858599929749498845 := by
  unfold tailWord_1337838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099370065906110673115771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32529973684832590256617445 6099370065906110673115771)
  ·
    refine ⟨9149055098859166009673657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6099370065906110673115771 9149055098859166009673657)
    ·
      refine ⟨6861791324144374507255243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9149055098859166009673657 6861791324144374507255243)
      ·
        refine ⟨10292686986216561760882865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6861791324144374507255243 10292686986216561760882865)
        ·
          refine ⟨7719515239662421320662149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10292686986216561760882865 7719515239662421320662149)
          ·
            refine ⟨1447409107436703997624153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7719515239662421320662149 1447409107436703997624153)
            ·
              refine ⟨1085556830577527998218115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447409107436703997624153 1085556830577527998218115)
              ·
                refine ⟨1628335245866291997327173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085556830577527998218115 1628335245866291997327173)
                ·
                  refine ⟨305312858599929749498845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628335245866291997327173 305312858599929749498845)
                  ·
                    rfl

theorem cell21_1337838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1337838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337838 prefixEnd_1337838 := by exact prefixLift 1337838
  have htrace : WordTrace (prefixWord ++ tailWord_1337838) baseStart_1337838 baseEnd_1337838 := by
    simpa [prefixWord, tailWord_1337838, baseEnd_1337838] using wordTrace_append hprefix tailTrace_1337838
  have hstable : (prefixWord ++ tailWord_1337838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337838).length < 2 ^ (prefixWord ++ tailWord_1337838).sum := by decide
  have hdescent : baseEnd_1337838 < baseStart_1337838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337866 : List Nat := [3, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_1337866 : Nat := 118140960795 + 1337866 * 2 ^ 59
def prefixEnd_1337866 : Nat := 4983230072969 + 3 ^ 40 * 1337866 * 2
def baseEnd_1337866 : Nat := 305319248581407923032121

theorem tailTrace_1337866 : CollatzResearch.WordTrace tailWord_1337866 prefixEnd_1337866 305319248581407923032121 := by
  unfold tailWord_1337866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12198995442786861541736363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32530654514098297444630301 12198995442786861541736363)
  ·
    refine ⟨18298493164180292312604545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12198995442786861541736363 18298493164180292312604545)
    ·
      refine ⟨13723869873135219234453409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18298493164180292312604545 13723869873135219234453409)
      ·
        refine ⟨10292902404851414425840057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13723869873135219234453409 10292902404851414425840057)
        ·
          refine ⟨7719676803638560819380043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10292902404851414425840057 7719676803638560819380043)
          ·
            refine ⟨11579515205457841229070065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7719676803638560819380043 11579515205457841229070065)
            ·
              refine ⟨8684636404093380921802549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11579515205457841229070065 8684636404093380921802549)
              ·
                refine ⟨814184662883754461418989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8684636404093380921802549 814184662883754461418989)
                ·
                  refine ⟨305319248581407923032121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814184662883754461418989 305319248581407923032121)
                  ·
                    rfl

theorem cell21_1337866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_1337866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337866 prefixEnd_1337866 := by exact prefixLift 1337866
  have htrace : WordTrace (prefixWord ++ tailWord_1337866) baseStart_1337866 baseEnd_1337866 := by
    simpa [prefixWord, tailWord_1337866, baseEnd_1337866] using wordTrace_append hprefix tailTrace_1337866
  have hstable : (prefixWord ++ tailWord_1337866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337866).length < 2 ^ (prefixWord ++ tailWord_1337866).sum := by decide
  have hdescent : baseEnd_1337866 < baseStart_1337866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1337880 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 4]
def baseStart_1337880 : Nat := 118140960795 + 1337880 * 2 ^ 59
def prefixEnd_1337880 : Nat := 4983230072969 + 3 ^ 40 * 1337880 * 2
def baseEnd_1337880 : Nat := 305322443572147009798759

theorem tailTrace_1337880 : CollatzResearch.WordTrace tailWord_1337880 prefixEnd_1337880 305322443572147009798759 := by
  unfold tailWord_1337880
  simp only [CollatzResearch.WordTrace]
  refine ⟨24398246196548363278977547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32530994928731151038636729 24398246196548363278977547)
  ·
    refine ⟨36597369294822544918466321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24398246196548363278977547 36597369294822544918466321)
    ·
      refine ⟨27448026971116908688849741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36597369294822544918466321 27448026971116908688849741)
      ·
        refine ⟨10293010114168840758318653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27448026971116908688849741 10293010114168840758318653)
        ·
          refine ⟨3859878792813315284369495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10293010114168840758318653 3859878792813315284369495)
          ·
            refine ⟨5789818189219972926554243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3859878792813315284369495 5789818189219972926554243)
            ·
              refine ⟨8684727283829959389831365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5789818189219972926554243 8684727283829959389831365)
              ·
                refine ⟨1628386365718117385593381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8684727283829959389831365 1628386365718117385593381)
                ·
                  refine ⟨305322443572147009798759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628386365718117385593381 305322443572147009798759)
                  ·
                    rfl

theorem cell21_1337880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 4].length) (baseStart_1337880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1337880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1337880 prefixEnd_1337880 := by exact prefixLift 1337880
  have htrace : WordTrace (prefixWord ++ tailWord_1337880) baseStart_1337880 baseEnd_1337880 := by
    simpa [prefixWord, tailWord_1337880, baseEnd_1337880] using wordTrace_append hprefix tailTrace_1337880
  have hstable : (prefixWord ++ tailWord_1337880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1337880).length < 2 ^ (prefixWord ++ tailWord_1337880).sum := by decide
  have hdescent : baseEnd_1337880 < baseStart_1337880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1337880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338052 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 3]
def baseStart_1338052 : Nat := 118140960795 + 1338052 * 2 ^ 59
def prefixEnd_1338052 : Nat := 4983230072969 + 3 ^ 40 * 1338052 * 2
def baseEnd_1338052 : Nat := 305361696315512932931741

theorem tailTrace_1338052 : CollatzResearch.WordTrace tailWord_1338052 prefixEnd_1338052 305361696315512932931741 := by
  unfold tailWord_1338052
  simp only [CollatzResearch.WordTrace]
  refine ⟨24401382874236799966608205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32535177165649066622144273 24401382874236799966608205)
  ·
    refine ⟨9150518577838799987478077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24401382874236799966608205 9150518577838799987478077)
    ·
      refine ⟨3431444466689549995304279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9150518577838799987478077 3431444466689549995304279)
      ·
        refine ⟨5147166700034324992956419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431444466689549995304279 5147166700034324992956419)
        ·
          refine ⟨7720750050051487489434629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5147166700034324992956419 7720750050051487489434629)
          ·
            refine ⟨1447640634384653904268993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7720750050051487489434629 1447640634384653904268993)
            ·
              refine ⟨1085730475788490428201745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447640634384653904268993 1085730475788490428201745)
              ·
                refine ⟨814297856841367821151309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1085730475788490428201745 814297856841367821151309)
                ·
                  refine ⟨305361696315512932931741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814297856841367821151309 305361696315512932931741)
                  ·
                    rfl

theorem cell21_1338052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_1338052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338052 prefixEnd_1338052 := by exact prefixLift 1338052
  have htrace : WordTrace (prefixWord ++ tailWord_1338052) baseStart_1338052 baseEnd_1338052 := by
    simpa [prefixWord, tailWord_1338052, baseEnd_1338052] using wordTrace_append hprefix tailTrace_1338052
  have hstable : (prefixWord ++ tailWord_1338052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338052).length < 2 ^ (prefixWord ++ tailWord_1338052).sum := by decide
  have hdescent : baseEnd_1338052 < baseStart_1338052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338094 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 3]
def baseStart_1338094 : Nat := 118140960795 + 1338094 * 2 ^ 59
def prefixEnd_1338094 : Nat := 4983230072969 + 3 ^ 40 * 1338094 * 2
def baseEnd_1338094 : Nat := 305371281287730193231655

theorem tailTrace_1338094 : CollatzResearch.WordTrace tailWord_1338094 prefixEnd_1338094 305371281287730193231655 := by
  unfold tailWord_1338094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6100537201790180138280667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32536198409547627404163557 6100537201790180138280667)
  ·
    refine ⟨9150805802685270207421001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6100537201790180138280667 9150805802685270207421001)
    ·
      refine ⟨6863104352013952655565751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9150805802685270207421001 6863104352013952655565751)
      ·
        refine ⟨10294656528020928983348627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6863104352013952655565751 10294656528020928983348627)
        ·
          refine ⟨15441984792031393475022941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10294656528020928983348627 15441984792031393475022941)
          ·
            refine ⟨5790744297011772553133603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15441984792031393475022941 5790744297011772553133603)
            ·
              refine ⟨8686116445517658829700405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5790744297011772553133603 8686116445517658829700405)
              ·
                refine ⟨814323416767280515284413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8686116445517658829700405 814323416767280515284413)
                ·
                  refine ⟨305371281287730193231655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814323416767280515284413 305371281287730193231655)
                  ·
                    rfl

theorem cell21_1338094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_1338094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338094 prefixEnd_1338094 := by exact prefixLift 1338094
  have htrace : WordTrace (prefixWord ++ tailWord_1338094) baseStart_1338094 baseEnd_1338094 := by
    simpa [prefixWord, tailWord_1338094, baseEnd_1338094] using wordTrace_append hprefix tailTrace_1338094
  have hstable : (prefixWord ++ tailWord_1338094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338094).length < 2 ^ (prefixWord ++ tailWord_1338094).sum := by decide
  have hdescent : baseEnd_1338094 < baseStart_1338094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338100 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1338100 : Nat := 118140960795 + 1338100 * 2 ^ 59
def prefixEnd_1338100 : Nat := 4983230072969 + 3 ^ 40 * 1338100 * 2
def baseEnd_1338100 : Nat := 305372650569475516131643

theorem tailTrace_1338100 : CollatzResearch.WordTrace tailWord_1338100 prefixEnd_1338100 305372650569475516131643 := by
  unfold tailWord_1338100
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402258226149852065481877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32536344301533136087309169 24402258226149852065481877)
  ·
    refine ⟨1143855854350774315569463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24402258226149852065481877 1143855854350774315569463)
    ·
      refine ⟨1715783781526161473354195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143855854350774315569463 1715783781526161473354195)
      ·
        refine ⟨2573675672289242210031293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1715783781526161473354195 2573675672289242210031293)
        ·
          refine ⟨965128377108465828761735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2573675672289242210031293 965128377108465828761735)
          ·
            refine ⟨1447692565662698743142603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965128377108465828761735 1447692565662698743142603)
            ·
              refine ⟨2171538848494048114713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447692565662698743142603 2171538848494048114713905)
              ·
                refine ⟨1628654136370536086035429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171538848494048114713905 1628654136370536086035429)
                ·
                  refine ⟨305372650569475516131643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628654136370536086035429 305372650569475516131643)
                  ·
                    rfl

theorem cell21_1338100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1338100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338100 prefixEnd_1338100 := by exact prefixLift 1338100
  have htrace : WordTrace (prefixWord ++ tailWord_1338100) baseStart_1338100 baseEnd_1338100 := by
    simpa [prefixWord, tailWord_1338100, baseEnd_1338100] using wordTrace_append hprefix tailTrace_1338100
  have hstable : (prefixWord ++ tailWord_1338100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338100).length < 2 ^ (prefixWord ++ tailWord_1338100).sum := by decide
  have hdescent : baseEnd_1338100 < baseStart_1338100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338108 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 4]
def baseStart_1338108 : Nat := 118140960795 + 1338108 * 2 ^ 59
def prefixEnd_1338108 : Nat := 4983230072969 + 3 ^ 40 * 1338108 * 2
def baseEnd_1338108 : Nat := 305374476278469279998293

theorem tailTrace_1338108 : CollatzResearch.WordTrace tailWord_1338108 prefixEnd_1338108 305374476278469279998293 := by
  unfold tailWord_1338108
  simp only [CollatzResearch.WordTrace]
  refine ⟨24402404118135360748627489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32536538824180480998169985 24402404118135360748627489)
  ·
    refine ⟨18301803088601520561470617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24402404118135360748627489 18301803088601520561470617)
    ·
      refine ⟨13726352316451140421102963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18301803088601520561470617 13726352316451140421102963)
      ·
        refine ⟨20589528474676710631654445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13726352316451140421102963 20589528474676710631654445)
        ·
          refine ⟨7721073178003766486870417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20589528474676710631654445 7721073178003766486870417)
          ·
            refine ⟨5790804883502824865152813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7721073178003766486870417 5790804883502824865152813)
            ·
              refine ⟨2171551831313559324432305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5790804883502824865152813 2171551831313559324432305)
              ·
                refine ⟨1628663873485169493324229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2171551831313559324432305 1628663873485169493324229)
                ·
                  refine ⟨305374476278469279998293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628663873485169493324229 305374476278469279998293)
                  ·
                    rfl

theorem cell21_1338108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 4].length) (baseStart_1338108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338108 prefixEnd_1338108 := by exact prefixLift 1338108
  have htrace : WordTrace (prefixWord ++ tailWord_1338108) baseStart_1338108 baseEnd_1338108 := by
    simpa [prefixWord, tailWord_1338108, baseEnd_1338108] using wordTrace_append hprefix tailTrace_1338108
  have hstable : (prefixWord ++ tailWord_1338108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338108).length < 2 ^ (prefixWord ++ tailWord_1338108).sum := by decide
  have hdescent : baseEnd_1338108 < baseStart_1338108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338167 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 4]
def baseStart_1338167 : Nat := 118140960795 + 1338167 * 2 ^ 59
def prefixEnd_1338167 : Nat := 4983230072969 + 3 ^ 40 * 1338167 * 2
def baseEnd_1338167 : Nat := 305387940882298288514839

theorem tailTrace_1338167 : CollatzResearch.WordTrace tailWord_1338167 prefixEnd_1338167 305387940882298288514839 := by
  unfold tailWord_1338167
  simp only [CollatzResearch.WordTrace]
  refine ⟨48806960143056974573652755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32537973428704649715768503 48806960143056974573652755)
  ·
    refine ⟨73210440214585461860479133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48806960143056974573652755 73210440214585461860479133)
    ·
      refine ⟨27453915080469548197679675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73210440214585461860479133 27453915080469548197679675)
      ·
        refine ⟨41180872620704322296519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27453915080469548197679675 41180872620704322296519513)
        ·
          refine ⟨30885654465528241722389635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41180872620704322296519513 30885654465528241722389635)
          ·
            refine ⟨46328481698292362583584453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30885654465528241722389635 46328481698292362583584453)
            ·
              refine ⟨8686590318429817984422085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46328481698292362583584453 8686590318429817984422085)
              ·
                refine ⟨1628735684705590872079141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8686590318429817984422085 1628735684705590872079141)
                ·
                  refine ⟨305387940882298288514839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628735684705590872079141 305387940882298288514839)
                  ·
                    rfl

theorem cell21_1338167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 4].length) (baseStart_1338167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338167 prefixEnd_1338167 := by exact prefixLift 1338167
  have htrace : WordTrace (prefixWord ++ tailWord_1338167) baseStart_1338167 baseEnd_1338167 := by
    simpa [prefixWord, tailWord_1338167, baseEnd_1338167] using wordTrace_append hprefix tailTrace_1338167
  have hstable : (prefixWord ++ tailWord_1338167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338167).length < 2 ^ (prefixWord ++ tailWord_1338167).sum := by decide
  have hdescent : baseEnd_1338167 < baseStart_1338167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338170 : List Nat := [3, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_1338170 : Nat := 118140960795 + 1338170 * 2 ^ 59
def prefixEnd_1338170 : Nat := 4983230072969 + 3 ^ 40 * 1338170 * 2
def baseEnd_1338170 : Nat := 305388625523170949964833

theorem tailTrace_1338170 : CollatzResearch.WordTrace tailWord_1338170 prefixEnd_1338170 305388625523170949964833 := by
  unfold tailWord_1338170
  simp only [CollatzResearch.WordTrace]
  refine ⟨12201767390511526521502991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32538046374697404057341309 12201767390511526521502991)
  ·
    refine ⟨18302651085767289782254487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12201767390511526521502991 18302651085767289782254487)
    ·
      refine ⟨27453976628650934673381731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18302651085767289782254487 27453976628650934673381731)
      ·
        refine ⟨41180964942976402010072597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27453976628650934673381731 41180964942976402010072597)
        ·
          refine ⟨1930357731702018844222153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41180964942976402010072597 1930357731702018844222153)
          ·
            refine ⟨1447768298776514133166615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1930357731702018844222153 1447768298776514133166615)
            ·
              refine ⟨2171652448164771199749923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447768298776514133166615 2171652448164771199749923)
              ·
                refine ⟨3257478672247156799624885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171652448164771199749923 3257478672247156799624885)
                ·
                  refine ⟨305388625523170949964833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3257478672247156799624885 305388625523170949964833)
                  ·
                    rfl

theorem cell21_1338170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_1338170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338170 prefixEnd_1338170 := by exact prefixLift 1338170
  have htrace : WordTrace (prefixWord ++ tailWord_1338170) baseStart_1338170 baseEnd_1338170 := by
    simpa [prefixWord, tailWord_1338170, baseEnd_1338170] using wordTrace_append hprefix tailTrace_1338170
  have hstable : (prefixWord ++ tailWord_1338170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338170).length < 2 ^ (prefixWord ++ tailWord_1338170).sum := by decide
  have hdescent : baseEnd_1338170 < baseStart_1338170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338243 : List Nat := [1, 1, 1, 3, 4, 1, 1, 5, 4]
def baseStart_1338243 : Nat := 118140960795 + 1338243 * 2 ^ 59
def prefixEnd_1338243 : Nat := 4983230072969 + 3 ^ 40 * 1338243 * 2
def baseEnd_1338243 : Nat := 305405285117739045248017

theorem tailTrace_1338243 : CollatzResearch.WordTrace tailWord_1338243 prefixEnd_1338243 305405285117739045248017 := by
  unfold tailWord_1338243
  simp only [CollatzResearch.WordTrace]
  refine ⟨48809732090781639553419383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32539821393854426368946255 48809732090781639553419383)
  ·
    refine ⟨73214598136172459330129075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48809732090781639553419383 73214598136172459330129075)
    ·
      refine ⟨109821897204258688995193613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73214598136172459330129075 109821897204258688995193613)
      ·
        refine ⟨41183211451597008373197605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109821897204258688995193613 41183211451597008373197605)
        ·
          refine ⟨7721852147174439069974551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41183211451597008373197605 7721852147174439069974551)
          ·
            refine ⟨11582778220761658604961827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7721852147174439069974551 11582778220761658604961827)
            ·
              refine ⟨17374167331142487907442741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11582778220761658604961827 17374167331142487907442741)
              ·
                refine ⟨1628828187294608241322757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17374167331142487907442741 1628828187294608241322757)
                ·
                  refine ⟨305405285117739045248017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628828187294608241322757 305405285117739045248017)
                  ·
                    rfl

theorem cell21_1338243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 4].length) (baseStart_1338243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338243 prefixEnd_1338243 := by exact prefixLift 1338243
  have htrace : WordTrace (prefixWord ++ tailWord_1338243) baseStart_1338243 baseEnd_1338243 := by
    simpa [prefixWord, tailWord_1338243, baseEnd_1338243] using wordTrace_append hprefix tailTrace_1338243
  have hstable : (prefixWord ++ tailWord_1338243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338243).length < 2 ^ (prefixWord ++ tailWord_1338243).sum := by decide
  have hdescent : baseEnd_1338243 < baseStart_1338243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338274 : List Nat := [3, 3, 1, 2, 2, 2, 8]
def baseStart_1338274 : Nat := 118140960795 + 1338274 * 2 ^ 59
def prefixEnd_1338274 : Nat := 4983230072969 + 3 ^ 40 * 1338274 * 2
def baseEnd_1338274 : Nat := 33934706637787764470143

theorem tailTrace_1338274 : CollatzResearch.WordTrace tailWord_1338274 prefixEnd_1338274 33934706637787764470143 := by
  unfold tailWord_1338274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12202715688417332961949469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32540575169112887898531917 12202715688417332961949469)
  ·
    refine ⟨4576018383156499860731051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12202715688417332961949469 4576018383156499860731051)
    ·
      refine ⟨6864027574734749791096577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4576018383156499860731051 6864027574734749791096577)
      ·
        refine ⟨5148020681051062343322433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6864027574734749791096577 5148020681051062343322433)
        ·
          refine ⟨3861015510788296757491825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5148020681051062343322433 3861015510788296757491825)
          ·
            refine ⟨2895761633091222568118869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861015510788296757491825 2895761633091222568118869)
            ·
              refine ⟨33934706637787764470143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2895761633091222568118869 33934706637787764470143)
              ·
                rfl

theorem cell21_1338274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 8].length) (baseStart_1338274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338274 prefixEnd_1338274 := by exact prefixLift 1338274
  have htrace : WordTrace (prefixWord ++ tailWord_1338274) baseStart_1338274 baseEnd_1338274 := by
    simpa [prefixWord, tailWord_1338274, baseEnd_1338274] using wordTrace_append hprefix tailTrace_1338274
  have hstable : (prefixWord ++ tailWord_1338274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338274).length < 2 ^ (prefixWord ++ tailWord_1338274).sum := by decide
  have hdescent : baseEnd_1338274 < baseStart_1338274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338353 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 4]
def baseStart_1338353 : Nat := 118140960795 + 1338353 * 2 ^ 59
def prefixEnd_1338353 : Nat := 4983230072969 + 3 ^ 40 * 1338353 * 2
def baseEnd_1338353 : Nat := 305430388616403298414459

theorem tailTrace_1338353 : CollatzResearch.WordTrace tailWord_1338353 prefixEnd_1338353 305430388616403298414459 := by
  unfold tailWord_1338353
  simp only [CollatzResearch.WordTrace]
  refine ⟨48813744120383128339923713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32542496080255418893282475 48813744120383128339923713)
  ·
    refine ⟨36610308090287346254942785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48813744120383128339923713 36610308090287346254942785)
    ·
      refine ⟨27457731067715509691207089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36610308090287346254942785 27457731067715509691207089)
      ·
        refine ⟨20593298300786632268405317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27457731067715509691207089 20593298300786632268405317)
        ·
          refine ⟨3861243431397493550325997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20593298300786632268405317 3861243431397493550325997)
          ·
            refine ⟨1447966286774060081372249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3861243431397493550325997 1447966286774060081372249)
            ·
              refine ⟨1085974715080545061029187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1447966286774060081372249 1085974715080545061029187)
              ·
                refine ⟨1628962072620817591543781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085974715080545061029187 1628962072620817591543781)
                ·
                  refine ⟨305430388616403298414459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1628962072620817591543781 305430388616403298414459)
                  ·
                    rfl

theorem cell21_1338353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_1338353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338353 prefixEnd_1338353 := by exact prefixLift 1338353
  have htrace : WordTrace (prefixWord ++ tailWord_1338353) baseStart_1338353 baseEnd_1338353 := by
    simpa [prefixWord, tailWord_1338353, baseEnd_1338353] using wordTrace_append hprefix tailTrace_1338353
  have hstable : (prefixWord ++ tailWord_1338353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338353).length < 2 ^ (prefixWord ++ tailWord_1338353).sum := by decide
  have hdescent : baseEnd_1338353 < baseStart_1338353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338592 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 5]
def baseStart_1338592 : Nat := 118140960795 + 1338592 * 2 ^ 59
def prefixEnd_1338592 : Nat := 4983230072969 + 3 ^ 40 * 1338592 * 2
def baseEnd_1338592 : Nat := 305484931672591993930637

theorem tailTrace_1338592 : CollatzResearch.WordTrace tailWord_1338592 prefixEnd_1338592 305484931672591993930637 := by
  unfold tailWord_1338592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411230583258636078937015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32548307444344848105249353 24411230583258636078937015)
  ·
    refine ⟨36616845874887954118405523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24411230583258636078937015 36616845874887954118405523)
    ·
      refine ⟨54925268812331931177608285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36616845874887954118405523 54925268812331931177608285)
      ·
        refine ⟨20596975804624474191603107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54925268812331931177608285 20596975804624474191603107)
        ·
          refine ⟨30895463706936711287404661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20596975804624474191603107 30895463706936711287404661)
          ·
            refine ⟨2896449722525316683194187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30895463706936711287404661 2896449722525316683194187)
            ·
              refine ⟨4344674583787975024791281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896449722525316683194187 4344674583787975024791281)
              ·
                refine ⟨3258505937840981268593461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4344674583787975024791281 3258505937840981268593461)
                ·
                  refine ⟨305484931672591993930637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3258505937840981268593461 305484931672591993930637)
                  ·
                    rfl

theorem cell21_1338592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 5].length) (baseStart_1338592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338592 prefixEnd_1338592 := by exact prefixLift 1338592
  have htrace : WordTrace (prefixWord ++ tailWord_1338592) baseStart_1338592 baseEnd_1338592 := by
    simpa [prefixWord, tailWord_1338592, baseEnd_1338592] using wordTrace_append hprefix tailTrace_1338592
  have hstable : (prefixWord ++ tailWord_1338592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338592).length < 2 ^ (prefixWord ++ tailWord_1338592).sum := by decide
  have hdescent : baseEnd_1338592 < baseStart_1338592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338612 : List Nat := [2, 6, 1, 2, 1, 1, 8]
def baseStart_1338612 : Nat := 118140960795 + 1338612 * 2 ^ 59
def prefixEnd_1338612 : Nat := 4983230072969 + 3 ^ 40 * 1338612 * 2
def baseEnd_1338612 : Nat := 33943277327230711510807

theorem tailTrace_1338612 : CollatzResearch.WordTrace tailWord_1338612 prefixEnd_1338612 33943277327230711510807 := by
  unfold tailWord_1338612
  simp only [CollatzResearch.WordTrace]
  refine ⟨24411595313222407786801045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32548793750963210382401393 24411595313222407786801045)
  ·
    refine ⟨1144293530307300365006299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24411595313222407786801045 1144293530307300365006299)
    ·
      refine ⟨1716440295460950547509449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144293530307300365006299 1716440295460950547509449)
      ·
        refine ⟨1287330221595712910632087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1716440295460950547509449 1287330221595712910632087)
        ·
          refine ⟨1930995332393569365948131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1287330221595712910632087 1930995332393569365948131)
          ·
            refine ⟨2896492998590354048922197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1930995332393569365948131 2896492998590354048922197)
            ·
              refine ⟨33943277327230711510807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2896492998590354048922197 33943277327230711510807)
              ·
                rfl

theorem cell21_1338612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 8].length) (baseStart_1338612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338612 prefixEnd_1338612 := by exact prefixLift 1338612
  have htrace : WordTrace (prefixWord ++ tailWord_1338612) baseStart_1338612 baseEnd_1338612 := by
    simpa [prefixWord, tailWord_1338612, baseEnd_1338612] using wordTrace_append hprefix tailTrace_1338612
  have hstable : (prefixWord ++ tailWord_1338612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338612).length < 2 ^ (prefixWord ++ tailWord_1338612).sum := by decide
  have hdescent : baseEnd_1338612 < baseStart_1338612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338623 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 4]
def baseStart_1338623 : Nat := 118140960795 + 1338623 * 2 ^ 59
def prefixEnd_1338623 : Nat := 4983230072969 + 3 ^ 40 * 1338623 * 2
def baseEnd_1338623 : Nat := 305492006294942828913907

theorem tailTrace_1338623 : CollatzResearch.WordTrace tailWord_1338623 prefixEnd_1338623 305492006294942828913907 := by
  unfold tailWord_1338623
  simp only [CollatzResearch.WordTrace]
  refine ⟨48823591829404964452252523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32549061219603309634835015 48823591829404964452252523)
  ·
    refine ⟨73235387744107446678378785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48823591829404964452252523 73235387744107446678378785)
    ·
      refine ⟨54926540808080585008784089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73235387744107446678378785 54926540808080585008784089)
      ·
        refine ⟨41194905606060438756588067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54926540808080585008784089 41194905606060438756588067)
        ·
          refine ⟨61792358409090658134882101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41194905606060438756588067 61792358409090658134882101)
          ·
            refine ⟨5793033600852249200145197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61792358409090658134882101 5793033600852249200145197)
            ·
              refine ⟨2172387600319593450054449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5793033600852249200145197 2172387600319593450054449)
              ·
                refine ⟨1629290700239695087540837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2172387600319593450054449 1629290700239695087540837)
                ·
                  refine ⟨305492006294942828913907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1629290700239695087540837 305492006294942828913907)
                  ·
                    rfl

theorem cell21_1338623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 4].length) (baseStart_1338623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338623 prefixEnd_1338623 := by exact prefixLift 1338623
  have htrace : WordTrace (prefixWord ++ tailWord_1338623) baseStart_1338623 baseEnd_1338623 := by
    simpa [prefixWord, tailWord_1338623, baseEnd_1338623] using wordTrace_append hprefix tailTrace_1338623
  have hstable : (prefixWord ++ tailWord_1338623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338623).length < 2 ^ (prefixWord ++ tailWord_1338623).sum := by decide
  have hdescent : baseEnd_1338623 < baseStart_1338623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338626 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1338626 : Nat := 118140960795 + 1338626 * 2 ^ 59
def prefixEnd_1338626 : Nat := 4983230072969 + 3 ^ 40 * 1338626 * 2
def baseEnd_1338626 : Nat := 305492690935815490363901

theorem tailTrace_1338626 : CollatzResearch.WordTrace tailWord_1338626 prefixEnd_1338626 305492690935815490363901 := by
  unfold tailWord_1338626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12205925312098523991152933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32549134165596063976407821 12205925312098523991152933)
  ·
    refine ⟨2288610996018473248341175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12205925312098523991152933 2288610996018473248341175)
    ·
      refine ⟨3432916494027709872511763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2288610996018473248341175 3432916494027709872511763)
      ·
        refine ⟨5149374741041564808767645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3432916494027709872511763 5149374741041564808767645)
        ·
          refine ⟨1931015527890586803287867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5149374741041564808767645 1931015527890586803287867)
          ·
            refine ⟨2896523291835880204931801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931015527890586803287867 2896523291835880204931801)
            ·
              refine ⟨2172392468876910153698851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2896523291835880204931801 2172392468876910153698851)
              ·
                refine ⟨3258588703315365230548277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172392468876910153698851 3258588703315365230548277)
                ·
                  refine ⟨305492690935815490363901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3258588703315365230548277 305492690935815490363901)
                  ·
                    rfl

theorem cell21_1338626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1338626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338626 prefixEnd_1338626 := by exact prefixLift 1338626
  have htrace : WordTrace (prefixWord ++ tailWord_1338626) baseStart_1338626 baseEnd_1338626 := by
    simpa [prefixWord, tailWord_1338626, baseEnd_1338626] using wordTrace_append hprefix tailTrace_1338626
  have hstable : (prefixWord ++ tailWord_1338626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338626).length < 2 ^ (prefixWord ++ tailWord_1338626).sum := by decide
  have hdescent : baseEnd_1338626 < baseStart_1338626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338682 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1338682 : Nat := 118140960795 + 1338682 * 2 ^ 59
def prefixEnd_1338682 : Nat := 4983230072969 + 3 ^ 40 * 1338682 * 2
def baseEnd_1338682 : Nat := 305505470898771837430453

theorem tailTrace_1338682 : CollatzResearch.WordTrace tailWord_1338682 prefixEnd_1338682 305505470898771837430453 := by
  unfold tailWord_1338682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206435934047804382162575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32550495824127478352433533 12206435934047804382162575)
  ·
    refine ⟨18309653901071706573243863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12206435934047804382162575 18309653901071706573243863)
    ·
      refine ⟨27464480851607559859865795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18309653901071706573243863 27464480851607559859865795)
      ·
        refine ⟨41196721277411339789798693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27464480851607559859865795 41196721277411339789798693)
        ·
          refine ⟨7724385239514626210587255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41196721277411339789798693 7724385239514626210587255)
          ·
            refine ⟨11586577859271939315880883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7724385239514626210587255 11586577859271939315880883)
            ·
              refine ⟨17379866788907908973821325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11586577859271939315880883 17379866788907908973821325)
              ·
                refine ⟨6517450045840465865182997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17379866788907908973821325 6517450045840465865182997)
                ·
                  refine ⟨305505470898771837430453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6517450045840465865182997 305505470898771837430453)
                  ·
                    rfl

theorem cell21_1338682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1338682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338682 prefixEnd_1338682 := by exact prefixLift 1338682
  have htrace : WordTrace (prefixWord ++ tailWord_1338682) baseStart_1338682 baseEnd_1338682 := by
    simpa [prefixWord, tailWord_1338682, baseEnd_1338682] using wordTrace_append hprefix tailTrace_1338682
  have hstable : (prefixWord ++ tailWord_1338682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338682).length < 2 ^ (prefixWord ++ tailWord_1338682).sum := by decide
  have hdescent : baseEnd_1338682 < baseStart_1338682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338730 : List Nat := [3, 1, 3, 3, 3, 8]
def baseStart_1338730 : Nat := 118140960795 + 1338730 * 2 ^ 59
def prefixEnd_1338730 : Nat := 4983230072969 + 3 ^ 40 * 1338730 * 2
def baseEnd_1338730 : Nat := 11315423153804978541865

theorem tailTrace_1338730 : CollatzResearch.WordTrace tailWord_1338730 prefixEnd_1338730 11315423153804978541865 := by
  unfold tailWord_1338730
  simp only [CollatzResearch.WordTrace]
  refine ⟨12206873610004330431599411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32551662960011547817598429 12206873610004330431599411)
  ·
    refine ⟨18310310415006495647399117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12206873610004330431599411 18310310415006495647399117)
    ·
      refine ⟨6866366405627435867774669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18310310415006495647399117 6866366405627435867774669)
      ·
        refine ⟨2574887402110288450415501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6866366405627435867774669 2574887402110288450415501)
        ·
          refine ⟨965582775791358168905813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2574887402110288450415501 965582775791358168905813)
          ·
            refine ⟨11315423153804978541865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 965582775791358168905813 11315423153804978541865)
            ·
              rfl

theorem cell21_1338730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 8].length) (baseStart_1338730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338730 prefixEnd_1338730 := by exact prefixLift 1338730
  have htrace : WordTrace (prefixWord ++ tailWord_1338730) baseStart_1338730 baseEnd_1338730 := by
    simpa [prefixWord, tailWord_1338730, baseEnd_1338730] using wordTrace_append hprefix tailTrace_1338730
  have hstable : (prefixWord ++ tailWord_1338730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338730).length < 2 ^ (prefixWord ++ tailWord_1338730).sum := by decide
  have hdescent : baseEnd_1338730 < baseStart_1338730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338792 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 6]
def baseStart_1338792 : Nat := 118140960795 + 1338792 * 2 ^ 59
def prefixEnd_1338792 : Nat := 4983230072969 + 3 ^ 40 * 1338792 * 2
def baseEnd_1338792 : Nat := 305530574397436090596895

theorem tailTrace_1338792 : CollatzResearch.WordTrace tailWord_1338792 prefixEnd_1338792 305530574397436090596895 := by
  unfold tailWord_1338792
  simp only [CollatzResearch.WordTrace]
  refine ⟨24414877882896353157577315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32553170510528470876769753 24414877882896353157577315)
  ·
    refine ⟨36622316824344529736365973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24414877882896353157577315 36622316824344529736365973)
    ·
      refine ⟨1716671101141149831392155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36622316824344529736365973 1716671101141149831392155)
      ·
        refine ⟨2575006651711724747088233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716671101141149831392155 2575006651711724747088233)
        ·
          refine ⟨1931254988783793560316175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2575006651711724747088233 1931254988783793560316175)
          ·
            refine ⟨2896882483175690340474263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931254988783793560316175 2896882483175690340474263)
            ·
              refine ⟨4345323724763535510711395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2896882483175690340474263 4345323724763535510711395)
              ·
                refine ⟨6517985587145303266067093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4345323724763535510711395 6517985587145303266067093)
                ·
                  refine ⟨305530574397436090596895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6517985587145303266067093 305530574397436090596895)
                  ·
                    rfl

theorem cell21_1338792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 6].length) (baseStart_1338792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338792 prefixEnd_1338792 := by exact prefixLift 1338792
  have htrace : WordTrace (prefixWord ++ tailWord_1338792) baseStart_1338792 baseEnd_1338792 := by
    simpa [prefixWord, tailWord_1338792, baseEnd_1338792] using wordTrace_append hprefix tailTrace_1338792
  have hstable : (prefixWord ++ tailWord_1338792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338792).length < 2 ^ (prefixWord ++ tailWord_1338792).sum := by decide
  have hdescent : baseEnd_1338792 < baseStart_1338792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338865 : List Nat := [1, 2, 2, 2, 3, 3, 2, 6]
def baseStart_1338865 : Nat := 118140960795 + 1338865 * 2 ^ 59
def prefixEnd_1338865 : Nat := 4983230072969 + 3 ^ 40 * 1338865 * 2
def baseEnd_1338865 : Nat := 101849077997334728626693

theorem tailTrace_1338865 : CollatzResearch.WordTrace tailWord_1338865 prefixEnd_1338865 101849077997334728626693 := by
  unfold tailWord_1338865
  simp only [CollatzResearch.WordTrace]
  refine ⟨48832418294528239782562049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32554945529685493188374699 48832418294528239782562049)
  ·
    refine ⟨36624313720896179836921537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48832418294528239782562049 36624313720896179836921537)
    ·
      refine ⟨27468235290672134877691153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36624313720896179836921537 27468235290672134877691153)
      ·
        refine ⟨20601176468004101158268365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27468235290672134877691153 20601176468004101158268365)
        ·
          refine ⟨7725441175501537934350637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20601176468004101158268365 7725441175501537934350637)
          ·
            refine ⟨2897040440813076725381489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7725441175501537934350637 2897040440813076725381489)
            ·
              refine ⟨2172780330609807544036117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897040440813076725381489 2172780330609807544036117)
              ·
                refine ⟨101849077997334728626693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2172780330609807544036117 101849077997334728626693)
                ·
                  rfl

theorem cell21_1338865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 6].length) (baseStart_1338865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338865 prefixEnd_1338865 := by exact prefixLift 1338865
  have htrace : WordTrace (prefixWord ++ tailWord_1338865) baseStart_1338865 baseEnd_1338865 := by
    simpa [prefixWord, tailWord_1338865, baseEnd_1338865] using wordTrace_append hprefix tailTrace_1338865
  have hstable : (prefixWord ++ tailWord_1338865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338865).length < 2 ^ (prefixWord ++ tailWord_1338865).sum := by decide
  have hdescent : baseEnd_1338865 < baseStart_1338865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338882 : List Nat := [3, 4, 1, 2, 1, 1, 2, 7]
def baseStart_1338882 : Nat := 118140960795 + 1338882 * 2 ^ 59
def prefixEnd_1338882 : Nat := 4983230072969 + 3 ^ 40 * 1338882 * 2
def baseEnd_1338882 : Nat := 101850371207871978032237

theorem tailTrace_1338882 : CollatzResearch.WordTrace tailWord_1338882 prefixEnd_1338882 101850371207871978032237 := by
  unfold tailWord_1338882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12208259583866662921482725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32555358890311101123953933 12208259583866662921482725)
  ·
    refine ⟨2289048671974999297778011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12208259583866662921482725 2289048671974999297778011)
    ·
      refine ⟨3433573007962498946667017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289048671974999297778011 3433573007962498946667017)
      ·
        refine ⟨2575179755971874210000263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3433573007962498946667017 2575179755971874210000263)
        ·
          refine ⟨3862769633957811315000395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575179755971874210000263 3862769633957811315000395)
          ·
            refine ⟨5794154450936716972500593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3862769633957811315000395 5794154450936716972500593)
            ·
              refine ⟨4345615838202537729375445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5794154450936716972500593 4345615838202537729375445)
              ·
                refine ⟨101850371207871978032237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4345615838202537729375445 101850371207871978032237)
                ·
                  rfl

theorem cell21_1338882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_1338882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338882 prefixEnd_1338882 := by exact prefixLift 1338882
  have htrace : WordTrace (prefixWord ++ tailWord_1338882) baseStart_1338882 baseEnd_1338882 := by
    simpa [prefixWord, tailWord_1338882, baseEnd_1338882] using wordTrace_append hprefix tailTrace_1338882
  have hstable : (prefixWord ++ tailWord_1338882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338882).length < 2 ^ (prefixWord ++ tailWord_1338882).sum := by decide
  have hdescent : baseEnd_1338882 < baseStart_1338882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338913 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 3]
def baseStart_1338913 : Nat := 118140960795 + 1338913 * 2 ^ 59
def prefixEnd_1338913 : Nat := 4983230072969 + 3 ^ 40 * 1338913 * 2
def baseEnd_1338913 : Nat := 305558188245966769079981

theorem tailTrace_1338913 : CollatzResearch.WordTrace tailWord_1338913 prefixEnd_1338913 305558188245966769079981 := by
  unfold tailWord_1338913
  simp only [CollatzResearch.WordTrace]
  refine ⟨48834168998354343980309393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32556112665569562653539595 48834168998354343980309393)
  ·
    refine ⟨36625626748765757985232045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48834168998354343980309393 36625626748765757985232045)
    ·
      refine ⟨13734610030787159244462017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36625626748765757985232045 13734610030787159244462017)
      ·
        refine ⟨10300957523090369433346513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13734610030787159244462017 10300957523090369433346513)
        ·
          refine ⟨7725718142317777075009885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10300957523090369433346513 7725718142317777075009885)
          ·
            refine ⟨2897144303369166403128707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7725718142317777075009885 2897144303369166403128707)
            ·
              refine ⟨4345716455053749604693061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2897144303369166403128707 4345716455053749604693061)
              ·
                refine ⟨814821835322578050879949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4345716455053749604693061 814821835322578050879949)
                ·
                  refine ⟨305558188245966769079981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814821835322578050879949 305558188245966769079981)
                  ·
                    rfl

theorem cell21_1338913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_1338913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338913 prefixEnd_1338913 := by exact prefixLift 1338913
  have htrace : WordTrace (prefixWord ++ tailWord_1338913) baseStart_1338913 baseEnd_1338913 := by
    simpa [prefixWord, tailWord_1338913, baseEnd_1338913] using wordTrace_append hprefix tailTrace_1338913
  have hstable : (prefixWord ++ tailWord_1338913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338913).length < 2 ^ (prefixWord ++ tailWord_1338913).sum := by decide
  have hdescent : baseEnd_1338913 < baseStart_1338913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1338972 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 5]
def baseStart_1338972 : Nat := 118140960795 + 1338972 * 2 ^ 59
def prefixEnd_1338972 : Nat := 4983230072969 + 3 ^ 40 * 1338972 * 2
def baseEnd_1338972 : Nat := 305571652849795777596527

theorem tailTrace_1338972 : CollatzResearch.WordTrace tailWord_1338972 prefixEnd_1338972 305571652849795777596527 := by
  unfold tailWord_1338972
  simp only [CollatzResearch.WordTrace]
  refine ⟨24418160452570298528353585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32557547270093731371138113 24418160452570298528353585)
  ·
    refine ⟨18313620339427723896265189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24418160452570298528353585 18313620339427723896265189)
    ·
      refine ⟨3433803813642698230549723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18313620339427723896265189 3433803813642698230549723)
      ·
        refine ⟨5150705720464047345824585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433803813642698230549723 5150705720464047345824585)
        ·
          refine ⟨3863029290348035509368439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5150705720464047345824585 3863029290348035509368439)
          ·
            refine ⟨5794543935522053264052659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863029290348035509368439 5794543935522053264052659)
            ·
              refine ⟨8691815903283079896078989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5794543935522053264052659 8691815903283079896078989)
              ·
                refine ⟨3259430963731154961029621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8691815903283079896078989 3259430963731154961029621)
                ·
                  refine ⟨305571652849795777596527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3259430963731154961029621 305571652849795777596527)
                  ·
                    rfl

theorem cell21_1338972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 5].length) (baseStart_1338972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1338972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1338972 prefixEnd_1338972 := by exact prefixLift 1338972
  have htrace : WordTrace (prefixWord ++ tailWord_1338972) baseStart_1338972 baseEnd_1338972 := by
    simpa [prefixWord, tailWord_1338972, baseEnd_1338972] using wordTrace_append hprefix tailTrace_1338972
  have hstable : (prefixWord ++ tailWord_1338972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1338972).length < 2 ^ (prefixWord ++ tailWord_1338972).sum := by decide
  have hdescent : baseEnd_1338972 < baseStart_1338972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1338972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339074 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1339074 : Nat := 118140960795 + 1339074 * 2 ^ 59
def prefixEnd_1339074 : Nat := 4983230072969 + 3 ^ 40 * 1339074 * 2
def baseEnd_1339074 : Nat := 305594930639466266896319

theorem tailTrace_1339074 : CollatzResearch.WordTrace tailWord_1339074 prefixEnd_1339074 305594930639466266896319 := by
  unfold tailWord_1339074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12210010287692767119230069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32560027433847378984613517 12210010287692767119230069)
  ·
    refine ⟨1144688464471196917427819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12210010287692767119230069 1144688464471196917427819)
    ·
      refine ⟨1717032696706795376141729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144688464471196917427819 1717032696706795376141729)
      ·
        refine ⟨1287774522530096532106297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717032696706795376141729 1287774522530096532106297)
        ·
          refine ⟨965830891897572399079723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1287774522530096532106297 965830891897572399079723)
          ·
            refine ⟨1448746337846358598619585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965830891897572399079723 1448746337846358598619585)
            ·
              refine ⟨1086559753384768948964689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448746337846358598619585 1086559753384768948964689)
              ·
                refine ⟨814919815038576711723517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1086559753384768948964689 814919815038576711723517)
                ·
                  refine ⟨305594930639466266896319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814919815038576711723517 305594930639466266896319)
                  ·
                    rfl

theorem cell21_1339074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1339074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339074 prefixEnd_1339074 := by exact prefixLift 1339074
  have htrace : WordTrace (prefixWord ++ tailWord_1339074) baseStart_1339074 baseEnd_1339074 := by
    simpa [prefixWord, tailWord_1339074, baseEnd_1339074] using wordTrace_append hprefix tailTrace_1339074
  have hstable : (prefixWord ++ tailWord_1339074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339074).length < 2 ^ (prefixWord ++ tailWord_1339074).sum := by decide
  have hdescent : baseEnd_1339074 < baseStart_1339074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339169 : List Nat := [1, 2, 3, 2, 1, 3, 4, 5]
def baseStart_1339169 : Nat := 118140960795 + 1339169 * 2 ^ 59
def prefixEnd_1339169 : Nat := 4983230072969 + 3 ^ 40 * 1339169 * 2
def baseEnd_1339169 : Nat := 101872203644589070937597

theorem tailTrace_1339169 : CollatzResearch.WordTrace tailWord_1339169 prefixEnd_1339169 101872203644589070937597 := by
  unfold tailWord_1339169
  simp only [CollatzResearch.WordTrace]
  refine ⟨48843506085426899701628561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32562337390284599801085707 48843506085426899701628561)
  ·
    refine ⟨36632629564070174776221421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48843506085426899701628561 36632629564070174776221421)
    ·
      refine ⟨13737236086526315541083033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36632629564070174776221421 13737236086526315541083033)
      ·
        refine ⟨10302927064894736655812275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13737236086526315541083033 10302927064894736655812275)
        ·
          refine ⟨15454390597342104983718413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10302927064894736655812275 15454390597342104983718413)
          ·
            refine ⟨5795396474003289368894405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15454390597342104983718413 5795396474003289368894405)
            ·
              refine ⟨1086636838875616756667701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5795396474003289368894405 1086636838875616756667701)
              ·
                refine ⟨101872203644589070937597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1086636838875616756667701 101872203644589070937597)
                ·
                  rfl

theorem cell21_1339169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 5].length) (baseStart_1339169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339169 prefixEnd_1339169 := by exact prefixLift 1339169
  have htrace : WordTrace (prefixWord ++ tailWord_1339169) baseStart_1339169 baseEnd_1339169 := by
    simpa [prefixWord, tailWord_1339169, baseEnd_1339169] using wordTrace_append hprefix tailTrace_1339169
  have hstable : (prefixWord ++ tailWord_1339169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339169).length < 2 ^ (prefixWord ++ tailWord_1339169).sum := by decide
  have hdescent : baseEnd_1339169 < baseStart_1339169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339206 : List Nat := [6, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1339206 : Nat := 118140960795 + 1339206 * 2 ^ 59
def prefixEnd_1339206 : Nat := 4983230072969 + 3 ^ 40 * 1339206 * 2
def baseEnd_1339206 : Nat := 305625054837863370696049

theorem tailTrace_1339206 : CollatzResearch.WordTrace tailWord_1339206 prefixEnd_1339206 305625054837863370696049 := by
  unfold tailWord_1339206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526401737071651719397671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32563237057528570013816981 1526401737071651719397671)
  ·
    refine ⟨2289602605607477579096507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526401737071651719397671 2289602605607477579096507)
    ·
      refine ⟨3434403908411216368644761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2289602605607477579096507 3434403908411216368644761)
      ·
        refine ⟨2575802931308412276483571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3434403908411216368644761 2575802931308412276483571)
        ·
          refine ⟨3863704396962618414725357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575802931308412276483571 3863704396962618414725357)
          ·
            refine ⟨1448889148860981905522009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3863704396962618414725357 1448889148860981905522009)
            ·
              refine ⟨1086666861645736429141507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448889148860981905522009 1086666861645736429141507)
              ·
                refine ⟨1630000292468604643712261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086666861645736429141507 1630000292468604643712261)
                ·
                  refine ⟨305625054837863370696049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630000292468604643712261 305625054837863370696049)
                  ·
                    rfl

theorem cell21_1339206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1339206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339206 prefixEnd_1339206 := by exact prefixLift 1339206
  have htrace : WordTrace (prefixWord ++ tailWord_1339206) baseStart_1339206 baseEnd_1339206 := by
    simpa [prefixWord, tailWord_1339206, baseEnd_1339206] using wordTrace_append hprefix tailTrace_1339206
  have hstable : (prefixWord ++ tailWord_1339206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339206).length < 2 ^ (prefixWord ++ tailWord_1339206).sum := by decide
  have hdescent : baseEnd_1339206 < baseStart_1339206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339262 : List Nat := [4, 2, 3, 1, 1, 1, 3, 6]
def baseStart_1339262 : Nat := 118140960795 + 1339262 * 2 ^ 59
def prefixEnd_1339262 : Nat := 4983230072969 + 3 ^ 40 * 1339262 * 2
def baseEnd_1339262 : Nat := 101879278266939905920867

theorem tailTrace_1339262 : CollatzResearch.WordTrace tailWord_1339262 prefixEnd_1339262 101879278266939905920867 := by
  unfold tailWord_1339262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105862259261247073095505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32564598716059984389842693 6105862259261247073095505)
  ·
    refine ⟨4579396694445935304821629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6105862259261247073095505 4579396694445935304821629)
    ·
      refine ⟨1717273760417225739308111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4579396694445935304821629 1717273760417225739308111)
      ·
        refine ⟨2575910640625838608962167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717273760417225739308111 2575910640625838608962167)
        ·
          refine ⟨3863865960938757913443251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2575910640625838608962167 3863865960938757913443251)
          ·
            refine ⟨5795798941408136870164877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3863865960938757913443251 5795798941408136870164877)
            ·
              refine ⟨2173424603028051326311829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5795798941408136870164877 2173424603028051326311829)
              ·
                refine ⟨101879278266939905920867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2173424603028051326311829 101879278266939905920867)
                ·
                  rfl

theorem cell21_1339262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_1339262 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339262 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339262 prefixEnd_1339262 := by exact prefixLift 1339262
  have htrace : WordTrace (prefixWord ++ tailWord_1339262) baseStart_1339262 baseEnd_1339262 := by
    simpa [prefixWord, tailWord_1339262, baseEnd_1339262] using wordTrace_append hprefix tailTrace_1339262
  have hstable : (prefixWord ++ tailWord_1339262).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339262).length < 2 ^ (prefixWord ++ tailWord_1339262).sum := by decide
  have hdescent : baseEnd_1339262 < baseStart_1339262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339293 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 3]
def baseStart_1339293 : Nat := 118140960795 + 1339293 * 2 ^ 59
def prefixEnd_1339293 : Nat := 4983230072969 + 3 ^ 40 * 1339293 * 2
def baseEnd_1339293 : Nat := 305644909423170552745871

theorem tailTrace_1339293 : CollatzResearch.WordTrace tailWord_1339293 prefixEnd_1339293 305644909423170552745871 := by
  unfold tailWord_1339293
  simp only [CollatzResearch.WordTrace]
  refine ⟨48848028736977668879142533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32565352491318445919428355 48848028736977668879142533)
  ·
    refine ⟨9159005388183312914839225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48848028736977668879142533 9159005388183312914839225)
    ·
      refine ⟨6869254041137484686129419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9159005388183312914839225 6869254041137484686129419)
      ·
        refine ⟨10303881061706227029194129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869254041137484686129419 10303881061706227029194129)
        ·
          refine ⟨7727910796279670271895597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10303881061706227029194129 7727910796279670271895597)
          ·
            refine ⟨2897966548604876351960849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7727910796279670271895597 2897966548604876351960849)
            ·
              refine ⟨2173474911453657263970637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897966548604876351960849 2173474911453657263970637)
              ·
                refine ⟨815053091795121473988989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2173474911453657263970637 815053091795121473988989)
                ·
                  refine ⟨305644909423170552745871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815053091795121473988989 305644909423170552745871)
                  ·
                    rfl

theorem cell21_1339293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_1339293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339293 prefixEnd_1339293 := by exact prefixLift 1339293
  have htrace : WordTrace (prefixWord ++ tailWord_1339293) baseStart_1339293 baseEnd_1339293 := by
    simpa [prefixWord, tailWord_1339293, baseEnd_1339293] using wordTrace_append hprefix tailTrace_1339293
  have hstable : (prefixWord ++ tailWord_1339293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339293).length < 2 ^ (prefixWord ++ tailWord_1339293).sum := by decide
  have hdescent : baseEnd_1339293 < baseStart_1339293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339431 : List Nat := [1, 1, 7, 1, 3, 1, 1, 6]
def baseStart_1339431 : Nat := 118140960795 + 1339431 * 2 ^ 59
def prefixEnd_1339431 : Nat := 4983230072969 + 3 ^ 40 * 1339431 * 2
def baseEnd_1339431 : Nat := 101892134301104326481863

theorem tailTrace_1339431 : CollatzResearch.WordTrace tailWord_1339431 prefixEnd_1339431 101892134301104326481863 := by
  unfold tailWord_1339431
  simp only [CollatzResearch.WordTrace]
  refine ⟨48853062010477718447666147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32568708006985145631777431 48853062010477718447666147)
  ·
    refine ⟨73279593015716577671499221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48853062010477718447666147 73279593015716577671499221)
    ·
      refine ⟨1717490461305857289175763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 73279593015716577671499221 1717490461305857289175763)
      ·
        refine ⟨2576235691958785933763645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1717490461305857289175763 2576235691958785933763645)
        ·
          refine ⟨966088384484544725161367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2576235691958785933763645 966088384484544725161367)
          ·
            refine ⟨1449132576726817087742051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966088384484544725161367 1449132576726817087742051)
            ·
              refine ⟨2173698865090225631613077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449132576726817087742051 2173698865090225631613077)
              ·
                refine ⟨101892134301104326481863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2173698865090225631613077 101892134301104326481863)
                ·
                  rfl

theorem cell21_1339431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 6].length) (baseStart_1339431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339431 prefixEnd_1339431 := by exact prefixLift 1339431
  have htrace : WordTrace (prefixWord ++ tailWord_1339431) baseStart_1339431 baseEnd_1339431 := by
    simpa [prefixWord, tailWord_1339431, baseEnd_1339431] using wordTrace_append hprefix tailTrace_1339431
  have hstable : (prefixWord ++ tailWord_1339431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339431).length < 2 ^ (prefixWord ++ tailWord_1339431).sum := by decide
  have hdescent : baseEnd_1339431 < baseStart_1339431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339439 : List Nat := [1, 1, 2, 1, 2, 1, 1, 12]
def baseStart_1339439 : Nat := 118140960795 + 1339439 * 2 ^ 59
def prefixEnd_1339439 : Nat := 4983230072969 + 3 ^ 40 * 1339439 * 2
def baseEnd_1339439 : Nat := 101892742870768914437413

theorem tailTrace_1339439 : CollatzResearch.WordTrace tailWord_1339439 prefixEnd_1339439 101892742870768914437413 := by
  unfold tailWord_1339439
  simp only [CollatzResearch.WordTrace]
  refine ⟨48853353794448735813957371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32568902529632490542638247 48853353794448735813957371)
  ·
    refine ⟨73280030691673103720936057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48853353794448735813957371 73280030691673103720936057)
    ·
      refine ⟨54960023018754827790702043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73280030691673103720936057 54960023018754827790702043)
      ·
        refine ⟨82440034528132241686053065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54960023018754827790702043 82440034528132241686053065)
        ·
          refine ⟨61830025896099181264539799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82440034528132241686053065 61830025896099181264539799)
          ·
            refine ⟨92745038844148771896809699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61830025896099181264539799 92745038844148771896809699)
            ·
              refine ⟨139117558266223157845214549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92745038844148771896809699 139117558266223157845214549)
              ·
                refine ⟨101892742870768914437413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 139117558266223157845214549 101892742870768914437413)
                ·
                  rfl

theorem cell21_1339439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_1339439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339439 prefixEnd_1339439 := by exact prefixLift 1339439
  have htrace : WordTrace (prefixWord ++ tailWord_1339439) baseStart_1339439 baseEnd_1339439 := by
    simpa [prefixWord, tailWord_1339439, baseEnd_1339439] using wordTrace_append hprefix tailTrace_1339439
  have hstable : (prefixWord ++ tailWord_1339439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339439).length < 2 ^ (prefixWord ++ tailWord_1339439).sum := by decide
  have hdescent : baseEnd_1339439 < baseStart_1339439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339442 : List Nat := [3, 2, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1339442 : Nat := 118140960795 + 1339442 * 2 ^ 59
def prefixEnd_1339442 : Nat := 4983230072969 + 3 ^ 40 * 1339442 * 2
def baseEnd_1339442 : Nat := 305678913253179404762233

theorem tailTrace_1339442 : CollatzResearch.WordTrace tailWord_1339442 prefixEnd_1339442 305678913253179404762233 := by
  unfold tailWord_1339442
  simp only [CollatzResearch.WordTrace]
  refine ⟨12213365803359466831579145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32568975475625244884211053 12213365803359466831579145)
  ·
    refine ⟨9160024352519600123684359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12213365803359466831579145 9160024352519600123684359)
    ·
      refine ⟨13740036528779400185526539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9160024352519600123684359 13740036528779400185526539)
      ·
        refine ⟨20610054793169100278289809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13740036528779400185526539 20610054793169100278289809)
        ·
          refine ⟨15457541094876825208717357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20610054793169100278289809 15457541094876825208717357)
          ·
            refine ⟨5796577910578809453269009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15457541094876825208717357 5796577910578809453269009)
            ·
              refine ⟨4347433432934107089951757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5796577910578809453269009 4347433432934107089951757)
              ·
                refine ⟨1630287537350290158731909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4347433432934107089951757 1630287537350290158731909)
                ·
                  refine ⟨305678913253179404762233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630287537350290158731909 305678913253179404762233)
                  ·
                    rfl

theorem cell21_1339442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1339442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339442 prefixEnd_1339442 := by exact prefixLift 1339442
  have htrace : WordTrace (prefixWord ++ tailWord_1339442) baseStart_1339442 baseEnd_1339442 := by
    simpa [prefixWord, tailWord_1339442, baseEnd_1339442] using wordTrace_append hprefix tailTrace_1339442
  have hstable : (prefixWord ++ tailWord_1339442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339442).length < 2 ^ (prefixWord ++ tailWord_1339442).sum := by decide
  have hdescent : baseEnd_1339442 < baseStart_1339442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339462 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1339462 : Nat := 118140960795 + 1339462 * 2 ^ 59
def prefixEnd_1339462 : Nat := 4983230072969 + 3 ^ 40 * 1339462 * 2
def baseEnd_1339462 : Nat := 305683477525663814428859

theorem tailTrace_1339462 : CollatzResearch.WordTrace tailWord_1339462 prefixEnd_1339462 305683477525663814428859 := by
  unfold tailWord_1339462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526693521042669085688895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32569461782243607161363093 1526693521042669085688895)
  ·
    refine ⟨2290040281564003628533343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1526693521042669085688895 2290040281564003628533343)
    ·
      refine ⟨3435060422346005442800015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2290040281564003628533343 3435060422346005442800015)
      ·
        refine ⟨5152590633519008164200023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3435060422346005442800015 5152590633519008164200023)
        ·
          refine ⟨7728885950278512246300035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5152590633519008164200023 7728885950278512246300035)
          ·
            refine ⟨11593328925417768369450053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7728885950278512246300035 11593328925417768369450053)
            ·
              refine ⟨2173749173515831569271885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11593328925417768369450053 2173749173515831569271885)
              ·
                refine ⟨815155940068436838476957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2173749173515831569271885 815155940068436838476957)
                ·
                  refine ⟨305683477525663814428859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815155940068436838476957 305683477525663814428859)
                  ·
                    rfl

theorem cell21_1339462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1339462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339462 prefixEnd_1339462 := by exact prefixLift 1339462
  have htrace : WordTrace (prefixWord ++ tailWord_1339462) baseStart_1339462 baseEnd_1339462 := by
    simpa [prefixWord, tailWord_1339462, baseEnd_1339462] using wordTrace_append hprefix tailTrace_1339462
  have hstable : (prefixWord ++ tailWord_1339462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339462).length < 2 ^ (prefixWord ++ tailWord_1339462).sum := by decide
  have hdescent : baseEnd_1339462 < baseStart_1339462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339594 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1339594 : Nat := 118140960795 + 1339594 * 2 ^ 59
def prefixEnd_1339594 : Nat := 4983230072969 + 3 ^ 40 * 1339594 * 2
def baseEnd_1339594 : Nat := 305713601724060918228589

theorem tailTrace_1339594 : CollatzResearch.WordTrace tailWord_1339594 prefixEnd_1339594 305713601724060918228589 := by
  unfold tailWord_1339594
  simp only [CollatzResearch.WordTrace]
  refine ⟨12214751777221799321462459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32572671405924798190566557 12214751777221799321462459)
  ·
    refine ⟨18322127665832698982193689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12214751777221799321462459 18322127665832698982193689)
    ·
      refine ⟨13741595749374524236645267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18322127665832698982193689 13741595749374524236645267)
      ·
        refine ⟨20612393624061786354967901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13741595749374524236645267 20612393624061786354967901)
        ·
          refine ⟨7729647609023169883112963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20612393624061786354967901 7729647609023169883112963)
          ·
            refine ⟨11594471413534754824669445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7729647609023169883112963 11594471413534754824669445)
            ·
              refine ⟨2173963390037766529625521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11594471413534754824669445 2173963390037766529625521)
              ·
                refine ⟨1630472542528324897219141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2173963390037766529625521 1630472542528324897219141)
                ·
                  refine ⟨305713601724060918228589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630472542528324897219141 305713601724060918228589)
                  ·
                    rfl

theorem cell21_1339594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1339594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339594 prefixEnd_1339594 := by exact prefixLift 1339594
  have htrace : WordTrace (prefixWord ++ tailWord_1339594) baseStart_1339594 baseEnd_1339594 := by
    simpa [prefixWord, tailWord_1339594, baseEnd_1339594] using wordTrace_append hprefix tailTrace_1339594
  have hstable : (prefixWord ++ tailWord_1339594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339594).length < 2 ^ (prefixWord ++ tailWord_1339594).sum := by decide
  have hdescent : baseEnd_1339594 < baseStart_1339594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339608 : List Nat := [2, 1, 2, 2, 4, 1, 3, 6]
def baseStart_1339608 : Nat := 118140960795 + 1339608 * 2 ^ 59
def prefixEnd_1339608 : Nat := 4983230072969 + 3 ^ 40 * 1339608 * 2
def baseEnd_1339608 : Nat := 101905598904933334998409

theorem tailTrace_1339608 : CollatzResearch.WordTrace tailWord_1339608 prefixEnd_1339608 101905598904933334998409 := by
  unfold tailWord_1339608
  simp only [CollatzResearch.WordTrace]
  refine ⟨24429758865418238838429739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32573011820557651784572985 24429758865418238838429739)
  ·
    refine ⟨36644638298127358257644609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24429758865418238838429739 36644638298127358257644609)
    ·
      refine ⟨27483478723595518693233457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36644638298127358257644609 27483478723595518693233457)
      ·
        refine ⟨20612609042696639019925093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27483478723595518693233457 20612609042696639019925093)
        ·
          refine ⟨3864864195505619816235955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20612609042696639019925093 3864864195505619816235955)
          ·
            refine ⟨5797296293258429724353933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3864864195505619816235955 5797296293258429724353933)
            ·
              refine ⟨2173986109971911146632725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5797296293258429724353933 2173986109971911146632725)
              ·
                refine ⟨101905598904933334998409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2173986109971911146632725 101905598904933334998409)
                ·
                  rfl

theorem cell21_1339608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_1339608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339608 prefixEnd_1339608 := by exact prefixLift 1339608
  have htrace : WordTrace (prefixWord ++ tailWord_1339608) baseStart_1339608 baseEnd_1339608 := by
    simpa [prefixWord, tailWord_1339608, baseEnd_1339608] using wordTrace_append hprefix tailTrace_1339608
  have hstable : (prefixWord ++ tailWord_1339608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339608).length < 2 ^ (prefixWord ++ tailWord_1339608).sum := by decide
  have hdescent : baseEnd_1339608 < baseStart_1339608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339653 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 4]
def baseStart_1339653 : Nat := 118140960795 + 1339653 * 2 ^ 59
def prefixEnd_1339653 : Nat := 4983230072969 + 3 ^ 40 * 1339653 * 2
def baseEnd_1339653 : Nat := 305727066327889926745135

theorem tailTrace_1339653 : CollatzResearch.WordTrace tailWord_1339653 prefixEnd_1339653 305727066327889926745135 := by
  unfold tailWord_1339653
  simp only [CollatzResearch.WordTrace]
  refine ⟨48861159015673450362247613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32574106010448966908165075 48861159015673450362247613)
  ·
    refine ⟨18322934630877543885842855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48861159015673450362247613 18322934630877543885842855)
    ·
      refine ⟨27484401946316315828764283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18322934630877543885842855 27484401946316315828764283)
      ·
        refine ⟨41226602919474473743146425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27484401946316315828764283 41226602919474473743146425)
        ·
          refine ⟨30919952189605855307359819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41226602919474473743146425 30919952189605855307359819)
          ·
            refine ⟨46379928284408782961039729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30919952189605855307359819 46379928284408782961039729)
            ·
              refine ⟨34784946213306587220779797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46379928284408782961039729 34784946213306587220779797)
              ·
                refine ⟨1630544353748746275974053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34784946213306587220779797 1630544353748746275974053)
                ·
                  refine ⟨305727066327889926745135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630544353748746275974053 305727066327889926745135)
                  ·
                    rfl

theorem cell21_1339653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_1339653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339653 prefixEnd_1339653 := by exact prefixLift 1339653
  have htrace : WordTrace (prefixWord ++ tailWord_1339653) baseStart_1339653 baseEnd_1339653 := by
    simpa [prefixWord, tailWord_1339653, baseEnd_1339653] using wordTrace_append hprefix tailTrace_1339653
  have hstable : (prefixWord ++ tailWord_1339653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339653).length < 2 ^ (prefixWord ++ tailWord_1339653).sum := by decide
  have hdescent : baseEnd_1339653 < baseStart_1339653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339656 : List Nat := [2, 1, 3, 2, 3, 1, 2, 4, 3]
def baseStart_1339656 : Nat := 118140960795 + 1339656 * 2 ^ 59
def prefixEnd_1339656 : Nat := 4983230072969 + 3 ^ 40 * 1339656 * 2
def baseEnd_1339656 : Nat := 305727750968762588195129

theorem tailTrace_1339656 : CollatzResearch.WordTrace tailWord_1339656 prefixEnd_1339656 305727750968762588195129 := by
  unfold tailWord_1339656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24430634217331290937303411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32574178956441721249737881 24430634217331290937303411)
  ·
    refine ⟨36645951325996936405955117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24430634217331290937303411 36645951325996936405955117)
    ·
      refine ⟨13742231747248851152233169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36645951325996936405955117 13742231747248851152233169)
      ·
        refine ⟨10306673810436638364174877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13742231747248851152233169 10306673810436638364174877)
        ·
          refine ⟨3865002678913739386565579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10306673810436638364174877 3865002678913739386565579)
          ·
            refine ⟨5797504018370609079848369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3865002678913739386565579 5797504018370609079848369)
            ·
              refine ⟨4348128013777956809886277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5797504018370609079848369 4348128013777956809886277)
              ·
                refine ⟨815274002583366901853677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4348128013777956809886277 815274002583366901853677)
                ·
                  refine ⟨305727750968762588195129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815274002583366901853677 305727750968762588195129)
                  ·
                    rfl

theorem cell21_1339656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 4, 3].length) (baseStart_1339656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339656 prefixEnd_1339656 := by exact prefixLift 1339656
  have htrace : WordTrace (prefixWord ++ tailWord_1339656) baseStart_1339656 baseEnd_1339656 := by
    simpa [prefixWord, tailWord_1339656, baseEnd_1339656] using wordTrace_append hprefix tailTrace_1339656
  have hstable : (prefixWord ++ tailWord_1339656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339656).length < 2 ^ (prefixWord ++ tailWord_1339656).sum := by decide
  have hdescent : baseEnd_1339656 < baseStart_1339656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339684 : List Nat := [2, 3, 1, 3, 1, 3, 1, 7]
def baseStart_1339684 : Nat := 118140960795 + 1339684 * 2 ^ 59
def prefixEnd_1339684 : Nat := 4983230072969 + 3 ^ 40 * 1339684 * 2
def baseEnd_1339684 : Nat := 101911380316746920576135

theorem tailTrace_1339684 : CollatzResearch.WordTrace tailWord_1339684 prefixEnd_1339684 101911380316746920576135 := by
  unfold tailWord_1339684
  simp only [CollatzResearch.WordTrace]
  refine ⟨24431144839280571328313053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32574859785707428437750737 24431144839280571328313053)
  ·
    refine ⟨9161679314730214248117395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24431144839280571328313053 9161679314730214248117395)
    ·
      refine ⟨13742518972095321372176093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9161679314730214248117395 13742518972095321372176093)
      ·
        refine ⟨5153444614535745514566035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13742518972095321372176093 5153444614535745514566035)
        ·
          refine ⟨7730166921803618271849053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5153444614535745514566035 7730166921803618271849053)
          ·
            refine ⟨2898812595676356851943395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7730166921803618271849053 2898812595676356851943395)
            ·
              refine ⟨4348218893514535277915093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898812595676356851943395 4348218893514535277915093)
              ·
                refine ⟨101911380316746920576135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4348218893514535277915093 101911380316746920576135)
                ·
                  rfl

theorem cell21_1339684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_1339684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339684 prefixEnd_1339684 := by exact prefixLift 1339684
  have htrace : WordTrace (prefixWord ++ tailWord_1339684) baseStart_1339684 baseEnd_1339684 := by
    simpa [prefixWord, tailWord_1339684, baseEnd_1339684] using wordTrace_append hprefix tailTrace_1339684
  have hstable : (prefixWord ++ tailWord_1339684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339684).length < 2 ^ (prefixWord ++ tailWord_1339684).sum := by decide
  have hdescent : baseEnd_1339684 < baseStart_1339684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339690 : List Nat := [3, 1, 4, 2, 2, 2, 1, 3, 3]
def baseStart_1339690 : Nat := 118140960795 + 1339690 * 2 ^ 59
def prefixEnd_1339690 : Nat := 4983230072969 + 3 ^ 40 * 1339690 * 2
def baseEnd_1339690 : Nat := 305735510231986084628393

theorem tailTrace_1339690 : CollatzResearch.WordTrace tailWord_1339690 prefixEnd_1339690 305735510231986084628393 := by
  unfold tailWord_1339690
  simp only [CollatzResearch.WordTrace]
  refine ⟨12215627129134851420336131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32575005677692937120896349 12215627129134851420336131)
  ·
    refine ⟨18323440693702277130504197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12215627129134851420336131 18323440693702277130504197)
    ·
      refine ⟨3435645130069176961969537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18323440693702277130504197 3435645130069176961969537)
      ·
        refine ⟨2576733847551882721477153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3435645130069176961969537 2576733847551882721477153)
        ·
          refine ⟨1932550385663912041107865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576733847551882721477153 1932550385663912041107865)
          ·
            refine ⟨1449412789247934030830899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932550385663912041107865 1449412789247934030830899)
            ·
              refine ⟨2174119183871901046246349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449412789247934030830899 2174119183871901046246349)
              ·
                refine ⟨815294693951962892342381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174119183871901046246349 815294693951962892342381)
                ·
                  refine ⟨305735510231986084628393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815294693951962892342381 305735510231986084628393)
                  ·
                    rfl

theorem cell21_1339690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 3, 3].length) (baseStart_1339690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339690 prefixEnd_1339690 := by exact prefixLift 1339690
  have htrace : WordTrace (prefixWord ++ tailWord_1339690) baseStart_1339690 baseEnd_1339690 := by
    simpa [prefixWord, tailWord_1339690, baseEnd_1339690] using wordTrace_append hprefix tailTrace_1339690
  have hstable : (prefixWord ++ tailWord_1339690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339690).length < 2 ^ (prefixWord ++ tailWord_1339690).sum := by decide
  have hdescent : baseEnd_1339690 < baseStart_1339690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339715 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 3]
def baseStart_1339715 : Nat := 118140960795 + 1339715 * 2 ^ 59
def prefixEnd_1339715 : Nat := 4983230072969 + 3 ^ 40 * 1339715 * 2
def baseEnd_1339715 : Nat := 305741215572591596711675

theorem tailTrace_1339715 : CollatzResearch.WordTrace tailWord_1339715 prefixEnd_1339715 305741215572591596711675 := by
  unfold tailWord_1339715
  simp only [CollatzResearch.WordTrace]
  refine ⟨48863420341448834951004599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32575613560965889967336399 48863420341448834951004599)
  ·
    refine ⟨73295130512173252426506899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48863420341448834951004599 73295130512173252426506899)
    ·
      refine ⟨109942695768259878639760349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73295130512173252426506899 109942695768259878639760349)
      ·
        refine ⟨41228510913097454489910131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109942695768259878639760349 41228510913097454489910131)
        ·
          refine ⟨61842766369646181734865197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41228510913097454489910131 61842766369646181734865197)
          ·
            refine ⟨23191037388617318150574449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61842766369646181734865197 23191037388617318150574449)
            ·
              refine ⟨17393278041462988612930837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23191037388617318150574449 17393278041462988612930837)
              ·
                refine ⟨815309908193577591231133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17393278041462988612930837 815309908193577591231133)
                ·
                  refine ⟨305741215572591596711675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815309908193577591231133 305741215572591596711675)
                  ·
                    rfl

theorem cell21_1339715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 3].length) (baseStart_1339715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339715 prefixEnd_1339715 := by exact prefixLift 1339715
  have htrace : WordTrace (prefixWord ++ tailWord_1339715) baseStart_1339715 baseEnd_1339715 := by
    simpa [prefixWord, tailWord_1339715, baseEnd_1339715] using wordTrace_append hprefix tailTrace_1339715
  have hstable : (prefixWord ++ tailWord_1339715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339715).length < 2 ^ (prefixWord ++ tailWord_1339715).sum := by decide
  have hdescent : baseEnd_1339715 < baseStart_1339715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339743 : List Nat := [1, 1, 2, 3, 1, 2, 4, 7]
def baseStart_1339743 : Nat := 118140960795 + 1339743 * 2 ^ 59
def prefixEnd_1339743 : Nat := 4983230072969 + 3 ^ 40 * 1339743 * 2
def baseEnd_1339743 : Nat := 101915868518023256748317

theorem tailTrace_1339743 : CollatzResearch.WordTrace tailWord_1339743 prefixEnd_1339743 101915868518023256748317 := by
  unfold tailWord_1339743
  simp only [CollatzResearch.WordTrace]
  refine ⟨48864441585347395733023883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32576294390231597155349255 48864441585347395733023883)
  ·
    refine ⟨73296662378021093599535825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48864441585347395733023883 73296662378021093599535825)
    ·
      refine ⟨54972496783515820199651869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73296662378021093599535825 54972496783515820199651869)
      ·
        refine ⟨20614686293818432574869451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54972496783515820199651869 20614686293818432574869451)
        ·
          refine ⟨30922029440727648862304177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20614686293818432574869451 30922029440727648862304177)
          ·
            refine ⟨23191522080545736646728133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30922029440727648862304177 23191522080545736646728133)
            ·
              refine ⟨4348410390102325621261525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23191522080545736646728133 4348410390102325621261525)
              ·
                refine ⟨101915868518023256748317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4348410390102325621261525 101915868518023256748317)
                ·
                  rfl

theorem cell21_1339743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 7].length) (baseStart_1339743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339743 prefixEnd_1339743 := by exact prefixLift 1339743
  have htrace : WordTrace (prefixWord ++ tailWord_1339743) baseStart_1339743 baseEnd_1339743 := by
    simpa [prefixWord, tailWord_1339743, baseEnd_1339743] using wordTrace_append hprefix tailTrace_1339743
  have hstable : (prefixWord ++ tailWord_1339743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339743).length < 2 ^ (prefixWord ++ tailWord_1339743).sum := by decide
  have hdescent : baseEnd_1339743 < baseStart_1339743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339766 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_1339766 : Nat := 118140960795 + 1339766 * 2 ^ 59
def prefixEnd_1339766 : Nat := 4983230072969 + 3 ^ 40 * 1339766 * 2
def baseEnd_1339766 : Nat := 305752854467426841361571

theorem tailTrace_1339766 : CollatzResearch.WordTrace tailWord_1339766 prefixEnd_1339766 305752854467426841361571 := by
  unfold tailWord_1339766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3054080029016504416319447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32576853642842713774074101 3054080029016504416319447)
  ·
    refine ⟨4581120043524756624479171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3054080029016504416319447 4581120043524756624479171)
    ·
      refine ⟨6871680065287134936718757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4581120043524756624479171 6871680065287134936718757)
      ·
        refine ⟨1288440012241337800634767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6871680065287134936718757 1288440012241337800634767)
        ·
          refine ⟨1932660018362006700952151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1288440012241337800634767 1932660018362006700952151)
          ·
            refine ⟨2898990027543010051428227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1932660018362006700952151 2898990027543010051428227)
            ·
              refine ⟨4348485041314515077142341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2898990027543010051428227 4348485041314515077142341)
              ·
                refine ⟨815340945246471576964189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4348485041314515077142341 815340945246471576964189)
                ·
                  refine ⟨305752854467426841361571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815340945246471576964189 305752854467426841361571)
                  ·
                    rfl

theorem cell21_1339766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_1339766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339766 prefixEnd_1339766 := by exact prefixLift 1339766
  have htrace : WordTrace (prefixWord ++ tailWord_1339766) baseStart_1339766 baseEnd_1339766 := by
    simpa [prefixWord, tailWord_1339766, baseEnd_1339766] using wordTrace_append hprefix tailTrace_1339766
  have hstable : (prefixWord ++ tailWord_1339766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339766).length < 2 ^ (prefixWord ++ tailWord_1339766).sum := by decide
  have hdescent : baseEnd_1339766 < baseStart_1339766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339777 : List Nat := [1, 2, 4, 3, 1, 3, 1, 6]
def baseStart_1339777 : Nat := 118140960795 + 1339777 * 2 ^ 59
def prefixEnd_1339777 : Nat := 4983230072969 + 3 ^ 40 * 1339777 * 2
def baseEnd_1339777 : Nat := 101918454939097755559405

theorem tailTrace_1339777 : CollatzResearch.WordTrace tailWord_1339777 prefixEnd_1339777 101918454939097755559405 := by
  unfold tailWord_1339777
  simp only [CollatzResearch.WordTrace]
  refine ⟨48865681667224219539761585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32577121111482813026507723 48865681667224219539761585)
  ·
    refine ⟨36649261250418164654821189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48865681667224219539761585 36649261250418164654821189)
    ·
      refine ⟨6871736484453405872778973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36649261250418164654821189 6871736484453405872778973)
      ·
        refine ⟨2576901181670027202292115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6871736484453405872778973 2576901181670027202292115)
        ·
          refine ⟨3865351772505040803438173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2576901181670027202292115 3865351772505040803438173)
          ·
            refine ⟨1449506914689390301289315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3865351772505040803438173 1449506914689390301289315)
            ·
              refine ⟨2174260372034085451933973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449506914689390301289315 2174260372034085451933973)
              ·
                refine ⟨101918454939097755559405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2174260372034085451933973 101918454939097755559405)
                ·
                  rfl

theorem cell21_1339777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 6].length) (baseStart_1339777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339777 prefixEnd_1339777 := by exact prefixLift 1339777
  have htrace : WordTrace (prefixWord ++ tailWord_1339777) baseStart_1339777 baseEnd_1339777 := by
    simpa [prefixWord, tailWord_1339777, baseEnd_1339777] using wordTrace_append hprefix tailTrace_1339777
  have hstable : (prefixWord ++ tailWord_1339777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339777).length < 2 ^ (prefixWord ++ tailWord_1339777).sum := by decide
  have hdescent : baseEnd_1339777 < baseStart_1339777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339808 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_1339808 : Nat := 118140960795 + 1339808 * 2 ^ 59
def prefixEnd_1339808 : Nat := 4983230072969 + 3 ^ 40 * 1339808 * 2
def baseEnd_1339808 : Nat := 305762439439644101661485

theorem tailTrace_1339808 : CollatzResearch.WordTrace tailWord_1339808 prefixEnd_1339808 305762439439644101661485 := by
  unfold tailWord_1339808
  simp only [CollatzResearch.WordTrace]
  refine ⟨24433406165055955917070039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32577874886741274556093385 24433406165055955917070039)
  ·
    refine ⟨36650109247583933875605059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24433406165055955917070039 36650109247583933875605059)
    ·
      refine ⟨54975163871375900813407589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36650109247583933875605059 54975163871375900813407589)
      ·
        refine ⟨10307843225882981402513923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54975163871375900813407589 10307843225882981402513923)
        ·
          refine ⟨15461764838824472103770885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10307843225882981402513923 15461764838824472103770885)
          ·
            refine ⟨2899080907279588519457041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15461764838824472103770885 2899080907279588519457041)
            ·
              refine ⟨2174310680459691389592781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899080907279588519457041 2174310680459691389592781)
              ·
                refine ⟨815366505172384271097293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174310680459691389592781 815366505172384271097293)
                ·
                  refine ⟨305762439439644101661485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815366505172384271097293 305762439439644101661485)
                  ·
                    rfl

theorem cell21_1339808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_1339808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339808 prefixEnd_1339808 := by exact prefixLift 1339808
  have htrace : WordTrace (prefixWord ++ tailWord_1339808) baseStart_1339808 baseEnd_1339808 := by
    simpa [prefixWord, tailWord_1339808, baseEnd_1339808] using wordTrace_append hprefix tailTrace_1339808
  have hstable : (prefixWord ++ tailWord_1339808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339808).length < 2 ^ (prefixWord ++ tailWord_1339808).sum := by decide
  have hdescent : baseEnd_1339808 < baseStart_1339808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339850 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_1339850 : Nat := 118140960795 + 1339850 * 2 ^ 59
def prefixEnd_1339850 : Nat := 4983230072969 + 3 ^ 40 * 1339850 * 2
def baseEnd_1339850 : Nat := 305772024411861361961399

theorem tailTrace_1339850 : CollatzResearch.WordTrace tailWord_1339850 prefixEnd_1339850 305772024411861361961399 := by
  unfold tailWord_1339850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12217086048989938251792251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32578896130639835338112669 12217086048989938251792251)
  ·
    refine ⟨18325629073484907377688377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12217086048989938251792251 18325629073484907377688377)
    ·
      refine ⟨13744221805113680533266283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18325629073484907377688377 13744221805113680533266283)
      ·
        refine ⟨20616332707670520799899425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13744221805113680533266283 20616332707670520799899425)
        ·
          refine ⟨15462249530752890599924569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20616332707670520799899425 15462249530752890599924569)
          ·
            refine ⟨11596687148064667949943427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15462249530752890599924569 11596687148064667949943427)
            ·
              refine ⟨17395030722097001924915141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11596687148064667949943427 17395030722097001924915141)
              ·
                refine ⟨3261568260393187860921589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17395030722097001924915141 3261568260393187860921589)
                ·
                  refine ⟨305772024411861361961399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3261568260393187860921589 305772024411861361961399)
                  ·
                    rfl

theorem cell21_1339850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_1339850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339850 prefixEnd_1339850 := by exact prefixLift 1339850
  have htrace : WordTrace (prefixWord ++ tailWord_1339850) baseStart_1339850 baseEnd_1339850 := by
    simpa [prefixWord, tailWord_1339850, baseEnd_1339850] using wordTrace_append hprefix tailTrace_1339850
  have hstable : (prefixWord ++ tailWord_1339850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339850).length < 2 ^ (prefixWord ++ tailWord_1339850).sum := by decide
  have hdescent : baseEnd_1339850 < baseStart_1339850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339884 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 3]
def baseStart_1339884 : Nat := 118140960795 + 1339884 * 2 ^ 59
def prefixEnd_1339884 : Nat := 4983230072969 + 3 ^ 40 * 1339884 * 2
def baseEnd_1339884 : Nat := 305779783675084858394663

theorem tailTrace_1339884 : CollatzResearch.WordTrace tailWord_1339884 prefixEnd_1339884 305779783675084858394663 := by
  unfold tailWord_1339884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24434792138918288406953353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32579722851891051209271137 24434792138918288406953353)
  ·
    refine ⟨18326094104188716305215015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24434792138918288406953353 18326094104188716305215015)
    ·
      refine ⟨27489141156283074457822523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18326094104188716305215015 27489141156283074457822523)
      ·
        refine ⟨41233711734424611686733785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27489141156283074457822523 41233711734424611686733785)
        ·
          refine ⟨30925283800818458765050339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41233711734424611686733785 30925283800818458765050339)
          ·
            refine ⟨46387925701227688147575509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30925283800818458765050339 46387925701227688147575509)
            ·
              refine ⟨1087217008622523940958801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46387925701227688147575509 1087217008622523940958801)
              ·
                refine ⟨815412756466892955719101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087217008622523940958801 815412756466892955719101)
                ·
                  refine ⟨305779783675084858394663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815412756466892955719101 305779783675084858394663)
                  ·
                    rfl

theorem cell21_1339884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 3].length) (baseStart_1339884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339884 prefixEnd_1339884 := by exact prefixLift 1339884
  have htrace : WordTrace (prefixWord ++ tailWord_1339884) baseStart_1339884 baseEnd_1339884 := by
    simpa [prefixWord, tailWord_1339884, baseEnd_1339884] using wordTrace_append hprefix tailTrace_1339884
  have hstable : (prefixWord ++ tailWord_1339884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339884).length < 2 ^ (prefixWord ++ tailWord_1339884).sum := by decide
  have hdescent : baseEnd_1339884 < baseStart_1339884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1339957 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_1339957 : Nat := 118140960795 + 1339957 * 2 ^ 59
def prefixEnd_1339957 : Nat := 4983230072969 + 3 ^ 40 * 1339957 * 2
def baseEnd_1339957 : Nat := 305796443269652953677847

theorem tailTrace_1339957 : CollatzResearch.WordTrace tailWord_1339957 prefixEnd_1339957 305796443269652953677847 := by
  unfold tailWord_1339957
  simp only [CollatzResearch.WordTrace]
  refine ⟨48872246806572110281314125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32581497871048073520876083 48872246806572110281314125)
  ·
    refine ⟨18327092552464541355492797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48872246806572110281314125 18327092552464541355492797)
    ·
      refine ⟨6872659707174203008309799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18327092552464541355492797 6872659707174203008309799)
      ·
        refine ⟨10308989560761304512464699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6872659707174203008309799 10308989560761304512464699)
        ·
          refine ⟨15463484341141956768697049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10308989560761304512464699 15463484341141956768697049)
          ·
            refine ⟨11597613255856467576522787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15463484341141956768697049 11597613255856467576522787)
            ·
              refine ⟨17396419883784701364784181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11597613255856467576522787 17396419883784701364784181)
              ·
                refine ⟨1630914364104815752948517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17396419883784701364784181 1630914364104815752948517)
                ·
                  refine ⟨305796443269652953677847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1630914364104815752948517 305796443269652953677847)
                  ·
                    rfl

theorem cell21_1339957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_1339957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1339957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1339957 prefixEnd_1339957 := by exact prefixLift 1339957
  have htrace : WordTrace (prefixWord ++ tailWord_1339957) baseStart_1339957 baseEnd_1339957 := by
    simpa [prefixWord, tailWord_1339957, baseEnd_1339957] using wordTrace_append hprefix tailTrace_1339957
  have hstable : (prefixWord ++ tailWord_1339957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1339957).length < 2 ^ (prefixWord ++ tailWord_1339957).sum := by decide
  have hdescent : baseEnd_1339957 < baseStart_1339957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1339957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340022 : List Nat := [5, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1340022 : Nat := 118140960795 + 1340022 * 2 ^ 59
def prefixEnd_1340022 : Nat := 4983230072969 + 3 ^ 40 * 1340022 * 2
def baseEnd_1340022 : Nat := 101937092385075761698127

theorem tailTrace_1340022 : CollatzResearch.WordTrace tailWord_1340022 prefixEnd_1340022 101937092385075761698127 := by
  unfold tailWord_1340022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3054663596958539148901895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32583078367557750921620213 3054663596958539148901895)
  ·
    refine ⟨4581995395437808723352843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3054663596958539148901895 4581995395437808723352843)
    ·
      refine ⟨6872993093156713085029265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4581995395437808723352843 6872993093156713085029265)
      ·
        refine ⟨5154744819867534813771949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6872993093156713085029265 5154744819867534813771949)
        ·
          refine ⟨1933029307450325555164481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5154744819867534813771949 1933029307450325555164481)
          ·
            refine ⟨1449771980587744166373361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1933029307450325555164481 1449771980587744166373361)
            ·
              refine ⟨1087328985440808124780021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1449771980587744166373361 1087328985440808124780021)
              ·
                refine ⟨101937092385075761698127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1087328985440808124780021 101937092385075761698127)
                ·
                  rfl

theorem cell21_1340022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1340022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340022 prefixEnd_1340022 := by exact prefixLift 1340022
  have htrace : WordTrace (prefixWord ++ tailWord_1340022) baseStart_1340022 baseEnd_1340022 := by
    simpa [prefixWord, tailWord_1340022, baseEnd_1340022] using wordTrace_append hprefix tailTrace_1340022
  have hstable : (prefixWord ++ tailWord_1340022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340022).length < 2 ^ (prefixWord ++ tailWord_1340022).sum := by decide
  have hdescent : baseEnd_1340022 < baseStart_1340022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340036 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 3]
def baseStart_1340036 : Nat := 118140960795 + 1340036 * 2 ^ 59
def prefixEnd_1340036 : Nat := 4983230072969 + 3 ^ 40 * 1340036 * 2
def baseEnd_1340036 : Nat := 305814472145966371861019

theorem tailTrace_1340036 : CollatzResearch.WordTrace tailWord_1340036 prefixEnd_1340036 305814472145966371861019 := by
  unfold tailWord_1340036
  simp only [CollatzResearch.WordTrace]
  refine ⟨24437564086642953386719981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32583418782190604515626641 24437564086642953386719981)
  ·
    refine ⟨9164086532491107520019993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24437564086642953386719981 9164086532491107520019993)
    ·
      refine ⟨6873064899368330640014995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9164086532491107520019993 6873064899368330640014995)
      ·
        refine ⟨10309597349052495960022493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6873064899368330640014995 10309597349052495960022493)
        ·
          refine ⟨3866099005894685985008435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10309597349052495960022493 3866099005894685985008435)
          ·
            refine ⟨5799148508842028977512653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866099005894685985008435 5799148508842028977512653)
            ·
              refine ⟨2174680690815760866567245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5799148508842028977512653 2174680690815760866567245)
              ·
                refine ⟨815505259055910324962717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174680690815760866567245 815505259055910324962717)
                ·
                  refine ⟨305814472145966371861019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815505259055910324962717 305814472145966371861019)
                  ·
                    rfl

theorem cell21_1340036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_1340036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340036 prefixEnd_1340036 := by exact prefixLift 1340036
  have htrace : WordTrace (prefixWord ++ tailWord_1340036) baseStart_1340036 baseEnd_1340036 := by
    simpa [prefixWord, tailWord_1340036, baseEnd_1340036] using wordTrace_append hprefix tailTrace_1340036
  have hstable : (prefixWord ++ tailWord_1340036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340036).length < 2 ^ (prefixWord ++ tailWord_1340036).sum := by decide
  have hdescent : baseEnd_1340036 < baseStart_1340036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340064 : List Nat := [2, 1, 1, 4, 4, 1, 2, 6]
def baseStart_1340064 : Nat := 118140960795 + 1340064 * 2 ^ 59
def prefixEnd_1340064 : Nat := 4983230072969 + 3 ^ 40 * 1340064 * 2
def baseEnd_1340064 : Nat := 101940287375814848464765

theorem tailTrace_1340064 : CollatzResearch.WordTrace tailWord_1340064 prefixEnd_1340064 101940287375814848464765 := by
  unfold tailWord_1340064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24438074708592233777729623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32584099611456311703639497 24438074708592233777729623)
  ·
    refine ⟨36657112062888350666594435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24438074708592233777729623 36657112062888350666594435)
    ·
      refine ⟨54985668094332525999891653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36657112062888350666594435 54985668094332525999891653)
      ·
        refine ⟨10309812767687348624979685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54985668094332525999891653 10309812767687348624979685)
        ·
          refine ⟨1933089893941377867183691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10309812767687348624979685 1933089893941377867183691)
          ·
            refine ⟨2899634840912066800775537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933089893941377867183691 2899634840912066800775537)
            ·
              refine ⟨2174726130684050100581653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2899634840912066800775537 2174726130684050100581653)
              ·
                refine ⟨101940287375814848464765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2174726130684050100581653 101940287375814848464765)
                ·
                  rfl

theorem cell21_1340064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_1340064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340064 prefixEnd_1340064 := by exact prefixLift 1340064
  have htrace : WordTrace (prefixWord ++ tailWord_1340064) baseStart_1340064 baseEnd_1340064 := by
    simpa [prefixWord, tailWord_1340064, baseEnd_1340064] using wordTrace_append hprefix tailTrace_1340064
  have hstable : (prefixWord ++ tailWord_1340064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340064).length < 2 ^ (prefixWord ++ tailWord_1340064).sum := by decide
  have hdescent : baseEnd_1340064 < baseStart_1340064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340137 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_1340137 : Nat := 118140960795 + 1340137 * 2 ^ 59
def prefixEnd_1340137 : Nat := 4983230072969 + 3 ^ 40 * 1340137 * 2
def baseEnd_1340137 : Nat := 305837521722012640677479

theorem tailTrace_1340137 : CollatzResearch.WordTrace tailWord_1340137 prefixEnd_1340137 305837521722012640677479 := by
  unfold tailWord_1340137
  simp only [CollatzResearch.WordTrace]
  refine ⟨48878811945920001022866665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32585874630613334015244443 48878811945920001022866665)
  ·
    refine ⟨36659108959440000767149999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48878811945920001022866665 36659108959440000767149999)
    ·
      refine ⟨54988663439160001150724999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36659108959440000767149999 54988663439160001150724999)
      ·
        refine ⟨82482995158740001726087499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54988663439160001150724999 82482995158740001726087499)
        ·
          refine ⟨123724492738110002589131249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82482995158740001726087499 123724492738110002589131249)
          ·
            refine ⟨92793369553582501941848437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123724492738110002589131249 92793369553582501941848437)
            ·
              refine ⟨8699378395648359557048291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92793369553582501941848437 8699378395648359557048291)
              ·
                refine ⟨13049067593472539335572437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8699378395648359557048291 13049067593472539335572437)
                ·
                  refine ⟨305837521722012640677479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13049067593472539335572437 305837521722012640677479)
                  ·
                    rfl

theorem cell21_1340137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_1340137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340137 prefixEnd_1340137 := by exact prefixLift 1340137
  have htrace : WordTrace (prefixWord ++ tailWord_1340137) baseStart_1340137 baseEnd_1340137 := by
    simpa [prefixWord, tailWord_1340137, baseEnd_1340137] using wordTrace_append hprefix tailTrace_1340137
  have hstable : (prefixWord ++ tailWord_1340137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340137).length < 2 ^ (prefixWord ++ tailWord_1340137).sum := by decide
  have hdescent : baseEnd_1340137 < baseStart_1340137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340278 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1340278 : Nat := 118140960795 + 1340278 * 2 ^ 59
def prefixEnd_1340278 : Nat := 4983230072969 + 3 ^ 40 * 1340278 * 2
def baseEnd_1340278 : Nat := 305869699843027728827191

theorem tailTrace_1340278 : CollatzResearch.WordTrace tailWord_1340278 prefixEnd_1340278 305869699843027728827191 := by
  unfold tailWord_1340278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055247164900573881484343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32589303092272788069166325 3055247164900573881484343)
  ·
    refine ⟨4582870747350860822226515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055247164900573881484343 4582870747350860822226515)
    ·
      refine ⟨6874306121026291233339773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4582870747350860822226515 6874306121026291233339773)
      ·
        refine ⟨2577864795384859212502415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6874306121026291233339773 2577864795384859212502415)
        ·
          refine ⟨3866797193077288818753623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577864795384859212502415 3866797193077288818753623)
          ·
            refine ⟨5800195789615933228130435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866797193077288818753623 5800195789615933228130435)
            ·
              refine ⟨8700293684423899842195653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5800195789615933228130435 8700293684423899842195653)
              ·
                refine ⟨1631305065829481220411685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8700293684423899842195653 1631305065829481220411685)
                ·
                  refine ⟨305869699843027728827191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1631305065829481220411685 305869699843027728827191)
                  ·
                    rfl

theorem cell21_1340278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1340278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340278 prefixEnd_1340278 := by exact prefixLift 1340278
  have htrace : WordTrace (prefixWord ++ tailWord_1340278) baseStart_1340278 baseEnd_1340278 := by
    simpa [prefixWord, tailWord_1340278, baseEnd_1340278] using wordTrace_append hprefix tailTrace_1340278
  have hstable : (prefixWord ++ tailWord_1340278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340278).length < 2 ^ (prefixWord ++ tailWord_1340278).sum := by decide
  have hdescent : baseEnd_1340278 < baseStart_1340278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340337 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 6]
def baseStart_1340337 : Nat := 118140960795 + 1340337 * 2 ^ 59
def prefixEnd_1340337 : Nat := 4983230072969 + 3 ^ 40 * 1340337 * 2
def baseEnd_1340337 : Nat := 305883164446856737343737

theorem tailTrace_1340337 : CollatzResearch.WordTrace tailWord_1340337 prefixEnd_1340337 305883164446856737343737 := by
  unfold tailWord_1340337
  simp only [CollatzResearch.WordTrace]
  refine ⟨48886106545195435180147265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32590737696796956786764843 48886106545195435180147265)
  ·
    refine ⟨36664579908896576385110449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48886106545195435180147265 36664579908896576385110449)
    ·
      refine ⟨27498434931672432288832837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36664579908896576385110449 27498434931672432288832837)
      ·
        refine ⟨5155956549688581054156157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27498434931672432288832837 5155956549688581054156157)
        ·
          refine ⟨1933483706133217895308559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5155956549688581054156157 1933483706133217895308559)
          ·
            refine ⟨2900225559199826842962839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1933483706133217895308559 2900225559199826842962839)
            ·
              refine ⟨4350338338799740264444259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2900225559199826842962839 4350338338799740264444259)
              ·
                refine ⟨6525507508199610396666389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4350338338799740264444259 6525507508199610396666389)
                ·
                  refine ⟨305883164446856737343737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6525507508199610396666389 305883164446856737343737)
                  ·
                    rfl

theorem cell21_1340337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_1340337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340337 prefixEnd_1340337 := by exact prefixLift 1340337
  have htrace : WordTrace (prefixWord ++ tailWord_1340337) baseStart_1340337 baseEnd_1340337 := by
    simpa [prefixWord, tailWord_1340337, baseEnd_1340337] using wordTrace_append hprefix tailTrace_1340337
  have hstable : (prefixWord ++ tailWord_1340337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340337).length < 2 ^ (prefixWord ++ tailWord_1340337).sum := by decide
  have hdescent : baseEnd_1340337 < baseStart_1340337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340340 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1340340 : Nat := 118140960795 + 1340340 * 2 ^ 59
def prefixEnd_1340340 : Nat := 4983230072969 + 3 ^ 40 * 1340340 * 2
def baseEnd_1340340 : Nat := 305883849087729398793731

theorem tailTrace_1340340 : CollatzResearch.WordTrace tailWord_1340340 prefixEnd_1340340 305883849087729398793731 := by
  unfold tailWord_1340340
  simp only [CollatzResearch.WordTrace]
  refine ⟨24443107982092283346253237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32590810642789711128337649 24443107982092283346253237)
  ·
    refine ⟨2291541373321151563711241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24443107982092283346253237 2291541373321151563711241)
    ·
      refine ⟨1718656029990863672783431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2291541373321151563711241 1718656029990863672783431)
      ·
        refine ⟨2577984044986295509175147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718656029990863672783431 2577984044986295509175147)
        ·
          refine ⟨3866976067479443263762721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577984044986295509175147 3866976067479443263762721)
          ·
            refine ⟨2900232050609582447822041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866976067479443263762721 2900232050609582447822041)
            ·
              refine ⟨2175174037957186835866531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900232050609582447822041 2175174037957186835866531)
              ·
                refine ⟨3262761056935780253799797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175174037957186835866531 3262761056935780253799797)
                ·
                  refine ⟨305883849087729398793731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3262761056935780253799797 305883849087729398793731)
                  ·
                    rfl

theorem cell21_1340340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1340340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340340 prefixEnd_1340340 := by exact prefixLift 1340340
  have htrace : WordTrace (prefixWord ++ tailWord_1340340) baseStart_1340340 baseEnd_1340340 := by
    simpa [prefixWord, tailWord_1340340, baseEnd_1340340] using wordTrace_append hprefix tailTrace_1340340
  have hstable : (prefixWord ++ tailWord_1340340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340340).length < 2 ^ (prefixWord ++ tailWord_1340340).sum := by decide
  have hdescent : baseEnd_1340340 < baseStart_1340340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340405 : List Nat := [1, 3, 5, 2, 2, 1, 2, 1, 4]
def baseStart_1340405 : Nat := 118140960795 + 1340405 * 2 ^ 59
def prefixEnd_1340405 : Nat := 4983230072969 + 3 ^ 40 * 1340405 * 2
def baseEnd_1340405 : Nat := 305898682973303730210265

theorem tailTrace_1340405 : CollatzResearch.WordTrace tailWord_1340405 prefixEnd_1340405 305898682973303730210265 := by
  unfold tailWord_1340405
  simp only [CollatzResearch.WordTrace]
  refine ⟨48888586708949082793622669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32592391139299388529081779 48888586708949082793622669)
  ·
    refine ⟨18333220015855906047608501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48888586708949082793622669 18333220015855906047608501)
    ·
      refine ⟨1718739376486491191963297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18333220015855906047608501 1718739376486491191963297)
      ·
        refine ⟨1289054532364868393972473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1718739376486491191963297 1289054532364868393972473)
        ·
          refine ⟨966790899273651295479355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289054532364868393972473 966790899273651295479355)
          ·
            refine ⟨1450186348910476943219033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966790899273651295479355 1450186348910476943219033)
            ·
              refine ⟨1087639761682857707414275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450186348910476943219033 1087639761682857707414275)
              ·
                refine ⟨1631459642524286561121413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1087639761682857707414275 1631459642524286561121413)
                ·
                  refine ⟨305898682973303730210265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1631459642524286561121413 305898682973303730210265)
                  ·
                    rfl

theorem cell21_1340405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_1340405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340405 prefixEnd_1340405 := by exact prefixLift 1340405
  have htrace : WordTrace (prefixWord ++ tailWord_1340405) baseStart_1340405 baseEnd_1340405 := by
    simpa [prefixWord, tailWord_1340405, baseEnd_1340405] using wordTrace_append hprefix tailTrace_1340405
  have hstable : (prefixWord ++ tailWord_1340405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340405).length < 2 ^ (prefixWord ++ tailWord_1340405).sum := by decide
  have hdescent : baseEnd_1340405 < baseStart_1340405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340534 : List Nat := [5, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1340534 : Nat := 118140960795 + 1340534 * 2 ^ 59
def prefixEnd_1340534 : Nat := 4983230072969 + 3 ^ 40 * 1340534 * 2
def baseEnd_1340534 : Nat := 305928122530828172560001

theorem tailTrace_1340534 : CollatzResearch.WordTrace tailWord_1340534 prefixEnd_1340534 305928122530828172560001 := by
  unfold tailWord_1340534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055830732842608614066791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32595527816987825216712437 3055830732842608614066791)
  ·
    refine ⟨4583746099263912921100187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055830732842608614066791 4583746099263912921100187)
    ·
      refine ⟨6875619148895869381650281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4583746099263912921100187 6875619148895869381650281)
      ·
        refine ⟨5156714361671902036237711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6875619148895869381650281 5156714361671902036237711)
        ·
          refine ⟨7735071542507853054356567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156714361671902036237711 7735071542507853054356567)
          ·
            refine ⟨11602607313761779581534851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735071542507853054356567 11602607313761779581534851)
            ·
              refine ⟨17403910970642669372302277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11602607313761779581534851 17403910970642669372302277)
              ·
                refine ⟨3263233306995500507306677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17403910970642669372302277 3263233306995500507306677)
                ·
                  refine ⟨305928122530828172560001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263233306995500507306677 305928122530828172560001)
                  ·
                    rfl

theorem cell21_1340534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1340534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340534 prefixEnd_1340534 := by exact prefixLift 1340534
  have htrace : WordTrace (prefixWord ++ tailWord_1340534) baseStart_1340534 baseEnd_1340534 := by
    simpa [prefixWord, tailWord_1340534, baseEnd_1340534] using wordTrace_append hprefix tailTrace_1340534
  have hstable : (prefixWord ++ tailWord_1340534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340534).length < 2 ^ (prefixWord ++ tailWord_1340534).sum := by decide
  have hdescent : baseEnd_1340534 < baseStart_1340534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340537 : List Nat := [1, 2, 1, 3, 6, 1, 2, 5]
def baseStart_1340537 : Nat := 118140960795 + 1340537 * 2 ^ 59
def prefixEnd_1340537 : Nat := 4983230072969 + 3 ^ 40 * 1340537 * 2
def baseEnd_1340537 : Nat := 101976269057233611336665

theorem tailTrace_1340537 : CollatzResearch.WordTrace tailWord_1340537 prefixEnd_1340537 101976269057233611336665 := by
  unfold tailWord_1340537
  simp only [CollatzResearch.WordTrace]
  refine ⟨48893401144470869337427865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32595600762980579558285243 48893401144470869337427865)
  ·
    refine ⟨36670050858353152003070899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48893401144470869337427865 36670050858353152003070899)
    ·
      refine ⟨55005076287529728004606349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36670050858353152003070899 55005076287529728004606349)
      ·
        refine ⟨20626903607823648001727381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55005076287529728004606349 20626903607823648001727381)
        ·
          refine ⟨966886106616733500080971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20626903607823648001727381 966886106616733500080971)
          ·
            refine ⟨1450329159925100250121457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966886106616733500080971 1450329159925100250121457)
            ·
              refine ⟨1087746869943825187591093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450329159925100250121457 1087746869943825187591093)
              ·
                refine ⟨101976269057233611336665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1087746869943825187591093 101976269057233611336665)
                ·
                  rfl

theorem cell21_1340537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 5].length) (baseStart_1340537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340537 prefixEnd_1340537 := by exact prefixLift 1340537
  have htrace : WordTrace (prefixWord ++ tailWord_1340537) baseStart_1340537 baseEnd_1340537 := by
    simpa [prefixWord, tailWord_1340537, baseEnd_1340537] using wordTrace_append hprefix tailTrace_1340537
  have hstable : (prefixWord ++ tailWord_1340537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340537).length < 2 ^ (prefixWord ++ tailWord_1340537).sum := by decide
  have hdescent : baseEnd_1340537 < baseStart_1340537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340548 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1340548 : Nat := 118140960795 + 1340548 * 2 ^ 59
def prefixEnd_1340548 : Nat := 4983230072969 + 3 ^ 40 * 1340548 * 2
def baseEnd_1340548 : Nat := 305931317521567259326639

theorem tailTrace_1340548 : CollatzResearch.WordTrace tailWord_1340548 prefixEnd_1340548 305931317521567259326639 := by
  unfold tailWord_1340548
  simp only [CollatzResearch.WordTrace]
  refine ⟨24446901173715509108039149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32595868231620678810718865 24446901173715509108039149)
  ·
    refine ⟨9167587940143315915514681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24446901173715509108039149 9167587940143315915514681)
    ·
      refine ⟨6875690955107486936636011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9167587940143315915514681 6875690955107486936636011)
      ·
        refine ⟨10313536432661230404954017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6875690955107486936636011 10313536432661230404954017)
        ·
          refine ⟨7735152324495922803715513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10313536432661230404954017 7735152324495922803715513)
          ·
            refine ⟨5801364243371942102786635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7735152324495922803715513 5801364243371942102786635)
            ·
              refine ⟨8702046365057913154179953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801364243371942102786635 8702046365057913154179953)
              ·
                refine ⟨6526534773793434865634965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702046365057913154179953 6526534773793434865634965)
                ·
                  refine ⟨305931317521567259326639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6526534773793434865634965 305931317521567259326639)
                  ·
                    rfl

theorem cell21_1340548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1340548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340548 prefixEnd_1340548 := by exact prefixLift 1340548
  have htrace : WordTrace (prefixWord ++ tailWord_1340548) baseStart_1340548 baseEnd_1340548 := by
    simpa [prefixWord, tailWord_1340548, baseEnd_1340548] using wordTrace_append hprefix tailTrace_1340548
  have hstable : (prefixWord ++ tailWord_1340548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340548).length < 2 ^ (prefixWord ++ tailWord_1340548).sum := by decide
  have hdescent : baseEnd_1340548 < baseStart_1340548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340568 : List Nat := [2, 1, 2, 4, 2, 2, 3, 2, 3]
def baseStart_1340568 : Nat := 118140960795 + 1340568 * 2 ^ 59
def prefixEnd_1340568 : Nat := 4983230072969 + 3 ^ 40 * 1340568 * 2
def baseEnd_1340568 : Nat := 305935881794051668993265

theorem tailTrace_1340568 : CollatzResearch.WordTrace tailWord_1340568 prefixEnd_1340568 305935881794051668993265 := by
  unfold tailWord_1340568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24447265903679280815903179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32596354538239041087870905 24447265903679280815903179)
  ·
    refine ⟨36670898855518921223854769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24447265903679280815903179 36670898855518921223854769)
    ·
      refine ⟨27503174141639190917891077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36670898855518921223854769 27503174141639190917891077)
      ·
        refine ⟨5156845151557348297104577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27503174141639190917891077 5156845151557348297104577)
        ·
          refine ⟨3867633863668011222828433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5156845151557348297104577 3867633863668011222828433)
          ·
            refine ⟨2900725397751008417121325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3867633863668011222828433 2900725397751008417121325)
            ·
              refine ⟨1087772024156628156420497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2900725397751008417121325 1087772024156628156420497)
              ·
                refine ⟨815829018117471117315373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1087772024156628156420497 815829018117471117315373)
                ·
                  refine ⟨305935881794051668993265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 815829018117471117315373 305935881794051668993265)
                  ·
                    rfl

theorem cell21_1340568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2, 3].length) (baseStart_1340568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340568 prefixEnd_1340568 := by exact prefixLift 1340568
  have htrace : WordTrace (prefixWord ++ tailWord_1340568) baseStart_1340568 baseEnd_1340568 := by
    simpa [prefixWord, tailWord_1340568, baseEnd_1340568] using wordTrace_append hprefix tailTrace_1340568
  have hstable : (prefixWord ++ tailWord_1340568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340568).length < 2 ^ (prefixWord ++ tailWord_1340568).sum := by decide
  have hdescent : baseEnd_1340568 < baseStart_1340568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340607 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 8]
def baseStart_1340607 : Nat := 118140960795 + 1340607 * 2 ^ 59
def prefixEnd_1340607 : Nat := 4983230072969 + 3 ^ 40 * 1340607 * 2
def baseEnd_1340607 : Nat := 305944782125396267843185

theorem tailTrace_1340607 : CollatzResearch.WordTrace tailWord_1340607 prefixEnd_1340607 305944782125396267843185 := by
  unfold tailWord_1340607
  simp only [CollatzResearch.WordTrace]
  refine ⟨48895954254217271292476075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32597302836144847528317383 48895954254217271292476075)
  ·
    refine ⟨73343931381325906938714113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48895954254217271292476075 73343931381325906938714113)
    ·
      refine ⟨55007948535994430204035585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73343931381325906938714113 55007948535994430204035585)
      ·
        refine ⟨41255961401995822653026689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55007948535994430204035585 41255961401995822653026689)
        ·
          refine ⟨30941971051496866989770017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41255961401995822653026689 30941971051496866989770017)
          ·
            refine ⟨23206478288622650242327513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30941971051496866989770017 23206478288622650242327513)
            ·
              refine ⟨17404858716466987681745635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23206478288622650242327513 17404858716466987681745635)
              ·
                refine ⟨26107288074700481522618453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17404858716466987681745635 26107288074700481522618453)
                ·
                  refine ⟨305944782125396267843185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26107288074700481522618453 305944782125396267843185)
                  ·
                    rfl

theorem cell21_1340607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 8].length) (baseStart_1340607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340607 prefixEnd_1340607 := by exact prefixLift 1340607
  have htrace : WordTrace (prefixWord ++ tailWord_1340607) baseStart_1340607 baseEnd_1340607 := by
    simpa [prefixWord, tailWord_1340607, baseEnd_1340607] using wordTrace_append hprefix tailTrace_1340607
  have hstable : (prefixWord ++ tailWord_1340607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340607).length < 2 ^ (prefixWord ++ tailWord_1340607).sum := by decide
  have hdescent : baseEnd_1340607 < baseStart_1340607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340630 : List Nat := [5, 2, 1, 2, 3, 1, 1, 6]
def baseStart_1340630 : Nat := 118140960795 + 1340630 * 2 ^ 59
def prefixEnd_1340630 : Nat := 4983230072969 + 3 ^ 40 * 1340630 * 2
def baseEnd_1340630 : Nat := 101983343679584446319935

theorem tailTrace_1340630 : CollatzResearch.WordTrace tailWord_1340630 prefixEnd_1340630 101983343679584446319935 := by
  unfold tailWord_1340630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056049570820871638785209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32597862088755964147042229 3056049570820871638785209)
  ·
    refine ⟨2292037178115653729088907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3056049570820871638785209 2292037178115653729088907)
    ·
      refine ⟨3438055767173480593633361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292037178115653729088907 3438055767173480593633361)
      ·
        refine ⟨2578541825380110445225021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438055767173480593633361 2578541825380110445225021)
        ·
          refine ⟨966953184517541416959383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2578541825380110445225021 966953184517541416959383)
          ·
            refine ⟨1450429776776312125439075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966953184517541416959383 1450429776776312125439075)
            ·
              refine ⟨2175644665164468188158613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450429776776312125439075 2175644665164468188158613)
              ·
                refine ⟨101983343679584446319935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2175644665164468188158613 101983343679584446319935)
                ·
                  rfl

theorem cell21_1340630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_1340630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340630 prefixEnd_1340630 := by exact prefixLift 1340630
  have htrace : WordTrace (prefixWord ++ tailWord_1340630) baseStart_1340630 baseEnd_1340630 := by
    simpa [prefixWord, tailWord_1340630, baseEnd_1340630] using wordTrace_append hprefix tailTrace_1340630
  have hstable : (prefixWord ++ tailWord_1340630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340630).length < 2 ^ (prefixWord ++ tailWord_1340630).sum := by decide
  have hdescent : baseEnd_1340630 < baseStart_1340630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340686 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1340686 : Nat := 118140960795 + 1340686 * 2 ^ 59
def prefixEnd_1340686 : Nat := 4983230072969 + 3 ^ 40 * 1340686 * 2
def baseEnd_1340686 : Nat := 305962811001709686026357

theorem tailTrace_1340686 : CollatzResearch.WordTrace tailWord_1340686 prefixEnd_1340686 305962811001709686026357 := by
  unfold tailWord_1340686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112354452616383473075239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32599223747287378523067941 6112354452616383473075239)
  ·
    refine ⟨9168531678924575209612859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6112354452616383473075239 9168531678924575209612859)
    ·
      refine ⟨13752797518386862814419289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9168531678924575209612859 13752797518386862814419289)
      ·
        refine ⟨10314598138790147110814467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13752797518386862814419289 10314598138790147110814467)
        ·
          refine ⟨15471897208185220666221701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314598138790147110814467 15471897208185220666221701)
          ·
            refine ⟨2900980726534728874916569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15471897208185220666221701 2900980726534728874916569)
            ·
              refine ⟨2175735544901046656187427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2900980726534728874916569 2175735544901046656187427)
              ·
                refine ⟨3263603317351569984281141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175735544901046656187427 3263603317351569984281141)
                ·
                  refine ⟨305962811001709686026357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263603317351569984281141 305962811001709686026357)
                  ·
                    rfl

theorem cell21_1340686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1340686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340686 prefixEnd_1340686 := by exact prefixLift 1340686
  have htrace : WordTrace (prefixWord ++ tailWord_1340686) baseStart_1340686 baseEnd_1340686 := by
    simpa [prefixWord, tailWord_1340686, baseEnd_1340686] using wordTrace_append hprefix tailTrace_1340686
  have hstable : (prefixWord ++ tailWord_1340686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340686).length < 2 ^ (prefixWord ++ tailWord_1340686).sum := by decide
  have hdescent : baseEnd_1340686 < baseStart_1340686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340700 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 4]
def baseStart_1340700 : Nat := 118140960795 + 1340700 * 2 ^ 59
def prefixEnd_1340700 : Nat := 4983230072969 + 3 ^ 40 * 1340700 * 2
def baseEnd_1340700 : Nat := 305966005992448772792995

theorem tailTrace_1340700 : CollatzResearch.WordTrace tailWord_1340700 prefixEnd_1340700 305966005992448772792995 := by
  unfold tailWord_1340700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24449673121440174087805777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32599564161920232117074369 24449673121440174087805777)
  ·
    refine ⟨18337254841080130565854333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24449673121440174087805777 18337254841080130565854333)
    ·
      refine ⟨6876470565405048962195375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18337254841080130565854333 6876470565405048962195375)
      ·
        refine ⟨10314705848107573443293063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876470565405048962195375 10314705848107573443293063)
        ·
          refine ⟨15472058772161360164939595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314705848107573443293063 15472058772161360164939595)
          ·
            refine ⟨23208088158242040247409393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15472058772161360164939595 23208088158242040247409393)
            ·
              refine ⟨17406066118681530185557045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23208088158242040247409393 17406066118681530185557045)
              ·
                refine ⟨1631818698626393454895973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17406066118681530185557045 1631818698626393454895973)
                ·
                  refine ⟨305966005992448772792995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1631818698626393454895973 305966005992448772792995)
                  ·
                    rfl

theorem cell21_1340700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 4].length) (baseStart_1340700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340700 prefixEnd_1340700 := by exact prefixLift 1340700
  have htrace : WordTrace (prefixWord ++ tailWord_1340700) baseStart_1340700 baseEnd_1340700 := by
    simpa [prefixWord, tailWord_1340700, baseEnd_1340700] using wordTrace_append hprefix tailTrace_1340700
  have hstable : (prefixWord ++ tailWord_1340700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340700).length < 2 ^ (prefixWord ++ tailWord_1340700).sum := by decide
  have hdescent : baseEnd_1340700 < baseStart_1340700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340717 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1340717 : Nat := 118140960795 + 1340717 * 2 ^ 59
def prefixEnd_1340717 : Nat := 4983230072969 + 3 ^ 40 * 1340717 * 2
def baseEnd_1340717 : Nat := 305969885624060521009627

theorem tailTrace_1340717 : CollatzResearch.WordTrace tailWord_1340717 prefixEnd_1340717 305969885624060521009627 := by
  unfold tailWord_1340717
  simp only [CollatzResearch.WordTrace]
  refine ⟨48899966283818760078980405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32599977522545840052653603 48899966283818760078980405)
  ·
    refine ⟨4584371839108008757404413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48899966283818760078980405 4584371839108008757404413)
    ·
      refine ⟨1719139439665503284026655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4584371839108008757404413 1719139439665503284026655)
      ·
        refine ⟨2578709159498254926039983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1719139439665503284026655 2578709159498254926039983)
        ·
          refine ⟨3868063739247382389059975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2578709159498254926039983 3868063739247382389059975)
          ·
            refine ⟨5802095608871073583589963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868063739247382389059975 5802095608871073583589963)
            ·
              refine ⟨8703143413306610375384945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802095608871073583589963 8703143413306610375384945)
              ·
                refine ⟨6527357559979957781538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8703143413306610375384945 6527357559979957781538709)
                ·
                  refine ⟨305969885624060521009627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527357559979957781538709 305969885624060521009627)
                  ·
                    rfl

theorem cell21_1340717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1340717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340717 prefixEnd_1340717 := by exact prefixLift 1340717
  have htrace : WordTrace (prefixWord ++ tailWord_1340717) baseStart_1340717 baseEnd_1340717 := by
    simpa [prefixWord, tailWord_1340717, baseEnd_1340717] using wordTrace_append hprefix tailTrace_1340717
  have hstable : (prefixWord ++ tailWord_1340717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340717).length < 2 ^ (prefixWord ++ tailWord_1340717).sum := by decide
  have hdescent : baseEnd_1340717 < baseStart_1340717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340745 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 5]
def baseStart_1340745 : Nat := 118140960795 + 1340745 * 2 ^ 59
def prefixEnd_1340745 : Nat := 4983230072969 + 3 ^ 40 * 1340745 * 2
def baseEnd_1340745 : Nat := 305976275605538694542903

theorem tailTrace_1340745 : CollatzResearch.WordTrace tailWord_1340745 prefixEnd_1340745 305976275605538694542903 := by
  unfold tailWord_1340745
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900987527717320860999689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32600658351811547240666459 48900987527717320860999689)
  ·
    refine ⟨36675740645787990645749767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48900987527717320860999689 36675740645787990645749767)
    ·
      refine ⟨55013610968681985968624651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36675740645787990645749767 55013610968681985968624651)
      ·
        refine ⟨82520416453022978952936977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55013610968681985968624651 82520416453022978952936977)
        ·
          refine ⟨61890312339767234214702733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82520416453022978952936977 61890312339767234214702733)
          ·
            refine ⟨23208867127412712830513525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61890312339767234214702733 23208867127412712830513525)
            ·
              refine ⟨2175831293194941827860643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23208867127412712830513525 2175831293194941827860643)
              ·
                refine ⟨3263746939792412741790965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2175831293194941827860643 3263746939792412741790965)
                ·
                  refine ⟨305976275605538694542903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263746939792412741790965 305976275605538694542903)
                  ·
                    rfl

theorem cell21_1340745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_1340745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340745 prefixEnd_1340745 := by exact prefixLift 1340745
  have htrace : WordTrace (prefixWord ++ tailWord_1340745) baseStart_1340745 baseEnd_1340745 := by
    simpa [prefixWord, tailWord_1340745, baseEnd_1340745] using wordTrace_append hprefix tailTrace_1340745
  have hstable : (prefixWord ++ tailWord_1340745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340745).length < 2 ^ (prefixWord ++ tailWord_1340745).sum := by decide
  have hdescent : baseEnd_1340745 < baseStart_1340745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340790 : List Nat := [5, 1, 1, 14]
def baseStart_1340790 : Nat := 118140960795 + 1340790 * 2 ^ 59
def prefixEnd_1340790 : Nat := 4983230072969 + 3 ^ 40 * 1340790 * 2
def baseEnd_1340790 : Nat := 1259203889788595128777

theorem tailTrace_1340790 : CollatzResearch.WordTrace tailWord_1340790 prefixEnd_1340790 1259203889788595128777 := by
  unfold tailWord_1340790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056414300784643346649239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32601752541702862364258549 3056414300784643346649239)
  ·
    refine ⟨4584621451176965019973859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3056414300784643346649239 4584621451176965019973859)
    ·
      refine ⟨6876932176765447529960789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4584621451176965019973859 6876932176765447529960789)
      ·
        refine ⟨1259203889788595128777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6876932176765447529960789 1259203889788595128777)
        ·
          rfl

theorem cell21_1340790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 14].length) (baseStart_1340790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340790 prefixEnd_1340790 := by exact prefixLift 1340790
  have htrace : WordTrace (prefixWord ++ tailWord_1340790) baseStart_1340790 baseEnd_1340790 := by
    simpa [prefixWord, tailWord_1340790, baseEnd_1340790] using wordTrace_append hprefix tailTrace_1340790
  have hstable : (prefixWord ++ tailWord_1340790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340790).length < 2 ^ (prefixWord ++ tailWord_1340790).sum := by decide
  have hdescent : baseEnd_1340790 < baseStart_1340790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340807 : List Nat := [1, 1, 4, 2, 2, 4, 1, 6]
def baseStart_1340807 : Nat := 118140960795 + 1340807 * 2 ^ 59
def prefixEnd_1340807 : Nat := 4983230072969 + 3 ^ 40 * 1340807 * 2
def baseEnd_1340807 : Nat := 101996808283413454836481

theorem tailTrace_1340807 : CollatzResearch.WordTrace tailWord_1340807 prefixEnd_1340807 101996808283413454836481 := by
  unfold tailWord_1340807
  simp only [CollatzResearch.WordTrace]
  refine ⟨48903248853492705449756675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32602165902328470299837783 48903248853492705449756675)
  ·
    refine ⟨73354873280239058174635013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48903248853492705449756675 73354873280239058174635013)
    ·
      refine ⟨13754038740044823407744065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73354873280239058174635013 13754038740044823407744065)
      ·
        refine ⟨10315529055033617555808049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13754038740044823407744065 10315529055033617555808049)
        ·
          refine ⟨7736646791275213166856037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10315529055033617555808049 7736646791275213166856037)
          ·
            refine ⟨1450621273364102468785507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7736646791275213166856037 1450621273364102468785507)
            ·
              refine ⟨2175931910046153703178261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1450621273364102468785507 2175931910046153703178261)
              ·
                refine ⟨101996808283413454836481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2175931910046153703178261 101996808283413454836481)
                ·
                  rfl

theorem cell21_1340807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 6].length) (baseStart_1340807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340807 prefixEnd_1340807 := by exact prefixLift 1340807
  have htrace : WordTrace (prefixWord ++ tailWord_1340807) baseStart_1340807 baseEnd_1340807 := by
    simpa [prefixWord, tailWord_1340807, baseEnd_1340807] using wordTrace_append hprefix tailTrace_1340807
  have hstable : (prefixWord ++ tailWord_1340807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340807).length < 2 ^ (prefixWord ++ tailWord_1340807).sum := by decide
  have hdescent : baseEnd_1340807 < baseStart_1340807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340824 : List Nat := [2, 1, 2, 5, 2, 1, 3, 5]
def baseStart_1340824 : Nat := 118140960795 + 1340824 * 2 ^ 59
def prefixEnd_1340824 : Nat := 4983230072969 + 3 ^ 40 * 1340824 * 2
def baseEnd_1340824 : Nat := 101998101493950704242025

theorem tailTrace_1340824 : CollatzResearch.WordTrace tailWord_1340824 prefixEnd_1340824 101998101493950704242025 := by
  unfold tailWord_1340824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24451934447215558676562763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32602579262954078235417017 24451934447215558676562763)
  ·
    refine ⟨36677901670823338014844145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24451934447215558676562763 36677901670823338014844145)
    ·
      refine ⟨27508426253117503511133109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36677901670823338014844145 27508426253117503511133109)
      ·
        refine ⟨2578914961229765954168729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27508426253117503511133109 2578914961229765954168729)
        ·
          refine ⟨1934186220922324465626547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578914961229765954168729 1934186220922324465626547)
          ·
            refine ⟨2901279331383486698439821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934186220922324465626547 2901279331383486698439821)
            ·
              refine ⟨1087979749268807511914933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2901279331383486698439821 1087979749268807511914933)
              ·
                refine ⟨101998101493950704242025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1087979749268807511914933 101998101493950704242025)
                ·
                  rfl

theorem cell21_1340824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_1340824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340824 prefixEnd_1340824 := by exact prefixLift 1340824
  have htrace : WordTrace (prefixWord ++ tailWord_1340824) baseStart_1340824 baseEnd_1340824 := by
    simpa [prefixWord, tailWord_1340824, baseEnd_1340824] using wordTrace_append hprefix tailTrace_1340824
  have hstable : (prefixWord ++ tailWord_1340824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340824).length < 2 ^ (prefixWord ++ tailWord_1340824).sum := by decide
  have hdescent : baseEnd_1340824 < baseStart_1340824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340835 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 6]
def baseStart_1340835 : Nat := 118140960795 + 1340835 * 2 ^ 59
def prefixEnd_1340835 : Nat := 4983230072969 + 3 ^ 40 * 1340835 * 2
def baseEnd_1340835 : Nat := 305996814831718538042719

theorem tailTrace_1340835 : CollatzResearch.WordTrace tailWord_1340835 prefixEnd_1340835 305996814831718538042719 := by
  unfold tailWord_1340835
  simp only [CollatzResearch.WordTrace]
  refine ⟨48904270097391266231775959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32602846731594177487850639 48904270097391266231775959)
  ·
    refine ⟨73356405146086899347663939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48904270097391266231775959 73356405146086899347663939)
    ·
      refine ⟨110034607719130349021495909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73356405146086899347663939 110034607719130349021495909)
      ·
        refine ⟨20631488947336940441530483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110034607719130349021495909 20631488947336940441530483)
        ·
          refine ⟨30947233421005410662295725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20631488947336940441530483 30947233421005410662295725)
          ·
            refine ⟨11605212532877028998360897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30947233421005410662295725 11605212532877028998360897)
            ·
              refine ⟨8703909399657771748770673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11605212532877028998360897 8703909399657771748770673)
              ·
                refine ⟨6527932049743328811578005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8703909399657771748770673 6527932049743328811578005)
                ·
                  refine ⟨305996814831718538042719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527932049743328811578005 305996814831718538042719)
                  ·
                    rfl

theorem cell21_1340835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 6].length) (baseStart_1340835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340835 prefixEnd_1340835 := by exact prefixLift 1340835
  have htrace : WordTrace (prefixWord ++ tailWord_1340835) baseStart_1340835 baseEnd_1340835 := by
    simpa [prefixWord, tailWord_1340835, baseEnd_1340835] using wordTrace_append hprefix tailTrace_1340835
  have hstable : (prefixWord ++ tailWord_1340835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340835).length < 2 ^ (prefixWord ++ tailWord_1340835).sum := by decide
  have hdescent : baseEnd_1340835 < baseStart_1340835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340911 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_1340911 : Nat := 118140960795 + 1340911 * 2 ^ 59
def prefixEnd_1340911 : Nat := 4983230072969 + 3 ^ 40 * 1340911 * 2
def baseEnd_1340911 : Nat := 306014159067159294775897

theorem tailTrace_1340911 : CollatzResearch.WordTrace tailWord_1340911 prefixEnd_1340911 306014159067159294775897 := by
  unfold tailWord_1340911
  simp only [CollatzResearch.WordTrace]
  refine ⟨48907042045115931211542587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32604694696743954141028391 48907042045115931211542587)
  ·
    refine ⟨73360563067673896817313881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48907042045115931211542587 73360563067673896817313881)
    ·
      refine ⟨55020422300755422612985411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73360563067673896817313881 55020422300755422612985411)
      ·
        refine ⟨82530633451133133919478117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55020422300755422612985411 82530633451133133919478117)
        ·
          refine ⟨15474493772087462609902147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82530633451133133919478117 15474493772087462609902147)
          ·
            refine ⟨23211740658131193914853221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15474493772087462609902147 23211740658131193914853221)
            ·
              refine ⟨4352201373399598859034979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23211740658131193914853221 4352201373399598859034979)
              ·
                refine ⟨6528302060099398288552469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352201373399598859034979 6528302060099398288552469)
                ·
                  refine ⟨306014159067159294775897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6528302060099398288552469 306014159067159294775897)
                  ·
                    rfl

theorem cell21_1340911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_1340911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340911 prefixEnd_1340911 := by exact prefixLift 1340911
  have htrace : WordTrace (prefixWord ++ tailWord_1340911) baseStart_1340911 baseEnd_1340911 := by
    simpa [prefixWord, tailWord_1340911, baseEnd_1340911] using wordTrace_append hprefix tailTrace_1340911
  have hstable : (prefixWord ++ tailWord_1340911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340911).length < 2 ^ (prefixWord ++ tailWord_1340911).sum := by decide
  have hdescent : baseEnd_1340911 < baseStart_1340911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1340914 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1340914 : Nat := 118140960795 + 1340914 * 2 ^ 59
def prefixEnd_1340914 : Nat := 4983230072969 + 3 ^ 40 * 1340914 * 2
def baseEnd_1340914 : Nat := 306014843708031956225891

theorem tailTrace_1340914 : CollatzResearch.WordTrace tailWord_1340914 prefixEnd_1340914 306014843708031956225891 := by
  unfold tailWord_1340914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12226787866026265680975449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32604767642736708482601197 12226787866026265680975449)
  ·
    refine ⟨9170090899519699260731587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12226787866026265680975449 9170090899519699260731587)
    ·
      refine ⟨13755136349279548891097381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170090899519699260731587 13755136349279548891097381)
      ·
        refine ⟨2579088065489915417080759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13755136349279548891097381 2579088065489915417080759)
        ·
          refine ⟨3868632098234873125621139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2579088065489915417080759 3868632098234873125621139)
          ·
            refine ⟨5802948147352309688431709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868632098234873125621139 5802948147352309688431709)
            ·
              refine ⟨2176105555257116133161891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5802948147352309688431709 2176105555257116133161891)
              ·
                refine ⟨3264158332885674199742837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2176105555257116133161891 3264158332885674199742837)
                ·
                  refine ⟨306014843708031956225891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3264158332885674199742837 306014843708031956225891)
                  ·
                    rfl

theorem cell21_1340914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1340914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1340914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1340914 prefixEnd_1340914 := by exact prefixLift 1340914
  have htrace : WordTrace (prefixWord ++ tailWord_1340914) baseStart_1340914 baseEnd_1340914 := by
    simpa [prefixWord, tailWord_1340914, baseEnd_1340914] using wordTrace_append hprefix tailTrace_1340914
  have hstable : (prefixWord ++ tailWord_1340914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1340914).length < 2 ^ (prefixWord ++ tailWord_1340914).sum := by decide
  have hdescent : baseEnd_1340914 < baseStart_1340914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1340914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341001 : List Nat := [1, 2, 1, 1, 2, 2, 1, 11]
def baseStart_1341001 : Nat := 118140960795 + 1341001 * 2 ^ 59
def prefixEnd_1341001 : Nat := 4983230072969 + 3 ^ 40 * 1341001 * 2
def baseEnd_1341001 : Nat := 102011566097779712758571

theorem tailTrace_1341001 : CollatzResearch.WordTrace tailWord_1341001 prefixEnd_1341001 102011566097779712758571 := by
  unfold tailWord_1341001
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910324614789876582318857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32606883076526584388212571 48910324614789876582318857)
  ·
    refine ⟨36682743461092407436739143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48910324614789876582318857 36682743461092407436739143)
    ·
      refine ⟨55024115191638611155108715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36682743461092407436739143 55024115191638611155108715)
      ·
        refine ⟨82536172787457916732663073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55024115191638611155108715 82536172787457916732663073)
        ·
          refine ⟨61902129590593437549497305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82536172787457916732663073 61902129590593437549497305)
          ·
            refine ⟨46426597192945078162122979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61902129590593437549497305 46426597192945078162122979)
            ·
              refine ⟨69639895789417617243184469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46426597192945078162122979 69639895789417617243184469)
              ·
                refine ⟨102011566097779712758571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69639895789417617243184469 102011566097779712758571)
                ·
                  rfl

theorem cell21_1341001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_1341001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341001 prefixEnd_1341001 := by exact prefixLift 1341001
  have htrace : WordTrace (prefixWord ++ tailWord_1341001) baseStart_1341001 baseEnd_1341001 := by
    simpa [prefixWord, tailWord_1341001, baseEnd_1341001] using wordTrace_append hprefix tailTrace_1341001
  have hstable : (prefixWord ++ tailWord_1341001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341001).length < 2 ^ (prefixWord ++ tailWord_1341001).sum := by decide
  have hdescent : baseEnd_1341001 < baseStart_1341001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341038 : List Nat := [4, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_1341038 : Nat := 118140960795 + 1341038 * 2 ^ 59
def prefixEnd_1341038 : Nat := 4983230072969 + 3 ^ 40 * 1341038 * 2
def baseEnd_1341038 : Nat := 306043142197435296158971

theorem tailTrace_1341038 : CollatzResearch.WordTrace tailWord_1341038 prefixEnd_1341038 306043142197435296158971 := by
  unfold tailWord_1341038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113959264456978987676971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32607782743770554600943845 6113959264456978987676971)
  ·
    refine ⟨9170938896685468481515457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6113959264456978987676971 9170938896685468481515457)
    ·
      refine ⟨6878204172514101361136593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9170938896685468481515457 6878204172514101361136593)
      ·
        refine ⟨5158653129385576020852445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6878204172514101361136593 5158653129385576020852445)
        ·
          refine ⟨1934494923519591007819667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5158653129385576020852445 1934494923519591007819667)
          ·
            refine ⟨2901742385279386511729501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1934494923519591007819667 2901742385279386511729501)
            ·
              refine ⟨1088153394479769941898563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2901742385279386511729501 1088153394479769941898563)
              ·
                refine ⟨1632230091719654912847845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088153394479769941898563 1632230091719654912847845)
                ·
                  refine ⟨306043142197435296158971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632230091719654912847845 306043142197435296158971)
                  ·
                    rfl

theorem cell21_1341038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_1341038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341038 prefixEnd_1341038 := by exact prefixLift 1341038
  have htrace : WordTrace (prefixWord ++ tailWord_1341038) baseStart_1341038 baseEnd_1341038 := by
    simpa [prefixWord, tailWord_1341038, baseEnd_1341038] using wordTrace_append hprefix tailTrace_1341038
  have hstable : (prefixWord ++ tailWord_1341038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341038).length < 2 ^ (prefixWord ++ tailWord_1341038).sum := by decide
  have hdescent : baseEnd_1341038 < baseStart_1341038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341063 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 6]
def baseStart_1341063 : Nat := 118140960795 + 1341063 * 2 ^ 59
def prefixEnd_1341063 : Nat := 4983230072969 + 3 ^ 40 * 1341063 * 2
def baseEnd_1341063 : Nat := 306048847538040808242253

theorem tailTrace_1341063 : CollatzResearch.WordTrace tailWord_1341063 prefixEnd_1341063 306048847538040808242253 := by
  unfold tailWord_1341063
  simp only [CollatzResearch.WordTrace]
  refine ⟨48912585940565261171075843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32608390627043507447383895 48912585940565261171075843)
  ·
    refine ⟨73368878910847891756613765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48912585940565261171075843 73368878910847891756613765)
    ·
      refine ⟨13756664795783979704365081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73368878910847891756613765 13756664795783979704365081)
      ·
        refine ⟨10317498596837984778273811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13756664795783979704365081 10317498596837984778273811)
        ·
          refine ⟨15476247895256977167410717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317498596837984778273811 15476247895256977167410717)
          ·
            refine ⟨5803592960721366437779019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15476247895256977167410717 5803592960721366437779019)
            ·
              refine ⟨8705389441082049656668529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5803592960721366437779019 8705389441082049656668529)
              ·
                refine ⟨6529042080811537242501397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8705389441082049656668529 6529042080811537242501397)
                ·
                  refine ⟨306048847538040808242253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6529042080811537242501397 306048847538040808242253)
                  ·
                    rfl

theorem cell21_1341063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 6].length) (baseStart_1341063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341063 prefixEnd_1341063 := by exact prefixLift 1341063
  have htrace : WordTrace (prefixWord ++ tailWord_1341063) baseStart_1341063 baseEnd_1341063 := by
    simpa [prefixWord, tailWord_1341063, baseEnd_1341063] using wordTrace_append hprefix tailTrace_1341063
  have hstable : (prefixWord ++ tailWord_1341063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341063).length < 2 ^ (prefixWord ++ tailWord_1341063).sum := by decide
  have hdescent : baseEnd_1341063 < baseStart_1341063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341235 : List Nat := [1, 1, 1, 2, 7, 2, 1, 3, 3]
def baseStart_1341235 : Nat := 118140960795 + 1341235 * 2 ^ 59
def prefixEnd_1341235 : Nat := 4983230072969 + 3 ^ 40 * 1341235 * 2
def baseEnd_1341235 : Nat := 306088100281406731375235

theorem tailTrace_1341235 : CollatzResearch.WordTrace tailWord_1341235 prefixEnd_1341235 306088100281406731375235 := by
  unfold tailWord_1341235
  simp only [CollatzResearch.WordTrace]
  refine ⟨48918859295942134546337159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32612572863961423030891439 48918859295942134546337159)
  ·
    refine ⟨73378288943913201819505739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48918859295942134546337159 73378288943913201819505739)
    ·
      refine ⟨110067433415869802729258609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73378288943913201819505739 110067433415869802729258609)
      ·
        refine ⟨82550575061902352046943957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110067433415869802729258609 82550575061902352046943957)
        ·
          refine ⟨1934779103013336376100249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82550575061902352046943957 1934779103013336376100249)
          ·
            refine ⟨1451084327260002282075187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1934779103013336376100249 1451084327260002282075187)
            ·
              refine ⟨2176626490890003423112781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451084327260002282075187 2176626490890003423112781)
              ·
                refine ⟨816234934083751283667293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2176626490890003423112781 816234934083751283667293)
                ·
                  refine ⟨306088100281406731375235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816234934083751283667293 306088100281406731375235)
                  ·
                    rfl

theorem cell21_1341235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 3, 3].length) (baseStart_1341235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341235 prefixEnd_1341235 := by exact prefixLift 1341235
  have htrace : WordTrace (prefixWord ++ tailWord_1341235) baseStart_1341235 baseEnd_1341235 := by
    simpa [prefixWord, tailWord_1341235, baseEnd_1341235] using wordTrace_append hprefix tailTrace_1341235
  have hstable : (prefixWord ++ tailWord_1341235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341235).length < 2 ^ (prefixWord ++ tailWord_1341235).sum := by decide
  have hdescent : baseEnd_1341235 < baseStart_1341235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341246 : List Nat := [4, 2, 1, 2, 2, 1, 9]
def baseStart_1341246 : Nat := 118140960795 + 1341246 * 2 ^ 59
def prefixEnd_1341246 : Nat := 4983230072969 + 3 ^ 40 * 1341246 * 2
def baseEnd_1341246 : Nat := 34010067847919239632431

theorem tailTrace_1341246 : CollatzResearch.WordTrace tailWord_1341246 prefixEnd_1341246 34010067847919239632431 := by
  unfold tailWord_1341246
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114907562362785428123449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32612840332601522283325061 6114907562362785428123449)
  ·
    refine ⟨4586180671772089071092587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6114907562362785428123449 4586180671772089071092587)
    ·
      refine ⟨6879271007658133606638881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4586180671772089071092587 6879271007658133606638881)
      ·
        refine ⟨5159453255743600204979161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6879271007658133606638881 5159453255743600204979161)
        ·
          refine ⟨3869589941807700153734371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5159453255743600204979161 3869589941807700153734371)
          ·
            refine ⟨5804384912711550230601557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869589941807700153734371 5804384912711550230601557)
            ·
              refine ⟨34010067847919239632431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5804384912711550230601557 34010067847919239632431)
              ·
                rfl

theorem cell21_1341246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 9].length) (baseStart_1341246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341246 prefixEnd_1341246 := by exact prefixLift 1341246
  have htrace : WordTrace (prefixWord ++ tailWord_1341246) baseStart_1341246 baseEnd_1341246 := by
    simpa [prefixWord, tailWord_1341246, baseEnd_1341246] using wordTrace_append hprefix tailTrace_1341246
  have hstable : (prefixWord ++ tailWord_1341246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341246).length < 2 ^ (prefixWord ++ tailWord_1341246).sum := by decide
  have hdescent : baseEnd_1341246 < baseStart_1341246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341415 : List Nat := [1, 1, 5, 2, 4, 1, 7]
def baseStart_1341415 : Nat := 118140960795 + 1341415 * 2 ^ 59
def prefixEnd_1341415 : Nat := 4983230072969 + 3 ^ 40 * 1341415 * 2
def baseEnd_1341415 : Nat := 34014353192640713152763

theorem tailTrace_1341415 : CollatzResearch.WordTrace tailWord_1341415 prefixEnd_1341415 34014353192640713152763 := by
  unfold tailWord_1341415
  simp only [CollatzResearch.WordTrace]
  refine ⟨48925424435290025287889699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32616949623526683525259799 48925424435290025287889699)
  ·
    refine ⟨73388136652935037931834549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48925424435290025287889699 73388136652935037931834549)
    ·
      refine ⟨6880137811212659806109489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73388136652935037931834549 6880137811212659806109489)
      ·
        refine ⟨5160103358409494854582117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6880137811212659806109489 5160103358409494854582117)
        ·
          refine ⟨967519379701780285234147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5160103358409494854582117 967519379701780285234147)
          ·
            refine ⟨1451279069552670427851221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967519379701780285234147 1451279069552670427851221)
            ·
              refine ⟨34014353192640713152763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1451279069552670427851221 34014353192640713152763)
              ·
                rfl

theorem cell21_1341415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 7].length) (baseStart_1341415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341415 prefixEnd_1341415 := by exact prefixLift 1341415
  have htrace : WordTrace (prefixWord ++ tailWord_1341415) baseStart_1341415 baseEnd_1341415 := by
    simpa [prefixWord, tailWord_1341415, baseEnd_1341415] using wordTrace_append hprefix tailTrace_1341415
  have hstable : (prefixWord ++ tailWord_1341415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341415).length < 2 ^ (prefixWord ++ tailWord_1341415).sum := by decide
  have hdescent : baseEnd_1341415 < baseStart_1341415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341505 : List Nat := [1, 2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_1341505 : Nat := 118140960795 + 1341505 * 2 ^ 59
def prefixEnd_1341505 : Nat := 4983230072969 + 3 ^ 40 * 1341505 * 2
def baseEnd_1341505 : Nat := 306149717959946261874683

theorem tailTrace_1341505 : CollatzResearch.WordTrace tailWord_1341505 prefixEnd_1341505 306149717959946261874683 := by
  unfold tailWord_1341505
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928707004963970658665969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32619138003309313772443979 48928707004963970658665969)
  ·
    refine ⟨36696530253722977993999477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48928707004963970658665969 36696530253722977993999477)
    ·
      refine ⟨3440299711286529186937451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36696530253722977993999477 3440299711286529186937451)
      ·
        refine ⟨5160449566929793780406177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440299711286529186937451 5160449566929793780406177)
        ·
          refine ⟨3870337175197345335304633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5160449566929793780406177 3870337175197345335304633)
          ·
            refine ⟨2902752881398009001478475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3870337175197345335304633 2902752881398009001478475)
            ·
              refine ⟨4354129322097013502217713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2902752881398009001478475 4354129322097013502217713)
              ·
                refine ⟨3265596991572760126663285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354129322097013502217713 3265596991572760126663285)
                ·
                  refine ⟨306149717959946261874683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3265596991572760126663285 306149717959946261874683)
                  ·
                    rfl

theorem cell21_1341505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_1341505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341505 prefixEnd_1341505 := by exact prefixLift 1341505
  have htrace : WordTrace (prefixWord ++ tailWord_1341505) baseStart_1341505 baseEnd_1341505 := by
    simpa [prefixWord, tailWord_1341505, baseEnd_1341505] using wordTrace_append hprefix tailTrace_1341505
  have hstable : (prefixWord ++ tailWord_1341505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341505).length < 2 ^ (prefixWord ++ tailWord_1341505).sum := by decide
  have hdescent : baseEnd_1341505 < baseStart_1341505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341536 : List Nat := [2, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_1341536 : Nat := 118140960795 + 1341536 * 2 ^ 59
def prefixEnd_1341536 : Nat := 4983230072969 + 3 ^ 40 * 1341536 * 2
def baseEnd_1341536 : Nat := 306156792582297096857953

theorem tailTrace_1341536 : CollatzResearch.WordTrace tailWord_1341536 prefixEnd_1341536 306156792582297096857953 := by
  unfold tailWord_1341536
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464918833925831476522231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32619891778567775302029641 24464918833925831476522231)
  ·
    refine ⟨36697378250888747214783347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24464918833925831476522231 36697378250888747214783347)
    ·
      refine ⟨55046067376333120822175021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36697378250888747214783347 55046067376333120822175021)
      ·
        refine ⟨20642275266124920308315633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55046067376333120822175021 20642275266124920308315633)
        ·
          refine ⟨15481706449593690231236725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20642275266124920308315633 15481706449593690231236725)
          ·
            refine ⟨1451409979649408459178443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15481706449593690231236725 1451409979649408459178443)
            ·
              refine ⟨2177114969474112688767665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451409979649408459178443 2177114969474112688767665)
              ·
                refine ⟨1632836227105584516575749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177114969474112688767665 1632836227105584516575749)
                ·
                  refine ⟨306156792582297096857953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1632836227105584516575749 306156792582297096857953)
                  ·
                    rfl

theorem cell21_1341536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_1341536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341536 prefixEnd_1341536 := by exact prefixLift 1341536
  have htrace : WordTrace (prefixWord ++ tailWord_1341536) baseStart_1341536 baseEnd_1341536 := by
    simpa [prefixWord, tailWord_1341536, baseEnd_1341536] using wordTrace_append hprefix tailTrace_1341536
  have hstable : (prefixWord ++ tailWord_1341536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341536).length < 2 ^ (prefixWord ++ tailWord_1341536).sum := by decide
  have hdescent : baseEnd_1341536 < baseStart_1341536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341564 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1341564 : Nat := 118140960795 + 1341564 * 2 ^ 59
def prefixEnd_1341564 : Nat := 4983230072969 + 3 ^ 40 * 1341564 * 2
def baseEnd_1341564 : Nat := 306163182563775270391229

theorem tailTrace_1341564 : CollatzResearch.WordTrace tailWord_1341564 prefixEnd_1341564 306163182563775270391229 := by
  unfold tailWord_1341564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24465429455875111867531873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32620572607833482490042497 24465429455875111867531873)
  ·
    refine ⟨18349072091906333900648905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24465429455875111867531873 18349072091906333900648905)
    ·
      refine ⟨13761804068929750425486679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18349072091906333900648905 13761804068929750425486679)
      ·
        refine ⟨20642706103394625638230019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761804068929750425486679 20642706103394625638230019)
        ·
          refine ⟨30964059155091938457345029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20642706103394625638230019 30964059155091938457345029)
          ·
            refine ⟨5805761091579738460752193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30964059155091938457345029 5805761091579738460752193)
            ·
              refine ⟨4354320818684803845564145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805761091579738460752193 4354320818684803845564145)
              ·
                refine ⟨3265740614013602884173109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4354320818684803845564145 3265740614013602884173109)
                ·
                  refine ⟨306163182563775270391229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3265740614013602884173109 306163182563775270391229)
                  ·
                    rfl

theorem cell21_1341564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1341564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341564 prefixEnd_1341564 := by exact prefixLift 1341564
  have htrace : WordTrace (prefixWord ++ tailWord_1341564) baseStart_1341564 baseEnd_1341564 := by
    simpa [prefixWord, tailWord_1341564, baseEnd_1341564] using wordTrace_append hprefix tailTrace_1341564
  have hstable : (prefixWord ++ tailWord_1341564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341564).length < 2 ^ (prefixWord ++ tailWord_1341564).sum := by decide
  have hdescent : baseEnd_1341564 < baseStart_1341564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341590 : List Nat := [5, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1341590 : Nat := 118140960795 + 1341590 * 2 ^ 59
def prefixEnd_1341590 : Nat := 4983230072969 + 3 ^ 40 * 1341590 * 2
def baseEnd_1341590 : Nat := 306169116118005002957843

theorem tailTrace_1341590 : CollatzResearch.WordTrace tailWord_1341590 prefixEnd_1341590 306169116118005002957843 := by
  unfold tailWord_1341590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058237950603501885969389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32621204806437353450340149 3058237950603501885969389)
  ·
    refine ⟨1146839231476313207238521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3058237950603501885969389 1146839231476313207238521)
    ·
      refine ⟨860129423607234905428891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1146839231476313207238521 860129423607234905428891)
      ·
        refine ⟨1290194135410852358143337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 860129423607234905428891 1290194135410852358143337)
        ·
          refine ⟨967645601558139268607503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1290194135410852358143337 967645601558139268607503)
          ·
            refine ⟨1451468402337208902911255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967645601558139268607503 1451468402337208902911255)
            ·
              refine ⟨2177202603505813354366883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451468402337208902911255 2177202603505813354366883)
              ·
                refine ⟨3265803905258720031550325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2177202603505813354366883 3265803905258720031550325)
                ·
                  refine ⟨306169116118005002957843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3265803905258720031550325 306169116118005002957843)
                  ·
                    rfl

theorem cell21_1341590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1341590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341590 prefixEnd_1341590 := by exact prefixLift 1341590
  have htrace : WordTrace (prefixWord ++ tailWord_1341590) baseStart_1341590 baseEnd_1341590 := by
    simpa [prefixWord, tailWord_1341590, baseEnd_1341590] using wordTrace_append hprefix tailTrace_1341590
  have hstable : (prefixWord ++ tailWord_1341590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341590).length < 2 ^ (prefixWord ++ tailWord_1341590).sum := by decide
  have hdescent : baseEnd_1341590 < baseStart_1341590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341660 : List Nat := [2, 2, 5, 2, 1, 2, 1, 6]
def baseStart_1341660 : Nat := 118140960795 + 1341660 * 2 ^ 59
def prefixEnd_1341660 : Nat := 4983230072969 + 3 ^ 40 * 1341660 * 2
def baseEnd_1341660 : Nat := 102061697023900145597011

theorem tailTrace_1341660 : CollatzResearch.WordTrace tailWord_1341660 prefixEnd_1341660 102061697023900145597011 := by
  unfold tailWord_1341660
  simp only [CollatzResearch.WordTrace]
  refine ⟨24467180159701216065279217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32622906879601621420372289 24467180159701216065279217)
  ·
    refine ⟨18350385119775912048959413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24467180159701216065279217 18350385119775912048959413)
    ·
      refine ⟨1720348604978991754589945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18350385119775912048959413 1720348604978991754589945)
      ·
        refine ⟨1290261453734243815942459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1720348604978991754589945 1290261453734243815942459)
        ·
          refine ⟨1935392180601365723913689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290261453734243815942459 1935392180601365723913689)
          ·
            refine ⟨1451544135451024292935267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935392180601365723913689 1451544135451024292935267)
            ·
              refine ⟨2177316203176536439402901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1451544135451024292935267 2177316203176536439402901)
              ·
                refine ⟨102061697023900145597011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2177316203176536439402901 102061697023900145597011)
                ·
                  rfl

theorem cell21_1341660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_1341660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341660 prefixEnd_1341660 := by exact prefixLift 1341660
  have htrace : WordTrace (prefixWord ++ tailWord_1341660) baseStart_1341660 baseEnd_1341660 := by
    simpa [prefixWord, tailWord_1341660, baseEnd_1341660] using wordTrace_append hprefix tailTrace_1341660
  have hstable : (prefixWord ++ tailWord_1341660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341660).length < 2 ^ (prefixWord ++ tailWord_1341660).sum := by decide
  have hdescent : baseEnd_1341660 < baseStart_1341660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341699 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_1341699 : Nat := 118140960795 + 1341699 * 2 ^ 59
def prefixEnd_1341699 : Nat := 4983230072969 + 3 ^ 40 * 1341699 * 2
def baseEnd_1341699 : Nat := 306193991403045035640953

theorem tailTrace_1341699 : CollatzResearch.WordTrace tailWord_1341699 prefixEnd_1341699 306193991403045035640953 := by
  unfold tailWord_1341699
  simp only [CollatzResearch.WordTrace]
  refine ⟨48935782766261141791228151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32623855177507427860818767 48935782766261141791228151)
  ·
    refine ⟨73403674149391712686842227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48935782766261141791228151 73403674149391712686842227)
    ·
      refine ⟨110105511224087569030263341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73403674149391712686842227 110105511224087569030263341)
      ·
        refine ⟨41289566709032838386348753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110105511224087569030263341 41289566709032838386348753)
        ·
          refine ⟨30967175031774628789761565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41289566709032838386348753 30967175031774628789761565)
          ·
            refine ⟨11612690636915485796160587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30967175031774628789761565 11612690636915485796160587)
            ·
              refine ⟨17419035955373228694240881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612690636915485796160587 17419035955373228694240881)
              ·
                refine ⟨13064276966529921520680661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17419035955373228694240881 13064276966529921520680661)
                ·
                  refine ⟨306193991403045035640953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13064276966529921520680661 306193991403045035640953)
                  ·
                    rfl

theorem cell21_1341699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_1341699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341699 prefixEnd_1341699 := by exact prefixLift 1341699
  have htrace : WordTrace (prefixWord ++ tailWord_1341699) baseStart_1341699 baseEnd_1341699 := by
    simpa [prefixWord, tailWord_1341699, baseEnd_1341699] using wordTrace_append hprefix tailTrace_1341699
  have hstable : (prefixWord ++ tailWord_1341699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341699).length < 2 ^ (prefixWord ++ tailWord_1341699).sum := by decide
  have hdescent : baseEnd_1341699 < baseStart_1341699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341736 : List Nat := [2, 1, 5, 1, 4, 1, 2, 5]
def baseStart_1341736 : Nat := 118140960795 + 1341736 * 2 ^ 59
def prefixEnd_1341736 : Nat := 4983230072969 + 3 ^ 40 * 1341736 * 2
def baseEnd_1341736 : Nat := 102067478435713731174737

theorem tailTrace_1341736 : CollatzResearch.WordTrace tailWord_1341736 prefixEnd_1341736 102067478435713731174737 := by
  unfold tailWord_1341736
  simp only [CollatzResearch.WordTrace]
  refine ⟨24468566133563548555162531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32624754844751398073550041 24468566133563548555162531)
  ·
    refine ⟨36702849200345322832743797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24468566133563548555162531 36702849200345322832743797)
    ·
      refine ⟨3440892112532374015569731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36702849200345322832743797 3440892112532374015569731)
      ·
        refine ⟨5161338168798561023354597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440892112532374015569731 5161338168798561023354597)
        ·
          refine ⟨967750906649730191878987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5161338168798561023354597 967750906649730191878987)
          ·
            refine ⟨1451626359974595287818481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967750906649730191878987 1451626359974595287818481)
            ·
              refine ⟨1088719769980946465863861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451626359974595287818481 1088719769980946465863861)
              ·
                refine ⟨102067478435713731174737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1088719769980946465863861 102067478435713731174737)
                ·
                  rfl

theorem cell21_1341736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_1341736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341736 prefixEnd_1341736 := by exact prefixLift 1341736
  have htrace : WordTrace (prefixWord ++ tailWord_1341736) baseStart_1341736 baseEnd_1341736 := by
    simpa [prefixWord, tailWord_1341736, baseEnd_1341736] using wordTrace_append hprefix tailTrace_1341736
  have hstable : (prefixWord ++ tailWord_1341736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341736).length < 2 ^ (prefixWord ++ tailWord_1341736).sum := by decide
  have hdescent : baseEnd_1341736 < baseStart_1341736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341775 : List Nat := [1, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_1341775 : Nat := 118140960795 + 1341775 * 2 ^ 59
def prefixEnd_1341775 : Nat := 4983230072969 + 3 ^ 40 * 1341775 * 2
def baseEnd_1341775 : Nat := 306211335638485792374131

theorem tailTrace_1341775 : CollatzResearch.WordTrace tailWord_1341775 prefixEnd_1341775 306211335638485792374131 := by
  unfold tailWord_1341775
  simp only [CollatzResearch.WordTrace]
  refine ⟨48938554713985806770994779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32625703142657204513996519 48938554713985806770994779)
  ·
    refine ⟨73407832070978710156492169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48938554713985806770994779 73407832070978710156492169)
    ·
      refine ⟨55055874053234032617369127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73407832070978710156492169 55055874053234032617369127)
      ·
        refine ⟨82583811079851048926053691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55055874053234032617369127 82583811079851048926053691)
        ·
          refine ⟨123875716619776573389080537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82583811079851048926053691 123875716619776573389080537)
          ·
            refine ⟨92906787464832430041810403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123875716619776573389080537 92906787464832430041810403)
            ·
              refine ⟨139360181197248645062715605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92906787464832430041810403 139360181197248645062715605)
              ·
                refine ⟨3266254246810515118657397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139360181197248645062715605 3266254246810515118657397)
                ·
                  refine ⟨306211335638485792374131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266254246810515118657397 306211335638485792374131)
                  ·
                    rfl

theorem cell21_1341775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_1341775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341775 prefixEnd_1341775 := by exact prefixLift 1341775
  have htrace : WordTrace (prefixWord ++ tailWord_1341775) baseStart_1341775 baseEnd_1341775 := by
    simpa [prefixWord, tailWord_1341775, baseEnd_1341775] using wordTrace_append hprefix tailTrace_1341775
  have hstable : (prefixWord ++ tailWord_1341775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341775).length < 2 ^ (prefixWord ++ tailWord_1341775).sum := by decide
  have hdescent : baseEnd_1341775 < baseStart_1341775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341781 : List Nat := [1, 3, 2, 2, 4, 2, 2, 1, 4]
def baseStart_1341781 : Nat := 118140960795 + 1341781 * 2 ^ 59
def prefixEnd_1341781 : Nat := 4983230072969 + 3 ^ 40 * 1341781 * 2
def baseEnd_1341781 : Nat := 306212704920231115274119

theorem tailTrace_1341781 : CollatzResearch.WordTrace tailWord_1341781 prefixEnd_1341781 306212704920231115274119 := by
  unfold tailWord_1341781
  simp only [CollatzResearch.WordTrace]
  refine ⟨48938773551964069795713197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32625849034642713197142131 48938773551964069795713197)
  ·
    refine ⟨18352040081986526173392449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48938773551964069795713197 18352040081986526173392449)
    ·
      refine ⟨13764030061489894630044337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18352040081986526173392449 13764030061489894630044337)
      ·
        refine ⟨10323022546117420972533253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13764030061489894630044337 10323022546117420972533253)
        ·
          refine ⟨1935566727397016432349985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10323022546117420972533253 1935566727397016432349985)
          ·
            refine ⟨1451675045547762324262489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1935566727397016432349985 1451675045547762324262489)
            ·
              refine ⟨1088756284160821743196867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1451675045547762324262489 1088756284160821743196867)
              ·
                refine ⟨1633134426241232614795301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088756284160821743196867 1633134426241232614795301)
                ·
                  refine ⟨306212704920231115274119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633134426241232614795301 306212704920231115274119)
                  ·
                    rfl

theorem cell21_1341781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_1341781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341781 prefixEnd_1341781 := by exact prefixLift 1341781
  have htrace : WordTrace (prefixWord ++ tailWord_1341781) baseStart_1341781 baseEnd_1341781 := by
    simpa [prefixWord, tailWord_1341781, baseEnd_1341781] using wordTrace_append hprefix tailTrace_1341781
  have hstable : (prefixWord ++ tailWord_1341781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341781).length < 2 ^ (prefixWord ++ tailWord_1341781).sum := by decide
  have hdescent : baseEnd_1341781 < baseStart_1341781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341885 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 3]
def baseStart_1341885 : Nat := 118140960795 + 1341885 * 2 ^ 59
def prefixEnd_1341885 : Nat := 4983230072969 + 3 ^ 40 * 1341885 * 2
def baseEnd_1341885 : Nat := 306236439137150045540573

theorem tailTrace_1341885 : CollatzResearch.WordTrace tailWord_1341885 prefixEnd_1341885 306236439137150045540573 := by
  unfold tailWord_1341885
  simp only [CollatzResearch.WordTrace]
  refine ⟨48942566743587295557499109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32628377829058197038332739 48942566743587295557499109)
  ·
    refine ⟨9176731264422617917031083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48942566743587295557499109 9176731264422617917031083)
    ·
      refine ⟨13765096896633926875546625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9176731264422617917031083 13765096896633926875546625)
      ·
        refine ⟨10323822672475445156659969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13765096896633926875546625 10323822672475445156659969)
        ·
          refine ⟨7742867004356583867494977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10323822672475445156659969 7742867004356583867494977)
          ·
            refine ⟨5807150253267437900621233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7742867004356583867494977 5807150253267437900621233)
            ·
              refine ⟨4355362689950578425465925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5807150253267437900621233 4355362689950578425465925)
              ·
                refine ⟨816630504365733454774861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4355362689950578425465925 816630504365733454774861)
                ·
                  refine ⟨306236439137150045540573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816630504365733454774861 306236439137150045540573)
                  ·
                    rfl

theorem cell21_1341885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_1341885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341885 prefixEnd_1341885 := by exact prefixLift 1341885
  have htrace : WordTrace (prefixWord ++ tailWord_1341885) baseStart_1341885 baseEnd_1341885 := by
    simpa [prefixWord, tailWord_1341885, baseEnd_1341885] using wordTrace_append hprefix tailTrace_1341885
  have hstable : (prefixWord ++ tailWord_1341885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341885).length < 2 ^ (prefixWord ++ tailWord_1341885).sum := by decide
  have hdescent : baseEnd_1341885 < baseStart_1341885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1341992 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 4]
def baseStart_1341992 : Nat := 118140960795 + 1341992 * 2 ^ 59
def prefixEnd_1341992 : Nat := 4983230072969 + 3 ^ 40 * 1341992 * 2
def baseEnd_1341992 : Nat := 306260857994941637257021

theorem tailTrace_1341992 : CollatzResearch.WordTrace tailWord_1341992 prefixEnd_1341992 306260857994941637257021 := by
  unfold tailWord_1341992
  simp only [CollatzResearch.WordTrace]
  refine ⟨24473234677099826415822115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32630979569466435221096153 24473234677099826415822115)
  ·
    refine ⟨36709852015649739623733173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24473234677099826415822115 36709852015649739623733173)
    ·
      refine ⟨3441548626467163089724985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36709852015649739623733173 3441548626467163089724985)
      ·
        refine ⟨2581161469850372317293739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3441548626467163089724985 2581161469850372317293739)
        ·
          refine ⟨3871742204775558475940609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581161469850372317293739 3871742204775558475940609)
          ·
            refine ⟨2903806653581668856955457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3871742204775558475940609 2903806653581668856955457)
            ·
              refine ⟨2177854990186251642716593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2903806653581668856955457 2177854990186251642716593)
              ·
                refine ⟨1633391242639688732037445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2177854990186251642716593 1633391242639688732037445)
                ·
                  refine ⟨306260857994941637257021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633391242639688732037445 306260857994941637257021)
                  ·
                    rfl

theorem cell21_1341992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_1341992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1341992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1341992 prefixEnd_1341992 := by exact prefixLift 1341992
  have htrace : WordTrace (prefixWord ++ tailWord_1341992) baseStart_1341992 baseEnd_1341992 := by
    simpa [prefixWord, tailWord_1341992, baseEnd_1341992] using wordTrace_append hprefix tailTrace_1341992
  have hstable : (prefixWord ++ tailWord_1341992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1341992).length < 2 ^ (prefixWord ++ tailWord_1341992).sum := by decide
  have hdescent : baseEnd_1341992 < baseStart_1341992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1341992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342003 : List Nat := [1, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_1342003 : Nat := 118140960795 + 1342003 * 2 ^ 59
def prefixEnd_1342003 : Nat := 4983230072969 + 3 ^ 40 * 1342003 * 2
def baseEnd_1342003 : Nat := 306263368344808062573665

theorem tailTrace_1342003 : CollatzResearch.WordTrace tailWord_1342003 prefixEnd_1342003 306263368344808062573665 := by
  unfold tailWord_1342003
  simp only [CollatzResearch.WordTrace]
  refine ⟨48946870557159801710294663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32631247038106534473529775 48946870557159801710294663)
  ·
    refine ⟨73420305835739702565441995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48946870557159801710294663 73420305835739702565441995)
    ·
      refine ⟨110130458753609553848162993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73420305835739702565441995 110130458753609553848162993)
      ·
        refine ⟨82597844065207165386122245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110130458753609553848162993 82597844065207165386122245)
        ·
          refine ⟨15487095762226343509897921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82597844065207165386122245 15487095762226343509897921)
          ·
            refine ⟨11615321821669757632423441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15487095762226343509897921 11615321821669757632423441)
            ·
              refine ⟨8711491366252318224317581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11615321821669757632423441 8711491366252318224317581)
              ·
                refine ⟨3266809262344619334119093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8711491366252318224317581 3266809262344619334119093)
                ·
                  refine ⟨306263368344808062573665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3266809262344619334119093 306263368344808062573665)
                  ·
                    rfl

theorem cell21_1342003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_1342003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342003 prefixEnd_1342003 := by exact prefixLift 1342003
  have htrace : WordTrace (prefixWord ++ tailWord_1342003) baseStart_1342003 baseEnd_1342003 := by
    simpa [prefixWord, tailWord_1342003, baseEnd_1342003] using wordTrace_append hprefix tailTrace_1342003
  have hstable : (prefixWord ++ tailWord_1342003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342003).length < 2 ^ (prefixWord ++ tailWord_1342003).sum := by decide
  have hdescent : baseEnd_1342003 < baseStart_1342003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342006 : List Nat := [5, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1342006 : Nat := 118140960795 + 1342006 * 2 ^ 59
def prefixEnd_1342006 : Nat := 4983230072969 + 3 ^ 40 * 1342006 * 2
def baseEnd_1342006 : Nat := 102088017661893574674553

theorem tailTrace_1342006 : CollatzResearch.WordTrace tailWord_1342006 prefixEnd_1342006 102088017661893574674553 := by
  unfold tailWord_1342006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059186248509308326415867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32631319984099288815102581 3059186248509308326415867)
  ·
    refine ⟨4588779372763962489623801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059186248509308326415867 4588779372763962489623801)
    ·
      refine ⟨3441584529572971867217851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4588779372763962489623801 3441584529572971867217851)
      ·
        refine ⟨5162376794359457800826777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441584529572971867217851 5162376794359457800826777)
        ·
          refine ⟨3871782595769593350620083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5162376794359457800826777 3871782595769593350620083)
          ·
            refine ⟨5807673893654390025930125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3871782595769593350620083 5807673893654390025930125)
            ·
              refine ⟨2177877710120396259723797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5807673893654390025930125 2177877710120396259723797)
              ·
                refine ⟨102088017661893574674553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2177877710120396259723797 102088017661893574674553)
                ·
                  rfl

theorem cell21_1342006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1342006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342006 prefixEnd_1342006 := by exact prefixLift 1342006
  have htrace : WordTrace (prefixWord ++ tailWord_1342006) baseStart_1342006 baseEnd_1342006 := by
    simpa [prefixWord, tailWord_1342006, baseEnd_1342006] using wordTrace_append hprefix tailTrace_1342006
  have hstable : (prefixWord ++ tailWord_1342006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342006).length < 2 ^ (prefixWord ++ tailWord_1342006).sum := by decide
  have hdescent : baseEnd_1342006 < baseStart_1342006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342034 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1342034 : Nat := 118140960795 + 1342034 * 2 ^ 59
def prefixEnd_1342034 : Nat := 4983230072969 + 3 ^ 40 * 1342034 * 2
def baseEnd_1342034 : Nat := 306270442967158897556935

theorem tailTrace_1342034 : CollatzResearch.WordTrace tailWord_1342034 prefixEnd_1342034 306270442967158897556935 := by
  unfold tailWord_1342034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12237000305011873501168289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32632000813364996003115437 12237000305011873501168289)
  ·
    refine ⟨9177750228758905125876217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12237000305011873501168289 9177750228758905125876217)
    ·
      refine ⟨6883312671569178844407163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9177750228758905125876217 6883312671569178844407163)
      ·
        refine ⟨10324969007353768266610745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6883312671569178844407163 10324969007353768266610745)
        ·
          refine ⟨7743726755515326199958059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10324969007353768266610745 7743726755515326199958059)
          ·
            refine ⟨11615590133272989299937089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7743726755515326199958059 11615590133272989299937089)
            ·
              refine ⟨8711692599954741974952817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11615590133272989299937089 8711692599954741974952817)
              ·
                refine ⟨6533769449966056481214613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8711692599954741974952817 6533769449966056481214613)
                ·
                  refine ⟨306270442967158897556935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6533769449966056481214613 306270442967158897556935)
                  ·
                    rfl

theorem cell21_1342034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1342034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342034 prefixEnd_1342034 := by exact prefixLift 1342034
  have htrace : WordTrace (prefixWord ++ tailWord_1342034) baseStart_1342034 baseEnd_1342034 := by
    simpa [prefixWord, tailWord_1342034, baseEnd_1342034] using wordTrace_append hprefix tailTrace_1342034
  have hstable : (prefixWord ++ tailWord_1342034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342034).length < 2 ^ (prefixWord ++ tailWord_1342034).sum := by decide
  have hdescent : baseEnd_1342034 < baseStart_1342034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342113 : List Nat := [1, 2, 3, 3, 3, 2, 1, 1, 5]
def baseStart_1342113 : Nat := 118140960795 + 1342113 * 2 ^ 59
def prefixEnd_1342113 : Nat := 4983230072969 + 3 ^ 40 * 1342113 * 2
def baseEnd_1342113 : Nat := 306288471843472315740107

theorem tailTrace_1342113 : CollatzResearch.WordTrace tailWord_1342113 prefixEnd_1342113 306288471843472315740107 := by
  unfold tailWord_1342113
  simp only [CollatzResearch.WordTrace]
  refine ⟨48950882586761290496798993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32633921724507526997865995 48950882586761290496798993)
  ·
    refine ⟨36713161940070967872599245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48950882586761290496798993 36713161940070967872599245)
    ·
      refine ⟨13767435727526612952224717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36713161940070967872599245 13767435727526612952224717)
      ·
        refine ⟨5162788397822479857084269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13767435727526612952224717 5162788397822479857084269)
        ·
          refine ⟨1936045649183429946406601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5162788397822479857084269 1936045649183429946406601)
          ·
            refine ⟨1452034236887572459804951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1936045649183429946406601 1452034236887572459804951)
            ·
              refine ⟨2178051355331358689707427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452034236887572459804951 2178051355331358689707427)
              ·
                refine ⟨3267077032997038034561141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178051355331358689707427 3267077032997038034561141)
                ·
                  refine ⟨306288471843472315740107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267077032997038034561141 306288471843472315740107)
                  ·
                    rfl

theorem cell21_1342113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_1342113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342113 prefixEnd_1342113 := by exact prefixLift 1342113
  have htrace : WordTrace (prefixWord ++ tailWord_1342113) baseStart_1342113 baseEnd_1342113 := by
    simpa [prefixWord, tailWord_1342113, baseEnd_1342113] using wordTrace_append hprefix tailTrace_1342113
  have hstable : (prefixWord ++ tailWord_1342113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342113).length < 2 ^ (prefixWord ++ tailWord_1342113).sum := by decide
  have hdescent : baseEnd_1342113 < baseStart_1342113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342127 : List Nat := [1, 1, 2, 1, 2, 5, 4, 1, 4]
def baseStart_1342127 : Nat := 118140960795 + 1342127 * 2 ^ 59
def prefixEnd_1342127 : Nat := 4983230072969 + 3 ^ 40 * 1342127 * 2
def baseEnd_1342127 : Nat := 306291666834211402506745

theorem tailTrace_1342127 : CollatzResearch.WordTrace tailWord_1342127 prefixEnd_1342127 306291666834211402506745 := by
  unfold tailWord_1342127
  simp only [CollatzResearch.WordTrace]
  refine ⟨48951393208710570887808635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32634262139140380591872423 48951393208710570887808635)
  ·
    refine ⟨73427089813065856331712953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48951393208710570887808635 73427089813065856331712953)
    ·
      refine ⟨55070317359799392248784715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73427089813065856331712953 55070317359799392248784715)
      ·
        refine ⟨82605476039699088373177073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55070317359799392248784715 82605476039699088373177073)
        ·
          refine ⟨61954107029774316279882805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82605476039699088373177073 61954107029774316279882805)
          ·
            refine ⟨5808197534041342151239013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61954107029774316279882805 5808197534041342151239013)
            ·
              refine ⟨1089037037632751653357315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5808197534041342151239013 1089037037632751653357315)
              ·
                refine ⟨1633555556449127480035973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089037037632751653357315 1633555556449127480035973)
                ·
                  refine ⟨306291666834211402506745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633555556449127480035973 306291666834211402506745)
                  ·
                    rfl

theorem cell21_1342127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 1, 4].length) (baseStart_1342127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342127 prefixEnd_1342127 := by exact prefixLift 1342127
  have htrace : WordTrace (prefixWord ++ tailWord_1342127) baseStart_1342127 baseEnd_1342127 := by
    simpa [prefixWord, tailWord_1342127, baseEnd_1342127] using wordTrace_append hprefix tailTrace_1342127
  have hstable : (prefixWord ++ tailWord_1342127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342127).length < 2 ^ (prefixWord ++ tailWord_1342127).sum := by decide
  have hdescent : baseEnd_1342127 < baseStart_1342127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342164 : List Nat := [2, 4, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1342164 : Nat := 118140960795 + 1342164 * 2 ^ 59
def prefixEnd_1342164 : Nat := 4983230072969 + 3 ^ 40 * 1342164 * 2
def baseEnd_1342164 : Nat := 306300110738307560390003

theorem tailTrace_1342164 : CollatzResearch.WordTrace tailWord_1342164 prefixEnd_1342164 306300110738307560390003 := by
  unfold tailWord_1342164
  simp only [CollatzResearch.WordTrace]
  refine ⟨24476371354788263103452773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32635161806384350804603697 24476371354788263103452773)
  ·
    refine ⟨4589319629022799331897395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24476371354788263103452773 4589319629022799331897395)
    ·
      refine ⟨6883979443534198997846093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4589319629022799331897395 6883979443534198997846093)
      ·
        refine ⟨2581492291325324624192285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6883979443534198997846093 2581492291325324624192285)
        ·
          refine ⟨968059609246996734072107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2581492291325324624192285 968059609246996734072107)
          ·
            refine ⟨1452089413870495101108161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968059609246996734072107 1452089413870495101108161)
            ·
              refine ⟨1089067060402871325831121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452089413870495101108161 1089067060402871325831121)
              ·
                refine ⟨816800295302153494373341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089067060402871325831121 816800295302153494373341)
                ·
                  refine ⟨306300110738307560390003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816800295302153494373341 306300110738307560390003)
                  ·
                    rfl

theorem cell21_1342164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1342164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342164 prefixEnd_1342164 := by exact prefixLift 1342164
  have htrace : WordTrace (prefixWord ++ tailWord_1342164) baseStart_1342164 baseEnd_1342164 := by
    simpa [prefixWord, tailWord_1342164, baseEnd_1342164] using wordTrace_append hprefix tailTrace_1342164
  have hstable : (prefixWord ++ tailWord_1342164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342164).length < 2 ^ (prefixWord ++ tailWord_1342164).sum := by decide
  have hdescent : baseEnd_1342164 < baseStart_1342164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342206 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1342206 : Nat := 118140960795 + 1342206 * 2 ^ 59
def prefixEnd_1342206 : Nat := 4983230072969 + 3 ^ 40 * 1342206 * 2
def baseEnd_1342206 : Nat := 306309695710524820689917

theorem tailTrace_1342206 : CollatzResearch.WordTrace tailWord_1342206 prefixEnd_1342206 306309695710524820689917 := by
  unfold tailWord_1342206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6119284321928045922491809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32636183050282911586622981 6119284321928045922491809)
  ·
    refine ⟨4589463241446034441868857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6119284321928045922491809 4589463241446034441868857)
    ·
      refine ⟨3442097431084525831401643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4589463241446034441868857 3442097431084525831401643)
      ·
        refine ⟨5163146146626788747102465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3442097431084525831401643 5163146146626788747102465)
        ·
          refine ⟨3872359609970091560326849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5163146146626788747102465 3872359609970091560326849)
          ·
            refine ⟨2904269707477568670245137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872359609970091560326849 2904269707477568670245137)
            ·
              refine ⟨2178202280608176502683853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904269707477568670245137 2178202280608176502683853)
              ·
                refine ⟨816825855228066188506445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178202280608176502683853 816825855228066188506445)
                ·
                  refine ⟨306309695710524820689917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816825855228066188506445 306309695710524820689917)
                  ·
                    rfl

theorem cell21_1342206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1342206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342206 prefixEnd_1342206 := by exact prefixLift 1342206
  have htrace : WordTrace (prefixWord ++ tailWord_1342206) baseStart_1342206 baseEnd_1342206 := by
    simpa [prefixWord, tailWord_1342206, baseEnd_1342206] using wordTrace_append hprefix tailTrace_1342206
  have hstable : (prefixWord ++ tailWord_1342206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342206).length < 2 ^ (prefixWord ++ tailWord_1342206).sum := by decide
  have hdescent : baseEnd_1342206 < baseStart_1342206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342237 : List Nat := [1, 4, 2, 4, 1, 1, 3, 1, 4]
def baseStart_1342237 : Nat := 118140960795 + 1342237 * 2 ^ 59
def prefixEnd_1342237 : Nat := 4983230072969 + 3 ^ 40 * 1342237 * 2
def baseEnd_1342237 : Nat := 306316770332875655673187

theorem tailTrace_1342237 : CollatzResearch.WordTrace tailWord_1342237 prefixEnd_1342237 306316770332875655673187 := by
  unfold tailWord_1342237
  simp only [CollatzResearch.WordTrace]
  refine ⟨48955405238312059674312965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32636936825541373116208643 48955405238312059674312965)
  ·
    refine ⟨9179138482183511188933681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48955405238312059674312965 9179138482183511188933681)
    ·
      refine ⟨6884353861637633391700261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9179138482183511188933681 6884353861637633391700261)
      ·
        refine ⟨1290816349057056260943799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6884353861637633391700261 1290816349057056260943799)
        ·
          refine ⟨1936224523585584391415699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290816349057056260943799 1936224523585584391415699)
          ·
            refine ⟨2904336785378376587123549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936224523585584391415699 2904336785378376587123549)
            ·
              refine ⟨1089126294516891220171331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2904336785378376587123549 1089126294516891220171331)
              ·
                refine ⟨1633689441775336830256997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089126294516891220171331 1633689441775336830256997)
                ·
                  refine ⟨306316770332875655673187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1633689441775336830256997 306316770332875655673187)
                  ·
                    rfl

theorem cell21_1342237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_1342237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342237 prefixEnd_1342237 := by exact prefixLift 1342237
  have htrace : WordTrace (prefixWord ++ tailWord_1342237) baseStart_1342237 baseEnd_1342237 := by
    simpa [prefixWord, tailWord_1342237, baseEnd_1342237] using wordTrace_append hprefix tailTrace_1342237
  have hstable : (prefixWord ++ tailWord_1342237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342237).length < 2 ^ (prefixWord ++ tailWord_1342237).sum := by decide
  have hdescent : baseEnd_1342237 < baseStart_1342237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342341 : List Nat := [1, 3, 1, 1, 3, 3, 4, 2, 3]
def baseStart_1342341 : Nat := 118140960795 + 1342341 * 2 ^ 59
def prefixEnd_1342341 : Nat := 4983230072969 + 3 ^ 40 * 1342341 * 2
def baseEnd_1342341 : Nat := 306340504549794585939641

theorem tailTrace_1342341 : CollatzResearch.WordTrace tailWord_1342341 prefixEnd_1342341 306340504549794585939641 := by
  unfold tailWord_1342341
  simp only [CollatzResearch.WordTrace]
  refine ⟨48959198429935285436098877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32639465619956856957399251 48959198429935285436098877)
  ·
    refine ⟨18359699411225732038537079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48959198429935285436098877 18359699411225732038537079)
    ·
      refine ⟨27539549116838598057805619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18359699411225732038537079 27539549116838598057805619)
      ·
        refine ⟨41309323675257897086708429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27539549116838598057805619 41309323675257897086708429)
        ·
          refine ⟨15490996378221711407515661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41309323675257897086708429 15490996378221711407515661)
          ·
            refine ⟨5809123641833141777818373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15490996378221711407515661 5809123641833141777818373)
            ·
              refine ⟨1089210682843714083340945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5809123641833141777818373 1089210682843714083340945)
              ·
                refine ⟨816908012132785562505709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089210682843714083340945 816908012132785562505709)
                ·
                  refine ⟨306340504549794585939641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816908012132785562505709 306340504549794585939641)
                  ·
                    rfl

theorem cell21_1342341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_1342341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342341 prefixEnd_1342341 := by exact prefixLift 1342341
  have htrace : WordTrace (prefixWord ++ tailWord_1342341) baseStart_1342341 baseEnd_1342341 := by
    simpa [prefixWord, tailWord_1342341, baseEnd_1342341] using wordTrace_append hprefix tailTrace_1342341
  have hstable : (prefixWord ++ tailWord_1342341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342341).length < 2 ^ (prefixWord ++ tailWord_1342341).sum := by decide
  have hdescent : baseEnd_1342341 < baseStart_1342341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342358 : List Nat := [5, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1342358 : Nat := 118140960795 + 1342358 * 2 ^ 59
def prefixEnd_1342358 : Nat := 4983230072969 + 3 ^ 40 * 1342358 * 2
def baseEnd_1342358 : Nat := 306344384181406334156273

theorem tailTrace_1342358 : CollatzResearch.WordTrace tailWord_1342358 prefixEnd_1342358 306344384181406334156273 := by
  unfold tailWord_1342358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059988654429606083716733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32639878980582464892978485 3059988654429606083716733)
  ·
    refine ⟨1147495745411102281393775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3059988654429606083716733 1147495745411102281393775)
    ·
      refine ⟨1721243618116653422090663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147495745411102281393775 1721243618116653422090663)
      ·
        refine ⟨2581865427174980133135995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721243618116653422090663 2581865427174980133135995)
        ·
          refine ⟨3872798140762470199703993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581865427174980133135995 3872798140762470199703993)
          ·
            refine ⟨2904598605571852649777995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3872798140762470199703993 2904598605571852649777995)
            ·
              refine ⟨4356897908357778974666993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904598605571852649777995 4356897908357778974666993)
              ·
                refine ⟨3267673431268334231000245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4356897908357778974666993 3267673431268334231000245)
                ·
                  refine ⟨306344384181406334156273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3267673431268334231000245 306344384181406334156273)
                  ·
                    rfl

theorem cell21_1342358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1342358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342358 prefixEnd_1342358 := by exact prefixLift 1342358
  have htrace : WordTrace (prefixWord ++ tailWord_1342358) baseStart_1342358 baseEnd_1342358 := by
    simpa [prefixWord, tailWord_1342358, baseEnd_1342358] using wordTrace_append hprefix tailTrace_1342358
  have hstable : (prefixWord ++ tailWord_1342358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342358).length < 2 ^ (prefixWord ++ tailWord_1342358).sum := by decide
  have hdescent : baseEnd_1342358 < baseStart_1342358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342400 : List Nat := [2, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_1342400 : Nat := 118140960795 + 1342400 * 2 ^ 59
def prefixEnd_1342400 : Nat := 4983230072969 + 3 ^ 40 * 1342400 * 2
def baseEnd_1342400 : Nat := 306353969153623594456187

theorem tailTrace_1342400 : CollatzResearch.WordTrace tailWord_1342400 prefixEnd_1342400 306353969153623594456187 := by
  unfold tailWord_1342400
  simp only [CollatzResearch.WordTrace]
  refine ⟨24480675168360769256248327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32640900224481025674997769 24480675168360769256248327)
  ·
    refine ⟨36721012752541153884372491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24480675168360769256248327 36721012752541153884372491)
    ·
      refine ⟨55081519128811730826558737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36721012752541153884372491 55081519128811730826558737)
      ·
        refine ⟨41311139346608798119919053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55081519128811730826558737 41311139346608798119919053)
        ·
          refine ⟨15491677254978299294969645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41311139346608798119919053 15491677254978299294969645)
          ·
            refine ⟨5809378970616862235613617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15491677254978299294969645 5809378970616862235613617)
            ·
              refine ⟨4357034227962646676710213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5809378970616862235613617 4357034227962646676710213)
              ·
                refine ⟨816943917742996251883165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4357034227962646676710213 816943917742996251883165)
                ·
                  refine ⟨306353969153623594456187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816943917742996251883165 306353969153623594456187)
                  ·
                    rfl

theorem cell21_1342400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_1342400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342400 prefixEnd_1342400 := by exact prefixLift 1342400
  have htrace : WordTrace (prefixWord ++ tailWord_1342400) baseStart_1342400 baseEnd_1342400 := by
    simpa [prefixWord, tailWord_1342400, baseEnd_1342400] using wordTrace_append hprefix tailTrace_1342400
  have hstable : (prefixWord ++ tailWord_1342400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342400).length < 2 ^ (prefixWord ++ tailWord_1342400).sum := by decide
  have hdescent : baseEnd_1342400 < baseStart_1342400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342434 : List Nat := [3, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1342434 : Nat := 118140960795 + 1342434 * 2 ^ 59
def prefixEnd_1342434 : Nat := 4983230072969 + 3 ^ 40 * 1342434 * 2
def baseEnd_1342434 : Nat := 306361728416847090889451

theorem tailTrace_1342434 : CollatzResearch.WordTrace tailWord_1342434 prefixEnd_1342434 306361728416847090889451 := by
  unfold tailWord_1342434
  simp only [CollatzResearch.WordTrace]
  refine ⟨12240647604649590579808589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32641726945732241546156237 12240647604649590579808589)
  ·
    refine ⟨4590242851743596467428221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12240647604649590579808589 4590242851743596467428221)
    ·
      refine ⟨1721341069403848675285583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4590242851743596467428221 1721341069403848675285583)
      ·
        refine ⟨2582011604105773012928375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721341069403848675285583 2582011604105773012928375)
        ·
          refine ⟨3873017406158659519392563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2582011604105773012928375 3873017406158659519392563)
          ·
            refine ⟨5809526109237989279088845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3873017406158659519392563 5809526109237989279088845)
            ·
              refine ⟨2178572290964245979658317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5809526109237989279088845 2178572290964245979658317)
              ·
                refine ⟨816964609111592242371869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178572290964245979658317 816964609111592242371869)
                ·
                  refine ⟨306361728416847090889451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816964609111592242371869 306361728416847090889451)
                  ·
                    rfl

theorem cell21_1342434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1342434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342434 prefixEnd_1342434 := by exact prefixLift 1342434
  have htrace : WordTrace (prefixWord ++ tailWord_1342434) baseStart_1342434 baseEnd_1342434 := by
    simpa [prefixWord, tailWord_1342434, baseEnd_1342434] using wordTrace_append hprefix tailTrace_1342434
  have hstable : (prefixWord ++ tailWord_1342434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342434).length < 2 ^ (prefixWord ++ tailWord_1342434).sum := by decide
  have hdescent : baseEnd_1342434 < baseStart_1342434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342462 : List Nat := [4, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1342462 : Nat := 118140960795 + 1342462 * 2 ^ 59
def prefixEnd_1342462 : Nat := 4983230072969 + 3 ^ 40 * 1342462 * 2
def baseEnd_1342462 : Nat := 102122706132775088140909

theorem tailTrace_1342462 : CollatzResearch.WordTrace tailWord_1342462 prefixEnd_1342462 102122706132775088140909 := by
  unfold tailWord_1342462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120451457812115387656705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32642407774997948734169093 6120451457812115387656705)
  ·
    refine ⟨4590338593359086540742529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6120451457812115387656705 4590338593359086540742529)
    ·
      refine ⟨3442753945019314905556897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4590338593359086540742529 3442753945019314905556897)
      ·
        refine ⟨2582065458764486179167673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3442753945019314905556897 2582065458764486179167673)
        ·
          refine ⟨1936549094073364634375755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2582065458764486179167673 1936549094073364634375755)
          ·
            refine ⟨2904823641110046951563633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936549094073364634375755 2904823641110046951563633)
            ·
              refine ⟨2178617730832535213672725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2904823641110046951563633 2178617730832535213672725)
              ·
                refine ⟨102122706132775088140909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2178617730832535213672725 102122706132775088140909)
                ·
                  rfl

theorem cell21_1342462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1342462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342462 prefixEnd_1342462 := by exact prefixLift 1342462
  have htrace : WordTrace (prefixWord ++ tailWord_1342462) baseStart_1342462 baseEnd_1342462 := by
    simpa [prefixWord, tailWord_1342462, baseEnd_1342462] using wordTrace_append hprefix tailTrace_1342462
  have hstable : (prefixWord ++ tailWord_1342462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342462).length < 2 ^ (prefixWord ++ tailWord_1342462).sum := by decide
  have hdescent : baseEnd_1342462 < baseStart_1342462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342521 : List Nat := [1, 2, 1, 5, 2, 3, 1, 6]
def baseStart_1342521 : Nat := 118140960795 + 1342521 * 2 ^ 59
def prefixEnd_1342521 : Nat := 4983230072969 + 3 ^ 40 * 1342521 * 2
def baseEnd_1342521 : Nat := 102127194334051424313091

theorem tailTrace_1342521 : CollatzResearch.WordTrace tailWord_1342521 prefixEnd_1342521 102127194334051424313091 := by
  unfold tailWord_1342521
  simp only [CollatzResearch.WordTrace]
  refine ⟨48965763569283176177651417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32643842379522117451767611 48965763569283176177651417)
  ·
    refine ⟨36724322676962382133238563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48965763569283176177651417 36724322676962382133238563)
    ·
      refine ⟨55086484015443573199857845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36724322676962382133238563 55086484015443573199857845)
      ·
        refine ⟨5164357876447834987486673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55086484015443573199857845 5164357876447834987486673)
        ·
          refine ⟨3873268407335876240615005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5164357876447834987486673 3873268407335876240615005)
          ·
            refine ⟨1452475652750953590230627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3873268407335876240615005 1452475652750953590230627)
            ·
              refine ⟨2178713479126430385345941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452475652750953590230627 2178713479126430385345941)
              ·
                refine ⟨102127194334051424313091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2178713479126430385345941 102127194334051424313091)
                ·
                  rfl

theorem cell21_1342521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 6].length) (baseStart_1342521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342521 prefixEnd_1342521 := by exact prefixLift 1342521
  have htrace : WordTrace (prefixWord ++ tailWord_1342521) baseStart_1342521 baseEnd_1342521 := by
    simpa [prefixWord, tailWord_1342521, baseEnd_1342521] using wordTrace_append hprefix tailTrace_1342521
  have hstable : (prefixWord ++ tailWord_1342521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342521).length < 2 ^ (prefixWord ++ tailWord_1342521).sum := by decide
  have hdescent : baseEnd_1342521 < baseStart_1342521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342535 : List Nat := [1, 1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_1342535 : Nat := 118140960795 + 1342535 * 2 ^ 59
def prefixEnd_1342535 : Nat := 4983230072969 + 3 ^ 40 * 1342535 * 2
def baseEnd_1342535 : Nat := 306384777992893359705911

theorem tailTrace_1342535 : CollatzResearch.WordTrace tailWord_1342535 prefixEnd_1342535 306384777992893359705911 := by
  unfold tailWord_1342535
  simp only [CollatzResearch.WordTrace]
  refine ⟨48966274191232456568661059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32644182794154971045774039 48966274191232456568661059)
  ·
    refine ⟨73449411286848684852991589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48966274191232456568661059 73449411286848684852991589)
    ·
      refine ⟨13771764616284128409935923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73449411286848684852991589 13771764616284128409935923)
      ·
        refine ⟨20657646924426192614903885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13771764616284128409935923 20657646924426192614903885)
        ·
          refine ⟨7746617596659822230588957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20657646924426192614903885 7746617596659822230588957)
          ·
            refine ⟨2904981598747433336470859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7746617596659822230588957 2904981598747433336470859)
            ·
              refine ⟨4357472398121150004706289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904981598747433336470859 4357472398121150004706289)
              ·
                refine ⟨3268104298590862503529717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4357472398121150004706289 3268104298590862503529717)
                ·
                  refine ⟨306384777992893359705911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3268104298590862503529717 306384777992893359705911)
                  ·
                    rfl

theorem cell21_1342535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_1342535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342535 prefixEnd_1342535 := by exact prefixLift 1342535
  have htrace : WordTrace (prefixWord ++ tailWord_1342535) baseStart_1342535 baseEnd_1342535 := by
    simpa [prefixWord, tailWord_1342535, baseEnd_1342535] using wordTrace_append hprefix tailTrace_1342535
  have hstable : (prefixWord ++ tailWord_1342535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342535).length < 2 ^ (prefixWord ++ tailWord_1342535).sum := by decide
  have hdescent : baseEnd_1342535 < baseStart_1342535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342549 : List Nat := [1, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_1342549 : Nat := 118140960795 + 1342549 * 2 ^ 59
def prefixEnd_1342549 : Nat := 4983230072969 + 3 ^ 40 * 1342549 * 2
def baseEnd_1342549 : Nat := 306387972983632446472549

theorem tailTrace_1342549 : CollatzResearch.WordTrace tailWord_1342549 prefixEnd_1342549 306387972983632446472549 := by
  unfold tailWord_1342549
  simp only [CollatzResearch.WordTrace]
  refine ⟨48966784813181736959670701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32644523208787824639780467 48966784813181736959670701)
  ·
    refine ⟨18362544304943151359876513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48966784813181736959670701 18362544304943151359876513)
    ·
      refine ⟨13771908228707363519907385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18362544304943151359876513 13771908228707363519907385)
      ·
        refine ⟨10328931171530522639930539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13771908228707363519907385 10328931171530522639930539)
        ·
          refine ⟨15493396757295783959895809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10328931171530522639930539 15493396757295783959895809)
          ·
            refine ⟨11620047567971837969921857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15493396757295783959895809 11620047567971837969921857)
            ·
              refine ⟨8715035675978878477441393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11620047567971837969921857 8715035675978878477441393)
              ·
                refine ⟨6536276756984158858081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8715035675978878477441393 6536276756984158858081045)
                ·
                  refine ⟨306387972983632446472549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6536276756984158858081045 306387972983632446472549)
                  ·
                    rfl

theorem cell21_1342549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_1342549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342549 prefixEnd_1342549 := by exact prefixLift 1342549
  have htrace : WordTrace (prefixWord ++ tailWord_1342549) baseStart_1342549 baseEnd_1342549 := by
    simpa [prefixWord, tailWord_1342549, baseEnd_1342549] using wordTrace_append hprefix tailTrace_1342549
  have hstable : (prefixWord ++ tailWord_1342549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342549).length < 2 ^ (prefixWord ++ tailWord_1342549).sum := by decide
  have hdescent : baseEnd_1342549 < baseStart_1342549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342552 : List Nat := [2, 1, 2, 2, 1, 3, 4, 3, 3]
def baseStart_1342552 : Nat := 118140960795 + 1342552 * 2 ^ 59
def prefixEnd_1342552 : Nat := 4983230072969 + 3 ^ 40 * 1342552 * 2
def baseEnd_1342552 : Nat := 306388657624505107922543

theorem tailTrace_1342552 : CollatzResearch.WordTrace tailWord_1342552 prefixEnd_1342552 306388657624505107922543 := by
  unfold tailWord_1342552
  simp only [CollatzResearch.WordTrace]
  refine ⟨24483447116085434236014955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32644596154780578981353273 24483447116085434236014955)
  ·
    refine ⟨36725170674128151354022433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24483447116085434236014955 36725170674128151354022433)
    ·
      refine ⟨27543878005596113515516825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36725170674128151354022433 27543878005596113515516825)
      ·
        refine ⟨20657908504197085136637619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27543878005596113515516825 20657908504197085136637619)
        ·
          refine ⟨30986862756295627704956429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20657908504197085136637619 30986862756295627704956429)
          ·
            refine ⟨11620073533610860389358661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30986862756295627704956429 11620073533610860389358661)
            ·
              refine ⟨2178763787552036323004749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11620073533610860389358661 2178763787552036323004749)
              ·
                refine ⟨817036420332013621126781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2178763787552036323004749 817036420332013621126781)
                ·
                  refine ⟨306388657624505107922543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817036420332013621126781 306388657624505107922543)
                  ·
                    rfl

theorem cell21_1342552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_1342552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342552 prefixEnd_1342552 := by exact prefixLift 1342552
  have htrace : WordTrace (prefixWord ++ tailWord_1342552) baseStart_1342552 baseEnd_1342552 := by
    simpa [prefixWord, tailWord_1342552, baseEnd_1342552] using wordTrace_append hprefix tailTrace_1342552
  have hstable : (prefixWord ++ tailWord_1342552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342552).length < 2 ^ (prefixWord ++ tailWord_1342552).sum := by decide
  have hdescent : baseEnd_1342552 < baseStart_1342552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342625 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_1342625 : Nat := 118140960795 + 1342625 * 2 ^ 59
def prefixEnd_1342625 : Nat := 4983230072969 + 3 ^ 40 * 1342625 * 2
def baseEnd_1342625 : Nat := 306405317219073203205727

theorem tailTrace_1342625 : CollatzResearch.WordTrace tailWord_1342625 prefixEnd_1342625 306405317219073203205727 := by
  unfold tailWord_1342625
  simp only [CollatzResearch.WordTrace]
  refine ⟨48969556760906401939437329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32646371173937601292958219 48969556760906401939437329)
  ·
    refine ⟨36727167570679801454577997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48969556760906401939437329 36727167570679801454577997)
    ·
      refine ⟨13772687839004925545466749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36727167570679801454577997 13772687839004925545466749)
      ·
        refine ⟨5164757939626847079550031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13772687839004925545466749 5164757939626847079550031)
        ·
          refine ⟨7747136909440270619325047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164757939626847079550031 7747136909440270619325047)
          ·
            refine ⟨11620705364160405928987571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7747136909440270619325047 11620705364160405928987571)
            ·
              refine ⟨17431058046240608893481357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11620705364160405928987571 17431058046240608893481357)
              ·
                refine ⟨6536646767340228335055509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17431058046240608893481357 6536646767340228335055509)
                ·
                  refine ⟨306405317219073203205727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6536646767340228335055509 306405317219073203205727)
                  ·
                    rfl

theorem cell21_1342625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_1342625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342625 prefixEnd_1342625 := by exact prefixLift 1342625
  have htrace : WordTrace (prefixWord ++ tailWord_1342625) baseStart_1342625 baseEnd_1342625 := by
    simpa [prefixWord, tailWord_1342625, baseEnd_1342625] using wordTrace_append hprefix tailTrace_1342625
  have hstable : (prefixWord ++ tailWord_1342625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342625).length < 2 ^ (prefixWord ++ tailWord_1342625).sum := by decide
  have hdescent : baseEnd_1342625 < baseStart_1342625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342628 : List Nat := [2, 3, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1342628 : Nat := 118140960795 + 1342628 * 2 ^ 59
def prefixEnd_1342628 : Nat := 4983230072969 + 3 ^ 40 * 1342628 * 2
def baseEnd_1342628 : Nat := 306406001859945864655721

theorem tailTrace_1342628 : CollatzResearch.WordTrace tailWord_1342628 prefixEnd_1342628 306406001859945864655721 := by
  unfold tailWord_1342628
  simp only [CollatzResearch.WordTrace]
  refine ⟨24484833089947766725898269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32646444119930355634531025 24484833089947766725898269)
  ·
    refine ⟨9181812408730412522211851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24484833089947766725898269 9181812408730412522211851)
    ·
      refine ⟨13772718613095618783317777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9181812408730412522211851 13772718613095618783317777)
      ·
        refine ⟨10329538959821714087488333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13772718613095618783317777 10329538959821714087488333)
        ·
          refine ⟨3873577109933142782808125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10329538959821714087488333 3873577109933142782808125)
          ·
            refine ⟨1452591416224928543553047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3873577109933142782808125 1452591416224928543553047)
            ·
              refine ⟨2178887124337392815329571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452591416224928543553047 2178887124337392815329571)
              ·
                refine ⟨3268330686506089222994357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2178887124337392815329571 3268330686506089222994357)
                ·
                  refine ⟨306406001859945864655721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3268330686506089222994357 306406001859945864655721)
                  ·
                    rfl

theorem cell21_1342628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1342628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342628 prefixEnd_1342628 := by exact prefixLift 1342628
  have htrace : WordTrace (prefixWord ++ tailWord_1342628) baseStart_1342628 baseEnd_1342628 := by
    simpa [prefixWord, tailWord_1342628, baseEnd_1342628] using wordTrace_append hprefix tailTrace_1342628
  have hstable : (prefixWord ++ tailWord_1342628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342628).length < 2 ^ (prefixWord ++ tailWord_1342628).sum := by decide
  have hdescent : baseEnd_1342628 < baseStart_1342628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342639 : List Nat := [1, 1, 2, 1, 2, 3, 3, 8]
def baseStart_1342639 : Nat := 118140960795 + 1342639 * 2 ^ 59
def prefixEnd_1342639 : Nat := 4983230072969 + 3 ^ 40 * 1342639 * 2
def baseEnd_1342639 : Nat := 102136170736604096657455

theorem tailTrace_1342639 : CollatzResearch.WordTrace tailWord_1342639 prefixEnd_1342639 102136170736604096657455 := by
  unfold tailWord_1342639
  simp only [CollatzResearch.WordTrace]
  refine ⟨48970067382855682330446971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32646711588570454886964647 48970067382855682330446971)
  ·
    refine ⟨73455101074283523495670457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48970067382855682330446971 73455101074283523495670457)
    ·
      refine ⟨55091325805712642621752843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73455101074283523495670457 55091325805712642621752843)
      ·
        refine ⟨82636988708568963932629265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55091325805712642621752843 82636988708568963932629265)
        ·
          refine ⟨61977741531426722949471949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82636988708568963932629265 61977741531426722949471949)
          ·
            refine ⟨23241653074285021106051981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61977741531426722949471949 23241653074285021106051981)
            ·
              refine ⟨8715619902856882914769493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23241653074285021106051981 8715619902856882914769493)
              ·
                refine ⟨102136170736604096657455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8715619902856882914769493 102136170736604096657455)
                ·
                  rfl

theorem cell21_1342639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_1342639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342639 prefixEnd_1342639 := by exact prefixLift 1342639
  have htrace : WordTrace (prefixWord ++ tailWord_1342639) baseStart_1342639 baseEnd_1342639 := by
    simpa [prefixWord, tailWord_1342639, baseEnd_1342639] using wordTrace_append hprefix tailTrace_1342639
  have hstable : (prefixWord ++ tailWord_1342639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342639).length < 2 ^ (prefixWord ++ tailWord_1342639).sum := by decide
  have hdescent : baseEnd_1342639 < baseStart_1342639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342642 : List Nat := [3, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_1342642 : Nat := 118140960795 + 1342642 * 2 ^ 59
def prefixEnd_1342642 : Nat := 4983230072969 + 3 ^ 40 * 1342642 * 2
def baseEnd_1342642 : Nat := 306409196850684951422359

theorem tailTrace_1342642 : CollatzResearch.WordTrace tailWord_1342642 prefixEnd_1342642 306409196850684951422359 := by
  unfold tailWord_1342642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12242544200461203460701545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32646784534563209228537453 12242544200461203460701545)
  ·
    refine ⟨9181908150345902595526159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12242544200461203460701545 9181908150345902595526159)
    ·
      refine ⟨13772862225518853893289239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9181908150345902595526159 13772862225518853893289239)
      ·
        refine ⟨20659293338278280839933859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13772862225518853893289239 20659293338278280839933859)
        ·
          refine ⟨30988940007417421259900789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20659293338278280839933859 30988940007417421259900789)
          ·
            refine ⟨2905213125695383243115699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30988940007417421259900789 2905213125695383243115699)
            ·
              refine ⟨4357819688543074864673549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905213125695383243115699 4357819688543074864673549)
              ·
                refine ⟨1634182383203653074252581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4357819688543074864673549 1634182383203653074252581)
                ·
                  refine ⟨306409196850684951422359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634182383203653074252581 306409196850684951422359)
                  ·
                    rfl

theorem cell21_1342642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_1342642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342642 prefixEnd_1342642 := by exact prefixLift 1342642
  have htrace : WordTrace (prefixWord ++ tailWord_1342642) baseStart_1342642 baseEnd_1342642 := by
    simpa [prefixWord, tailWord_1342642, baseEnd_1342642] using wordTrace_append hprefix tailTrace_1342642
  have hstable : (prefixWord ++ tailWord_1342642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342642).length < 2 ^ (prefixWord ++ tailWord_1342642).sum := by decide
  have hdescent : baseEnd_1342642 < baseStart_1342642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342676 : List Nat := [2, 4, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1342676 : Nat := 118140960795 + 1342676 * 2 ^ 59
def prefixEnd_1342676 : Nat := 4983230072969 + 3 ^ 40 * 1342676 * 2
def baseEnd_1342676 : Nat := 306416956113908447855623

theorem tailTrace_1342676 : CollatzResearch.WordTrace tailWord_1342676 prefixEnd_1342676 306416956113908447855623 := by
  unfold tailWord_1342676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24485708441860818824771941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32647611255814425099695921 24485708441860818824771941)
  ·
    refine ⟨4591070332848903529644739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24485708441860818824771941 4591070332848903529644739)
    ·
      refine ⟨6886605499273355294467109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591070332848903529644739 6886605499273355294467109)
      ·
        refine ⟨1291238531113754117712583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6886605499273355294467109 1291238531113754117712583)
        ·
          refine ⟨1936857796670631176568875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291238531113754117712583 1936857796670631176568875)
          ·
            refine ⟨2905286695005946764853313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936857796670631176568875 2905286695005946764853313)
            ·
              refine ⟨2178965021254460073639985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2905286695005946764853313 2178965021254460073639985)
              ·
                refine ⟨1634223765940845055229989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2178965021254460073639985 1634223765940845055229989)
                ·
                  refine ⟨306416956113908447855623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634223765940845055229989 306416956113908447855623)
                  ·
                    rfl

theorem cell21_1342676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1342676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342676 prefixEnd_1342676 := by exact prefixLift 1342676
  have htrace : WordTrace (prefixWord ++ tailWord_1342676) baseStart_1342676 baseEnd_1342676 := by
    simpa [prefixWord, tailWord_1342676, baseEnd_1342676] using wordTrace_append hprefix tailTrace_1342676
  have hstable : (prefixWord ++ tailWord_1342676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342676).length < 2 ^ (prefixWord ++ tailWord_1342676).sum := by decide
  have hdescent : baseEnd_1342676 < baseStart_1342676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342780 : List Nat := [2, 2, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1342780 : Nat := 118140960795 + 1342780 * 2 ^ 59
def prefixEnd_1342780 : Nat := 4983230072969 + 3 ^ 40 * 1342780 * 2
def baseEnd_1342780 : Nat := 306440690330827378122077

theorem tailTrace_1342780 : CollatzResearch.WordTrace tailWord_1342780 prefixEnd_1342780 306440690330827378122077 := by
  unfold tailWord_1342780
  simp only [CollatzResearch.WordTrace]
  refine ⟨24487605037672431705664897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32650140050229908940886529 24487605037672431705664897)
  ·
    refine ⟨18365703778254323779248673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24487605037672431705664897 18365703778254323779248673)
    ·
      refine ⟨13774277833690742834436505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18365703778254323779248673 13774277833690742834436505)
      ·
        refine ⟨10330708375268057125827379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13774277833690742834436505 10330708375268057125827379)
        ·
          refine ⟨15496062562902085688741069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330708375268057125827379 15496062562902085688741069)
          ·
            refine ⟨5811023461088282133277901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15496062562902085688741069 5811023461088282133277901)
            ·
              refine ⟨2179133797908105799979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5811023461088282133277901 2179133797908105799979213)
              ·
                refine ⟨817175174215539674992205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2179133797908105799979213 817175174215539674992205)
                ·
                  refine ⟨306440690330827378122077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817175174215539674992205 306440690330827378122077)
                  ·
                    rfl

theorem cell21_1342780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1342780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342780 prefixEnd_1342780 := by exact prefixLift 1342780
  have htrace : WordTrace (prefixWord ++ tailWord_1342780) baseStart_1342780 baseEnd_1342780 := by
    simpa [prefixWord, tailWord_1342780, baseEnd_1342780] using wordTrace_append hprefix tailTrace_1342780
  have hstable : (prefixWord ++ tailWord_1342780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342780).length < 2 ^ (prefixWord ++ tailWord_1342780).sum := by decide
  have hdescent : baseEnd_1342780 < baseStart_1342780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342791 : List Nat := [1, 1, 4, 1, 2, 3, 9]
def baseStart_1342791 : Nat := 118140960795 + 1342791 * 2 ^ 59
def prefixEnd_1342791 : Nat := 4983230072969 + 3 ^ 40 * 1342791 * 2
def baseEnd_1342791 : Nat := 34049244520077089270969

theorem tailTrace_1342791 : CollatzResearch.WordTrace tailWord_1342791 prefixEnd_1342791 34049244520077089270969 := by
  unfold tailWord_1342791
  simp only [CollatzResearch.WordTrace]
  refine ⟨48975611278305012289980227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32650407518870008193320151 48975611278305012289980227)
  ·
    refine ⟨73463416917457518434970341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48975611278305012289980227 73463416917457518434970341)
    ·
      refine ⟨13774390672023284706556939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73463416917457518434970341 13774390672023284706556939)
      ·
        refine ⟨20661586008034927059835409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13774390672023284706556939 20661586008034927059835409)
        ·
          refine ⟨15496189506026195294876557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20661586008034927059835409 15496189506026195294876557)
          ·
            refine ⟨5811071064759823235578709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15496189506026195294876557 5811071064759823235578709)
            ·
              refine ⟨34049244520077089270969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5811071064759823235578709 34049244520077089270969)
              ·
                rfl

theorem cell21_1342791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 9].length) (baseStart_1342791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342791 prefixEnd_1342791 := by exact prefixLift 1342791
  have htrace : WordTrace (prefixWord ++ tailWord_1342791) baseStart_1342791 baseEnd_1342791 := by
    simpa [prefixWord, tailWord_1342791, baseEnd_1342791] using wordTrace_append hprefix tailTrace_1342791
  have hstable : (prefixWord ++ tailWord_1342791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342791).length < 2 ^ (prefixWord ++ tailWord_1342791).sum := by decide
  have hdescent : baseEnd_1342791 < baseStart_1342791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342839 : List Nat := [1, 1, 3, 1, 1, 2, 4, 5, 3]
def baseStart_1342839 : Nat := 118140960795 + 1342839 * 2 ^ 59
def prefixEnd_1342839 : Nat := 4983230072969 + 3 ^ 40 * 1342839 * 2
def baseEnd_1342839 : Nat := 306454154934656386638623

theorem tailTrace_1342839 : CollatzResearch.WordTrace tailWord_1342839 prefixEnd_1342839 306454154934656386638623 := by
  unfold tailWord_1342839
  simp only [CollatzResearch.WordTrace]
  refine ⟨48977361982131116487727571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32651574654754077658485047 48977361982131116487727571)
  ·
    refine ⟨73466042973196674731591357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48977361982131116487727571 73466042973196674731591357)
    ·
      refine ⟨27549766114948753024346759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73466042973196674731591357 27549766114948753024346759)
      ·
        refine ⟨41324649172423129536520139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27549766114948753024346759 41324649172423129536520139)
        ·
          refine ⟨61986973758634694304780209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41324649172423129536520139 61986973758634694304780209)
          ·
            refine ⟨46490230318976020728585157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61986973758634694304780209 46490230318976020728585157)
            ·
              refine ⟨8716918184808003886609717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46490230318976020728585157 8716918184808003886609717)
              ·
                refine ⟨817211079825750364369661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8716918184808003886609717 817211079825750364369661)
                ·
                  refine ⟨306454154934656386638623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817211079825750364369661 306454154934656386638623)
                  ·
                    rfl

theorem cell21_1342839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 5, 3].length) (baseStart_1342839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342839 prefixEnd_1342839 := by exact prefixLift 1342839
  have htrace : WordTrace (prefixWord ++ tailWord_1342839) baseStart_1342839 baseEnd_1342839 := by
    simpa [prefixWord, tailWord_1342839, baseEnd_1342839] using wordTrace_append hprefix tailTrace_1342839
  have hstable : (prefixWord ++ tailWord_1342839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342839).length < 2 ^ (prefixWord ++ tailWord_1342839).sum := by decide
  have hdescent : baseEnd_1342839 < baseStart_1342839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342853 : List Nat := [1, 3, 1, 1, 3, 1, 3, 4, 4]
def baseStart_1342853 : Nat := 118140960795 + 1342853 * 2 ^ 59
def prefixEnd_1342853 : Nat := 4983230072969 + 3 ^ 40 * 1342853 * 2
def baseEnd_1342853 : Nat := 306457349925395473405261

theorem tailTrace_1342853 : CollatzResearch.WordTrace tailWord_1342853 prefixEnd_1342853 306457349925395473405261 := by
  unfold tailWord_1342853
  simp only [CollatzResearch.WordTrace]
  refine ⟨48977872604080396878737213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32651915069386931252491475 48977872604080396878737213)
  ·
    refine ⟨18366702226530148829526455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48977872604080396878737213 18366702226530148829526455)
    ·
      refine ⟨27550053339795223244289683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18366702226530148829526455 27550053339795223244289683)
      ·
        refine ⟨41325080009692834866434525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27550053339795223244289683 41325080009692834866434525)
        ·
          refine ⟨15496905003634813074912947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41325080009692834866434525 15496905003634813074912947)
          ·
            refine ⟨23245357505452219612369421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15496905003634813074912947 23245357505452219612369421)
            ·
              refine ⟨8717009064544582354638533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23245357505452219612369421 8717009064544582354638533)
              ·
                refine ⟨1634439199602109191494725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8717009064544582354638533 1634439199602109191494725)
                ·
                  refine ⟨306457349925395473405261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634439199602109191494725 306457349925395473405261)
                  ·
                    rfl

theorem cell21_1342853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_1342853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342853 prefixEnd_1342853 := by exact prefixLift 1342853
  have htrace : WordTrace (prefixWord ++ tailWord_1342853) baseStart_1342853 baseEnd_1342853 := by
    simpa [prefixWord, tailWord_1342853, baseEnd_1342853] using wordTrace_append hprefix tailTrace_1342853
  have hstable : (prefixWord ++ tailWord_1342853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342853).length < 2 ^ (prefixWord ++ tailWord_1342853).sum := by decide
  have hdescent : baseEnd_1342853 < baseStart_1342853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342856 : List Nat := [2, 1, 3, 3, 1, 3, 1, 4, 3]
def baseStart_1342856 : Nat := 118140960795 + 1342856 * 2 ^ 59
def prefixEnd_1342856 : Nat := 4983230072969 + 3 ^ 40 * 1342856 * 2
def baseEnd_1342856 : Nat := 306458034566268134855255

theorem tailTrace_1342856 : CollatzResearch.WordTrace tailWord_1342856 prefixEnd_1342856 306458034566268134855255 := by
  unfold tailWord_1342856
  simp only [CollatzResearch.WordTrace]
  refine ⟨24488991011534764195548211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32651988015379685594064281 24488991011534764195548211)
  ·
    refine ⟨36733486517302146293322317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24488991011534764195548211 36733486517302146293322317)
    ·
      refine ⟨13775057443988304859995869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36733486517302146293322317 13775057443988304859995869)
      ·
        refine ⟨5165646541495614322498451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13775057443988304859995869 5165646541495614322498451)
        ·
          refine ⟨7748469812243421483747677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5165646541495614322498451 7748469812243421483747677)
          ·
            refine ⟨2905676179591283056405379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7748469812243421483747677 2905676179591283056405379)
            ·
              refine ⟨4358514269386924584608069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905676179591283056405379 4358514269386924584608069)
              ·
                refine ⟨817221425510048359614013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4358514269386924584608069 817221425510048359614013)
                ·
                  refine ⟨306458034566268134855255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817221425510048359614013 306458034566268134855255)
                  ·
                    rfl

theorem cell21_1342856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_1342856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342856 prefixEnd_1342856 := by exact prefixLift 1342856
  have htrace : WordTrace (prefixWord ++ tailWord_1342856) baseStart_1342856 baseEnd_1342856 := by
    simpa [prefixWord, tailWord_1342856, baseEnd_1342856] using wordTrace_append hprefix tailTrace_1342856
  have hstable : (prefixWord ++ tailWord_1342856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342856).length < 2 ^ (prefixWord ++ tailWord_1342856).sum := by decide
  have hdescent : baseEnd_1342856 < baseStart_1342856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342915 : List Nat := [1, 1, 1, 3, 1, 1, 6, 4, 3]
def baseStart_1342915 : Nat := 118140960795 + 1342915 * 2 ^ 59
def prefixEnd_1342915 : Nat := 4983230072969 + 3 ^ 40 * 1342915 * 2
def baseEnd_1342915 : Nat := 306471499170097143371801

theorem tailTrace_1342915 : CollatzResearch.WordTrace tailWord_1342915 prefixEnd_1342915 306471499170097143371801 := by
  unfold tailWord_1342915
  simp only [CollatzResearch.WordTrace]
  refine ⟨48980133929855781467494199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32653422619903854311662799 48980133929855781467494199)
  ·
    refine ⟨73470200894783672201241299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48980133929855781467494199 73470200894783672201241299)
    ·
      refine ⟨110205301342175508301861949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73470200894783672201241299 110205301342175508301861949)
      ·
        refine ⟨41326988003315815613198231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110205301342175508301861949 41326988003315815613198231)
        ·
          refine ⟨61990482004973723419797347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41326988003315815613198231 61990482004973723419797347)
          ·
            refine ⟨92985723007460585129696021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61990482004973723419797347 92985723007460585129696021)
            ·
              refine ⟨4358705765974714927954501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 92985723007460585129696021 4358705765974714927954501)
              ·
                refine ⟨817257331120259048991469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4358705765974714927954501 817257331120259048991469)
                ·
                  refine ⟨306471499170097143371801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817257331120259048991469 306471499170097143371801)
                  ·
                    rfl

theorem cell21_1342915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 4, 3].length) (baseStart_1342915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342915 prefixEnd_1342915 := by exact prefixLift 1342915
  have htrace : WordTrace (prefixWord ++ tailWord_1342915) baseStart_1342915 baseEnd_1342915 := by
    simpa [prefixWord, tailWord_1342915, baseEnd_1342915] using wordTrace_append hprefix tailTrace_1342915
  have hstable : (prefixWord ++ tailWord_1342915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342915).length < 2 ^ (prefixWord ++ tailWord_1342915).sum := by decide
  have hdescent : baseEnd_1342915 < baseStart_1342915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342943 : List Nat := [1, 1, 2, 3, 3, 1, 3, 7]
def baseStart_1342943 : Nat := 118140960795 + 1342943 * 2 ^ 59
def prefixEnd_1342943 : Nat := 4983230072969 + 3 ^ 40 * 1342943 * 2
def baseEnd_1342943 : Nat := 102159296383858438968359

theorem tailTrace_1342943 : CollatzResearch.WordTrace tailWord_1342943 prefixEnd_1342943 102159296383858438968359 := by
  unfold tailWord_1342943
  simp only [CollatzResearch.WordTrace]
  refine ⟨48981155173754342249513483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32654103449169561499675655 48981155173754342249513483)
  ·
    refine ⟨73471732760631513374270225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48981155173754342249513483 73471732760631513374270225)
    ·
      refine ⟨55103799570473635030702669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73471732760631513374270225 55103799570473635030702669)
      ·
        refine ⟨20663924838927613136513501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55103799570473635030702669 20663924838927613136513501)
        ·
          refine ⟨7748971814597854926192563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20663924838927613136513501 7748971814597854926192563)
          ·
            refine ⟨11623457721896782389288845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7748971814597854926192563 11623457721896782389288845)
            ·
              refine ⟨4358796645711293395983317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11623457721896782389288845 4358796645711293395983317)
              ·
                refine ⟨102159296383858438968359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4358796645711293395983317 102159296383858438968359)
                ·
                  rfl

theorem cell21_1342943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 7].length) (baseStart_1342943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342943 prefixEnd_1342943 := by exact prefixLift 1342943
  have htrace : WordTrace (prefixWord ++ tailWord_1342943) baseStart_1342943 baseEnd_1342943 := by
    simpa [prefixWord, tailWord_1342943, baseEnd_1342943] using wordTrace_append hprefix tailTrace_1342943
  have hstable : (prefixWord ++ tailWord_1342943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342943).length < 2 ^ (prefixWord ++ tailWord_1342943).sum := by decide
  have hdescent : baseEnd_1342943 < baseStart_1342943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342949 : List Nat := [1, 3, 1, 5, 1, 3, 1, 3, 3]
def baseStart_1342949 : Nat := 118140960795 + 1342949 * 2 ^ 59
def prefixEnd_1342949 : Nat := 4983230072969 + 3 ^ 40 * 1342949 * 2
def baseEnd_1342949 : Nat := 306479258433320639805065

theorem tailTrace_1342949 : CollatzResearch.WordTrace tailWord_1342949 prefixEnd_1342949 306479258433320639805065 := by
  unfold tailWord_1342949
  simp only [CollatzResearch.WordTrace]
  refine ⟨48981374011732605274231901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32654249341155070182821267 48981374011732605274231901)
  ·
    refine ⟨18368015254399726977836963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48981374011732605274231901 18368015254399726977836963)
    ·
      refine ⟨27552022881599590466755445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18368015254399726977836963 27552022881599590466755445)
      ·
        refine ⟨2583002145149961606258323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27552022881599590466755445 2583002145149961606258323)
        ·
          refine ⟨3874503217724942409387485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583002145149961606258323 3874503217724942409387485)
          ·
            refine ⟨1452938706646853403520307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3874503217724942409387485 1452938706646853403520307)
            ·
              refine ⟨2179408059970280105280461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1452938706646853403520307 2179408059970280105280461)
              ·
                refine ⟨817278022488855039480173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2179408059970280105280461 817278022488855039480173)
                ·
                  refine ⟨306479258433320639805065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817278022488855039480173 306479258433320639805065)
                  ·
                    rfl

theorem cell21_1342949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_1342949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342949 prefixEnd_1342949 := by exact prefixLift 1342949
  have htrace : WordTrace (prefixWord ++ tailWord_1342949) baseStart_1342949 baseEnd_1342949 := by
    simpa [prefixWord, tailWord_1342949, baseEnd_1342949] using wordTrace_append hprefix tailTrace_1342949
  have hstable : (prefixWord ++ tailWord_1342949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342949).length < 2 ^ (prefixWord ++ tailWord_1342949).sum := by decide
  have hdescent : baseEnd_1342949 < baseStart_1342949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1342980 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1342980 : Nat := 118140960795 + 1342980 * 2 ^ 59
def prefixEnd_1342980 : Nat := 4983230072969 + 3 ^ 40 * 1342980 * 2
def baseEnd_1342980 : Nat := 306486333055671474788335

theorem tailTrace_1342980 : CollatzResearch.WordTrace tailWord_1342980 prefixEnd_1342980 306486333055671474788335 := by
  unfold tailWord_1342980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24491252337310148784305197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32655003116413531712406929 24491252337310148784305197)
  ·
    refine ⟨9184219626491305794114449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24491252337310148784305197 9184219626491305794114449)
    ·
      refine ⟨6888164719868479345585837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9184219626491305794114449 6888164719868479345585837)
      ·
        refine ⟨2583061769950679754594689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6888164719868479345585837 2583061769950679754594689)
        ·
          refine ⟨1937296327463009815946017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2583061769950679754594689 1937296327463009815946017)
          ·
            refine ⟨1452972245597257361959513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1937296327463009815946017 1452972245597257361959513)
            ·
              refine ⟨1089729184197943021469635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1452972245597257361959513 1089729184197943021469635)
              ·
                refine ⟨1634593776296914532204453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1089729184197943021469635 1634593776296914532204453)
                ·
                  refine ⟨306486333055671474788335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634593776296914532204453 306486333055671474788335)
                  ·
                    rfl

theorem cell21_1342980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1342980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1342980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1342980 prefixEnd_1342980 := by exact prefixLift 1342980
  have htrace : WordTrace (prefixWord ++ tailWord_1342980) baseStart_1342980 baseEnd_1342980 := by
    simpa [prefixWord, tailWord_1342980, baseEnd_1342980] using wordTrace_append hprefix tailTrace_1342980
  have hstable : (prefixWord ++ tailWord_1342980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1342980).length < 2 ^ (prefixWord ++ tailWord_1342980).sum := by decide
  have hdescent : baseEnd_1342980 < baseStart_1342980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1342980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343022 : List Nat := [4, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_1343022 : Nat := 118140960795 + 1343022 * 2 ^ 59
def prefixEnd_1343022 : Nat := 4983230072969 + 3 ^ 40 * 1343022 * 2
def baseEnd_1343022 : Nat := 306495918027888735088249

theorem tailTrace_1343022 : CollatzResearch.WordTrace tailWord_1343022 prefixEnd_1343022 306495918027888735088249 := by
  unfold tailWord_1343022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6123004567558517342704915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32656024360312092494426213 6123004567558517342704915)
  ·
    refine ⟨9184506851337776014057373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6123004567558517342704915 9184506851337776014057373)
    ·
      refine ⟨3444190069251666005271515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9184506851337776014057373 3444190069251666005271515)
      ·
        refine ⟨5166285103877499007907273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3444190069251666005271515 5166285103877499007907273)
        ·
          refine ⟨3874713827908124255930455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5166285103877499007907273 3874713827908124255930455)
          ·
            refine ⟨5812070741862186383895683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3874713827908124255930455 5812070741862186383895683)
            ·
              refine ⟨8718106112793279575843525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5812070741862186383895683 8718106112793279575843525)
              ·
                refine ⟨1634644896148739920470661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8718106112793279575843525 1634644896148739920470661)
                ·
                  refine ⟨306495918027888735088249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634644896148739920470661 306495918027888735088249)
                  ·
                    rfl

theorem cell21_1343022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_1343022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343022 prefixEnd_1343022 := by exact prefixLift 1343022
  have htrace : WordTrace (prefixWord ++ tailWord_1343022) baseStart_1343022 baseEnd_1343022 := by
    simpa [prefixWord, tailWord_1343022, baseEnd_1343022] using wordTrace_append hprefix tailTrace_1343022
  have hstable : (prefixWord ++ tailWord_1343022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343022).length < 2 ^ (prefixWord ++ tailWord_1343022).sum := by decide
  have hdescent : baseEnd_1343022 < baseStart_1343022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343050 : List Nat := [3, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_1343050 : Nat := 118140960795 + 1343050 * 2 ^ 59
def prefixEnd_1343050 : Nat := 4983230072969 + 3 ^ 40 * 1343050 * 2
def baseEnd_1343050 : Nat := 306502308009366908621525

theorem tailTrace_1343050 : CollatzResearch.WordTrace tailWord_1343050 prefixEnd_1343050 306502308009366908621525 := by
  unfold tailWord_1343050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12246264446091674880914651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32656705189577799682439069 12246264446091674880914651)
  ·
    refine ⟨18369396669137512321371977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12246264446091674880914651 18369396669137512321371977)
    ·
      refine ⟨13777047501853134241028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18369396669137512321371977 13777047501853134241028983)
      ·
        refine ⟨20665571252779701361543475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13777047501853134241028983 20665571252779701361543475)
        ·
          refine ⟨30998356879169552042315213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20665571252779701361543475 30998356879169552042315213)
          ·
            refine ⟨11624383829688582015868205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30998356879169552042315213 11624383829688582015868205)
            ·
              refine ⟨4359143936133218255950577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11624383829688582015868205 4359143936133218255950577)
              ·
                refine ⟨3269357952099913691962933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4359143936133218255950577 3269357952099913691962933)
                ·
                  refine ⟨306502308009366908621525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3269357952099913691962933 306502308009366908621525)
                  ·
                    rfl

theorem cell21_1343050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_1343050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343050 prefixEnd_1343050 := by exact prefixLift 1343050
  have htrace : WordTrace (prefixWord ++ tailWord_1343050) baseStart_1343050 baseEnd_1343050 := by
    simpa [prefixWord, tailWord_1343050, baseEnd_1343050] using wordTrace_append hprefix tailTrace_1343050
  have hstable : (prefixWord ++ tailWord_1343050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343050).length < 2 ^ (prefixWord ++ tailWord_1343050).sum := by decide
  have hdescent : baseEnd_1343050 < baseStart_1343050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343064 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_1343064 : Nat := 118140960795 + 1343064 * 2 ^ 59
def prefixEnd_1343064 : Nat := 4983230072969 + 3 ^ 40 * 1343064 * 2
def baseEnd_1343064 : Nat := 306505503000105995388163

theorem tailTrace_1343064 : CollatzResearch.WordTrace tailWord_1343064 prefixEnd_1343064 306505503000105995388163 := by
  unfold tailWord_1343064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24492784203157989957334123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32657045604210653276445497 24492784203157989957334123)
  ·
    refine ⟨36739176304736984936001185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24492784203157989957334123 36739176304736984936001185)
    ·
      refine ⟨27554382228552738702000889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36739176304736984936001185 27554382228552738702000889)
      ·
        refine ⟨20665786671414554026500667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27554382228552738702000889 20665786671414554026500667)
        ·
          refine ⟨30998680007121831039751001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20665786671414554026500667 30998680007121831039751001)
          ·
            refine ⟨23249010005341373279813251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30998680007121831039751001 23249010005341373279813251)
            ·
              refine ⟨34873515008012059919719877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23249010005341373279813251 34873515008012059919719877)
              ·
                refine ⟨6538784064002261234947477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34873515008012059919719877 6538784064002261234947477)
                ·
                  refine ⟨306505503000105995388163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6538784064002261234947477 306505503000105995388163)
                  ·
                    rfl

theorem cell21_1343064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_1343064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343064 prefixEnd_1343064 := by exact prefixLift 1343064
  have htrace : WordTrace (prefixWord ++ tailWord_1343064) baseStart_1343064 baseEnd_1343064 := by
    simpa [prefixWord, tailWord_1343064, baseEnd_1343064] using wordTrace_append hprefix tailTrace_1343064
  have hstable : (prefixWord ++ tailWord_1343064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343064).length < 2 ^ (prefixWord ++ tailWord_1343064).sum := by decide
  have hdescent : baseEnd_1343064 < baseStart_1343064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343081 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 4]
def baseStart_1343081 : Nat := 118140960795 + 1343081 * 2 ^ 59
def prefixEnd_1343081 : Nat := 4983230072969 + 3 ^ 40 * 1343081 * 2
def baseEnd_1343081 : Nat := 306509382631717743604795

theorem tailTrace_1343081 : CollatzResearch.WordTrace tailWord_1343081 prefixEnd_1343081 306509382631717743604795 := by
  unfold tailWord_1343081
  simp only [CollatzResearch.WordTrace]
  refine ⟨48986188447254391818037097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32657458964836261212024731 48986188447254391818037097)
  ·
    refine ⟨36739641335440793863527823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48986188447254391818037097 36739641335440793863527823)
    ·
      refine ⟨55109462003161190795291735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36739641335440793863527823 55109462003161190795291735)
      ·
        refine ⟨82664193004741786192937603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55109462003161190795291735 82664193004741786192937603)
        ·
          refine ⟨123996289507112679289406405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82664193004741786192937603 123996289507112679289406405)
          ·
            refine ⟨23249304282583627366763701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123996289507112679289406405 23249304282583627366763701)
            ·
              refine ⟨2179622276492215065634097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23249304282583627366763701 2179622276492215065634097)
              ·
                refine ⟨1634716707369161299225573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2179622276492215065634097 1634716707369161299225573)
                ·
                  refine ⟨306509382631717743604795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1634716707369161299225573 306509382631717743604795)
                  ·
                    rfl

theorem cell21_1343081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_1343081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343081 prefixEnd_1343081 := by exact prefixLift 1343081
  have htrace : WordTrace (prefixWord ++ tailWord_1343081) baseStart_1343081 baseEnd_1343081 := by
    simpa [prefixWord, tailWord_1343081, baseEnd_1343081] using wordTrace_append hprefix tailTrace_1343081
  have hstable : (prefixWord ++ tailWord_1343081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343081).length < 2 ^ (prefixWord ++ tailWord_1343081).sum := by decide
  have hdescent : baseEnd_1343081 < baseStart_1343081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343236 : List Nat := [2, 3, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1343236 : Nat := 118140960795 + 1343236 * 2 ^ 59
def prefixEnd_1343236 : Nat := 4983230072969 + 3 ^ 40 * 1343236 * 2
def baseEnd_1343236 : Nat := 306544755743471918521145

theorem tailTrace_1343236 : CollatzResearch.WordTrace tailWord_1343236 prefixEnd_1343236 306544755743471918521145 := by
  unfold tailWord_1343236
  simp only [CollatzResearch.WordTrace]
  refine ⟨24495920880846426644964781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32661227841128568859953041 24495920880846426644964781)
  ·
    refine ⟨9185970330317409991861793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24495920880846426644964781 9185970330317409991861793)
    ·
      refine ⟨6889477747738057493896345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9185970330317409991861793 6889477747738057493896345)
      ·
        refine ⟨5167108310803543120422259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6889477747738057493896345 5167108310803543120422259)
        ·
          refine ⟨7750662466205314680633389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5167108310803543120422259 7750662466205314680633389)
          ·
            refine ⟨2906498424826993005237521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7750662466205314680633389 2906498424826993005237521)
            ·
              refine ⟨2179873818620244753928141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2906498424826993005237521 2179873818620244753928141)
              ·
                refine ⟨817452681982591782723053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2179873818620244753928141 817452681982591782723053)
                ·
                  refine ⟨306544755743471918521145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817452681982591782723053 306544755743471918521145)
                  ·
                    rfl

theorem cell21_1343236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1343236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343236 prefixEnd_1343236 := by exact prefixLift 1343236
  have htrace : WordTrace (prefixWord ++ tailWord_1343236) baseStart_1343236 baseEnd_1343236 := by
    simpa [prefixWord, tailWord_1343236, baseEnd_1343236] using wordTrace_append hprefix tailTrace_1343236
  have hstable : (prefixWord ++ tailWord_1343236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343236).length < 2 ^ (prefixWord ++ tailWord_1343236).sum := by decide
  have hdescent : baseEnd_1343236 < baseStart_1343236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343250 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_1343250 : Nat := 118140960795 + 1343250 * 2 ^ 59
def prefixEnd_1343250 : Nat := 4983230072969 + 3 ^ 40 * 1343250 * 2
def baseEnd_1343250 : Nat := 306547950734211005287783

theorem tailTrace_1343250 : CollatzResearch.WordTrace tailWord_1343250 prefixEnd_1343250 306547950734211005287783 := by
  unfold tailWord_1343250
  simp only [CollatzResearch.WordTrace]
  refine ⟨12248088095910533420234801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32661568255761422453959469 12248088095910533420234801)
  ·
    refine ⟨9186066071932900065176101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12248088095910533420234801 9186066071932900065176101)
    ·
      refine ⟨1722387388487418762220519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9186066071932900065176101 1722387388487418762220519)
      ·
        refine ⟨2583581082731128143330779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722387388487418762220519 2583581082731128143330779)
        ·
          refine ⟨3875371624096692214996169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2583581082731128143330779 3875371624096692214996169)
          ·
            refine ⟨2906528718072519161247127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875371624096692214996169 2906528718072519161247127)
            ·
              refine ⟨4359793077108778741870691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2906528718072519161247127 4359793077108778741870691)
              ·
                refine ⟨6539689615663168112806037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4359793077108778741870691 6539689615663168112806037)
                ·
                  refine ⟨306547950734211005287783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6539689615663168112806037 306547950734211005287783)
                  ·
                    rfl

theorem cell21_1343250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_1343250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343250 prefixEnd_1343250 := by exact prefixLift 1343250
  have htrace : WordTrace (prefixWord ++ tailWord_1343250) baseStart_1343250 baseEnd_1343250 := by
    simpa [prefixWord, tailWord_1343250, baseEnd_1343250] using wordTrace_append hprefix tailTrace_1343250
  have hstable : (prefixWord ++ tailWord_1343250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343250).length < 2 ^ (prefixWord ++ tailWord_1343250).sum := by decide
  have hdescent : baseEnd_1343250 < baseStart_1343250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343292 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1343292 : Nat := 118140960795 + 1343292 * 2 ^ 59
def prefixEnd_1343292 : Nat := 4983230072969 + 3 ^ 40 * 1343292 * 2
def baseEnd_1343292 : Nat := 306557535706428265587697

theorem tailTrace_1343292 : CollatzResearch.WordTrace tailWord_1343292 prefixEnd_1343292 306557535706428265587697 := by
  unfold tailWord_1343292
  simp only [CollatzResearch.WordTrace]
  refine ⟨24496942124744987426984065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32662589499659983235978753 24496942124744987426984065)
  ·
    refine ⟨18372706593558740570238049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24496942124744987426984065 18372706593558740570238049)
    ·
      refine ⟨13779529945169055427678537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18372706593558740570238049 13779529945169055427678537)
      ·
        refine ⟨10334647458876791570758903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13779529945169055427678537 10334647458876791570758903)
        ·
          refine ⟨15501971188315187356138355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10334647458876791570758903 15501971188315187356138355)
          ·
            refine ⟨23252956782472781034207533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15501971188315187356138355 23252956782472781034207533)
            ·
              refine ⟨8719858793427292887827825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23252956782472781034207533 8719858793427292887827825)
              ·
                refine ⟨6539894095070469665870869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8719858793427292887827825 6539894095070469665870869)
                ·
                  refine ⟨306557535706428265587697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6539894095070469665870869 306557535706428265587697)
                  ·
                    rfl

theorem cell21_1343292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1343292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343292 prefixEnd_1343292 := by exact prefixLift 1343292
  have htrace : WordTrace (prefixWord ++ tailWord_1343292) baseStart_1343292 baseEnd_1343292 := by
    simpa [prefixWord, tailWord_1343292, baseEnd_1343292] using wordTrace_append hprefix tailTrace_1343292
  have hstable : (prefixWord ++ tailWord_1343292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343292).length < 2 ^ (prefixWord ++ tailWord_1343292).sum := by decide
  have hdescent : baseEnd_1343292 < baseStart_1343292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343337 : List Nat := [1, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_1343337 : Nat := 118140960795 + 1343337 * 2 ^ 59
def prefixEnd_1343337 : Nat := 4983230072969 + 3 ^ 40 * 1343337 * 2
def baseEnd_1343337 : Nat := 306567805319518187337605

theorem tailTrace_1343337 : CollatzResearch.WordTrace tailWord_1343337 prefixEnd_1343337 306567805319518187337605 := by
  unfold tailWord_1343337
  simp only [CollatzResearch.WordTrace]
  refine ⟨48995525534326947539356265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32663683689551298359570843 48995525534326947539356265)
  ·
    refine ⟨36746644150745210654517199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48995525534326947539356265 36746644150745210654517199)
    ·
      refine ⟨55119966226117815981775799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36746644150745210654517199 55119966226117815981775799)
      ·
        refine ⟨82679949339176723972663699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55119966226117815981775799 82679949339176723972663699)
        ·
          refine ⟨124019924008765085958995549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82679949339176723972663699 124019924008765085958995549)
          ·
            refine ⟨46507471503286907234623331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124019924008765085958995549 46507471503286907234623331)
            ·
              refine ⟨69761207254930360851934997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46507471503286907234623331 69761207254930360851934997)
              ·
                refine ⟨3270056590074860664934453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69761207254930360851934997 3270056590074860664934453)
                ·
                  refine ⟨306567805319518187337605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3270056590074860664934453 306567805319518187337605)
                  ·
                    rfl

theorem cell21_1343337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_1343337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343337 prefixEnd_1343337 := by exact prefixLift 1343337
  have htrace : WordTrace (prefixWord ++ tailWord_1343337) baseStart_1343337 baseEnd_1343337 := by
    simpa [prefixWord, tailWord_1343337, baseEnd_1343337] using wordTrace_append hprefix tailTrace_1343337
  have hstable : (prefixWord ++ tailWord_1343337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343337).length < 2 ^ (prefixWord ++ tailWord_1343337).sum := by decide
  have hdescent : baseEnd_1343337 < baseStart_1343337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343374 : List Nat := [4, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1343374 : Nat := 118140960795 + 1343374 * 2 ^ 59
def prefixEnd_1343374 : Nat := 4983230072969 + 3 ^ 40 * 1343374 * 2
def baseEnd_1343374 : Nat := 102192083074538115073621

theorem tailTrace_1343374 : CollatzResearch.WordTrace tailWord_1343374 prefixEnd_1343374 102192083074538115073621 := by
  unfold tailWord_1343374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124609379399112857306647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32664583356795268572302117 6124609379399112857306647)
  ·
    refine ⟨9186914069098669285959971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6124609379399112857306647 9186914069098669285959971)
    ·
      refine ⟨13780371103648003928939957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9186914069098669285959971 13780371103648003928939957)
      ·
        refine ⟨1291909790967000368338121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13780371103648003928939957 1291909790967000368338121)
        ·
          refine ⟨968932343225250276253591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1291909790967000368338121 968932343225250276253591)
          ·
            refine ⟨1453398514837875414380387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 968932343225250276253591 1453398514837875414380387)
            ·
              refine ⟨2180097772256813121570581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1453398514837875414380387 2180097772256813121570581)
              ·
                refine ⟨102192083074538115073621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2180097772256813121570581 102192083074538115073621)
                ·
                  rfl

theorem cell21_1343374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1343374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343374 prefixEnd_1343374 := by exact prefixLift 1343374
  have htrace : WordTrace (prefixWord ++ tailWord_1343374) baseStart_1343374 baseEnd_1343374 := by
    simpa [prefixWord, tailWord_1343374, baseEnd_1343374] using wordTrace_append hprefix tailTrace_1343374
  have hstable : (prefixWord ++ tailWord_1343374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343374).length < 2 ^ (prefixWord ++ tailWord_1343374).sum := by decide
  have hdescent : baseEnd_1343374 < baseStart_1343374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343537 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 4]
def baseStart_1343537 : Nat := 118140960795 + 1343537 * 2 ^ 59
def prefixEnd_1343537 : Nat := 4983230072969 + 3 ^ 40 * 1343537 * 2
def baseEnd_1343537 : Nat := 306613448044362284003863

theorem tailTrace_1343537 : CollatzResearch.WordTrace tailWord_1343537 prefixEnd_1343537 306613448044362284003863 := by
  unfold tailWord_1343537
  simp only [CollatzResearch.WordTrace]
  refine ⟨49002820133602381696636865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32668546755734921131091243 49002820133602381696636865)
  ·
    refine ⟨36752115100201786272477649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49002820133602381696636865 36752115100201786272477649)
    ·
      refine ⟨27564086325151339704358237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36752115100201786272477649 27564086325151339704358237)
      ·
        refine ⟨10336532371931752389134339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27564086325151339704358237 10336532371931752389134339)
        ·
          refine ⟨15504798557897628583701509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10336532371931752389134339 15504798557897628583701509)
          ·
            refine ⟨2907149729605805359444033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15504798557897628583701509 2907149729605805359444033)
            ·
              refine ⟨2180362297204354019583025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2907149729605805359444033 2180362297204354019583025)
              ·
                refine ⟨1635271722903265514687269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2180362297204354019583025 1635271722903265514687269)
                ·
                  refine ⟨306613448044362284003863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635271722903265514687269 306613448044362284003863)
                  ·
                    rfl

theorem cell21_1343537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_1343537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343537 prefixEnd_1343537 := by exact prefixLift 1343537
  have htrace : WordTrace (prefixWord ++ tailWord_1343537) baseStart_1343537 baseEnd_1343537 := by
    simpa [prefixWord, tailWord_1343537, baseEnd_1343537] using wordTrace_append hprefix tailTrace_1343537
  have hstable : (prefixWord ++ tailWord_1343537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343537).length < 2 ^ (prefixWord ++ tailWord_1343537).sum := by decide
  have hdescent : baseEnd_1343537 < baseStart_1343537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343596 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1343596 : Nat := 118140960795 + 1343596 * 2 ^ 59
def prefixEnd_1343596 : Nat := 4983230072969 + 3 ^ 40 * 1343596 * 2
def baseEnd_1343596 : Nat := 306626912648191292520409

theorem tailTrace_1343596 : CollatzResearch.WordTrace tailWord_1343596 prefixEnd_1343596 306626912648191292520409 := by
  unfold tailWord_1343596
  simp only [CollatzResearch.WordTrace]
  refine ⟨24502486020194317386517321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32669981360259089848689761 24502486020194317386517321)
  ·
    refine ⟨18376864515145738039887991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24502486020194317386517321 18376864515145738039887991)
    ·
      refine ⟨27565296772718607059831987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18376864515145738039887991 27565296772718607059831987)
      ·
        refine ⟨41347945159077910589747981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27565296772718607059831987 41347945159077910589747981)
        ·
          refine ⟨15505479434654216471155493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41347945159077910589747981 15505479434654216471155493)
          ·
            refine ⟨2907277393997665588341655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15505479434654216471155493 2907277393997665588341655)
            ·
              refine ⟨4360916090996498382512483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2907277393997665588341655 4360916090996498382512483)
              ·
                refine ⟨6541374136494747573768725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4360916090996498382512483 6541374136494747573768725)
                ·
                  refine ⟨306626912648191292520409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6541374136494747573768725 306626912648191292520409)
                  ·
                    rfl

theorem cell21_1343596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1343596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343596 prefixEnd_1343596 := by exact prefixLift 1343596
  have htrace : WordTrace (prefixWord ++ tailWord_1343596) baseStart_1343596 baseEnd_1343596 := by
    simpa [prefixWord, tailWord_1343596, baseEnd_1343596] using wordTrace_append hprefix tailTrace_1343596
  have hstable : (prefixWord ++ tailWord_1343596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343596).length < 2 ^ (prefixWord ++ tailWord_1343596).sum := by decide
  have hdescent : baseEnd_1343596 < baseStart_1343596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343672 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 4]
def baseStart_1343672 : Nat := 118140960795 + 1343672 * 2 ^ 59
def prefixEnd_1343672 : Nat := 4983230072969 + 3 ^ 40 * 1343672 * 2
def baseEnd_1343672 : Nat := 306644256883632049253587

theorem tailTrace_1343672 : CollatzResearch.WordTrace tailWord_1343672 prefixEnd_1343672 306644256883632049253587 := by
  unfold tailWord_1343672
  simp only [CollatzResearch.WordTrace]
  refine ⟨24503871994056649876400635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32671829325408866501867513 24503871994056649876400635)
  ·
    refine ⟨36755807991084974814600953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24503871994056649876400635 36755807991084974814600953)
    ·
      refine ⟨27566855993313731110950715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36755807991084974814600953 27566855993313731110950715)
      ·
        refine ⟨41350283989970596666426073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27566855993313731110950715 41350283989970596666426073)
        ·
          refine ⟨31012712992477947499819555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41350283989970596666426073 31012712992477947499819555)
          ·
            refine ⟨46519069488716921249729333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31012712992477947499819555 46519069488716921249729333)
            ·
              refine ⟨4361162764567211367162125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46519069488716921249729333 4361162764567211367162125)
              ·
                refine ⟨1635436036712704262685797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4361162764567211367162125 1635436036712704262685797)
                ·
                  refine ⟨306644256883632049253587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1635436036712704262685797 306644256883632049253587)
                  ·
                    rfl

theorem cell21_1343672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_1343672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343672 prefixEnd_1343672 := by exact prefixLift 1343672
  have htrace : WordTrace (prefixWord ++ tailWord_1343672) baseStart_1343672 baseEnd_1343672 := by
    simpa [prefixWord, tailWord_1343672, baseEnd_1343672] using wordTrace_append hprefix tailTrace_1343672
  have hstable : (prefixWord ++ tailWord_1343672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343672).length < 2 ^ (prefixWord ++ tailWord_1343672).sum := by decide
  have hdescent : baseEnd_1343672 < baseStart_1343672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343709 : List Nat := [1, 4, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1343709 : Nat := 118140960795 + 1343709 * 2 ^ 59
def prefixEnd_1343709 : Nat := 4983230072969 + 3 ^ 40 * 1343709 * 2
def baseEnd_1343709 : Nat := 306652700787728207136845

theorem tailTrace_1343709 : CollatzResearch.WordTrace tailWord_1343709 prefixEnd_1343709 306652700787728207136845 := by
  unfold tailWord_1343709
  simp only [CollatzResearch.WordTrace]
  refine ⟨49009093488979255071898181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32672728992652836714598787 49009093488979255071898181)
  ·
    refine ⟨9189205029183610325980909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49009093488979255071898181 9189205029183610325980909)
    ·
      refine ⟨3445951885943853872242841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9189205029183610325980909 3445951885943853872242841)
      ·
        refine ⟨2584463914457890404182131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3445951885943853872242841 2584463914457890404182131)
        ·
          refine ⟨3876695871686835606273197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2584463914457890404182131 3876695871686835606273197)
          ·
            refine ⟨1453760951882563352352449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3876695871686835606273197 1453760951882563352352449)
            ·
              refine ⟨1090320713911922514264337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453760951882563352352449 1090320713911922514264337)
              ·
                refine ⟨817740535433941885698253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1090320713911922514264337 817740535433941885698253)
                ·
                  refine ⟨306652700787728207136845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 817740535433941885698253 306652700787728207136845)
                  ·
                    rfl

theorem cell21_1343709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1343709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343709 prefixEnd_1343709 := by exact prefixLift 1343709
  have htrace : WordTrace (prefixWord ++ tailWord_1343709) baseStart_1343709 baseEnd_1343709 := by
    simpa [prefixWord, tailWord_1343709, baseEnd_1343709] using wordTrace_append hprefix tailTrace_1343709
  have hstable : (prefixWord ++ tailWord_1343709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343709).length < 2 ^ (prefixWord ++ tailWord_1343709).sum := by decide
  have hdescent : baseEnd_1343709 < baseStart_1343709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343796 : List Nat := [2, 5, 1, 1, 1, 2, 4, 5]
def baseStart_1343796 : Nat := 118140960795 + 1343796 * 2 ^ 59
def prefixEnd_1343796 : Nat := 4983230072969 + 3 ^ 40 * 1343796 * 2
def baseEnd_1343796 : Nat := 102224185124345129728889

theorem tailTrace_1343796 : CollatzResearch.WordTrace tailWord_1343796 prefixEnd_1343796 102224185124345129728889 := by
  unfold tailWord_1343796
  simp only [CollatzResearch.WordTrace]
  refine ⟨24506133319832034465157621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32674844426442712620210161 24506133319832034465157621)
  ·
    refine ⟨2297449998734253231108527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24506133319832034465157621 2297449998734253231108527)
    ·
      refine ⟨3446174998101379846662791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2297449998734253231108527 3446174998101379846662791)
      ·
        refine ⟨5169262497152069769994187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3446174998101379846662791 5169262497152069769994187)
        ·
          refine ⟨7753893745728104654991281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169262497152069769994187 7753893745728104654991281)
          ·
            refine ⟨5815420309296078491243461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7753893745728104654991281 5815420309296078491243461)
            ·
              refine ⟨1090391307993014717108149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5815420309296078491243461 1090391307993014717108149)
              ·
                refine ⟨102224185124345129728889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1090391307993014717108149 102224185124345129728889)
                ·
                  rfl

theorem cell21_1343796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_1343796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343796 prefixEnd_1343796 := by exact prefixLift 1343796
  have htrace : WordTrace (prefixWord ++ tailWord_1343796) baseStart_1343796 baseEnd_1343796 := by
    simpa [prefixWord, tailWord_1343796, baseEnd_1343796] using wordTrace_append hprefix tailTrace_1343796
  have hstable : (prefixWord ++ tailWord_1343796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343796).length < 2 ^ (prefixWord ++ tailWord_1343796).sum := by decide
  have hdescent : baseEnd_1343796 < baseStart_1343796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343807 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 8]
def baseStart_1343807 : Nat := 118140960795 + 1343807 * 2 ^ 59
def prefixEnd_1343807 : Nat := 4983230072969 + 3 ^ 40 * 1343807 * 2
def baseEnd_1343807 : Nat := 306675065722901814503311

theorem tailTrace_1343807 : CollatzResearch.WordTrace tailWord_1343807 prefixEnd_1343807 306675065722901814503311 := by
  unfold tailWord_1343807
  simp only [CollatzResearch.WordTrace]
  refine ⟨49012667842624217808965675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32675111895082811872643783 49012667842624217808965675)
  ·
    refine ⟨73519001763936326713448513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49012667842624217808965675 73519001763936326713448513)
    ·
      refine ⟨55139251322952245035086385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73519001763936326713448513 55139251322952245035086385)
      ·
        refine ⟨41354438492214183776314789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55139251322952245035086385 41354438492214183776314789)
        ·
          refine ⟨7753957217290159458059023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41354438492214183776314789 7753957217290159458059023)
          ·
            refine ⟨11630935825935239187088535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7753957217290159458059023 11630935825935239187088535)
            ·
              refine ⟨17446403738902858780632803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11630935825935239187088535 17446403738902858780632803)
              ·
                refine ⟨26169605608354288170949205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17446403738902858780632803 26169605608354288170949205)
                ·
                  refine ⟨306675065722901814503311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26169605608354288170949205 306675065722901814503311)
                  ·
                    rfl

theorem cell21_1343807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_1343807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343807 prefixEnd_1343807 := by exact prefixLift 1343807
  have htrace : WordTrace (prefixWord ++ tailWord_1343807) baseStart_1343807 baseEnd_1343807 := by
    simpa [prefixWord, tailWord_1343807, baseEnd_1343807] using wordTrace_append hprefix tailTrace_1343807
  have hstable : (prefixWord ++ tailWord_1343807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343807).length < 2 ^ (prefixWord ++ tailWord_1343807).sum := by decide
  have hdescent : baseEnd_1343807 < baseStart_1343807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1343928 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_1343928 : Nat := 118140960795 + 1343928 * 2 ^ 59
def prefixEnd_1343928 : Nat := 4983230072969 + 3 ^ 40 * 1343928 * 2
def baseEnd_1343928 : Nat := 306702679571432492986397

theorem tailTrace_1343928 : CollatzResearch.WordTrace tailWord_1343928 prefixEnd_1343928 306702679571432492986397 := by
  unfold tailWord_1343928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24508540537592927737060219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32678054050123903649413625 24508540537592927737060219)
  ·
    refine ⟨36762810806389391605590329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24508540537592927737060219 36762810806389391605590329)
    ·
      refine ⟨27572108104792043704192747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36762810806389391605590329 27572108104792043704192747)
      ·
        refine ⟨41358162157188065556289121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27572108104792043704192747 41358162157188065556289121)
        ·
          refine ⟨31018621617891049167216841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41358162157188065556289121 31018621617891049167216841)
          ·
            refine ⟨23263966213418286875412631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31018621617891049167216841 23263966213418286875412631)
            ·
              refine ⟨34895949320127430313118947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23263966213418286875412631 34895949320127430313118947)
              ·
                refine ⟨52343923980191145469678421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34895949320127430313118947 52343923980191145469678421)
                ·
                  refine ⟨306702679571432492986397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52343923980191145469678421 306702679571432492986397)
                  ·
                    rfl

theorem cell21_1343928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_1343928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1343928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1343928 prefixEnd_1343928 := by exact prefixLift 1343928
  have htrace : WordTrace (prefixWord ++ tailWord_1343928) baseStart_1343928 baseEnd_1343928 := by
    simpa [prefixWord, tailWord_1343928, baseEnd_1343928] using wordTrace_append hprefix tailTrace_1343928
  have hstable : (prefixWord ++ tailWord_1343928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1343928).length < 2 ^ (prefixWord ++ tailWord_1343928).sum := by decide
  have hdescent : baseEnd_1343928 < baseStart_1343928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1343928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344007 : List Nat := [1, 1, 4, 3, 3, 1, 2, 6]
def baseStart_1344007 : Nat := 118140960795 + 1344007 * 2 ^ 59
def prefixEnd_1344007 : Nat := 4983230072969 + 3 ^ 40 * 1344007 * 2
def baseEnd_1344007 : Nat := 102240236149248637056523

theorem tailTrace_1344007 : CollatzResearch.WordTrace tailWord_1344007 prefixEnd_1344007 102240236149248637056523 := by
  unfold tailWord_1344007
  simp only [CollatzResearch.WordTrace]
  refine ⟨49019962441899651966246275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32679974961266434644164183 49019962441899651966246275)
  ·
    refine ⟨73529943662849477949369413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49019962441899651966246275 73529943662849477949369413)
    ·
      refine ⟨13786864436784277115506765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73529943662849477949369413 13786864436784277115506765)
      ·
        refine ⟨5170074163794103918315037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13786864436784277115506765 5170074163794103918315037)
        ·
          refine ⟨1938777811422788969368139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5170074163794103918315037 1938777811422788969368139)
          ·
            refine ⟨2908166717134183454052209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938777811422788969368139 2908166717134183454052209)
            ·
              refine ⟨2181125037850637590539157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908166717134183454052209 2181125037850637590539157)
              ·
                refine ⟨102240236149248637056523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2181125037850637590539157 102240236149248637056523)
                ·
                  rfl

theorem cell21_1344007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_1344007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344007 prefixEnd_1344007 := by exact prefixLift 1344007
  have htrace : WordTrace (prefixWord ++ tailWord_1344007) baseStart_1344007 baseEnd_1344007 := by
    simpa [prefixWord, tailWord_1344007, baseEnd_1344007] using wordTrace_append hprefix tailTrace_1344007
  have hstable : (prefixWord ++ tailWord_1344007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344007).length < 2 ^ (prefixWord ++ tailWord_1344007).sum := by decide
  have hdescent : baseEnd_1344007 < baseStart_1344007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344114 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_1344114 : Nat := 118140960795 + 1344114 * 2 ^ 59
def prefixEnd_1344114 : Nat := 4983230072969 + 3 ^ 40 * 1344114 * 2
def baseEnd_1344114 : Nat := 306745127305537502886017

theorem tailTrace_1344114 : CollatzResearch.WordTrace tailWord_1344114 prefixEnd_1344114 306745127305537502886017 := by
  unfold tailWord_1344114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12255966263128002310097849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32682576701674672826927597 12255966263128002310097849)
  ·
    refine ⟨9191974697346001732573387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12255966263128002310097849 9191974697346001732573387)
    ·
      refine ⟨13787962046019002598860081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9191974697346001732573387 13787962046019002598860081)
      ·
        refine ⟨10340971534514251949145061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13787962046019002598860081 10340971534514251949145061)
        ·
          refine ⟨1938932162721422240464699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10340971534514251949145061 1938932162721422240464699)
          ·
            refine ⟨2908398244082133360697049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1938932162721422240464699 2908398244082133360697049)
            ·
              refine ⟨2181298683061600020522787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2908398244082133360697049 2181298683061600020522787)
              ·
                refine ⟨3271948024592400030784181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2181298683061600020522787 3271948024592400030784181)
                ·
                  refine ⟨306745127305537502886017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3271948024592400030784181 306745127305537502886017)
                  ·
                    rfl

theorem cell21_1344114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_1344114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344114 prefixEnd_1344114 := by exact prefixLift 1344114
  have htrace : WordTrace (prefixWord ++ tailWord_1344114) baseStart_1344114 baseEnd_1344114 := by
    simpa [prefixWord, tailWord_1344114, baseEnd_1344114] using wordTrace_append hprefix tailTrace_1344114
  have hstable : (prefixWord ++ tailWord_1344114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344114).length < 2 ^ (prefixWord ++ tailWord_1344114).sum := by decide
  have hdescent : baseEnd_1344114 < baseStart_1344114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344142 : List Nat := [4, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1344142 : Nat := 118140960795 + 1344142 * 2 ^ 59
def prefixEnd_1344142 : Nat := 4983230072969 + 3 ^ 40 * 1344142 * 2
def baseEnd_1344142 : Nat := 102250505762338558806431

theorem tailTrace_1344142 : CollatzResearch.WordTrace tailWord_1344142 prefixEnd_1344142 102250505762338558806431 := by
  unfold tailWord_1344142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6128110787051321252801335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32683257530940380014940453 6128110787051321252801335)
  ·
    refine ⟨9192166180576981879202003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6128110787051321252801335 9192166180576981879202003)
    ·
      refine ⟨13788249270865472818803005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9192166180576981879202003 13788249270865472818803005)
      ·
        refine ⟨5170593476574552307051127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13788249270865472818803005 5170593476574552307051127)
        ·
          refine ⟨7755890214861828460576691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5170593476574552307051127 7755890214861828460576691)
          ·
            refine ⟨11633835322292742690865037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7755890214861828460576691 11633835322292742690865037)
            ·
              refine ⟨4362688245859778509074389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11633835322292742690865037 4362688245859778509074389)
              ·
                refine ⟨102250505762338558806431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4362688245859778509074389 102250505762338558806431)
                ·
                  rfl

theorem cell21_1344142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1344142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344142 prefixEnd_1344142 := by exact prefixLift 1344142
  have htrace : WordTrace (prefixWord ++ tailWord_1344142) baseStart_1344142 baseEnd_1344142 := by
    simpa [prefixWord, tailWord_1344142, baseEnd_1344142] using wordTrace_append hprefix tailTrace_1344142
  have hstable : (prefixWord ++ tailWord_1344142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344142).length < 2 ^ (prefixWord ++ tailWord_1344142).sum := by decide
  have hdescent : baseEnd_1344142 < baseStart_1344142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344148 : List Nat := [2, 4, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1344148 : Nat := 118140960795 + 1344148 * 2 ^ 59
def prefixEnd_1344148 : Nat := 4983230072969 + 3 ^ 40 * 1344148 * 2
def baseEnd_1344148 : Nat := 306752886568760999319281

theorem tailTrace_1344148 : CollatzResearch.WordTrace tailWord_1344148 prefixEnd_1344148 306752886568760999319281 := by
  unfold tailWord_1344148
  simp only [CollatzResearch.WordTrace]
  refine ⟨24512552567194416523564549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32683403422925888698086065 24512552567194416523564549)
  ·
    refine ⟨4596103606348953098168353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24512552567194416523564549 4596103606348953098168353)
    ·
      refine ⟨3447077704761714823626265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4596103606348953098168353 3447077704761714823626265)
      ·
        refine ⟨2585308278571286117719699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3447077704761714823626265 2585308278571286117719699)
        ·
          refine ⟨3877962417856929176579549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2585308278571286117719699 3877962417856929176579549)
          ·
            refine ⟨1454235906696348441217331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3877962417856929176579549 1454235906696348441217331)
            ·
              refine ⟨2181353860044522661825997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454235906696348441217331 2181353860044522661825997)
              ·
                refine ⟨818007697516695998184749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2181353860044522661825997 818007697516695998184749)
                ·
                  refine ⟨306752886568760999319281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818007697516695998184749 306752886568760999319281)
                  ·
                    rfl

theorem cell21_1344148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1344148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344148 prefixEnd_1344148 := by exact prefixLift 1344148
  have htrace : WordTrace (prefixWord ++ tailWord_1344148) baseStart_1344148 baseEnd_1344148 := by
    simpa [prefixWord, tailWord_1344148, baseEnd_1344148] using wordTrace_append hprefix tailTrace_1344148
  have hstable : (prefixWord ++ tailWord_1344148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344148).length < 2 ^ (prefixWord ++ tailWord_1344148).sum := by decide
  have hdescent : baseEnd_1344148 < baseStart_1344148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344266 : List Nat := [3, 1, 2, 2, 1, 2, 4, 3, 3]
def baseStart_1344266 : Nat := 118140960795 + 1344266 * 2 ^ 59
def prefixEnd_1344266 : Nat := 4983230072969 + 3 ^ 40 * 1344266 * 2
def baseEnd_1344266 : Nat := 306779815776419016352373

theorem tailTrace_1344266 : CollatzResearch.WordTrace tailWord_1344266 prefixEnd_1344266 306779815776419016352373 := by
  unfold tailWord_1344266
  simp only [CollatzResearch.WordTrace]
  refine ⟨12257352236990334799981163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32686272631974226133283101 12257352236990334799981163)
  ·
    refine ⟨18386028355485502199971745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12257352236990334799981163 18386028355485502199971745)
    ·
      refine ⟨13789521266614126649978809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18386028355485502199971745 13789521266614126649978809)
      ·
        refine ⟨10342140949960594987484107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13789521266614126649978809 10342140949960594987484107)
        ·
          refine ⟨15513211424940892481226161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10342140949960594987484107 15513211424940892481226161)
          ·
            refine ⟨11634908568705669360919621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15513211424940892481226161 11634908568705669360919621)
            ·
              refine ⟨2181545356632313005172429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11634908568705669360919621 2181545356632313005172429)
              ·
                refine ⟨818079508737117376939661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2181545356632313005172429 818079508737117376939661)
                ·
                  refine ⟨306779815776419016352373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818079508737117376939661 306779815776419016352373)
                  ·
                    rfl

theorem cell21_1344266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_1344266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344266 prefixEnd_1344266 := by exact prefixLift 1344266
  have htrace : WordTrace (prefixWord ++ tailWord_1344266) baseStart_1344266 baseEnd_1344266 := by
    simpa [prefixWord, tailWord_1344266, baseEnd_1344266] using wordTrace_append hprefix tailTrace_1344266
  have hstable : (prefixWord ++ tailWord_1344266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344266).length < 2 ^ (prefixWord ++ tailWord_1344266).sum := by decide
  have hdescent : baseEnd_1344266 < baseStart_1344266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344277 : List Nat := [1, 3, 2, 1, 2, 2, 10]
def baseStart_1344277 : Nat := 118140960795 + 1344277 * 2 ^ 59
def prefixEnd_1344277 : Nat := 4983230072969 + 3 ^ 40 * 1344277 * 2
def baseEnd_1344277 : Nat := 34086925125142826852113

theorem tailTrace_1344277 : CollatzResearch.WordTrace tailWord_1344277 prefixEnd_1344277 34086925125142826852113 := by
  unfold tailWord_1344277
  simp only [CollatzResearch.WordTrace]
  refine ⟨49029810150921488078575085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32686540100614325385716723 49029810150921488078575085)
  ·
    refine ⟨18386178806595558029465657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49029810150921488078575085 18386178806595558029465657)
    ·
      refine ⟨13789634104946668522099243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18386178806595558029465657 13789634104946668522099243)
      ·
        refine ⟨20684451157420002783148865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13789634104946668522099243 20684451157420002783148865)
        ·
          refine ⟨15513338368065002087361649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20684451157420002783148865 15513338368065002087361649)
          ·
            refine ⟨11635003776048751565521237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15513338368065002087361649 11635003776048751565521237)
            ·
              refine ⟨34086925125142826852113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11635003776048751565521237 34086925125142826852113)
              ·
                rfl

theorem cell21_1344277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 10].length) (baseStart_1344277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344277 prefixEnd_1344277 := by exact prefixLift 1344277
  have htrace : WordTrace (prefixWord ++ tailWord_1344277) baseStart_1344277 baseEnd_1344277 := by
    simpa [prefixWord, tailWord_1344277, baseEnd_1344277] using wordTrace_append hprefix tailTrace_1344277
  have hstable : (prefixWord ++ tailWord_1344277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344277).length < 2 ^ (prefixWord ++ tailWord_1344277).sum := by decide
  have hdescent : baseEnd_1344277 < baseStart_1344277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344325 : List Nat := [1, 3, 1, 1, 1, 2, 2, 7, 3]
def baseStart_1344325 : Nat := 118140960795 + 1344325 * 2 ^ 59
def prefixEnd_1344325 : Nat := 4983230072969 + 3 ^ 40 * 1344325 * 2
def baseEnd_1344325 : Nat := 306793280380248024868919

theorem tailTrace_1344325 : CollatzResearch.WordTrace tailWord_1344325 prefixEnd_1344325 306793280380248024868919 := by
  unfold tailWord_1344325
  simp only [CollatzResearch.WordTrace]
  refine ⟨49031560854747592276322429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32687707236498394850881619 49031560854747592276322429)
  ·
    refine ⟨18386835320530347103620911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49031560854747592276322429 18386835320530347103620911)
    ·
      refine ⟨27580252980795520655431367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18386835320530347103620911 27580252980795520655431367)
      ·
        refine ⟨41370379471193280983147051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27580252980795520655431367 41370379471193280983147051)
        ·
          refine ⟨62055569206789921474720577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41370379471193280983147051 62055569206789921474720577)
          ·
            refine ⟨46541676905092441106040433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62055569206789921474720577 46541676905092441106040433)
            ·
              refine ⟨34906257678819330829530325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46541676905092441106040433 34906257678819330829530325)
              ·
                refine ⟨818115414347328066317117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 34906257678819330829530325 818115414347328066317117)
                ·
                  refine ⟨306793280380248024868919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818115414347328066317117 306793280380248024868919)
                  ·
                    rfl

theorem cell21_1344325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_1344325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344325 prefixEnd_1344325 := by exact prefixLift 1344325
  have htrace : WordTrace (prefixWord ++ tailWord_1344325) baseStart_1344325 baseEnd_1344325 := by
    simpa [prefixWord, tailWord_1344325, baseEnd_1344325] using wordTrace_append hprefix tailTrace_1344325
  have hstable : (prefixWord ++ tailWord_1344325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344325).length < 2 ^ (prefixWord ++ tailWord_1344325).sum := by decide
  have hdescent : baseEnd_1344325 < baseStart_1344325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344356 : List Nat := [2, 3, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1344356 : Nat := 118140960795 + 1344356 * 2 ^ 59
def prefixEnd_1344356 : Nat := 4983230072969 + 3 ^ 40 * 1344356 * 2
def baseEnd_1344356 : Nat := 306800355002598859852189

theorem tailTrace_1344356 : CollatzResearch.WordTrace tailWord_1344356 prefixEnd_1344356 306800355002598859852189 := by
  unfold tailWord_1344356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24516345758817642285350461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32688461011756856380467281 24516345758817642285350461)
  ·
    refine ⟨9193629659556615857006423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24516345758817642285350461 9193629659556615857006423)
    ·
      refine ⟨13790444489334923785509635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9193629659556615857006423 13790444489334923785509635)
      ·
        refine ⟨20685666734002385678264453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13790444489334923785509635 20685666734002385678264453)
        ·
          refine ⟨3878562512625447314674585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20685666734002385678264453 3878562512625447314674585)
          ·
            refine ⟨2908921884469085486005939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3878562512625447314674585 2908921884469085486005939)
            ·
              refine ⟨4363382826703628229008909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2908921884469085486005939 4363382826703628229008909)
              ·
                refine ⟨1636268560013860585878341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4363382826703628229008909 1636268560013860585878341)
                ·
                  refine ⟨306800355002598859852189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636268560013860585878341 306800355002598859852189)
                  ·
                    rfl

theorem cell21_1344356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1344356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344356 prefixEnd_1344356 := by exact prefixLift 1344356
  have htrace : WordTrace (prefixWord ++ tailWord_1344356) baseStart_1344356 baseEnd_1344356 := by
    simpa [prefixWord, tailWord_1344356, baseEnd_1344356] using wordTrace_append hprefix tailTrace_1344356
  have hstable : (prefixWord ++ tailWord_1344356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344356).length < 2 ^ (prefixWord ++ tailWord_1344356).sum := by decide
  have hdescent : baseEnd_1344356 < baseStart_1344356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344477 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_1344477 : Nat := 118140960795 + 1344477 * 2 ^ 59
def prefixEnd_1344477 : Nat := 4983230072969 + 3 ^ 40 * 1344477 * 2
def baseEnd_1344477 : Nat := 306827968851129538335275

theorem tailTrace_1344477 : CollatzResearch.WordTrace tailWord_1344477 prefixEnd_1344477 306827968851129538335275 := by
  unfold tailWord_1344477
  simp only [CollatzResearch.WordTrace]
  refine ⟨49037104750196922235855685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32691403166797948157237123 49037104750196922235855685)
  ·
    refine ⟨9194457140661922919222941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49037104750196922235855685 9194457140661922919222941)
    ·
      refine ⟨3447921427748221094708603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9194457140661922919222941 3447921427748221094708603)
      ·
        refine ⟨5171882141622331642062905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3447921427748221094708603 5171882141622331642062905)
        ·
          refine ⟨3878911606216748731547179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5171882141622331642062905 3878911606216748731547179)
          ·
            refine ⟨5818367409325123097320769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3878911606216748731547179 5818367409325123097320769)
            ·
              refine ⟨4363775556993842322990577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5818367409325123097320769 4363775556993842322990577)
              ·
                refine ⟨3272831667745381742242933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4363775556993842322990577 3272831667745381742242933)
                ·
                  refine ⟨306827968851129538335275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3272831667745381742242933 306827968851129538335275)
                  ·
                    rfl

theorem cell21_1344477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_1344477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344477 prefixEnd_1344477 := by exact prefixLift 1344477
  have htrace : WordTrace (prefixWord ++ tailWord_1344477) baseStart_1344477 baseEnd_1344477 := by
    simpa [prefixWord, tailWord_1344477, baseEnd_1344477] using wordTrace_append hprefix tailTrace_1344477
  have hstable : (prefixWord ++ tailWord_1344477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344477).length < 2 ^ (prefixWord ++ tailWord_1344477).sum := by decide
  have hdescent : baseEnd_1344477 < baseStart_1344477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344522 : List Nat := [3, 1, 2, 2, 3, 2, 2, 6]
def baseStart_1344522 : Nat := 118140960795 + 1344522 * 2 ^ 59
def prefixEnd_1344522 : Nat := 4983230072969 + 3 ^ 40 * 1344522 * 2
def baseEnd_1344522 : Nat := 102279412821406486695061

theorem tailTrace_1344522 : CollatzResearch.WordTrace tailWord_1344522 prefixEnd_1344522 102279412821406486695061 := by
  unfold tailWord_1344522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12259686508758473730310955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32692497356689263280829213 12259686508758473730310955)
  ·
    refine ⟨18389529763137710595466433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12259686508758473730310955 18389529763137710595466433)
    ·
      refine ⟨13792147322353282946599825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18389529763137710595466433 13792147322353282946599825)
      ·
        refine ⟨10344110491764962209949869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13792147322353282946599825 10344110491764962209949869)
        ·
          refine ⟨3879041434411860828731201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10344110491764962209949869 3879041434411860828731201)
          ·
            refine ⟨2909281075808895621548401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3879041434411860828731201 2909281075808895621548401)
            ·
              refine ⟨2181960806856671716161301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2909281075808895621548401 2181960806856671716161301)
              ·
                refine ⟨102279412821406486695061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2181960806856671716161301 102279412821406486695061)
                ·
                  rfl

theorem cell21_1344522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_1344522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344522 prefixEnd_1344522 := by exact prefixLift 1344522
  have htrace : WordTrace (prefixWord ++ tailWord_1344522) baseStart_1344522 baseEnd_1344522 := by
    simpa [prefixWord, tailWord_1344522, baseEnd_1344522] using wordTrace_append hprefix tailTrace_1344522
  have hstable : (prefixWord ++ tailWord_1344522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344522).length < 2 ^ (prefixWord ++ tailWord_1344522).sum := by decide
  have hdescent : baseEnd_1344522 < baseStart_1344522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344570 : List Nat := [3, 1, 1, 1, 3, 1, 6, 2, 3]
def baseStart_1344570 : Nat := 118140960795 + 1344570 * 2 ^ 59
def prefixEnd_1344570 : Nat := 4983230072969 + 3 ^ 40 * 1344570 * 2
def baseEnd_1344570 : Nat := 306849192718182043285085

theorem tailTrace_1344570 : CollatzResearch.WordTrace tailWord_1344570 prefixEnd_1344570 306849192718182043285085 := by
  unfold tailWord_1344570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12260124184714999779747791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32693664492573332745994109 12260124184714999779747791)
  ·
    refine ⟨18390186277072499669621687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12260124184714999779747791 18390186277072499669621687)
    ·
      refine ⟨27585279415608749504432531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18390186277072499669621687 27585279415608749504432531)
      ·
        refine ⟨41377919123413124256648797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27585279415608749504432531 41377919123413124256648797)
        ·
          refine ⟨15516719671279921596243299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41377919123413124256648797 15516719671279921596243299)
          ·
            refine ⟨23275079506919882394364949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15516719671279921596243299 23275079506919882394364949)
            ·
              refine ⟨1091019351886869487235857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23275079506919882394364949 1091019351886869487235857)
              ·
                refine ⟨818264513915152115426893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091019351886869487235857 818264513915152115426893)
                ·
                  refine ⟨306849192718182043285085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818264513915152115426893 306849192718182043285085)
                  ·
                    rfl

theorem cell21_1344570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 2, 3].length) (baseStart_1344570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344570 prefixEnd_1344570 := by exact prefixLift 1344570
  have htrace : WordTrace (prefixWord ++ tailWord_1344570) baseStart_1344570 baseEnd_1344570 := by
    simpa [prefixWord, tailWord_1344570, baseEnd_1344570] using wordTrace_append hprefix tailTrace_1344570
  have hstable : (prefixWord ++ tailWord_1344570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344570).length < 2 ^ (prefixWord ++ tailWord_1344570).sum := by decide
  have hdescent : baseEnd_1344570 < baseStart_1344570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344581 : List Nat := [1, 3, 1, 1, 1, 3, 5, 6]
def baseStart_1344581 : Nat := 118140960795 + 1344581 * 2 ^ 59
def prefixEnd_1344581 : Nat := 4983230072969 + 3 ^ 40 * 1344581 * 2
def baseEnd_1344581 : Nat := 102283901022682822867243

theorem tailTrace_1344581 : CollatzResearch.WordTrace tailWord_1344581 prefixEnd_1344581 102283901022682822867243 := by
  unfold tailWord_1344581
  simp only [CollatzResearch.WordTrace]
  refine ⟨49040897941820147997641597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32693931961213431998427731 49040897941820147997641597)
  ·
    refine ⟨18390336728182555499115599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49040897941820147997641597 18390336728182555499115599)
    ·
      refine ⟨27585505092273833248673399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18390336728182555499115599 27585505092273833248673399)
      ·
        refine ⟨41378257638410749873010099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27585505092273833248673399 41378257638410749873010099)
        ·
          refine ⟨62067386457616124809515149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41378257638410749873010099 62067386457616124809515149)
          ·
            refine ⟨23275269921606046803568181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62067386457616124809515149 23275269921606046803568181)
            ·
              refine ⟨2182056555150566887834517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23275269921606046803568181 2182056555150566887834517)
              ·
                refine ⟨102283901022682822867243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2182056555150566887834517 102283901022682822867243)
                ·
                  rfl

theorem cell21_1344581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 5, 6].length) (baseStart_1344581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344581 prefixEnd_1344581 := by exact prefixLift 1344581
  have htrace : WordTrace (prefixWord ++ tailWord_1344581) baseStart_1344581 baseEnd_1344581 := by
    simpa [prefixWord, tailWord_1344581, baseEnd_1344581] using wordTrace_append hprefix tailTrace_1344581
  have hstable : (prefixWord ++ tailWord_1344581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344581).length < 2 ^ (prefixWord ++ tailWord_1344581).sum := by decide
  have hdescent : baseEnd_1344581 < baseStart_1344581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344595 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 7]
def baseStart_1344595 : Nat := 118140960795 + 1344595 * 2 ^ 59
def prefixEnd_1344595 : Nat := 4983230072969 + 3 ^ 40 * 1344595 * 2
def baseEnd_1344595 : Nat := 306854898058787555368367

theorem tailTrace_1344595 : CollatzResearch.WordTrace tailWord_1344595 prefixEnd_1344595 306854898058787555368367 := by
  unfold tailWord_1344595
  simp only [CollatzResearch.WordTrace]
  refine ⟨49041408563769428388651239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32694272375846285592434159 49041408563769428388651239)
  ·
    refine ⟨73562112845654142582976859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49041408563769428388651239 73562112845654142582976859)
    ·
      refine ⟨110343169268481213874465289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73562112845654142582976859 110343169268481213874465289)
      ·
        refine ⟨82757376951360910405848967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110343169268481213874465289 82757376951360910405848967)
        ·
          refine ⟨124136065427041365608773451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82757376951360910405848967 124136065427041365608773451)
          ·
            refine ⟨186204098140562048413160177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124136065427041365608773451 186204098140562048413160177)
            ·
              refine ⟨139653073605421536309870133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186204098140562048413160177 139653073605421536309870133)
              ·
                refine ⟨13092475650508269029050325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139653073605421536309870133 13092475650508269029050325)
                ·
                  refine ⟨306854898058787555368367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13092475650508269029050325 306854898058787555368367)
                  ·
                    rfl

theorem cell21_1344595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 7].length) (baseStart_1344595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344595 prefixEnd_1344595 := by exact prefixLift 1344595
  have htrace : WordTrace (prefixWord ++ tailWord_1344595) baseStart_1344595 baseEnd_1344595 := by
    simpa [prefixWord, tailWord_1344595, baseEnd_1344595] using wordTrace_append hprefix tailTrace_1344595
  have hstable : (prefixWord ++ tailWord_1344595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344595).length < 2 ^ (prefixWord ++ tailWord_1344595).sum := by decide
  have hdescent : baseEnd_1344595 < baseStart_1344595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344694 : List Nat := [5, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1344694 : Nat := 118140960795 + 1344694 * 2 ^ 59
def prefixEnd_1344694 : Nat := 4983230072969 + 3 ^ 40 * 1344694 * 2
def baseEnd_1344694 : Nat := 306877491207585383218165

theorem tailTrace_1344694 : CollatzResearch.WordTrace tailWord_1344694 prefixEnd_1344694 306877491207585383218165 := by
  unfold tailWord_1344694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065313711900673018531571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32696679593607178864336757 3065313711900673018531571)
  ·
    refine ⟨4597970567851009527797357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3065313711900673018531571 4597970567851009527797357)
    ·
      refine ⟨1724238962944128572924009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4597970567851009527797357 1724238962944128572924009)
      ·
        refine ⟨1293179222208096429693007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1724238962944128572924009 1293179222208096429693007)
        ·
          refine ⟨1939768833312144644539511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293179222208096429693007 1939768833312144644539511)
          ·
            refine ⟨2909653249968216966809267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1939768833312144644539511 2909653249968216966809267)
            ·
              refine ⟨4364479874952325450213901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2909653249968216966809267 4364479874952325450213901)
              ·
                refine ⟨1636679953107122043830213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4364479874952325450213901 1636679953107122043830213)
                ·
                  refine ⟨306877491207585383218165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1636679953107122043830213 306877491207585383218165)
                  ·
                    rfl

theorem cell21_1344694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1344694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344694 prefixEnd_1344694 := by exact prefixLift 1344694
  have htrace : WordTrace (prefixWord ++ tailWord_1344694) baseStart_1344694 baseEnd_1344694 := by
    simpa [prefixWord, tailWord_1344694, baseEnd_1344694] using wordTrace_append hprefix tailTrace_1344694
  have hstable : (prefixWord ++ tailWord_1344694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344694).length < 2 ^ (prefixWord ++ tailWord_1344694).sum := by decide
  have hdescent : baseEnd_1344694 < baseStart_1344694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344733 : List Nat := [1, 4, 3, 2, 11]
def baseStart_1344733 : Nat := 118140960795 + 1344733 * 2 ^ 59
def prefixEnd_1344733 : Nat := 4983230072969 + 3 ^ 40 * 1344733 * 2
def baseEnd_1344733 : Nat := 3788720883196666445285

theorem tailTrace_1344733 : CollatzResearch.WordTrace tailWord_1344733 prefixEnd_1344733 3788720883196666445285 := by
  unfold tailWord_1344733
  simp only [CollatzResearch.WordTrace]
  refine ⟨49046441837269477957174853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32697627891512985304783235 49046441837269477957174853)
  ·
    refine ⟨9196207844488027116970285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49046441837269477957174853 9196207844488027116970285)
    ·
      refine ⟨3448577941683010168863857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9196207844488027116970285 3448577941683010168863857)
      ·
        refine ⟨2586433456262257626647893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3448577941683010168863857 2586433456262257626647893)
        ·
          refine ⟨3788720883196666445285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2586433456262257626647893 3788720883196666445285)
          ·
            rfl

theorem cell21_1344733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 11].length) (baseStart_1344733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344733 prefixEnd_1344733 := by exact prefixLift 1344733
  have htrace : WordTrace (prefixWord ++ tailWord_1344733) baseStart_1344733 baseEnd_1344733 := by
    simpa [prefixWord, tailWord_1344733, baseEnd_1344733] using wordTrace_append hprefix tailTrace_1344733
  have hstable : (prefixWord ++ tailWord_1344733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344733).length < 2 ^ (prefixWord ++ tailWord_1344733).sum := by decide
  have hdescent : baseEnd_1344733 < baseStart_1344733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344778 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_1344778 : Nat := 118140960795 + 1344778 * 2 ^ 59
def prefixEnd_1344778 : Nat := 4983230072969 + 3 ^ 40 * 1344778 * 2
def baseEnd_1344778 : Nat := 306896661152019903817993

theorem tailTrace_1344778 : CollatzResearch.WordTrace tailWord_1344778 prefixEnd_1344778 306896661152019903817993 := by
  unfold tailWord_1344778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12262020780526612660640747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32698722081404300428375325 12262020780526612660640747)
  ·
    refine ⟨18393031170789918990961121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12262020780526612660640747 18393031170789918990961121)
    ·
      refine ⟨13794773378092439243220841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18393031170789918990961121 13794773378092439243220841)
      ·
        refine ⟨10346080033569329432415631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13794773378092439243220841 10346080033569329432415631)
        ·
          refine ⟨15519120050353994148623447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10346080033569329432415631 15519120050353994148623447)
          ·
            refine ⟨23278680075530991222935171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15519120050353994148623447 23278680075530991222935171)
            ·
              refine ⟨34918020113296486834402757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23278680075530991222935171 34918020113296486834402757)
              ·
                refine ⟨6547128771243091281450517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34918020113296486834402757 6547128771243091281450517)
                ·
                  refine ⟨306896661152019903817993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6547128771243091281450517 306896661152019903817993)
                  ·
                    rfl

theorem cell21_1344778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_1344778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344778 prefixEnd_1344778 := by exact prefixLift 1344778
  have htrace : WordTrace (prefixWord ++ tailWord_1344778) baseStart_1344778 baseEnd_1344778 := by
    simpa [prefixWord, tailWord_1344778, baseEnd_1344778] using wordTrace_append hprefix tailTrace_1344778
  have hstable : (prefixWord ++ tailWord_1344778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344778).length < 2 ^ (prefixWord ++ tailWord_1344778).sum := by decide
  have hdescent : baseEnd_1344778 < baseStart_1344778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344964 : List Nat := [2, 3, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1344964 : Nat := 118140960795 + 1344964 * 2 ^ 59
def prefixEnd_1344964 : Nat := 4983230072969 + 3 ^ 40 * 1344964 * 2
def baseEnd_1344964 : Nat := 306939108886124913717613

theorem tailTrace_1344964 : CollatzResearch.WordTrace tailWord_1344964 prefixEnd_1344964 306939108886124913717613 := by
  unfold tailWord_1344964
  simp only [CollatzResearch.WordTrace]
  refine ⟨24527433549716302204416973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32703244732955069605889297 24527433549716302204416973)
  ·
    refine ⟨9197787581143613326656365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24527433549716302204416973 9197787581143613326656365)
    ·
      refine ⟨3449170342928854997496137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9197787581143613326656365 3449170342928854997496137)
      ·
        refine ⟨2586877757196641248122103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3449170342928854997496137 2586877757196641248122103)
        ·
          refine ⟨3880316635794961872183155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586877757196641248122103 3880316635794961872183155)
          ·
            refine ⟨5820474953692442808274733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3880316635794961872183155 5820474953692442808274733)
            ·
              refine ⟨2182678107634666053103025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5820474953692442808274733 2182678107634666053103025)
              ·
                refine ⟨1637008580725999539827269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182678107634666053103025 1637008580725999539827269)
                ·
                  refine ⟨306939108886124913717613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637008580725999539827269 306939108886124913717613)
                  ·
                    rfl

theorem cell21_1344964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1344964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344964 prefixEnd_1344964 := by exact prefixLift 1344964
  have htrace : WordTrace (prefixWord ++ tailWord_1344964) baseStart_1344964 baseEnd_1344964 := by
    simpa [prefixWord, tailWord_1344964, baseEnd_1344964] using wordTrace_append hprefix tailTrace_1344964
  have hstable : (prefixWord ++ tailWord_1344964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344964).length < 2 ^ (prefixWord ++ tailWord_1344964).sum := by decide
  have hdescent : baseEnd_1344964 < baseStart_1344964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1344975 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_1344975 : Nat := 118140960795 + 1344975 * 2 ^ 59
def prefixEnd_1344975 : Nat := 4983230072969 + 3 ^ 40 * 1344975 * 2
def baseEnd_1344975 : Nat := 306941619235991339034257

theorem tailTrace_1344975 : CollatzResearch.WordTrace tailWord_1344975 prefixEnd_1344975 306941619235991339034257 := by
  unfold tailWord_1344975
  simp only [CollatzResearch.WordTrace]
  refine ⟨49055268302392753287484379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32703512201595168858322919 49055268302392753287484379)
  ·
    refine ⟨73582902453589129931226569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49055268302392753287484379 73582902453589129931226569)
    ·
      refine ⟨55187176840191847448419927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73582902453589129931226569 55187176840191847448419927)
      ·
        refine ⟨82780765260287771172629891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55187176840191847448419927 82780765260287771172629891)
        ·
          refine ⟨124171147890431656758944837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82780765260287771172629891 124171147890431656758944837)
          ·
            refine ⟨23282090229455935642302157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124171147890431656758944837 23282090229455935642302157)
            ·
              refine ⟨8730783836045975865863309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23282090229455935642302157 8730783836045975865863309)
              ·
                refine ⟨3274043938517240949698741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8730783836045975865863309 3274043938517240949698741)
                ·
                  refine ⟨306941619235991339034257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274043938517240949698741 306941619235991339034257)
                  ·
                    rfl

theorem cell21_1344975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_1344975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1344975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1344975 prefixEnd_1344975 := by exact prefixLift 1344975
  have htrace : WordTrace (prefixWord ++ tailWord_1344975) baseStart_1344975 baseEnd_1344975 := by
    simpa [prefixWord, tailWord_1344975, baseEnd_1344975] using wordTrace_append hprefix tailTrace_1344975
  have hstable : (prefixWord ++ tailWord_1344975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1344975).length < 2 ^ (prefixWord ++ tailWord_1344975).sum := by decide
  have hdescent : baseEnd_1344975 < baseStart_1344975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1344975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345006 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1345006 : Nat := 118140960795 + 1345006 * 2 ^ 59
def prefixEnd_1345006 : Nat := 4983230072969 + 3 ^ 40 * 1345006 * 2
def baseEnd_1345006 : Nat := 306948693858342174017527

theorem tailTrace_1345006 : CollatzResearch.WordTrace tailWord_1345006 prefixEnd_1345006 306948693858342174017527 := by
  unfold tailWord_1345006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6132049870660055697732859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32704265976853630387908581 6132049870660055697732859)
  ·
    refine ⟨9198074805990083546599289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6132049870660055697732859 9198074805990083546599289)
    ·
      refine ⟨6898556104492562659949467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9198074805990083546599289 6898556104492562659949467)
      ·
        refine ⟨10347834156738843989924201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6898556104492562659949467 10347834156738843989924201)
        ·
          refine ⟨7760875617554132992443151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10347834156738843989924201 7760875617554132992443151)
          ·
            refine ⟨11641313426331199488664727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7760875617554132992443151 11641313426331199488664727)
            ·
              refine ⟨17461970139496799232997091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11641313426331199488664727 17461970139496799232997091)
              ·
                refine ⟨26192955209245198849495637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17461970139496799232997091 26192955209245198849495637)
                ·
                  refine ⟨306948693858342174017527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26192955209245198849495637 306948693858342174017527)
                  ·
                    rfl

theorem cell21_1345006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1345006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345006 prefixEnd_1345006 := by exact prefixLift 1345006
  have htrace : WordTrace (prefixWord ++ tailWord_1345006) baseStart_1345006 baseEnd_1345006 := by
    simpa [prefixWord, tailWord_1345006, baseEnd_1345006] using wordTrace_append hprefix tailTrace_1345006
  have hstable : (prefixWord ++ tailWord_1345006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345006).length < 2 ^ (prefixWord ++ tailWord_1345006).sum := by decide
  have hdescent : baseEnd_1345006 < baseStart_1345006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345009 : List Nat := [1, 2, 2, 2, 3, 2, 3, 3, 3]
def baseStart_1345009 : Nat := 118140960795 + 1345009 * 2 ^ 59
def prefixEnd_1345009 : Nat := 4983230072969 + 3 ^ 40 * 1345009 * 2
def baseEnd_1345009 : Nat := 306949378499214835467521

theorem tailTrace_1345009 : CollatzResearch.WordTrace tailWord_1345009 prefixEnd_1345009 306949378499214835467521 := by
  unfold tailWord_1345009
  simp only [CollatzResearch.WordTrace]
  refine ⟨49056508384269577094222081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32704338922846384729481387 49056508384269577094222081)
  ·
    refine ⟨36792381288202182820666561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49056508384269577094222081 36792381288202182820666561)
    ·
      refine ⟨27594285966151637115499921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36792381288202182820666561 27594285966151637115499921)
      ·
        refine ⟨20695714474613727836624941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27594285966151637115499921 20695714474613727836624941)
        ·
          refine ⟨7760892927980147938734353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20695714474613727836624941 7760892927980147938734353)
          ·
            refine ⟨5820669695985110954050765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7760892927980147938734353 5820669695985110954050765)
            ·
              refine ⟨2182751135994416607769037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5820669695985110954050765 2182751135994416607769037)
              ·
                refine ⟨818531675997906227913389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2182751135994416607769037 818531675997906227913389)
                ·
                  refine ⟨306949378499214835467521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818531675997906227913389 306949378499214835467521)
                  ·
                    rfl

theorem cell21_1345009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_1345009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345009 prefixEnd_1345009 := by exact prefixLift 1345009
  have htrace : WordTrace (prefixWord ++ tailWord_1345009) baseStart_1345009 baseEnd_1345009 := by
    simpa [prefixWord, tailWord_1345009, baseEnd_1345009] using wordTrace_append hprefix tailTrace_1345009
  have hstable : (prefixWord ++ tailWord_1345009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345009).length < 2 ^ (prefixWord ++ tailWord_1345009).sum := by decide
  have hdescent : baseEnd_1345009 < baseStart_1345009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345020 : List Nat := [2, 2, 2, 1, 2, 1, 11]
def baseStart_1345020 : Nat := 118140960795 + 1345020 * 2 ^ 59
def prefixEnd_1345020 : Nat := 4983230072969 + 3 ^ 40 * 1345020 * 2
def baseEnd_1345020 : Nat := 34105765427675695642685

theorem tailTrace_1345020 : CollatzResearch.WordTrace tailWord_1345020 prefixEnd_1345020 34105765427675695642685 := by
  unfold tailWord_1345020
  simp only [CollatzResearch.WordTrace]
  refine ⟨24528454793614862986436257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32704606391486483981915009 24528454793614862986436257)
  ·
    refine ⟨18396341095211147239827193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24528454793614862986436257 18396341095211147239827193)
    ·
      refine ⟨13797255821408360429870395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18396341095211147239827193 13797255821408360429870395)
      ·
        refine ⟨20695883732112540644805593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13797255821408360429870395 20695883732112540644805593)
        ·
          refine ⟨15521912799084405483604195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20695883732112540644805593 15521912799084405483604195)
          ·
            refine ⟨23282869198626608225406293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15521912799084405483604195 23282869198626608225406293)
            ·
              refine ⟨34105765427675695642685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23282869198626608225406293 34105765427675695642685)
              ·
                rfl

theorem cell21_1345020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 11].length) (baseStart_1345020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345020 prefixEnd_1345020 := by exact prefixLift 1345020
  have htrace : WordTrace (prefixWord ++ tailWord_1345020) baseStart_1345020 baseEnd_1345020 := by
    simpa [prefixWord, tailWord_1345020, baseEnd_1345020] using wordTrace_append hprefix tailTrace_1345020
  have hstable : (prefixWord ++ tailWord_1345020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345020).length < 2 ^ (prefixWord ++ tailWord_1345020).sum := by decide
  have hdescent : baseEnd_1345020 < baseStart_1345020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345026 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1345026 : Nat := 118140960795 + 1345026 * 2 ^ 59
def prefixEnd_1345026 : Nat := 4983230072969 + 3 ^ 40 * 1345026 * 2
def baseEnd_1345026 : Nat := 306953258130826583684153

theorem tailTrace_1345026 : CollatzResearch.WordTrace tailWord_1345026 prefixEnd_1345026 306953258130826583684153 := by
  unfold tailWord_1345026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12264282106301997249397733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32704752283471992665060621 12264282106301997249397733)
  ·
    refine ⟨2299552894931624484262075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12264282106301997249397733 2299552894931624484262075)
    ·
      refine ⟨3449329342397436726393113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299552894931624484262075 3449329342397436726393113)
      ·
        refine ⟨2586997006798077544794835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3449329342397436726393113 2586997006798077544794835)
        ·
          refine ⟨3880495510197116317192253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586997006798077544794835 3880495510197116317192253)
          ·
            refine ⟨1455185816323918618947095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3880495510197116317192253 1455185816323918618947095)
            ·
              refine ⟨2182778724485877928420643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455185816323918618947095 2182778724485877928420643)
              ·
                refine ⟨3274168086728816892630965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182778724485877928420643 3274168086728816892630965)
                ·
                  refine ⟨306953258130826583684153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3274168086728816892630965 306953258130826583684153)
                  ·
                    rfl

theorem cell21_1345026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1345026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345026 prefixEnd_1345026 := by exact prefixLift 1345026
  have htrace : WordTrace (prefixWord ++ tailWord_1345026) baseStart_1345026 baseEnd_1345026 := by
    simpa [prefixWord, tailWord_1345026, baseEnd_1345026] using wordTrace_append hprefix tailTrace_1345026
  have hstable : (prefixWord ++ tailWord_1345026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345026).length < 2 ^ (prefixWord ++ tailWord_1345026).sum := by decide
  have hdescent : baseEnd_1345026 < baseStart_1345026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345133 : List Nat := [1, 5, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1345133 : Nat := 118140960795 + 1345133 * 2 ^ 59
def prefixEnd_1345133 : Nat := 4983230072969 + 3 ^ 40 * 1345133 * 2
def baseEnd_1345133 : Nat := 306977676988618175400601

theorem tailTrace_1345133 : CollatzResearch.WordTrace tailWord_1345133 prefixEnd_1345133 306977676988618175400601 := by
  unfold tailWord_1345133
  simp only [CollatzResearch.WordTrace]
  refine ⟨49061031035820346271736053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32707354023880230847824035 49061031035820346271736053)
  ·
    refine ⟨4599471659608157462975255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49061031035820346271736053 4599471659608157462975255)
    ·
      refine ⟨6899207489412236194462883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599471659608157462975255 6899207489412236194462883)
      ·
        refine ⟨10348811234118354291694325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6899207489412236194462883 10348811234118354291694325)
        ·
          refine ⟨970201053198595714846343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10348811234118354291694325 970201053198595714846343)
          ·
            refine ⟨1455301579797893572269515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970201053198595714846343 1455301579797893572269515)
            ·
              refine ⟨2182952369696840358404273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455301579797893572269515 2182952369696840358404273)
              ·
                refine ⟨1637214277272630268803205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2182952369696840358404273 1637214277272630268803205)
                ·
                  refine ⟨306977676988618175400601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637214277272630268803205 306977676988618175400601)
                  ·
                    rfl

theorem cell21_1345133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1345133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345133 prefixEnd_1345133 := by exact prefixLift 1345133
  have htrace : WordTrace (prefixWord ++ tailWord_1345133) baseStart_1345133 baseEnd_1345133 := by
    simpa [prefixWord, tailWord_1345133, baseEnd_1345133] using wordTrace_append hprefix tailTrace_1345133
  have hstable : (prefixWord ++ tailWord_1345133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345133).length < 2 ^ (prefixWord ++ tailWord_1345133).sum := by decide
  have hdescent : baseEnd_1345133 < baseStart_1345133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345206 : List Nat := [5, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1345206 : Nat := 118140960795 + 1345206 * 2 ^ 59
def prefixEnd_1345206 : Nat := 4983230072969 + 3 ^ 40 * 1345206 * 2
def baseEnd_1345206 : Nat := 102331445527728756894595

theorem tailTrace_1345206 : CollatzResearch.WordTrace tailWord_1345206 prefixEnd_1345206 102331445527728756894595 := by
  unfold tailWord_1345206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066480847784742483696467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32709129043037253159428981 3066480847784742483696467)
  ·
    refine ⟨4599721271677113725544701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3066480847784742483696467 4599721271677113725544701)
    ·
      refine ⟨1724895476878917647079263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4599721271677113725544701 1724895476878917647079263)
      ·
        refine ⟨2587343215318376470618895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724895476878917647079263 2587343215318376470618895)
        ·
          refine ⟨3881014822977564705928343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587343215318376470618895 3881014822977564705928343)
          ·
            refine ⟨5821522234466347058892515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881014822977564705928343 5821522234466347058892515)
            ·
              refine ⟨8732283351699520588338773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5821522234466347058892515 8732283351699520588338773)
              ·
                refine ⟨102331445527728756894595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8732283351699520588338773 102331445527728756894595)
                ·
                  rfl

theorem cell21_1345206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1345206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345206 prefixEnd_1345206 := by exact prefixLift 1345206
  have htrace : WordTrace (prefixWord ++ tailWord_1345206) baseStart_1345206 baseEnd_1345206 := by
    simpa [prefixWord, tailWord_1345206, baseEnd_1345206] using wordTrace_append hprefix tailTrace_1345206
  have hstable : (prefixWord ++ tailWord_1345206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345206).length < 2 ^ (prefixWord ++ tailWord_1345206).sum := by decide
  have hdescent : baseEnd_1345206 < baseStart_1345206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345265 : List Nat := [1, 2, 2, 2, 2, 5, 1, 6]
def baseStart_1345265 : Nat := 118140960795 + 1345265 * 2 ^ 59
def prefixEnd_1345265 : Nat := 4983230072969 + 3 ^ 40 * 1345265 * 2
def baseEnd_1345265 : Nat := 102335933729005093066777

theorem tailTrace_1345265 : CollatzResearch.WordTrace tailWord_1345265 prefixEnd_1345265 102335933729005093066777 := by
  unfold tailWord_1345265
  simp only [CollatzResearch.WordTrace]
  refine ⟨49065845471342132815541249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32710563647561421877027499 49065845471342132815541249)
  ·
    refine ⟨36799384103506599611655937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49065845471342132815541249 36799384103506599611655937)
    ·
      refine ⟨27599538077629949708741953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36799384103506599611655937 27599538077629949708741953)
      ·
        refine ⟨20699653558222462281556465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27599538077629949708741953 20699653558222462281556465)
        ·
          refine ⟨15524740168666846711167349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20699653558222462281556465 15524740168666846711167349)
          ·
            refine ⟨1455444390812516879171939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15524740168666846711167349 1455444390812516879171939)
            ·
              refine ⟨2183166586218775318757909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455444390812516879171939 2183166586218775318757909)
              ·
                refine ⟨102335933729005093066777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2183166586218775318757909 102335933729005093066777)
                ·
                  rfl

theorem cell21_1345265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 6].length) (baseStart_1345265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345265 prefixEnd_1345265 := by exact prefixLift 1345265
  have htrace : WordTrace (prefixWord ++ tailWord_1345265) baseStart_1345265 baseEnd_1345265 := by
    simpa [prefixWord, tailWord_1345265, baseEnd_1345265] using wordTrace_append hprefix tailTrace_1345265
  have hstable : (prefixWord ++ tailWord_1345265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345265).length < 2 ^ (prefixWord ++ tailWord_1345265).sum := by decide
  have hdescent : baseEnd_1345265 < baseStart_1345265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345282 : List Nat := [3, 4, 1, 1, 1, 1, 5, 5]
def baseStart_1345282 : Nat := 118140960795 + 1345282 * 2 ^ 59
def prefixEnd_1345282 : Nat := 4983230072969 + 3 ^ 40 * 1345282 * 2
def baseEnd_1345282 : Nat := 102337226939542342472321

theorem tailTrace_1345282 : CollatzResearch.WordTrace tailWord_1345282 prefixEnd_1345282 102337226939542342472321 := by
  unfold tailWord_1345282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12266616378070136179727525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32710977008187029812606733 12266616378070136179727525)
  ·
    refine ⟨2299990570888150533698911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12266616378070136179727525 2299990570888150533698911)
    ·
      refine ⟨3449985856332225800548367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299990570888150533698911 3449985856332225800548367)
      ·
        refine ⟨5174978784498338700822551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449985856332225800548367 5174978784498338700822551)
        ·
          refine ⟨7762468176747508051233827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174978784498338700822551 7762468176747508051233827)
          ·
            refine ⟨11643702265121262076850741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7762468176747508051233827 11643702265121262076850741)
            ·
              refine ⟨1091597087355118319704757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11643702265121262076850741 1091597087355118319704757)
              ·
                refine ⟨102337226939542342472321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1091597087355118319704757 102337226939542342472321)
                ·
                  rfl

theorem cell21_1345282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_1345282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345282 prefixEnd_1345282 := by exact prefixLift 1345282
  have htrace : WordTrace (prefixWord ++ tailWord_1345282) baseStart_1345282 baseEnd_1345282 := by
    simpa [prefixWord, tailWord_1345282, baseEnd_1345282] using wordTrace_append hprefix tailTrace_1345282
  have hstable : (prefixWord ++ tailWord_1345282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345282).length < 2 ^ (prefixWord ++ tailWord_1345282).sum := by decide
  have hdescent : baseEnd_1345282 < baseStart_1345282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345341 : List Nat := [1, 4, 1, 4, 1, 2, 1, 7]
def baseStart_1345341 : Nat := 118140960795 + 1345341 * 2 ^ 59
def prefixEnd_1345341 : Nat := 4983230072969 + 3 ^ 40 * 1345341 * 2
def baseEnd_1345341 : Nat := 102341715140818678644503

theorem tailTrace_1345341 : CollatzResearch.WordTrace tailWord_1345341 prefixEnd_1345341 102341715140818678644503 := by
  unfold tailWord_1345341
  simp only [CollatzResearch.WordTrace]
  refine ⟨49068617419066797795307877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32712411612711198530205251 49068617419066797795307877)
  ·
    refine ⟨9200365766075024586620227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49068617419066797795307877 9200365766075024586620227)
    ·
      refine ⟨13800548649112536879930341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9200365766075024586620227 13800548649112536879930341)
      ·
        refine ⟨2587602871708600664986939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13800548649112536879930341 2587602871708600664986939)
        ·
          refine ⟨3881404307562900997480409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587602871708600664986939 3881404307562900997480409)
          ·
            refine ⟨2911053230672175748110307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3881404307562900997480409 2911053230672175748110307)
            ·
              refine ⟨4366579846008263622165461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911053230672175748110307 4366579846008263622165461)
              ·
                refine ⟨102341715140818678644503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4366579846008263622165461 102341715140818678644503)
                ·
                  rfl

theorem cell21_1345341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_1345341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345341 prefixEnd_1345341 := by exact prefixLift 1345341
  have htrace : WordTrace (prefixWord ++ tailWord_1345341) baseStart_1345341 baseEnd_1345341 := by
    simpa [prefixWord, tailWord_1345341, baseEnd_1345341] using wordTrace_append hprefix tailTrace_1345341
  have hstable : (prefixWord ++ tailWord_1345341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345341).length < 2 ^ (prefixWord ++ tailWord_1345341).sum := by decide
  have hdescent : baseEnd_1345341 < baseStart_1345341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345369 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 6]
def baseStart_1345369 : Nat := 118140960795 + 1345369 * 2 ^ 59
def prefixEnd_1345369 : Nat := 4983230072969 + 3 ^ 40 * 1345369 * 2
def baseEnd_1345369 : Nat := 307031535403934209466785

theorem tailTrace_1345369 : CollatzResearch.WordTrace tailWord_1345369 prefixEnd_1345369 307031535403934209466785 := by
  unfold tailWord_1345369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49069638662965358577327161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32713092441976905718218107 49069638662965358577327161)
  ·
    refine ⟨36802228997224018932995371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49069638662965358577327161 36802228997224018932995371)
    ·
      refine ⟨55203343495836028399493057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36802228997224018932995371 55203343495836028399493057)
      ·
        refine ⟨41402507621877021299619793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55203343495836028399493057 41402507621877021299619793)
        ·
          refine ⟨31051880716407765974714845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41402507621877021299619793 31051880716407765974714845)
          ·
            refine ⟨11644455268652912240518067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31051880716407765974714845 11644455268652912240518067)
            ·
              refine ⟨17466682902979368360777101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11644455268652912240518067 17466682902979368360777101)
              ·
                refine ⟨6550006088617263135291413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17466682902979368360777101 6550006088617263135291413)
                ·
                  refine ⟨307031535403934209466785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6550006088617263135291413 307031535403934209466785)
                  ·
                    rfl

theorem cell21_1345369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_1345369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345369 prefixEnd_1345369 := by exact prefixLift 1345369
  have htrace : WordTrace (prefixWord ++ tailWord_1345369) baseStart_1345369 baseEnd_1345369 := by
    simpa [prefixWord, tailWord_1345369, baseEnd_1345369] using wordTrace_append hprefix tailTrace_1345369
  have hstable : (prefixWord ++ tailWord_1345369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345369).length < 2 ^ (prefixWord ++ tailWord_1345369).sum := by decide
  have hdescent : baseEnd_1345369 < baseStart_1345369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345507 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 5]
def baseStart_1345507 : Nat := 118140960795 + 1345507 * 2 ^ 59
def prefixEnd_1345507 : Nat := 4983230072969 + 3 ^ 40 * 1345507 * 2
def baseEnd_1345507 : Nat := 307063028884076636166503

theorem tailTrace_1345507 : CollatzResearch.WordTrace tailWord_1345507 prefixEnd_1345507 307063028884076636166503 := by
  unfold tailWord_1345507
  simp only [CollatzResearch.WordTrace]
  refine ⟨49074671936465408145850775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32716447957643605430567183 49074671936465408145850775)
  ·
    refine ⟨73612007904698112218776163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49074671936465408145850775 73612007904698112218776163)
    ·
      refine ⟨110418011857047168328164245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73612007904698112218776163 110418011857047168328164245)
      ·
        refine ⟨5175844305799086015382699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110418011857047168328164245 5175844305799086015382699)
        ·
          refine ⟨7763766458698629023074049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5175844305799086015382699 7763766458698629023074049)
          ·
            refine ⟨5822824844023971767305537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7763766458698629023074049 5822824844023971767305537)
            ·
              refine ⟨4367118633017978825479153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5822824844023971767305537 4367118633017978825479153)
              ·
                refine ⟨3275338974763484119109365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4367118633017978825479153 3275338974763484119109365)
                ·
                  refine ⟨307063028884076636166503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3275338974763484119109365 307063028884076636166503)
                  ·
                    rfl

theorem cell21_1345507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 5].length) (baseStart_1345507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345507 prefixEnd_1345507 := by exact prefixLift 1345507
  have htrace : WordTrace (prefixWord ++ tailWord_1345507) baseStart_1345507 baseEnd_1345507 := by
    simpa [prefixWord, tailWord_1345507, baseEnd_1345507] using wordTrace_append hprefix tailTrace_1345507
  have hstable : (prefixWord ++ tailWord_1345507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345507).length < 2 ^ (prefixWord ++ tailWord_1345507).sum := by decide
  have hdescent : baseEnd_1345507 < baseStart_1345507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345541 : List Nat := [1, 3, 1, 1, 2, 5, 3, 2, 3]
def baseStart_1345541 : Nat := 118140960795 + 1345541 * 2 ^ 59
def prefixEnd_1345541 : Nat := 4983230072969 + 3 ^ 40 * 1345541 * 2
def baseEnd_1345541 : Nat := 307070788147300132599767

theorem tailTrace_1345541 : CollatzResearch.WordTrace tailWord_1345541 prefixEnd_1345541 307070788147300132599767 := by
  unfold tailWord_1345541
  simp only [CollatzResearch.WordTrace]
  refine ⟨49075912018342231952588477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32717274678894821301725651 49075912018342231952588477)
  ·
    refine ⟨18403467006878336982220679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49075912018342231952588477 18403467006878336982220679)
    ·
      refine ⟨27605200510317505473331019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18403467006878336982220679 27605200510317505473331019)
      ·
        refine ⟨41407800765476258209996529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27605200510317505473331019 41407800765476258209996529)
        ·
          refine ⟨31055850574107193657497397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41407800765476258209996529 31055850574107193657497397)
          ·
            refine ⟨2911485991322549405390381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31055850574107193657497397 2911485991322549405390381)
            ·
              refine ⟨1091807246745956027021393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2911485991322549405390381 1091807246745956027021393)
              ·
                refine ⟨818855435059467020266045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1091807246745956027021393 818855435059467020266045)
                ·
                  refine ⟨307070788147300132599767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818855435059467020266045 307070788147300132599767)
                  ·
                    rfl

theorem cell21_1345541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_1345541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345541 prefixEnd_1345541 := by exact prefixLift 1345541
  have htrace : WordTrace (prefixWord ++ tailWord_1345541) baseStart_1345541 baseEnd_1345541 := by
    simpa [prefixWord, tailWord_1345541, baseEnd_1345541] using wordTrace_append hprefix tailTrace_1345541
  have hstable : (prefixWord ++ tailWord_1345541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345541).length < 2 ^ (prefixWord ++ tailWord_1345541).sum := by decide
  have hdescent : baseEnd_1345541 < baseStart_1345541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345600 : List Nat := [2, 1, 1, 2, 2, 5, 1, 4, 3]
def baseStart_1345600 : Nat := 118140960795 + 1345600 * 2 ^ 59
def prefixEnd_1345600 : Nat := 4983230072969 + 3 ^ 40 * 1345600 * 2
def baseEnd_1345600 : Nat := 307084252751129141116313

theorem tailTrace_1345600 : CollatzResearch.WordTrace tailWord_1345600 prefixEnd_1345600 307084252751129141116313 := by
  unfold tailWord_1345600
  simp only [CollatzResearch.WordTrace]
  refine ⟨24539031962564242514493127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32718709283418990019324169 24539031962564242514493127)
  ·
    refine ⟨36808547943846363771739691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24539031962564242514493127 36808547943846363771739691)
    ·
      refine ⟨55212821915769545657609537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36808547943846363771739691 55212821915769545657609537)
      ·
        refine ⟨41409616436827159243207153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55212821915769545657609537 41409616436827159243207153)
        ·
          refine ⟨31057212327620369432405365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41409616436827159243207153 31057212327620369432405365)
          ·
            refine ⟨2911613655714409634288003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31057212327620369432405365 2911613655714409634288003)
            ·
              refine ⟨4367420483571614451432005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2911613655714409634288003 4367420483571614451432005)
              ·
                refine ⟨818891340669677709643501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4367420483571614451432005 818891340669677709643501)
                ·
                  refine ⟨307084252751129141116313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818891340669677709643501 307084252751129141116313)
                  ·
                    rfl

theorem cell21_1345600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_1345600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345600 prefixEnd_1345600 := by exact prefixLift 1345600
  have htrace : WordTrace (prefixWord ++ tailWord_1345600) baseStart_1345600 baseEnd_1345600 := by
    simpa [prefixWord, tailWord_1345600, baseEnd_1345600] using wordTrace_append hprefix tailTrace_1345600
  have hstable : (prefixWord ++ tailWord_1345600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345600).length < 2 ^ (prefixWord ++ tailWord_1345600).sum := by decide
  have hdescent : baseEnd_1345600 < baseStart_1345600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345614 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_1345614 : Nat := 118140960795 + 1345614 * 2 ^ 59
def prefixEnd_1345614 : Nat := 4983230072969 + 3 ^ 40 * 1345614 * 2
def baseEnd_1345614 : Nat := 307087447741868227882951

theorem tailTrace_1345614 : CollatzResearch.WordTrace tailWord_1345614 prefixEnd_1345614 307087447741868227882951 := by
  unfold tailWord_1345614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6134821818384720677499487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32719049698051843613330597 6134821818384720677499487)
  ·
    refine ⟨9202232727577081016249231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6134821818384720677499487 9202232727577081016249231)
    ·
      refine ⟨13803349091365621524373847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9202232727577081016249231 13803349091365621524373847)
      ·
        refine ⟨20705023637048432286560771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13803349091365621524373847 20705023637048432286560771)
        ·
          refine ⟨31057535455572648429841157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20705023637048432286560771 31057535455572648429841157)
          ·
            refine ⟨5823287897919871580595217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31057535455572648429841157 5823287897919871580595217)
            ·
              refine ⟨4367465923439903685446413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5823287897919871580595217 4367465923439903685446413)
              ·
                refine ⟨1637799721289963882042405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4367465923439903685446413 1637799721289963882042405)
                ·
                  refine ⟨307087447741868227882951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637799721289963882042405 307087447741868227882951)
                  ·
                    rfl

theorem cell21_1345614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_1345614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345614 prefixEnd_1345614 := by exact prefixLift 1345614
  have htrace : WordTrace (prefixWord ++ tailWord_1345614) baseStart_1345614 baseEnd_1345614 := by
    simpa [prefixWord, tailWord_1345614, baseEnd_1345614] using wordTrace_append hprefix tailTrace_1345614
  have hstable : (prefixWord ++ tailWord_1345614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345614).length < 2 ^ (prefixWord ++ tailWord_1345614).sum := by decide
  have hdescent : baseEnd_1345614 < baseStart_1345614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345634 : List Nat := [3, 3, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1345634 : Nat := 118140960795 + 1345634 * 2 ^ 59
def prefixEnd_1345634 : Nat := 4983230072969 + 3 ^ 40 * 1345634 * 2
def baseEnd_1345634 : Nat := 307092012014352637549577

theorem tailTrace_1345634 : CollatzResearch.WordTrace tailWord_1345634 prefixEnd_1345634 307092012014352637549577 := by
  unfold tailWord_1345634
  simp only [CollatzResearch.WordTrace]
  refine ⟨12269826001751327208930989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32719536004670205890482637 12269826001751327208930989)
  ·
    refine ⟨4601184750656747703349121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12269826001751327208930989 4601184750656747703349121)
    ·
      refine ⟨3450888562992560777511841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4601184750656747703349121 3450888562992560777511841)
      ·
        refine ⟨2588166422244420583133881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3450888562992560777511841 2588166422244420583133881)
        ·
          refine ⟨1941124816683315437350411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2588166422244420583133881 1941124816683315437350411)
          ·
            refine ⟨2911687225024973156025617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1941124816683315437350411 2911687225024973156025617)
            ·
              refine ⟨2183765418768729867019213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2911687225024973156025617 2183765418768729867019213)
              ·
                refine ⟨818912032038273700132205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2183765418768729867019213 818912032038273700132205)
                ·
                  refine ⟨307092012014352637549577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818912032038273700132205 307092012014352637549577)
                  ·
                    rfl

theorem cell21_1345634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1345634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345634 prefixEnd_1345634 := by exact prefixLift 1345634
  have htrace : WordTrace (prefixWord ++ tailWord_1345634) baseStart_1345634 baseEnd_1345634 := by
    simpa [prefixWord, tailWord_1345634, baseEnd_1345634] using wordTrace_append hprefix tailTrace_1345634
  have hstable : (prefixWord ++ tailWord_1345634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345634).length < 2 ^ (prefixWord ++ tailWord_1345634).sum := by decide
  have hdescent : baseEnd_1345634 < baseStart_1345634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345693 : List Nat := [1, 4, 2, 1, 1, 5, 1, 3, 3]
def baseStart_1345693 : Nat := 118140960795 + 1345693 * 2 ^ 59
def prefixEnd_1345693 : Nat := 4983230072969 + 3 ^ 40 * 1345693 * 2
def baseEnd_1345693 : Nat := 307105476618181646066123

theorem tailTrace_1345693 : CollatzResearch.WordTrace tailWord_1345693 prefixEnd_1345693 307105476618181646066123 := by
  unfold tailWord_1345693
  simp only [CollatzResearch.WordTrace]
  refine ⟨49081455913791561912121733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32720970609194374608081155 49081455913791561912121733)
  ·
    refine ⟨9202772983835917858522825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49081455913791561912121733 9202772983835917858522825)
    ·
      refine ⟨6902079737876938393892119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9202772983835917858522825 6902079737876938393892119)
      ·
        refine ⟨10353119606815407590838179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6902079737876938393892119 10353119606815407590838179)
        ·
          refine ⟨15529679410223111386257269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10353119606815407590838179 15529679410223111386257269)
          ·
            refine ⟨1455907444708416692461619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15529679410223111386257269 1455907444708416692461619)
            ·
              refine ⟨2183861167062625038692429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455907444708416692461619 2183861167062625038692429)
              ·
                refine ⟨818947937648484389509661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2183861167062625038692429 818947937648484389509661)
                ·
                  refine ⟨307105476618181646066123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 818947937648484389509661 307105476618181646066123)
                  ·
                    rfl

theorem cell21_1345693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_1345693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345693 prefixEnd_1345693 := by exact prefixLift 1345693
  have htrace : WordTrace (prefixWord ++ tailWord_1345693) baseStart_1345693 baseEnd_1345693 := by
    simpa [prefixWord, tailWord_1345693, baseEnd_1345693] using wordTrace_append hprefix tailTrace_1345693
  have hstable : (prefixWord ++ tailWord_1345693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345693).length < 2 ^ (prefixWord ++ tailWord_1345693).sum := by decide
  have hdescent : baseEnd_1345693 < baseStart_1345693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345710 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_1345710 : Nat := 118140960795 + 1345710 * 2 ^ 59
def prefixEnd_1345710 : Nat := 4983230072969 + 3 ^ 40 * 1345710 * 2
def baseEnd_1345710 : Nat := 307109356249793394282755

theorem tailTrace_1345710 : CollatzResearch.WordTrace tailWord_1345710 prefixEnd_1345710 307109356249793394282755 := by
  unfold tailWord_1345710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6135259494341246726936323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32721383969819982543660389 6135259494341246726936323)
  ·
    refine ⟨9202889241511870090404485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6135259494341246726936323 9202889241511870090404485)
    ·
      refine ⟨1725541732783475641950841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9202889241511870090404485 1725541732783475641950841)
      ·
        refine ⟨1294156299587606731463131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725541732783475641950841 1294156299587606731463131)
        ·
          refine ⟨1941234449381410097194697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1294156299587606731463131 1941234449381410097194697)
          ·
            refine ⟨1455925837036057572896023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941234449381410097194697 1455925837036057572896023)
            ·
              refine ⟨2183888755554086359344035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1455925837036057572896023 2183888755554086359344035)
              ·
                refine ⟨3275833133331129539016053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2183888755554086359344035 3275833133331129539016053)
                ·
                  refine ⟨307109356249793394282755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3275833133331129539016053 307109356249793394282755)
                  ·
                    rfl

theorem cell21_1345710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_1345710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345710 prefixEnd_1345710 := by exact prefixLift 1345710
  have htrace : WordTrace (prefixWord ++ tailWord_1345710) baseStart_1345710 baseEnd_1345710 := by
    simpa [prefixWord, tailWord_1345710, baseEnd_1345710] using wordTrace_append hprefix tailTrace_1345710
  have hstable : (prefixWord ++ tailWord_1345710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345710).length < 2 ^ (prefixWord ++ tailWord_1345710).sum := by decide
  have hdescent : baseEnd_1345710 < baseStart_1345710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345724 : List Nat := [2, 2, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1345724 : Nat := 118140960795 + 1345724 * 2 ^ 59
def prefixEnd_1345724 : Nat := 4983230072969 + 3 ^ 40 * 1345724 * 2
def baseEnd_1345724 : Nat := 307112551240532481049393

theorem tailTrace_1345724 : CollatzResearch.WordTrace tailWord_1345724 prefixEnd_1345724 307112551240532481049393 := by
  unfold tailWord_1345724
  simp only [CollatzResearch.WordTrace]
  refine ⟨24541293288339627103250113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32721724384452836137666817 24541293288339627103250113)
  ·
    refine ⟨18405969966254720327437585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24541293288339627103250113 18405969966254720327437585)
    ·
      refine ⟨13804477474691040245578189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18405969966254720327437585 13804477474691040245578189)
      ·
        refine ⟨5176679053009140092091821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13804477474691040245578189 5176679053009140092091821)
        ·
          refine ⟨1941254644878427534534433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5176679053009140092091821 1941254644878427534534433)
          ·
            refine ⟨1455940983658820650900825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941254644878427534534433 1455940983658820650900825)
            ·
              refine ⟨1091955737744115488175619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1455940983658820650900825 1091955737744115488175619)
              ·
                refine ⟨1637933606616173232263429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1091955737744115488175619 1637933606616173232263429)
                ·
                  refine ⟨307112551240532481049393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1637933606616173232263429 307112551240532481049393)
                  ·
                    rfl

theorem cell21_1345724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1345724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345724 prefixEnd_1345724 := by exact prefixLift 1345724
  have htrace : WordTrace (prefixWord ++ tailWord_1345724) baseStart_1345724 baseEnd_1345724 := by
    simpa [prefixWord, tailWord_1345724, baseEnd_1345724] using wordTrace_append hprefix tailTrace_1345724
  have hstable : (prefixWord ++ tailWord_1345724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345724).length < 2 ^ (prefixWord ++ tailWord_1345724).sum := by decide
  have hdescent : baseEnd_1345724 < baseStart_1345724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345828 : List Nat := [2, 3, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1345828 : Nat := 118140960795 + 1345828 * 2 ^ 59
def prefixEnd_1345828 : Nat := 4983230072969 + 3 ^ 40 * 1345828 * 2
def baseEnd_1345828 : Nat := 307136285457451411315847

theorem tailTrace_1345828 : CollatzResearch.WordTrace tailWord_1345828 prefixEnd_1345828 307136285457451411315847 := by
  unfold tailWord_1345828
  simp only [CollatzResearch.WordTrace]
  refine ⟨24543189884151239984143069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32724253178868319978857425 24543189884151239984143069)
  ·
    refine ⟨9203696206556714994053651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24543189884151239984143069 9203696206556714994053651)
    ·
      refine ⟨13805544309835072491080477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9203696206556714994053651 13805544309835072491080477)
      ·
        refine ⟨5177079116188152184155179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13805544309835072491080477 5177079116188152184155179)
        ·
          refine ⟨7765618674282228276232769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5177079116188152184155179 7765618674282228276232769)
          ·
            refine ⟨5824214005711671207174577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7765618674282228276232769 5824214005711671207174577)
            ·
              refine ⟨4368160504283753405380933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824214005711671207174577 4368160504283753405380933)
              ·
                refine ⟨819030094553203763508925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4368160504283753405380933 819030094553203763508925)
                ·
                  refine ⟨307136285457451411315847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819030094553203763508925 307136285457451411315847)
                  ·
                    rfl

theorem cell21_1345828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1345828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345828 prefixEnd_1345828 := by exact prefixLift 1345828
  have htrace : WordTrace (prefixWord ++ tailWord_1345828) baseStart_1345828 baseEnd_1345828 := by
    simpa [prefixWord, tailWord_1345828, baseEnd_1345828] using wordTrace_append hprefix tailTrace_1345828
  have hstable : (prefixWord ++ tailWord_1345828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345828).length < 2 ^ (prefixWord ++ tailWord_1345828).sum := by decide
  have hdescent : baseEnd_1345828 < baseStart_1345828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345887 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 3]
def baseStart_1345887 : Nat := 118140960795 + 1345887 * 2 ^ 59
def prefixEnd_1345887 : Nat := 4983230072969 + 3 ^ 40 * 1345887 * 2
def baseEnd_1345887 : Nat := 307149750061280419832393

theorem tailTrace_1345887 : CollatzResearch.WordTrace tailWord_1345887 prefixEnd_1345887 307149750061280419832393 := by
  unfold tailWord_1345887
  simp only [CollatzResearch.WordTrace]
  refine ⟨49088531675088733044683915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32725687783392488696455943 49088531675088733044683915)
  ·
    refine ⟨73632797512633099567025873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49088531675088733044683915 73632797512633099567025873)
    ·
      refine ⟨55224598134474824675269405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73632797512633099567025873 55224598134474824675269405)
      ·
        refine ⟨20709224300428059253226027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55224598134474824675269405 20709224300428059253226027)
        ·
          refine ⟨31063836450642088879839041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20709224300428059253226027 31063836450642088879839041)
          ·
            refine ⟨23297877337981566659879281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31063836450642088879839041 23297877337981566659879281)
            ·
              refine ⟨17473408003486174994909461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23297877337981566659879281 17473408003486174994909461)
              ·
                refine ⟨819066000163414452886381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17473408003486174994909461 819066000163414452886381)
                ·
                  refine ⟨307149750061280419832393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819066000163414452886381 307149750061280419832393)
                  ·
                    rfl

theorem cell21_1345887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 3].length) (baseStart_1345887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345887 prefixEnd_1345887 := by exact prefixLift 1345887
  have htrace : WordTrace (prefixWord ++ tailWord_1345887) baseStart_1345887 baseEnd_1345887 := by
    simpa [prefixWord, tailWord_1345887, baseEnd_1345887] using wordTrace_append hprefix tailTrace_1345887
  have hstable : (prefixWord ++ tailWord_1345887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345887).length < 2 ^ (prefixWord ++ tailWord_1345887).sum := by decide
  have hdescent : baseEnd_1345887 < baseStart_1345887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345915 : List Nat := [1, 1, 1, 1, 1, 7, 2, 7]
def baseStart_1345915 : Nat := 118140960795 + 1345915 * 2 ^ 59
def prefixEnd_1345915 : Nat := 4983230072969 + 3 ^ 40 * 1345915 * 2
def baseEnd_1345915 : Nat := 102385380014252864455223

theorem tailTrace_1345915 : CollatzResearch.WordTrace tailWord_1345915 prefixEnd_1345915 102385380014252864455223 := by
  unfold tailWord_1345915
  simp only [CollatzResearch.WordTrace]
  refine ⟨49089552918987293826703199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32726368612658195884468799 49089552918987293826703199)
  ·
    refine ⟨73634329378480940740054799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49089552918987293826703199 73634329378480940740054799)
    ·
      refine ⟨110451494067721411110082199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73634329378480940740054799 110451494067721411110082199)
      ·
        refine ⟨165677241101582116665123299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110451494067721411110082199 165677241101582116665123299)
        ·
          refine ⟨248515861652373174997684949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165677241101582116665123299 248515861652373174997684949)
          ·
            refine ⟨5824590507477496289008241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 248515861652373174997684949 5824590507477496289008241)
            ·
              refine ⟨4368442880608122216756181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5824590507477496289008241 4368442880608122216756181)
              ·
                refine ⟨102385380014252864455223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4368442880608122216756181 102385380014252864455223)
                ·
                  rfl

theorem cell21_1345915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 7].length) (baseStart_1345915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345915 prefixEnd_1345915 := by exact prefixLift 1345915
  have htrace : WordTrace (prefixWord ++ tailWord_1345915) baseStart_1345915 baseEnd_1345915 := by
    simpa [prefixWord, tailWord_1345915, baseEnd_1345915] using wordTrace_append hprefix tailTrace_1345915
  have hstable : (prefixWord ++ tailWord_1345915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345915).length < 2 ^ (prefixWord ++ tailWord_1345915).sum := by decide
  have hdescent : baseEnd_1345915 < baseStart_1345915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345949 : List Nat := [1, 4, 2, 1, 4, 2, 1, 6]
def baseStart_1345949 : Nat := 118140960795 + 1345949 * 2 ^ 59
def prefixEnd_1345949 : Nat := 4983230072969 + 3 ^ 40 * 1345949 * 2
def baseEnd_1345949 : Nat := 102387966435327363266311

theorem tailTrace_1345949 : CollatzResearch.WordTrace tailWord_1345949 prefixEnd_1345949 102387966435327363266311 := by
  unfold tailWord_1345949
  simp only [CollatzResearch.WordTrace]
  refine ⟨49090793000864117633440901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32727195333909411755627267 49090793000864117633440901)
  ·
    refine ⟨9204523687662022056270169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49090793000864117633440901 9204523687662022056270169)
    ·
      refine ⟨6903392765746516542202627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9204523687662022056270169 6903392765746516542202627)
      ·
        refine ⟨10355089148619774813303941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6903392765746516542202627 10355089148619774813303941)
        ·
          refine ⟨1941579215366207777494489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10355089148619774813303941 1941579215366207777494489)
          ·
            refine ⟨1456184411524655833120867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1941579215366207777494489 1456184411524655833120867)
            ·
              refine ⟨2184276617286983749681301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456184411524655833120867 2184276617286983749681301)
              ·
                refine ⟨102387966435327363266311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2184276617286983749681301 102387966435327363266311)
                ·
                  rfl

theorem cell21_1345949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 6].length) (baseStart_1345949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345949 prefixEnd_1345949 := by exact prefixLift 1345949
  have htrace : WordTrace (prefixWord ++ tailWord_1345949) baseStart_1345949 baseEnd_1345949 := by
    simpa [prefixWord, tailWord_1345949, baseEnd_1345949] using wordTrace_append hprefix tailTrace_1345949
  have hstable : (prefixWord ++ tailWord_1345949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345949).length < 2 ^ (prefixWord ++ tailWord_1345949).sum := by decide
  have hdescent : baseEnd_1345949 < baseStart_1345949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345980 : List Nat := [2, 2, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1345980 : Nat := 118140960795 + 1345980 * 2 ^ 59
def prefixEnd_1345980 : Nat := 4983230072969 + 3 ^ 40 * 1345980 * 2
def baseEnd_1345980 : Nat := 307170973928332924782203

theorem tailTrace_1345980 : CollatzResearch.WordTrace tailWord_1345980 prefixEnd_1345980 307170973928332924782203 := by
  unfold tailWord_1345980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24545961831875904963909697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32727949109167873285212929 24545961831875904963909697)
  ·
    refine ⟨18409471373906928722932273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24545961831875904963909697 18409471373906928722932273)
    ·
      refine ⟨13807103530430196542199205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18409471373906928722932273 13807103530430196542199205)
      ·
        refine ⟨2588831911955661851662351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13807103530430196542199205 2588831911955661851662351)
        ·
          refine ⟨3883247867933492777493527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2588831911955661851662351 3883247867933492777493527)
          ·
            refine ⟨5824871801900239166240291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883247867933492777493527 5824871801900239166240291)
            ·
              refine ⟨8737307702850358749360437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5824871801900239166240291 8737307702850358749360437)
              ·
                refine ⟨819122597142221132752541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8737307702850358749360437 819122597142221132752541)
                ·
                  refine ⟨307170973928332924782203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819122597142221132752541 307170973928332924782203)
                  ·
                    rfl

theorem cell21_1345980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1345980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345980 prefixEnd_1345980 := by exact prefixLift 1345980
  have htrace : WordTrace (prefixWord ++ tailWord_1345980) baseStart_1345980 baseEnd_1345980 := by
    simpa [prefixWord, tailWord_1345980, baseEnd_1345980] using wordTrace_append hprefix tailTrace_1345980
  have hstable : (prefixWord ++ tailWord_1345980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345980).length < 2 ^ (prefixWord ++ tailWord_1345980).sum := by decide
  have hdescent : baseEnd_1345980 < baseStart_1345980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1345991 : List Nat := [1, 1, 4, 1, 1, 5, 8]
def baseStart_1345991 : Nat := 118140960795 + 1345991 * 2 ^ 59
def prefixEnd_1345991 : Nat := 4983230072969 + 3 ^ 40 * 1345991 * 2
def baseEnd_1345991 : Nat := 34130387142022150010983

theorem tailTrace_1345991 : CollatzResearch.WordTrace tailWord_1345991 prefixEnd_1345991 34130387142022150010983 := by
  unfold tailWord_1345991
  simp only [CollatzResearch.WordTrace]
  refine ⟨49092324866711958806469827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32728216577807972537646551 49092324866711958806469827)
  ·
    refine ⟨73638487300067938209704741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49092324866711958806469827 73638487300067938209704741)
    ·
      refine ⟨13807216368762738414319639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73638487300067938209704741 13807216368762738414319639)
      ·
        refine ⟨20710824553144107621479459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13807216368762738414319639 20710824553144107621479459)
        ·
          refine ⟨31066236829716161432219189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20710824553144107621479459 31066236829716161432219189)
          ·
            refine ⟨2912459702785890134270549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31066236829716161432219189 2912459702785890134270549)
            ·
              refine ⟨34130387142022150010983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2912459702785890134270549 34130387142022150010983)
              ·
                rfl

theorem cell21_1345991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 8].length) (baseStart_1345991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1345991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1345991 prefixEnd_1345991 := by exact prefixLift 1345991
  have htrace : WordTrace (prefixWord ++ tailWord_1345991) baseStart_1345991 baseEnd_1345991 := by
    simpa [prefixWord, tailWord_1345991, baseEnd_1345991] using wordTrace_append hprefix tailTrace_1345991
  have hstable : (prefixWord ++ tailWord_1345991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1345991).length < 2 ^ (prefixWord ++ tailWord_1345991).sum := by decide
  have hdescent : baseEnd_1345991 < baseStart_1345991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1345991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346067 : List Nat := [1, 1, 1, 2, 1, 5, 4, 6]
def baseStart_1346067 : Nat := 118140960795 + 1346067 * 2 ^ 59
def prefixEnd_1346067 : Nat := 4983230072969 + 3 ^ 40 * 1346067 * 2
def baseEnd_1346067 : Nat := 102396942837880035610675

theorem tailTrace_1346067 : CollatzResearch.WordTrace tailWord_1346067 prefixEnd_1346067 102396942837880035610675 := by
  unfold tailWord_1346067
  simp only [CollatzResearch.WordTrace]
  refine ⟨49095096814436623786236455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32730064542957749190824303 49095096814436623786236455)
  ·
    refine ⟨73642645221654935679354683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49095096814436623786236455 73642645221654935679354683)
    ·
      refine ⟨110463967832482403519032025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73642645221654935679354683 110463967832482403519032025)
      ·
        refine ⟨82847975874361802639274019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110463967832482403519032025 82847975874361802639274019)
        ·
          refine ⟨124271963811542703958911029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82847975874361802639274019 124271963811542703958911029)
          ·
            refine ⟨11650496607332128496147909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124271963811542703958911029 11650496607332128496147909)
            ·
              refine ⟨2184468113874774093027733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11650496607332128496147909 2184468113874774093027733)
              ·
                refine ⟨102396942837880035610675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2184468113874774093027733 102396942837880035610675)
                ·
                  rfl

theorem cell21_1346067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_1346067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346067 prefixEnd_1346067 := by exact prefixLift 1346067
  have htrace : WordTrace (prefixWord ++ tailWord_1346067) baseStart_1346067 baseEnd_1346067 := by
    simpa [prefixWord, tailWord_1346067, baseEnd_1346067] using wordTrace_append hprefix tailTrace_1346067
  have hstable : (prefixWord ++ tailWord_1346067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346067).length < 2 ^ (prefixWord ++ tailWord_1346067).sum := by decide
  have hdescent : baseEnd_1346067 < baseStart_1346067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346112 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_1346112 : Nat := 118140960795 + 1346112 * 2 ^ 59
def prefixEnd_1346112 : Nat := 4983230072969 + 3 ^ 40 * 1346112 * 2
def baseEnd_1346112 : Nat := 307201098126730028581933

theorem tailTrace_1346112 : CollatzResearch.WordTrace tailWord_1346112 prefixEnd_1346112 307201098126730028581933 := by
  unfold tailWord_1346112
  simp only [CollatzResearch.WordTrace]
  refine ⟨24548369049636798235812295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32731158732849064314416393 24548369049636798235812295)
  ·
    refine ⟨36822553574455197353718443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24548369049636798235812295 36822553574455197353718443)
    ·
      refine ⟨55233830361682796030577665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36822553574455197353718443 55233830361682796030577665)
      ·
        refine ⟨41425372771262097022933249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55233830361682796030577665 41425372771262097022933249)
        ·
          refine ⟨31069029578446572767199937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41425372771262097022933249 31069029578446572767199937)
          ·
            refine ⟨23301772183834929575399953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31069029578446572767199937 23301772183834929575399953)
            ·
              refine ⟨17476329137876197181549965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23301772183834929575399953 17476329137876197181549965)
              ·
                refine ⟨6553623426703573943081237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17476329137876197181549965 6553623426703573943081237)
                ·
                  refine ⟨307201098126730028581933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6553623426703573943081237 307201098126730028581933)
                  ·
                    rfl

theorem cell21_1346112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_1346112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346112 prefixEnd_1346112 := by exact prefixLift 1346112
  have htrace : WordTrace (prefixWord ++ tailWord_1346112) baseStart_1346112 baseEnd_1346112 := by
    simpa [prefixWord, tailWord_1346112, baseEnd_1346112] using wordTrace_append hprefix tailTrace_1346112
  have hstable : (prefixWord ++ tailWord_1346112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346112).length < 2 ^ (prefixWord ++ tailWord_1346112).sum := by decide
  have hdescent : baseEnd_1346112 < baseStart_1346112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346118 : List Nat := [6, 1, 1, 1, 2, 3, 1, 6]
def baseStart_1346118 : Nat := 118140960795 + 1346118 * 2 ^ 59
def prefixEnd_1346118 : Nat := 4983230072969 + 3 ^ 40 * 1346118 * 2
def baseEnd_1346118 : Nat := 102400822469491783827307

theorem tailTrace_1346118 : CollatzResearch.WordTrace tailWord_1346118 prefixEnd_1346118 102400822469491783827307 := by
  unfold tailWord_1346118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534279904289120609260719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32731304624834572997562005 1534279904289120609260719)
  ·
    refine ⟨2301419856433680913891079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1534279904289120609260719 2301419856433680913891079)
    ·
      refine ⟨3452129784650521370836619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2301419856433680913891079 3452129784650521370836619)
      ·
        refine ⟨5178194676975782056254929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3452129784650521370836619 5178194676975782056254929)
        ·
          refine ⟨3883646007731836542191197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5178194676975782056254929 3883646007731836542191197)
          ·
            refine ⟨1456367252899438703321699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3883646007731836542191197 1456367252899438703321699)
            ·
              refine ⟨2184550879349158054982549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456367252899438703321699 2184550879349158054982549)
              ·
                refine ⟨102400822469491783827307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2184550879349158054982549 102400822469491783827307)
                ·
                  rfl

theorem cell21_1346118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_1346118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346118 prefixEnd_1346118 := by exact prefixLift 1346118
  have htrace : WordTrace (prefixWord ++ tailWord_1346118) baseStart_1346118 baseEnd_1346118 := by
    simpa [prefixWord, tailWord_1346118, baseEnd_1346118] using wordTrace_append hprefix tailTrace_1346118
  have hstable : (prefixWord ++ tailWord_1346118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346118).length < 2 ^ (prefixWord ++ tailWord_1346118).sum := by decide
  have hdescent : baseEnd_1346118 < baseStart_1346118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346129 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 4]
def baseStart_1346129 : Nat := 118140960795 + 1346129 * 2 ^ 59
def prefixEnd_1346129 : Nat := 4983230072969 + 3 ^ 40 * 1346129 * 2
def baseEnd_1346129 : Nat := 307204977758341776798565

theorem tailTrace_1346129 : CollatzResearch.WordTrace tailWord_1346129 prefixEnd_1346129 307204977758341776798565 := by
  unfold tailWord_1346129
  simp only [CollatzResearch.WordTrace]
  refine ⟨49097358140212008374993441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32731572093474672249995627 49097358140212008374993441)
  ·
    refine ⟨36823018605159006281245081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49097358140212008374993441 36823018605159006281245081)
    ·
      refine ⟨27617263953869254710933811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36823018605159006281245081 27617263953869254710933811)
      ·
        refine ⟨41425895930803882066400717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27617263953869254710933811 41425895930803882066400717)
        ·
          refine ⟨15534710974051455774900269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41425895930803882066400717 15534710974051455774900269)
          ·
            refine ⟨5825516615269295915587601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15534710974051455774900269 5825516615269295915587601)
            ·
              refine ⟨4369137461451971936690701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5825516615269295915587601 4369137461451971936690701)
              ·
                refine ⟨1638426548044489476259013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4369137461451971936690701 1638426548044489476259013)
                ·
                  refine ⟨307204977758341776798565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638426548044489476259013 307204977758341776798565)
                  ·
                    rfl

theorem cell21_1346129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_1346129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346129 prefixEnd_1346129 := by exact prefixLift 1346129
  have htrace : WordTrace (prefixWord ++ tailWord_1346129) baseStart_1346129 baseEnd_1346129 := by
    simpa [prefixWord, tailWord_1346129, baseEnd_1346129] using wordTrace_append hprefix tailTrace_1346129
  have hstable : (prefixWord ++ tailWord_1346129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346129).length < 2 ^ (prefixWord ++ tailWord_1346129).sum := by decide
  have hdescent : baseEnd_1346129 < baseStart_1346129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346222 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_1346222 : Nat := 118140960795 + 1346222 * 2 ^ 59
def prefixEnd_1346222 : Nat := 4983230072969 + 3 ^ 40 * 1346222 * 2
def baseEnd_1346222 : Nat := 307226201625394281748375

theorem tailTrace_1346222 : CollatzResearch.WordTrace tailWord_1346222 prefixEnd_1346222 307226201625394281748375 := by
  unfold tailWord_1346222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6137593766109385657266115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32733833419250056838752613 6137593766109385657266115)
  ·
    refine ⟨9206390649164078485899173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6137593766109385657266115 9206390649164078485899173)
    ·
      refine ⟨1726198246718264716106095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9206390649164078485899173 1726198246718264716106095)
      ·
        refine ⟨2589297370077397074159143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726198246718264716106095 2589297370077397074159143)
        ·
          refine ⟨3883946055116095611238715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589297370077397074159143 3883946055116095611238715)
          ·
            refine ⟨5825919082674143416858073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3883946055116095611238715 5825919082674143416858073)
            ·
              refine ⟨4369439312005607562643555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5825919082674143416858073 4369439312005607562643555)
              ·
                refine ⟨6554158968008411343965333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4369439312005607562643555 6554158968008411343965333)
                ·
                  refine ⟨307226201625394281748375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6554158968008411343965333 307226201625394281748375)
                  ·
                    rfl

theorem cell21_1346222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_1346222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346222 prefixEnd_1346222 := by exact prefixLift 1346222
  have htrace : WordTrace (prefixWord ++ tailWord_1346222) baseStart_1346222 baseEnd_1346222 := by
    simpa [prefixWord, tailWord_1346222, baseEnd_1346222] using wordTrace_append hprefix tailTrace_1346222
  have hstable : (prefixWord ++ tailWord_1346222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346222).length < 2 ^ (prefixWord ++ tailWord_1346222).sum := by decide
  have hdescent : baseEnd_1346222 < baseStart_1346222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346225 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 5]
def baseStart_1346225 : Nat := 118140960795 + 1346225 * 2 ^ 59
def prefixEnd_1346225 : Nat := 4983230072969 + 3 ^ 40 * 1346225 * 2
def baseEnd_1346225 : Nat := 307226886266266943198369

theorem tailTrace_1346225 : CollatzResearch.WordTrace tailWord_1346225 prefixEnd_1346225 307226886266266943198369 := by
  unfold tailWord_1346225
  simp only [CollatzResearch.WordTrace]
  refine ⟨49100859547864216770488129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32733906365242811180325419 49100859547864216770488129)
  ·
    refine ⟨36825644660898162577866097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49100859547864216770488129 36825644660898162577866097)
    ·
      refine ⟨27619233495673621933399573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36825644660898162577866097 27619233495673621933399573)
      ·
        refine ⟨1294651570109701028128105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27619233495673621933399573 1294651570109701028128105)
        ·
          refine ⟨970988677582275771096079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294651570109701028128105 970988677582275771096079)
          ·
            refine ⟨1456483016373413656644119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 970988677582275771096079 1456483016373413656644119)
            ·
              refine ⟨2184724524560120484966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456483016373413656644119 2184724524560120484966179)
              ·
                refine ⟨3277086786840180727449269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2184724524560120484966179 3277086786840180727449269)
                ·
                  refine ⟨307226886266266943198369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3277086786840180727449269 307226886266266943198369)
                  ·
                    rfl

theorem cell21_1346225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_1346225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346225 prefixEnd_1346225 := by exact prefixLift 1346225
  have htrace : WordTrace (prefixWord ++ tailWord_1346225) baseStart_1346225 baseEnd_1346225 := by
    simpa [prefixWord, tailWord_1346225, baseEnd_1346225] using wordTrace_append hprefix tailTrace_1346225
  have hstable : (prefixWord ++ tailWord_1346225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346225).length < 2 ^ (prefixWord ++ tailWord_1346225).sum := by decide
  have hdescent : baseEnd_1346225 < baseStart_1346225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346312 : List Nat := [2, 1, 3, 2, 2, 3, 3, 5]
def baseStart_1346312 : Nat := 118140960795 + 1346312 * 2 ^ 59
def prefixEnd_1346312 : Nat := 4983230072969 + 3 ^ 40 * 1346312 * 2
def baseEnd_1346312 : Nat := 102415580283858041749397

theorem tailTrace_1346312 : CollatzResearch.WordTrace tailWord_1346312 prefixEnd_1346312 102415580283858041749397 := by
  unfold tailWord_1346312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24552016349274515314452595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32736021799032687085936793 24552016349274515314452595)
  ·
    refine ⟨36828024523911772971678893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24552016349274515314452595 36828024523911772971678893)
    ·
      refine ⟨13810509196466914864379585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36828024523911772971678893 13810509196466914864379585)
      ·
        refine ⟨10357881897350186148284689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13810509196466914864379585 10357881897350186148284689)
        ·
          refine ⟨7768411423012639611213517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10357881897350186148284689 7768411423012639611213517)
          ·
            refine ⟨2913154283629739854205069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7768411423012639611213517 2913154283629739854205069)
            ·
              refine ⟨1092432856361152445326901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2913154283629739854205069 1092432856361152445326901)
              ·
                refine ⟨102415580283858041749397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1092432856361152445326901 102415580283858041749397)
                ·
                  rfl

theorem cell21_1346312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 3, 5].length) (baseStart_1346312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346312 prefixEnd_1346312 := by exact prefixLift 1346312
  have htrace : WordTrace (prefixWord ++ tailWord_1346312) baseStart_1346312 baseEnd_1346312 := by
    simpa [prefixWord, tailWord_1346312, baseEnd_1346312] using wordTrace_append hprefix tailTrace_1346312
  have hstable : (prefixWord ++ tailWord_1346312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346312).length < 2 ^ (prefixWord ++ tailWord_1346312).sum := by decide
  have hdescent : baseEnd_1346312 < baseStart_1346312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346388 : List Nat := [2, 4, 1, 1, 4, 2, 7]
def baseStart_1346388 : Nat := 118140960795 + 1346388 * 2 ^ 59
def prefixEnd_1346388 : Nat := 4983230072969 + 3 ^ 40 * 1346388 * 2
def baseEnd_1346388 : Nat := 34140453898557209109041

theorem tailTrace_1346388 : CollatzResearch.WordTrace tailWord_1346388 prefixEnd_1346388 34140453898557209109041 := by
  unfold tailWord_1346388
  simp only [CollatzResearch.WordTrace]
  refine ⟨24553402323136847804335909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32737869764182463739114545 24553402323136847804335909)
  ·
    refine ⟨4603762935588158963312983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24553402323136847804335909 4603762935588158963312983)
    ·
      refine ⟨6905644403382238444969475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4603762935588158963312983 6905644403382238444969475)
      ·
        refine ⟨10358466605073357667454213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6905644403382238444969475 10358466605073357667454213)
        ·
          refine ⟨1942212488451254562647665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10358466605073357667454213 1942212488451254562647665)
          ·
            refine ⟨1456659366338440921985749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942212488451254562647665 1456659366338440921985749)
            ·
              refine ⟨34140453898557209109041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1456659366338440921985749 34140453898557209109041)
              ·
                rfl

theorem cell21_1346388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 7].length) (baseStart_1346388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346388 prefixEnd_1346388 := by exact prefixLift 1346388
  have htrace : WordTrace (prefixWord ++ tailWord_1346388) baseStart_1346388 baseEnd_1346388 := by
    simpa [prefixWord, tailWord_1346388, baseEnd_1346388] using wordTrace_append hprefix tailTrace_1346388
  have hstable : (prefixWord ++ tailWord_1346388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346388).length < 2 ^ (prefixWord ++ tailWord_1346388).sum := by decide
  have hdescent : baseEnd_1346388 < baseStart_1346388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346546 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 3]
def baseStart_1346546 : Nat := 118140960795 + 1346546 * 2 ^ 59
def prefixEnd_1346546 : Nat := 4983230072969 + 3 ^ 40 * 1346546 * 2
def baseEnd_1346546 : Nat := 307300142839641718347713

theorem tailTrace_1346546 : CollatzResearch.WordTrace tailWord_1346546 prefixEnd_1346546 307300142839641718347713 := by
  unfold tailWord_1346546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12278141844925322148230873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32741711586467525728615661 12278141844925322148230873)
  ·
    refine ⟨9208606383693991611173155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12278141844925322148230873 9208606383693991611173155)
    ·
      refine ⟨13812909575540987416759733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9208606383693991611173155 13812909575540987416759733)
      ·
        refine ⟨1294960272706967570321225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13812909575540987416759733 1294960272706967570321225)
        ·
          refine ⟨971220204530225677740919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1294960272706967570321225 971220204530225677740919)
          ·
            refine ⟨1456830306795338516611379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971220204530225677740919 1456830306795338516611379)
            ·
              refine ⟨2185245460193007774917069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1456830306795338516611379 2185245460193007774917069)
              ·
                refine ⟨819467047572377915593901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2185245460193007774917069 819467047572377915593901)
                ·
                  refine ⟨307300142839641718347713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819467047572377915593901 307300142839641718347713)
                  ·
                    rfl

theorem cell21_1346546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_1346546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346546 prefixEnd_1346546 := by exact prefixLift 1346546
  have htrace : WordTrace (prefixWord ++ tailWord_1346546) baseStart_1346546 baseEnd_1346546 := by
    simpa [prefixWord, tailWord_1346546, baseEnd_1346546] using wordTrace_append hprefix tailTrace_1346546
  have hstable : (prefixWord ++ tailWord_1346546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346546).length < 2 ^ (prefixWord ++ tailWord_1346546).sum := by decide
  have hdescent : baseEnd_1346546 < baseStart_1346546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346568 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1346568 : Nat := 118140960795 + 1346568 * 2 ^ 59
def prefixEnd_1346568 : Nat := 4983230072969 + 3 ^ 40 * 1346568 * 2
def baseEnd_1346568 : Nat := 307305163539374568981001

theorem tailTrace_1346568 : CollatzResearch.WordTrace tailWord_1346568 prefixEnd_1346568 307305163539374568981001 := by
  unfold tailWord_1346568
  simp only [CollatzResearch.WordTrace]
  refine ⟨24556684892810793175112179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32742246523747724233482905 24556684892810793175112179)
  ·
    refine ⟨36835027339216189762668269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24556684892810793175112179 36835027339216189762668269)
    ·
      refine ⟨13813135252206071161000601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36835027339216189762668269 13813135252206071161000601)
      ·
        refine ⟨10359851439154553370750451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13813135252206071161000601 10359851439154553370750451)
        ·
          refine ⟨15539777158731830056125677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10359851439154553370750451 15539777158731830056125677)
          ·
            refine ⟨5827416434524436271047129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15539777158731830056125677 5827416434524436271047129)
            ·
              refine ⟨4370562325893327203285347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5827416434524436271047129 4370562325893327203285347)
              ·
                refine ⟨6555843488839990804928021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4370562325893327203285347 6555843488839990804928021)
                ·
                  refine ⟨307305163539374568981001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6555843488839990804928021 307305163539374568981001)
                  ·
                    rfl

theorem cell21_1346568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1346568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346568 prefixEnd_1346568 := by exact prefixLift 1346568
  have htrace : WordTrace (prefixWord ++ tailWord_1346568) baseStart_1346568 baseEnd_1346568 := by
    simpa [prefixWord, tailWord_1346568, baseEnd_1346568] using wordTrace_append hprefix tailTrace_1346568
  have hstable : (prefixWord ++ tailWord_1346568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346568).length < 2 ^ (prefixWord ++ tailWord_1346568).sum := by decide
  have hdescent : baseEnd_1346568 < baseStart_1346568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346585 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 4]
def baseStart_1346585 : Nat := 118140960795 + 1346585 * 2 ^ 59
def prefixEnd_1346585 : Nat := 4983230072969 + 3 ^ 40 * 1346585 * 2
def baseEnd_1346585 : Nat := 307309043170986317197633

theorem tailTrace_1346585 : CollatzResearch.WordTrace tailWord_1346585 prefixEnd_1346585 307309043170986317197633 := by
  unfold tailWord_1346585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49113989826559998253593209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32742659884373332169062139 49113989826559998253593209)
  ·
    refine ⟨36835492369919998690194907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49113989826559998253593209 36835492369919998690194907)
    ·
      refine ⟨55253238554879998035292361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36835492369919998690194907 55253238554879998035292361)
      ·
        refine ⟨41439928916159998526469271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55253238554879998035292361 41439928916159998526469271)
        ·
          refine ⟨62159893374239997789703907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41439928916159998526469271 62159893374239997789703907)
          ·
            refine ⟨93239840061359996684555861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62159893374239997789703907 93239840061359996684555861)
            ·
              refine ⟨1092654375719062461147139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 93239840061359996684555861 1092654375719062461147139)
              ·
                refine ⟨1638981563578593691720709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1092654375719062461147139 1638981563578593691720709)
                ·
                  refine ⟨307309043170986317197633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1638981563578593691720709 307309043170986317197633)
                  ·
                    rfl

theorem cell21_1346585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_1346585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346585 prefixEnd_1346585 := by exact prefixLift 1346585
  have htrace : WordTrace (prefixWord ++ tailWord_1346585) baseStart_1346585 baseEnd_1346585 := by
    simpa [prefixWord, tailWord_1346585, baseEnd_1346585] using wordTrace_append hprefix tailTrace_1346585
  have hstable : (prefixWord ++ tailWord_1346585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346585).length < 2 ^ (prefixWord ++ tailWord_1346585).sum := by decide
  have hdescent : baseEnd_1346585 < baseStart_1346585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346706 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_1346706 : Nat := 118140960795 + 1346706 * 2 ^ 59
def prefixEnd_1346706 : Nat := 4983230072969 + 3 ^ 40 * 1346706 * 2
def baseEnd_1346706 : Nat := 307336657019516995680719

theorem tailTrace_1346706 : CollatzResearch.WordTrace tailWord_1346706 prefixEnd_1346706 307336657019516995680719 := by
  unfold tailWord_1346706
  simp only [CollatzResearch.WordTrace]
  refine ⟨12279600764780408979686993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32745602039414423945831981 12279600764780408979686993)
  ·
    refine ⟨9209700573585306734765245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12279600764780408979686993 9209700573585306734765245)
    ·
      refine ⟨3453637715094490025536967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9209700573585306734765245 3453637715094490025536967)
      ·
        refine ⟨5180456572641735038305451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3453637715094490025536967 5180456572641735038305451)
        ·
          refine ⟨7770684858962602557458177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5180456572641735038305451 7770684858962602557458177)
          ·
            refine ⟨5828013644221951918093633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7770684858962602557458177 5828013644221951918093633)
            ·
              refine ⟨4371010233166463938570225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5828013644221951918093633 4371010233166463938570225)
              ·
                refine ⟨3278257674874847953927669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371010233166463938570225 3278257674874847953927669)
                ·
                  refine ⟨307336657019516995680719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278257674874847953927669 307336657019516995680719)
                  ·
                    rfl

theorem cell21_1346706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_1346706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346706 prefixEnd_1346706 := by exact prefixLift 1346706
  have htrace : WordTrace (prefixWord ++ tailWord_1346706) baseStart_1346706 baseEnd_1346706 := by
    simpa [prefixWord, tailWord_1346706, baseEnd_1346706] using wordTrace_append hprefix tailTrace_1346706
  have hstable : (prefixWord ++ tailWord_1346706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346706).length < 2 ^ (prefixWord ++ tailWord_1346706).sum := by decide
  have hdescent : baseEnd_1346706 < baseStart_1346706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346796 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1346796 : Nat := 118140960795 + 1346796 * 2 ^ 59
def prefixEnd_1346796 : Nat := 4983230072969 + 3 ^ 40 * 1346796 * 2
def baseEnd_1346796 : Nat := 307357196245696839180535

theorem tailTrace_1346796 : CollatzResearch.WordTrace tailWord_1346796 prefixEnd_1346796 307357196245696839180535 := by
  unfold tailWord_1346796
  simp only [CollatzResearch.WordTrace]
  refine ⟨24560842814397790644762121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32747790419197054193016161 24560842814397790644762121)
  ·
    refine ⟨18420632110798342983571591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24560842814397790644762121 18420632110798342983571591)
    ·
      refine ⟨27630948166197514475357387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18420632110798342983571591 27630948166197514475357387)
      ·
        refine ⟨41446422249296271713036081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27630948166197514475357387 41446422249296271713036081)
        ·
          refine ⟨31084816686972203784777061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41446422249296271713036081 31084816686972203784777061)
          ·
            refine ⟨5828403128807288209645699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31084816686972203784777061 5828403128807288209645699)
            ·
              refine ⟨8742604693210932314468549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828403128807288209645699 8742604693210932314468549)
              ·
                refine ⟨1639238379977049808962853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8742604693210932314468549 1639238379977049808962853)
                ·
                  refine ⟨307357196245696839180535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639238379977049808962853 307357196245696839180535)
                  ·
                    rfl

theorem cell21_1346796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1346796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346796 prefixEnd_1346796 := by exact prefixLift 1346796
  have htrace : WordTrace (prefixWord ++ tailWord_1346796) baseStart_1346796 baseEnd_1346796 := by
    simpa [prefixWord, tailWord_1346796, baseEnd_1346796] using wordTrace_append hprefix tailTrace_1346796
  have hstable : (prefixWord ++ tailWord_1346796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346796).length < 2 ^ (prefixWord ++ tailWord_1346796).sum := by decide
  have hdescent : baseEnd_1346796 < baseStart_1346796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346799 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 3]
def baseStart_1346799 : Nat := 118140960795 + 1346799 * 2 ^ 59
def prefixEnd_1346799 : Nat := 4983230072969 + 3 ^ 40 * 1346799 * 2
def baseEnd_1346799 : Nat := 307357880886569500630529

theorem tailTrace_1346799 : CollatzResearch.WordTrace tailWord_1346799 prefixEnd_1346799 307357880886569500630529 := by
  unfold tailWord_1346799
  simp only [CollatzResearch.WordTrace]
  refine ⟨49121795047784712801883451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32747863365189808534588967 49121795047784712801883451)
  ·
    refine ⟨73682692571677069202825177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49121795047784712801883451 73682692571677069202825177)
    ·
      refine ⟨55262019428757801902118883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73682692571677069202825177 55262019428757801902118883)
      ·
        refine ⟨82893029143136702853178325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55262019428757801902118883 82893029143136702853178325)
        ·
          refine ⟨1942805370542266473121367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 82893029143136702853178325 1942805370542266473121367)
          ·
            refine ⟨2914208055813399709682051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1942805370542266473121367 2914208055813399709682051)
            ·
              refine ⟨4371312083720099564523077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2914208055813399709682051 4371312083720099564523077)
              ·
                refine ⟨819621015697518668348077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4371312083720099564523077 819621015697518668348077)
                ·
                  refine ⟨307357880886569500630529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819621015697518668348077 307357880886569500630529)
                  ·
                    rfl

theorem cell21_1346799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 3].length) (baseStart_1346799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346799 prefixEnd_1346799 := by exact prefixLift 1346799
  have htrace : WordTrace (prefixWord ++ tailWord_1346799) baseStart_1346799 baseEnd_1346799 := by
    simpa [prefixWord, tailWord_1346799, baseEnd_1346799] using wordTrace_append hprefix tailTrace_1346799
  have hstable : (prefixWord ++ tailWord_1346799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346799).length < 2 ^ (prefixWord ++ tailWord_1346799).sum := by decide
  have hdescent : baseEnd_1346799 < baseStart_1346799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346827 : List Nat := [1, 1, 1, 1, 5, 4, 3, 5]
def baseStart_1346827 : Nat := 118140960795 + 1346827 * 2 ^ 59
def prefixEnd_1346827 : Nat := 4983230072969 + 3 ^ 40 * 1346827 * 2
def baseEnd_1346827 : Nat := 102454756956015891387935

theorem tailTrace_1346827 : CollatzResearch.WordTrace tailWord_1346827 prefixEnd_1346827 102454756956015891387935 := by
  unfold tailWord_1346827
  simp only [CollatzResearch.WordTrace]
  refine ⟨49122816291683273583902735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32748544194455515722601823 49122816291683273583902735)
  ·
    refine ⟨73684224437524910375854103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49122816291683273583902735 73684224437524910375854103)
    ·
      refine ⟨110526336656287365563781155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73684224437524910375854103 110526336656287365563781155)
      ·
        refine ⟨165789504984431048345671733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110526336656287365563781155 165789504984431048345671733)
        ·
          refine ⟨15542766092290410782406725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 165789504984431048345671733 15542766092290410782406725)
          ·
            refine ⟨2914268642304452021701261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15542766092290410782406725 2914268642304452021701261)
            ·
              refine ⟨1092850740864169508137973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2914268642304452021701261 1092850740864169508137973)
              ·
                refine ⟨102454756956015891387935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1092850740864169508137973 102454756956015891387935)
                ·
                  rfl

theorem cell21_1346827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 3, 5].length) (baseStart_1346827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346827 prefixEnd_1346827 := by exact prefixLift 1346827
  have htrace : WordTrace (prefixWord ++ tailWord_1346827) baseStart_1346827 baseEnd_1346827 := by
    simpa [prefixWord, tailWord_1346827, baseEnd_1346827] using wordTrace_append hprefix tailTrace_1346827
  have hstable : (prefixWord ++ tailWord_1346827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346827).length < 2 ^ (prefixWord ++ tailWord_1346827).sum := by decide
  have hdescent : baseEnd_1346827 < baseStart_1346827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346858 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 5]
def baseStart_1346858 : Nat := 118140960795 + 1346858 * 2 ^ 59
def prefixEnd_1346858 : Nat := 4983230072969 + 3 ^ 40 * 1346858 * 2
def baseEnd_1346858 : Nat := 307371345490398509147075

theorem tailTrace_1346858 : CollatzResearch.WordTrace tailWord_1346858 prefixEnd_1346858 307371345490398509147075 := by
  unfold tailWord_1346858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12280986738642741469570307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32749297969713977252187485 12280986738642741469570307)
  ·
    refine ⟨18421480107964112204355461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12280986738642741469570307 18421480107964112204355461)
    ·
      refine ⟨3454027520243271038316649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18421480107964112204355461 3454027520243271038316649)
      ·
        refine ⟨2590520640182453278737487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454027520243271038316649 2590520640182453278737487)
        ·
          refine ⟨3885780960273679918106231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2590520640182453278737487 3885780960273679918106231)
          ·
            refine ⟨5828671440410519877159347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3885780960273679918106231 5828671440410519877159347)
            ·
              refine ⟨8743007160615779815739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5828671440410519877159347 8743007160615779815739021)
              ·
                refine ⟨3278627685230917430902133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8743007160615779815739021 3278627685230917430902133)
                ·
                  refine ⟨307371345490398509147075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278627685230917430902133 307371345490398509147075)
                  ·
                    rfl

theorem cell21_1346858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_1346858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346858 prefixEnd_1346858 := by exact prefixLift 1346858
  have htrace : WordTrace (prefixWord ++ tailWord_1346858) baseStart_1346858 baseEnd_1346858 := by
    simpa [prefixWord, tailWord_1346858, baseEnd_1346858] using wordTrace_append hprefix tailTrace_1346858
  have hstable : (prefixWord ++ tailWord_1346858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346858).length < 2 ^ (prefixWord ++ tailWord_1346858).sum := by decide
  have hdescent : baseEnd_1346858 < baseStart_1346858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346909 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1346909 : Nat := 118140960795 + 1346909 * 2 ^ 59
def prefixEnd_1346909 : Nat := 4983230072969 + 3 ^ 40 * 1346909 * 2
def baseEnd_1346909 : Nat := 307382984385233753796971

theorem tailTrace_1346909 : CollatzResearch.WordTrace tailWord_1346909 prefixEnd_1346909 307382984385233753796971 := by
  unfold tailWord_1346909
  simp only [CollatzResearch.WordTrace]
  refine ⟨49125807077386201588387781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32750538051590801058925187 49125807077386201588387781)
  ·
    refine ⟨9211088827009912797822709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49125807077386201588387781 9211088827009912797822709)
    ·
      refine ⟨863539577532179324795879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9211088827009912797822709 863539577532179324795879)
      ·
        refine ⟨1295309366298268987193819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863539577532179324795879 1295309366298268987193819)
        ·
          refine ⟨1942964049447403480790729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295309366298268987193819 1942964049447403480790729)
          ·
            refine ⟨1457223037085552610593047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1942964049447403480790729 1457223037085552610593047)
            ·
              refine ⟨2185834555628328915889571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457223037085552610593047 2185834555628328915889571)
              ·
                refine ⟨3278751833442493373834357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2185834555628328915889571 3278751833442493373834357)
                ·
                  refine ⟨307382984385233753796971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278751833442493373834357 307382984385233753796971)
                  ·
                    rfl

theorem cell21_1346909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1346909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346909 prefixEnd_1346909 := by exact prefixLift 1346909
  have htrace : WordTrace (prefixWord ++ tailWord_1346909) baseStart_1346909 baseEnd_1346909 := by
    simpa [prefixWord, tailWord_1346909, baseEnd_1346909] using wordTrace_append hprefix tailTrace_1346909
  have hstable : (prefixWord ++ tailWord_1346909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346909).length < 2 ^ (prefixWord ++ tailWord_1346909).sum := by decide
  have hdescent : baseEnd_1346909 < baseStart_1346909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1346993 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 5]
def baseStart_1346993 : Nat := 118140960795 + 1346993 * 2 ^ 59
def prefixEnd_1346993 : Nat := 4983230072969 + 3 ^ 40 * 1346993 * 2
def baseEnd_1346993 : Nat := 307402154329668274396799

theorem tailTrace_1346993 : CollatzResearch.WordTrace tailWord_1346993 prefixEnd_1346993 307402154329668274396799 := by
  unfold tailWord_1346993
  simp only [CollatzResearch.WordTrace]
  refine ⟨49128870809081883934445633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32752580539387922622963755 49128870809081883934445633)
  ·
    refine ⟨36846653106811412950834225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49128870809081883934445633 36846653106811412950834225)
    ·
      refine ⟨27634989830108559713125669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36846653106811412950834225 27634989830108559713125669)
      ·
        refine ⟨5181560593145354946211063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27634989830108559713125669 5181560593145354946211063)
        ·
          refine ⟨7772340889718032419316595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5181560593145354946211063 7772340889718032419316595)
          ·
            refine ⟨11658511334577048628974893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772340889718032419316595 11658511334577048628974893)
            ·
              refine ⟨4371941750466393235865585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11658511334577048628974893 4371941750466393235865585)
              ·
                refine ⟨3278956312849794926899189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4371941750466393235865585 3278956312849794926899189)
                ·
                  refine ⟨307402154329668274396799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3278956312849794926899189 307402154329668274396799)
                  ·
                    rfl

theorem cell21_1346993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_1346993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1346993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1346993 prefixEnd_1346993 := by exact prefixLift 1346993
  have htrace : WordTrace (prefixWord ++ tailWord_1346993) baseStart_1346993 baseEnd_1346993 := by
    simpa [prefixWord, tailWord_1346993, baseEnd_1346993] using wordTrace_append hprefix tailTrace_1346993
  have hstable : (prefixWord ++ tailWord_1346993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1346993).length < 2 ^ (prefixWord ++ tailWord_1346993).sum := by decide
  have hdescent : baseEnd_1346993 < baseStart_1346993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1346993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347041 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 4]
def baseStart_1347041 : Nat := 118140960795 + 1347041 * 2 ^ 59
def prefixEnd_1347041 : Nat := 4983230072969 + 3 ^ 40 * 1347041 * 2
def baseEnd_1347041 : Nat := 307413108583630857596701

theorem tailTrace_1347041 : CollatzResearch.WordTrace tailWord_1347041 prefixEnd_1347041 307413108583630857596701 := by
  unfold tailWord_1347041
  simp only [CollatzResearch.WordTrace]
  refine ⟨49130621512907988132192977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32753747675271992088128651 49130621512907988132192977)
  ·
    refine ⟨36847966134680991099144733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49130621512907988132192977 36847966134680991099144733)
    ·
      refine ⟨13817987300505371662179275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36847966134680991099144733 13817987300505371662179275)
      ·
        refine ⟨20726980950758057493268913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13817987300505371662179275 20726980950758057493268913)
        ·
          refine ⟨15545235713068543119951685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20726980950758057493268913 15545235713068543119951685)
          ·
            refine ⟨2914731696200351834990941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15545235713068543119951685 2914731696200351834990941)
            ·
              refine ⟨1093024386075131938121603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2914731696200351834990941 1093024386075131938121603)
              ·
                refine ⟨1639536579112697907182405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093024386075131938121603 1639536579112697907182405)
                ·
                  refine ⟨307413108583630857596701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639536579112697907182405 307413108583630857596701)
                  ·
                    rfl

theorem cell21_1347041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_1347041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347041 prefixEnd_1347041 := by exact prefixLift 1347041
  have htrace : WordTrace (prefixWord ++ tailWord_1347041) baseStart_1347041 baseEnd_1347041 := by
    simpa [prefixWord, tailWord_1347041, baseEnd_1347041] using wordTrace_append hprefix tailTrace_1347041
  have hstable : (prefixWord ++ tailWord_1347041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347041).length < 2 ^ (prefixWord ++ tailWord_1347041).sum := by decide
  have hdescent : baseEnd_1347041 < baseStart_1347041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347052 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1347052 : Nat := 118140960795 + 1347052 * 2 ^ 59
def prefixEnd_1347052 : Nat := 4983230072969 + 3 ^ 40 * 1347052 * 2
def baseEnd_1347052 : Nat := 307415618933497282913345

theorem tailTrace_1347052 : CollatzResearch.WordTrace tailWord_1347052 prefixEnd_1347052 307415618933497282913345 := by
  unfold tailWord_1347052
  simp only [CollatzResearch.WordTrace]
  refine ⟨24565511357934068505421705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32754015143912091340562273 24565511357934068505421705)
  ·
    refine ⟨18424133518450551379066279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24565511357934068505421705 18424133518450551379066279)
    ·
      refine ⟨27636200277675827068599419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18424133518450551379066279 27636200277675827068599419)
      ·
        refine ⟨41454300416513740602899129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27636200277675827068599419 41454300416513740602899129)
        ·
          refine ⟨31090725312385305452174347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41454300416513740602899129 31090725312385305452174347)
          ·
            refine ⟨46636087968577958178261521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31090725312385305452174347 46636087968577958178261521)
            ·
              refine ⟨34977065976433468633696141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46636087968577958178261521 34977065976433468633696141)
              ·
                refine ⟨13116399741162550737636053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34977065976433468633696141 13116399741162550737636053)
                ·
                  refine ⟨307415618933497282913345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13116399741162550737636053 307415618933497282913345)
                  ·
                    rfl

theorem cell21_1347052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1347052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347052 prefixEnd_1347052 := by exact prefixLift 1347052
  have htrace : WordTrace (prefixWord ++ tailWord_1347052) baseStart_1347052 baseEnd_1347052 := by
    simpa [prefixWord, tailWord_1347052, baseEnd_1347052] using wordTrace_append hprefix tailTrace_1347052
  have hstable : (prefixWord ++ tailWord_1347052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347052).length < 2 ^ (prefixWord ++ tailWord_1347052).sum := by decide
  have hdescent : baseEnd_1347052 < baseStart_1347052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347078 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1347078 : Nat := 118140960795 + 1347078 * 2 ^ 59
def prefixEnd_1347078 : Nat := 4983230072969 + 3 ^ 40 * 1347078 * 2
def baseEnd_1347078 : Nat := 307421552487727015479959

theorem tailTrace_1347078 : CollatzResearch.WordTrace tailWord_1347078 prefixEnd_1347078 307421552487727015479959 := by
  unfold tailWord_1347078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535374094180435732852809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32754647342515962300859925 1535374094180435732852809)
  ·
    refine ⟨1151530570635326799639607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1535374094180435732852809 1151530570635326799639607)
    ·
      refine ⟨1727295855952990199459411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151530570635326799639607 1727295855952990199459411)
      ·
        refine ⟨2590943783929485299189117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727295855952990199459411 2590943783929485299189117)
        ·
          refine ⟨971603918973556987195919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2590943783929485299189117 971603918973556987195919)
          ·
            refine ⟨1457405878460335480793879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971603918973556987195919 1457405878460335480793879)
            ·
              refine ⟨2186108817690503221190819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457405878460335480793879 2186108817690503221190819)
              ·
                refine ⟨3279163226535754831786229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2186108817690503221190819 3279163226535754831786229)
                ·
                  refine ⟨307421552487727015479959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3279163226535754831786229 307421552487727015479959)
                  ·
                    rfl

theorem cell21_1347078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1347078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347078 prefixEnd_1347078 := by exact prefixLift 1347078
  have htrace : WordTrace (prefixWord ++ tailWord_1347078) baseStart_1347078 baseEnd_1347078 := by
    simpa [prefixWord, tailWord_1347078, baseEnd_1347078] using wordTrace_append hprefix tailTrace_1347078
  have hstable : (prefixWord ++ tailWord_1347078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347078).length < 2 ^ (prefixWord ++ tailWord_1347078).sum := by decide
  have hdescent : baseEnd_1347078 < baseStart_1347078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347092 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1347092 : Nat := 118140960795 + 1347092 * 2 ^ 59
def prefixEnd_1347092 : Nat := 4983230072969 + 3 ^ 40 * 1347092 * 2
def baseEnd_1347092 : Nat := 307424747478466102246597

theorem tailTrace_1347092 : CollatzResearch.WordTrace tailWord_1347092 prefixEnd_1347092 307424747478466102246597 := by
  unfold tailWord_1347092
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566240817861611921149765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32754987757148815894866353 24566240817861611921149765)
  ·
    refine ⟨4606170153349052235215581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24566240817861611921149765 4606170153349052235215581)
    ·
      refine ⟨1727313807505894588205843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4606170153349052235215581 1727313807505894588205843)
      ·
        refine ⟨2590970711258841882308765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1727313807505894588205843 2590970711258841882308765)
        ·
          refine ⟨971614016722065705865787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2590970711258841882308765 971614016722065705865787)
          ·
            refine ⟨1457421025083098558798681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971614016722065705865787 1457421025083098558798681)
            ·
              refine ⟨1093065768812323919099011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457421025083098558798681 1093065768812323919099011)
              ·
                refine ⟨1639598653218485878648517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093065768812323919099011 1639598653218485878648517)
                ·
                  refine ⟨307424747478466102246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639598653218485878648517 307424747478466102246597)
                  ·
                    rfl

theorem cell21_1347092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1347092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347092 prefixEnd_1347092 := by exact prefixLift 1347092
  have htrace : WordTrace (prefixWord ++ tailWord_1347092) baseStart_1347092 baseEnd_1347092 := by
    simpa [prefixWord, tailWord_1347092, baseEnd_1347092] using wordTrace_append hprefix tailTrace_1347092
  have hstable : (prefixWord ++ tailWord_1347092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347092).length < 2 ^ (prefixWord ++ tailWord_1347092).sum := by decide
  have hdescent : baseEnd_1347092 < baseStart_1347092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347100 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1347100 : Nat := 118140960795 + 1347100 * 2 ^ 59
def prefixEnd_1347100 : Nat := 4983230072969 + 3 ^ 40 * 1347100 * 2
def baseEnd_1347100 : Nat := 307426573187459866113247

theorem tailTrace_1347100 : CollatzResearch.WordTrace tailWord_1347100 prefixEnd_1347100 307426573187459866113247 := by
  unfold tailWord_1347100
  simp only [CollatzResearch.WordTrace]
  refine ⟨24566386709847120604295377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32755182279796160805727169 24566386709847120604295377)
  ·
    refine ⟨18424790032385340453221533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24566386709847120604295377 18424790032385340453221533)
    ·
      refine ⟨6909296262144502669958075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18424790032385340453221533 6909296262144502669958075)
      ·
        refine ⟨10363944393216754004937113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6909296262144502669958075 10363944393216754004937113)
        ·
          refine ⟨7772958294912565503702835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10363944393216754004937113 7772958294912565503702835)
          ·
            refine ⟨11659437442368848255554253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7772958294912565503702835 11659437442368848255554253)
            ·
              refine ⟨4372289040888318095832845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11659437442368848255554253 4372289040888318095832845)
              ·
                refine ⟨1639608390333119285937317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4372289040888318095832845 1639608390333119285937317)
                ·
                  refine ⟨307426573187459866113247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1639608390333119285937317 307426573187459866113247)
                  ·
                    rfl

theorem cell21_1347100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1347100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347100 prefixEnd_1347100 := by exact prefixLift 1347100
  have htrace : WordTrace (prefixWord ++ tailWord_1347100) baseStart_1347100 baseEnd_1347100 := by
    simpa [prefixWord, tailWord_1347100, baseEnd_1347100] using wordTrace_append hprefix tailTrace_1347100
  have hstable : (prefixWord ++ tailWord_1347100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347100).length < 2 ^ (prefixWord ++ tailWord_1347100).sum := by decide
  have hdescent : baseEnd_1347100 < baseStart_1347100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347114 : List Nat := [3, 1, 4, 1, 1, 1, 1, 9]
def baseStart_1347114 : Nat := 118140960795 + 1347114 * 2 ^ 59
def prefixEnd_1347114 : Nat := 4983230072969 + 3 ^ 40 * 1347114 * 2
def baseEnd_1347114 : Nat := 102476589392732984293295

theorem tailTrace_1347114 : CollatzResearch.WordTrace tailWord_1347114 prefixEnd_1347114 102476589392732984293295 := by
  unfold tailWord_1347114
  simp only [CollatzResearch.WordTrace]
  refine ⟨12283321010410880399900099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32755522694429014399733597 12283321010410880399900099)
  ·
    refine ⟨18424981515616320599850149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12283321010410880399900099 18424981515616320599850149)
    ·
      refine ⟨3454684034178060112471903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18424981515616320599850149 3454684034178060112471903)
      ·
        refine ⟨5182026051267090168707855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3454684034178060112471903 5182026051267090168707855)
        ·
          refine ⟨7773039076900635253061783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182026051267090168707855 7773039076900635253061783)
          ·
            refine ⟨11659558615350952879592675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7773039076900635253061783 11659558615350952879592675)
            ·
              refine ⟨17489337923026429319389013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11659558615350952879592675 17489337923026429319389013)
              ·
                refine ⟨102476589392732984293295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17489337923026429319389013 102476589392732984293295)
                ·
                  rfl

theorem cell21_1347114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_1347114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347114 prefixEnd_1347114 := by exact prefixLift 1347114
  have htrace : WordTrace (prefixWord ++ tailWord_1347114) baseStart_1347114 baseEnd_1347114 := by
    simpa [prefixWord, tailWord_1347114, baseEnd_1347114] using wordTrace_append hprefix tailTrace_1347114
  have hstable : (prefixWord ++ tailWord_1347114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347114).length < 2 ^ (prefixWord ++ tailWord_1347114).sum := by decide
  have hdescent : baseEnd_1347114 < baseStart_1347114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347165 : List Nat := [1, 4, 4, 2, 1, 1, 3, 5]
def baseStart_1347165 : Nat := 118140960795 + 1347165 * 2 ^ 59
def prefixEnd_1347165 : Nat := 4983230072969 + 3 ^ 40 * 1347165 * 2
def baseEnd_1347165 : Nat := 102480469024344732509927

theorem tailTrace_1347165 : CollatzResearch.WordTrace tailWord_1347165 prefixEnd_1347165 102480469024344732509927 := by
  unfold tailWord_1347165
  simp only [CollatzResearch.WordTrace]
  refine ⟨49135144164458757309706949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32756762776305838206471299 49135144164458757309706949)
  ·
    refine ⟨9212839530836016995570053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49135144164458757309706949 9212839530836016995570053)
    ·
      refine ⟨1727407412031753186669385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9212839530836016995570053 1727407412031753186669385)
      ·
        refine ⟨1295555559023814890002039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727407412031753186669385 1295555559023814890002039)
        ·
          refine ⟨1943333338535722335003059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295555559023814890002039 1943333338535722335003059)
          ·
            refine ⟨2915000007803583502504589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943333338535722335003059 2915000007803583502504589)
            ·
              refine ⟨1093125002926343813439221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2915000007803583502504589 1093125002926343813439221)
              ·
                refine ⟨102480469024344732509927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093125002926343813439221 102480469024344732509927)
                ·
                  rfl

theorem cell21_1347165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 3, 5].length) (baseStart_1347165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347165 prefixEnd_1347165 := by exact prefixLift 1347165
  have htrace : WordTrace (prefixWord ++ tailWord_1347165) baseStart_1347165 baseEnd_1347165 := by
    simpa [prefixWord, tailWord_1347165, baseEnd_1347165] using wordTrace_append hprefix tailTrace_1347165
  have hstable : (prefixWord ++ tailWord_1347165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347165).length < 2 ^ (prefixWord ++ tailWord_1347165).sum := by decide
  have hdescent : baseEnd_1347165 < baseStart_1347165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347255 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 3]
def baseStart_1347255 : Nat := 118140960795 + 1347255 * 2 ^ 59
def prefixEnd_1347255 : Nat := 4983230072969 + 3 ^ 40 * 1347255 * 2
def baseEnd_1347255 : Nat := 307461946299214041029597

theorem tailTrace_1347255 : CollatzResearch.WordTrace tailWord_1347255 prefixEnd_1347255 307461946299214041029597 := by
  unfold tailWord_1347255
  simp only [CollatzResearch.WordTrace]
  refine ⟨49138426734132702680483219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32758951156088468453655479 49138426734132702680483219)
  ·
    refine ⟨73707640101199054020724829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49138426734132702680483219 73707640101199054020724829)
    ·
      refine ⟨27640365037949645257771811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73707640101199054020724829 27640365037949645257771811)
      ·
        refine ⟨41460547556924467886657717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27640365037949645257771811 41460547556924467886657717)
        ·
          refine ⟨3886926333461668864374161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41460547556924467886657717 3886926333461668864374161)
          ·
            refine ⟨2915194750096251648280621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3886926333461668864374161 2915194750096251648280621)
            ·
              refine ⟨1093198031286094368105233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2915194750096251648280621 1093198031286094368105233)
              ·
                refine ⟨819898523464570776078925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093198031286094368105233 819898523464570776078925)
                ·
                  refine ⟨307461946299214041029597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819898523464570776078925 307461946299214041029597)
                  ·
                    rfl

theorem cell21_1347255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 3].length) (baseStart_1347255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347255 prefixEnd_1347255 := by exact prefixLift 1347255
  have htrace : WordTrace (prefixWord ++ tailWord_1347255) baseStart_1347255 baseEnd_1347255 := by
    simpa [prefixWord, tailWord_1347255, baseEnd_1347255] using wordTrace_append hprefix tailTrace_1347255
  have hstable : (prefixWord ++ tailWord_1347255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347255).length < 2 ^ (prefixWord ++ tailWord_1347255).sum := by decide
  have hdescent : baseEnd_1347255 < baseStart_1347255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347314 : List Nat := [3, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1347314 : Nat := 118140960795 + 1347314 * 2 ^ 59
def prefixEnd_1347314 : Nat := 4983230072969 + 3 ^ 40 * 1347314 * 2
def baseEnd_1347314 : Nat := 307475410903043049546143

theorem tailTrace_1347314 : CollatzResearch.WordTrace tailWord_1347314 prefixEnd_1347314 307475410903043049546143 := by
  unfold tailWord_1347314
  simp only [CollatzResearch.WordTrace]
  refine ⟨12285144660229738939220249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32760385760612637171253997 12285144660229738939220249)
  ·
    refine ⟨9213858495172304204415187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12285144660229738939220249 9213858495172304204415187)
    ·
      refine ⟨13820787742758456306622781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9213858495172304204415187 13820787742758456306622781)
      ·
        refine ⟨5182795403534421114983543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13820787742758456306622781 5182795403534421114983543)
        ·
          refine ⟨7774193105301631672475315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5182795403534421114983543 7774193105301631672475315)
          ·
            refine ⟨11661289657952447508712973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7774193105301631672475315 11661289657952447508712973)
            ·
              refine ⟨4372983621732167815767365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11661289657952447508712973 4372983621732167815767365)
              ·
                refine ⟨819934429074781465456381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4372983621732167815767365 819934429074781465456381)
                ·
                  refine ⟨307475410903043049546143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819934429074781465456381 307475410903043049546143)
                  ·
                    rfl

theorem cell21_1347314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1347314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347314 prefixEnd_1347314 := by exact prefixLift 1347314
  have htrace : WordTrace (prefixWord ++ tailWord_1347314) baseStart_1347314 baseEnd_1347314 := by
    simpa [prefixWord, tailWord_1347314, baseEnd_1347314] using wordTrace_append hprefix tailTrace_1347314
  have hstable : (prefixWord ++ tailWord_1347314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347314).length < 2 ^ (prefixWord ++ tailWord_1347314).sum := by decide
  have hdescent : baseEnd_1347314 < baseStart_1347314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347325 : List Nat := [1, 4, 1, 1, 1, 1, 2, 10]
def baseStart_1347325 : Nat := 118140960795 + 1347325 * 2 ^ 59
def prefixEnd_1347325 : Nat := 4983230072969 + 3 ^ 40 * 1347325 * 2
def baseEnd_1347325 : Nat := 102492640417636491620929

theorem tailTrace_1347325 : CollatzResearch.WordTrace tailWord_1347325 prefixEnd_1347325 102492640417636491620929 := by
  unfold tailWord_1347325
  simp only [CollatzResearch.WordTrace]
  refine ⟨49140979843879104635531429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32760653229252736423687619 49140979843879104635531429)
  ·
    refine ⟨9213933720727332119162143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49140979843879104635531429 9213933720727332119162143)
    ·
      refine ⟨13820900581090998178743215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9213933720727332119162143 13820900581090998178743215)
      ·
        refine ⟨20731350871636497268114823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13820900581090998178743215 20731350871636497268114823)
        ·
          refine ⟨31097026307454745902172235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20731350871636497268114823 31097026307454745902172235)
          ·
            refine ⟨46645539461182118853258353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31097026307454745902172235 46645539461182118853258353)
            ·
              refine ⟨34984154595886589139943765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46645539461182118853258353 34984154595886589139943765)
              ·
                refine ⟨102492640417636491620929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34984154595886589139943765 102492640417636491620929)
                ·
                  rfl

theorem cell21_1347325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 10].length) (baseStart_1347325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347325 prefixEnd_1347325 := by exact prefixLift 1347325
  have htrace : WordTrace (prefixWord ++ tailWord_1347325) baseStart_1347325 baseEnd_1347325 := by
    simpa [prefixWord, tailWord_1347325, baseEnd_1347325] using wordTrace_append hprefix tailTrace_1347325
  have hstable : (prefixWord ++ tailWord_1347325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347325).length < 2 ^ (prefixWord ++ tailWord_1347325).sum := by decide
  have hdescent : baseEnd_1347325 < baseStart_1347325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347356 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1347356 : Nat := 118140960795 + 1347356 * 2 ^ 59
def prefixEnd_1347356 : Nat := 4983230072969 + 3 ^ 40 * 1347356 * 2
def baseEnd_1347356 : Nat := 307484995875260309846057

theorem tailTrace_1347356 : CollatzResearch.WordTrace tailWord_1347356 prefixEnd_1347356 307484995875260309846057 := by
  unfold tailWord_1347356
  simp only [CollatzResearch.WordTrace]
  refine ⟨24571055253383398464954961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32761407004511197953273281 24571055253383398464954961)
  ·
    refine ⟨18428291440037548848716221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24571055253383398464954961 18428291440037548848716221)
    ·
      refine ⟨6910609290014080818268583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18428291440037548848716221 6910609290014080818268583)
      ·
        refine ⟨10365913935021121227402875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6910609290014080818268583 10365913935021121227402875)
        ·
          refine ⟨15548870902531681841104313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10365913935021121227402875 15548870902531681841104313)
          ·
            refine ⟨11661653176898761380828235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15548870902531681841104313 11661653176898761380828235)
            ·
              refine ⟨17492479765348142071242353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11661653176898761380828235 17492479765348142071242353)
              ·
                refine ⟨13119359824011106553431765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17492479765348142071242353 13119359824011106553431765)
                ·
                  refine ⟨307484995875260309846057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13119359824011106553431765 307484995875260309846057)
                  ·
                    rfl

theorem cell21_1347356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1347356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347356 prefixEnd_1347356 := by exact prefixLift 1347356
  have htrace : WordTrace (prefixWord ++ tailWord_1347356) baseStart_1347356 baseEnd_1347356 := by
    simpa [prefixWord, tailWord_1347356, baseEnd_1347356] using wordTrace_append hprefix tailTrace_1347356
  have hstable : (prefixWord ++ tailWord_1347356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347356).length < 2 ^ (prefixWord ++ tailWord_1347356).sum := by decide
  have hdescent : baseEnd_1347356 < baseStart_1347356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347401 : List Nat := [1, 2, 1, 1, 2, 4, 3, 7]
def baseStart_1347401 : Nat := 118140960795 + 1347401 * 2 ^ 59
def prefixEnd_1347401 : Nat := 4983230072969 + 3 ^ 40 * 1347401 * 2
def baseEnd_1347401 : Nat := 102498421829450077198655

theorem tailTrace_1347401 : CollatzResearch.WordTrace tailWord_1347401 prefixEnd_1347401 102498421829450077198655 := by
  unfold tailWord_1347401
  simp only [CollatzResearch.WordTrace]
  refine ⟨49143751791603769615298057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32762501194402513076865371 49143751791603769615298057)
  ·
    refine ⟨36857813843702827211473543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49143751791603769615298057 36857813843702827211473543)
    ·
      refine ⟨55286720765554240817210315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36857813843702827211473543 55286720765554240817210315)
      ·
        refine ⟨82930081148331361225815473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55286720765554240817210315 82930081148331361225815473)
        ·
          refine ⟨62197560861248520919361605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82930081148331361225815473 62197560861248520919361605)
          ·
            refine ⟨11662042661484097672380301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62197560861248520919361605 11662042661484097672380301)
            ·
              refine ⟨4373265998056536627142613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11662042661484097672380301 4373265998056536627142613)
              ·
                refine ⟨102498421829450077198655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4373265998056536627142613 102498421829450077198655)
                ·
                  rfl

theorem cell21_1347401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 7].length) (baseStart_1347401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347401 prefixEnd_1347401 := by exact prefixLift 1347401
  have htrace : WordTrace (prefixWord ++ tailWord_1347401) baseStart_1347401 baseEnd_1347401 := by
    simpa [prefixWord, tailWord_1347401, baseEnd_1347401] using wordTrace_append hprefix tailTrace_1347401
  have hstable : (prefixWord ++ tailWord_1347401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347401).length < 2 ^ (prefixWord ++ tailWord_1347401).sum := by decide
  have hdescent : baseEnd_1347401 < baseStart_1347401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347438 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_1347438 : Nat := 118140960795 + 1347438 * 2 ^ 59
def prefixEnd_1347438 : Nat := 4983230072969 + 3 ^ 40 * 1347438 * 2
def baseEnd_1347438 : Nat := 307503709392446389479223

theorem tailTrace_1347438 : CollatzResearch.WordTrace tailWord_1347438 prefixEnd_1347438 307503709392446389479223 := by
  unfold tailWord_1347438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143137661558715616799371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32763400861646483289596645 6143137661558715616799371)
  ·
    refine ⟨9214706492338073425199057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6143137661558715616799371 9214706492338073425199057)
    ·
      refine ⟨6911029869253555068899293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9214706492338073425199057 6911029869253555068899293)
      ·
        refine ⟨2591636200970083150837235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6911029869253555068899293 2591636200970083150837235)
        ·
          refine ⟨3887454301455124726255853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591636200970083150837235 3887454301455124726255853)
          ·
            refine ⟨1457795363045671772345945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3887454301455124726255853 1457795363045671772345945)
            ·
              refine ⟨1093346522284253829259459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457795363045671772345945 1093346522284253829259459)
              ·
                refine ⟨1640019783426380743889189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093346522284253829259459 1640019783426380743889189)
                ·
                  refine ⟨307503709392446389479223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640019783426380743889189 307503709392446389479223)
                  ·
                    rfl

theorem cell21_1347438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_1347438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347438 prefixEnd_1347438 := by exact prefixLift 1347438
  have htrace : WordTrace (prefixWord ++ tailWord_1347438) baseStart_1347438 baseEnd_1347438 := by
    simpa [prefixWord, tailWord_1347438, baseEnd_1347438] using wordTrace_append hprefix tailTrace_1347438
  have hstable : (prefixWord ++ tailWord_1347438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347438).length < 2 ^ (prefixWord ++ tailWord_1347438).sum := by decide
  have hdescent : baseEnd_1347438 < baseStart_1347438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347556 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1347556 : Nat := 118140960795 + 1347556 * 2 ^ 59
def prefixEnd_1347556 : Nat := 4983230072969 + 3 ^ 40 * 1347556 * 2
def baseEnd_1347556 : Nat := 307530638600104406512315

theorem tailTrace_1347556 : CollatzResearch.WordTrace tailWord_1347556 prefixEnd_1347556 307530638600104406512315 := by
  unfold tailWord_1347556
  simp only [CollatzResearch.WordTrace]
  refine ⟨24574702553021115543595261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32766270070694820724793681 24574702553021115543595261)
  ·
    refine ⟨9215513457382918328848223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24574702553021115543595261 9215513457382918328848223)
    ·
      refine ⟨13823270186074377493272335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9215513457382918328848223 13823270186074377493272335)
      ·
        refine ⟨20734905279111566239908503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13823270186074377493272335 20734905279111566239908503)
        ·
          refine ⟨31102357918667349359862755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20734905279111566239908503 31102357918667349359862755)
          ·
            refine ⟨46653536878001024039794133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31102357918667349359862755 46653536878001024039794133)
            ·
              refine ⟨1093442270578149000932675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46653536878001024039794133 1093442270578149000932675)
              ·
                refine ⟨1640163405867223501399013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1093442270578149000932675 1640163405867223501399013)
                ·
                  refine ⟨307530638600104406512315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640163405867223501399013 307530638600104406512315)
                  ·
                    rfl

theorem cell21_1347556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1347556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347556 prefixEnd_1347556 := by exact prefixLift 1347556
  have htrace : WordTrace (prefixWord ++ tailWord_1347556) baseStart_1347556 baseEnd_1347556 := by
    simpa [prefixWord, tailWord_1347556, baseEnd_1347556] using wordTrace_append hprefix tailTrace_1347556
  have hstable : (prefixWord ++ tailWord_1347556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347556).length < 2 ^ (prefixWord ++ tailWord_1347556).sum := by decide
  have hdescent : baseEnd_1347556 < baseStart_1347556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347604 : List Nat := [2, 4, 3, 2, 1, 1, 2, 6]
def baseStart_1347604 : Nat := 118140960795 + 1347604 * 2 ^ 59
def prefixEnd_1347604 : Nat := 4983230072969 + 3 ^ 40 * 1347604 * 2
def baseEnd_1347604 : Nat := 102513864284688996570739

theorem tailTrace_1347604 : CollatzResearch.WordTrace tailWord_1347604 prefixEnd_1347604 102513864284688996570739 := by
  unfold tailWord_1347604
  simp only [CollatzResearch.WordTrace]
  refine ⟨24575577904934167642468933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32767437206578890189958577 24575577904934167642468933)
  ·
    refine ⟨4607920857175156432962925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24575577904934167642468933 4607920857175156432962925)
    ·
      refine ⟨1727970321440683662361097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4607920857175156432962925 1727970321440683662361097)
      ·
        refine ⟨1295977741080512746770823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727970321440683662361097 1295977741080512746770823)
        ·
          refine ⟨1943966611620769120156235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295977741080512746770823 1943966611620769120156235)
          ·
            refine ⟨2915949917431153680234353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943966611620769120156235 2915949917431153680234353)
            ·
              refine ⟨2186962438073365260175765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915949917431153680234353 2186962438073365260175765)
              ·
                refine ⟨102513864284688996570739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2186962438073365260175765 102513864284688996570739)
                ·
                  rfl

theorem cell21_1347604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_1347604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347604 prefixEnd_1347604 := by exact prefixLift 1347604
  have htrace : WordTrace (prefixWord ++ tailWord_1347604) baseStart_1347604 baseEnd_1347604 := by
    simpa [prefixWord, tailWord_1347604, baseEnd_1347604] using wordTrace_append hprefix tailTrace_1347604
  have hstable : (prefixWord ++ tailWord_1347604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347604).length < 2 ^ (prefixWord ++ tailWord_1347604).sum := by decide
  have hdescent : baseEnd_1347604 < baseStart_1347604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347615 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 4]
def baseStart_1347615 : Nat := 118140960795 + 1347615 * 2 ^ 59
def prefixEnd_1347615 : Nat := 4983230072969 + 3 ^ 40 * 1347615 * 2
def baseEnd_1347615 : Nat := 307544103203933415028861

theorem tailTrace_1347615 : CollatzResearch.WordTrace tailWord_1347615 prefixEnd_1347615 307544103203933415028861 := by
  unfold tailWord_1347615
  simp only [CollatzResearch.WordTrace]
  refine ⟨49151557012828484163588299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32767704675218989442392199 49151557012828484163588299)
  ·
    refine ⟨73727335519242726245382449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49151557012828484163588299 73727335519242726245382449)
    ·
      refine ⟨55295501639432044684036837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73727335519242726245382449 55295501639432044684036837)
      ·
        refine ⟨10367906557393508378256907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55295501639432044684036837 10367906557393508378256907)
        ·
          refine ⟨15551859836090262567385361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367906557393508378256907 15551859836090262567385361)
          ·
            refine ⟨11663894877067696925539021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15551859836090262567385361 11663894877067696925539021)
            ·
              refine ⟨4373960578900386347077133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11663894877067696925539021 4373960578900386347077133)
              ·
                refine ⟨1640235217087644880153925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4373960578900386347077133 1640235217087644880153925)
                ·
                  refine ⟨307544103203933415028861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640235217087644880153925 307544103203933415028861)
                  ·
                    rfl

theorem cell21_1347615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 4].length) (baseStart_1347615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347615 prefixEnd_1347615 := by exact prefixLift 1347615
  have htrace : WordTrace (prefixWord ++ tailWord_1347615) baseStart_1347615 baseEnd_1347615 := by
    simpa [prefixWord, tailWord_1347615, baseEnd_1347615] using wordTrace_append hprefix tailTrace_1347615
  have hstable : (prefixWord ++ tailWord_1347615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347615).length < 2 ^ (prefixWord ++ tailWord_1347615).sum := by decide
  have hdescent : baseEnd_1347615 < baseStart_1347615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347643 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 7]
def baseStart_1347643 : Nat := 118140960795 + 1347643 * 2 ^ 59
def prefixEnd_1347643 : Nat := 4983230072969 + 3 ^ 40 * 1347643 * 2
def baseEnd_1347643 : Nat := 307550493185411588562137

theorem tailTrace_1347643 : CollatzResearch.WordTrace tailWord_1347643 prefixEnd_1347643 307550493185411588562137 := by
  unfold tailWord_1347643
  simp only [CollatzResearch.WordTrace]
  refine ⟨49152578256727044945607583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32768385504484696630405055 49152578256727044945607583)
  ·
    refine ⟨73728867385090567418411375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49152578256727044945607583 73728867385090567418411375)
    ·
      refine ⟨110593301077635851127617063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73728867385090567418411375 110593301077635851127617063)
      ·
        refine ⟨165889951616453776691425595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110593301077635851127617063 165889951616453776691425595)
        ·
          refine ⟨248834927424680665037138393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165889951616453776691425595 248834927424680665037138393)
          ·
            refine ⟨186626195568510498777853795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248834927424680665037138393 186626195568510498777853795)
            ·
              refine ⟨279939293352765748166780693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186626195568510498777853795 279939293352765748166780693)
              ·
                refine ⟨13122154375910894445317845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 279939293352765748166780693 13122154375910894445317845)
                ·
                  refine ⟨307550493185411588562137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13122154375910894445317845 307550493185411588562137)
                  ·
                    rfl

theorem cell21_1347643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_1347643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347643 prefixEnd_1347643 := by exact prefixLift 1347643
  have htrace : WordTrace (prefixWord ++ tailWord_1347643) baseStart_1347643 baseEnd_1347643 := by
    simpa [prefixWord, tailWord_1347643, baseEnd_1347643] using wordTrace_append hprefix tailTrace_1347643
  have hstable : (prefixWord ++ tailWord_1347643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347643).length < 2 ^ (prefixWord ++ tailWord_1347643).sum := by decide
  have hdescent : baseEnd_1347643 < baseStart_1347643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347646 : List Nat := [4, 2, 1, 3, 2, 9]
def baseStart_1347646 : Nat := 118140960795 + 1347646 * 2 ^ 59
def prefixEnd_1347646 : Nat := 4983230072969 + 3 ^ 40 * 1347646 * 2
def baseEnd_1347646 : Nat := 11390784363936453704153

theorem tailTrace_1347646 : CollatzResearch.WordTrace tailWord_1347646 prefixEnd_1347646 11390784363936453704153 := by
  unfold tailWord_1347646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144085959464522057245849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32768458450477450971977861 6144085959464522057245849)
  ·
    refine ⟨4608064469598391542934387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6144085959464522057245849 4608064469598391542934387)
    ·
      refine ⟨6912096704397587314401581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4608064469598391542934387 6912096704397587314401581)
      ·
        refine ⟨2592036264149095242900593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6912096704397587314401581 2592036264149095242900593)
        ·
          refine ⟨1944027198111821432175445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592036264149095242900593 1944027198111821432175445)
          ·
            refine ⟨11390784363936453704153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1944027198111821432175445 11390784363936453704153)
            ·
              rfl

theorem cell21_1347646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 9].length) (baseStart_1347646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347646 prefixEnd_1347646 := by exact prefixLift 1347646
  have htrace : WordTrace (prefixWord ++ tailWord_1347646) baseStart_1347646 baseEnd_1347646 := by
    simpa [prefixWord, tailWord_1347646, baseEnd_1347646] using wordTrace_append hprefix tailTrace_1347646
  have hstable : (prefixWord ++ tailWord_1347646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347646).length < 2 ^ (prefixWord ++ tailWord_1347646).sum := by decide
  have hdescent : baseEnd_1347646 < baseStart_1347646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347677 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1347677 : Nat := 118140960795 + 1347677 * 2 ^ 59
def prefixEnd_1347677 : Nat := 4983230072969 + 3 ^ 40 * 1347677 * 2
def baseEnd_1347677 : Nat := 307558252448635084995401

theorem tailTrace_1347677 : CollatzResearch.WordTrace tailWord_1347677 prefixEnd_1347677 307558252448635084995401 := by
  unfold tailWord_1347677
  simp only [CollatzResearch.WordTrace]
  refine ⟨49153818338603868752345285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32769212225735912501563523 49153818338603868752345285)
  ·
    refine ⟨9216340938488225391064741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49153818338603868752345285 9216340938488225391064741)
    ·
      refine ⟨1728063925966542260824639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9216340938488225391064741 1728063925966542260824639)
      ·
        refine ⟨2592095888949813391236959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728063925966542260824639 2592095888949813391236959)
        ·
          refine ⟨3888143833424720086855439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2592095888949813391236959 3888143833424720086855439)
          ·
            refine ⟨5832215750137080130283159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3888143833424720086855439 5832215750137080130283159)
            ·
              refine ⟨8748323625205620195424739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5832215750137080130283159 8748323625205620195424739)
              ·
                refine ⟨13122485437808430293137109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8748323625205620195424739 13122485437808430293137109)
                ·
                  refine ⟨307558252448635084995401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13122485437808430293137109 307558252448635084995401)
                  ·
                    rfl

theorem cell21_1347677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1347677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347677 prefixEnd_1347677 := by exact prefixLift 1347677
  have htrace : WordTrace (prefixWord ++ tailWord_1347677) baseStart_1347677 baseEnd_1347677 := by
    simpa [prefixWord, tailWord_1347677, baseEnd_1347677] using wordTrace_append hprefix tailTrace_1347677
  have hstable : (prefixWord ++ tailWord_1347677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347677).length < 2 ^ (prefixWord ++ tailWord_1347677).sum := by decide
  have hdescent : baseEnd_1347677 < baseStart_1347677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347694 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_1347694 : Nat := 118140960795 + 1347694 * 2 ^ 59
def prefixEnd_1347694 : Nat := 4983230072969 + 3 ^ 40 * 1347694 * 2
def baseEnd_1347694 : Nat := 307562132080246833212033

theorem tailTrace_1347694 : CollatzResearch.WordTrace tailWord_1347694 prefixEnd_1347694 307562132080246833212033 := by
  unfold tailWord_1347694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6144304797442785081964267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32769625586361520437142757 6144304797442785081964267)
  ·
    refine ⟨9216457196164177622946401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6144304797442785081964267 9216457196164177622946401)
    ·
      refine ⟨6912342897123133217209801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9216457196164177622946401 6912342897123133217209801)
      ·
        refine ⟨5184257172842349912907351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6912342897123133217209801 5184257172842349912907351)
        ·
          refine ⟨7776385759263524869361027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5184257172842349912907351 7776385759263524869361027)
          ·
            refine ⟨11664578638895287304041541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7776385759263524869361027 11664578638895287304041541)
            ·
              refine ⟨2187108494792866369507789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11664578638895287304041541 2187108494792866369507789)
              ·
                refine ⟨820165685547324888565421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2187108494792866369507789 820165685547324888565421)
                ·
                  refine ⟨307562132080246833212033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820165685547324888565421 307562132080246833212033)
                  ·
                    rfl

theorem cell21_1347694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_1347694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347694 prefixEnd_1347694 := by exact prefixLift 1347694
  have htrace : WordTrace (prefixWord ++ tailWord_1347694) baseStart_1347694 baseEnd_1347694 := by
    simpa [prefixWord, tailWord_1347694, baseEnd_1347694] using wordTrace_append hprefix tailTrace_1347694
  have hstable : (prefixWord ++ tailWord_1347694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347694).length < 2 ^ (prefixWord ++ tailWord_1347694).sum := by decide
  have hdescent : baseEnd_1347694 < baseStart_1347694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347705 : List Nat := [1, 2, 1, 3, 4, 2, 8]
def baseStart_1347705 : Nat := 118140960795 + 1347705 * 2 ^ 59
def prefixEnd_1347705 : Nat := 4983230072969 + 3 ^ 40 * 1347705 * 2
def baseEnd_1347705 : Nat := 34173849158901473169853

theorem tailTrace_1347705 : CollatzResearch.WordTrace tailWord_1347705 prefixEnd_1347705 34173849158901473169853 := by
  unfold tailWord_1347705
  simp only [CollatzResearch.WordTrace]
  refine ⟨49154839582502429534364569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32769893055001619689576379 49154839582502429534364569)
  ·
    refine ⟨36866129686876822150773427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49154839582502429534364569 36866129686876822150773427)
    ·
      refine ⟨55299194530315233226160141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36866129686876822150773427 55299194530315233226160141)
      ·
        refine ⟨20737197948868212459810053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55299194530315233226160141 20737197948868212459810053)
        ·
          refine ⟨3888224615412789836214385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20737197948868212459810053 3888224615412789836214385)
          ·
            refine ⟨2916168461559592377160789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3888224615412789836214385 2916168461559592377160789)
            ·
              refine ⟨34173849158901473169853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2916168461559592377160789 34173849158901473169853)
              ·
                rfl

theorem cell21_1347705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 8].length) (baseStart_1347705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347705 prefixEnd_1347705 := by exact prefixLift 1347705
  have htrace : WordTrace (prefixWord ++ tailWord_1347705) baseStart_1347705 baseEnd_1347705 := by
    simpa [prefixWord, tailWord_1347705, baseEnd_1347705] using wordTrace_append hprefix tailTrace_1347705
  have hstable : (prefixWord ++ tailWord_1347705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347705).length < 2 ^ (prefixWord ++ tailWord_1347705).sum := by decide
  have hdescent : baseEnd_1347705 < baseStart_1347705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347708 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1347708 : Nat := 118140960795 + 1347708 * 2 ^ 59
def prefixEnd_1347708 : Nat := 4983230072969 + 3 ^ 40 * 1347708 * 2
def baseEnd_1347708 : Nat := 307565327070985919978671

theorem tailTrace_1347708 : CollatzResearch.WordTrace tailWord_1347708 prefixEnd_1347708 307565327070985919978671 := by
  unfold tailWord_1347708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24577474500745780523361889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32769966000994374031149185 24577474500745780523361889)
  ·
    refine ⟨18433105875559335392521417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24577474500745780523361889 18433105875559335392521417)
    ·
      refine ⟨13824829406669501544391063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18433105875559335392521417 13824829406669501544391063)
      ·
        refine ⟨20737244110004252316586595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13824829406669501544391063 20737244110004252316586595)
        ·
          refine ⟨31105866165006378474879893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20737244110004252316586595 31105866165006378474879893)
          ·
            refine ⟨1458087476484673991009995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31105866165006378474879893 1458087476484673991009995)
            ·
              refine ⟨2187131214727010986514993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458087476484673991009995 2187131214727010986514993)
              ·
                refine ⟨1640348411045258239886245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187131214727010986514993 1640348411045258239886245)
                ·
                  refine ⟨307565327070985919978671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640348411045258239886245 307565327070985919978671)
                  ·
                    rfl

theorem cell21_1347708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1347708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347708 prefixEnd_1347708 := by exact prefixLift 1347708
  have htrace : WordTrace (prefixWord ++ tailWord_1347708) baseStart_1347708 baseEnd_1347708 := by
    simpa [prefixWord, tailWord_1347708, baseEnd_1347708] using wordTrace_append hprefix tailTrace_1347708
  have hstable : (prefixWord ++ tailWord_1347708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347708).length < 2 ^ (prefixWord ++ tailWord_1347708).sum := by decide
  have hdescent : baseEnd_1347708 < baseStart_1347708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347877 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 4]
def baseStart_1347877 : Nat := 118140960795 + 1347877 * 2 ^ 59
def prefixEnd_1347877 : Nat := 4983230072969 + 3 ^ 40 * 1347877 * 2
def baseEnd_1347877 : Nat := 307603895173479181661659

theorem tailTrace_1347877 : CollatzResearch.WordTrace tailWord_1347877 prefixEnd_1347877 307603895173479181661659 := by
  unfold tailWord_1347877
  simp only [CollatzResearch.WordTrace]
  refine ⟨49161112937879302909625885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32774075291919535273083923 49161112937879302909625885)
  ·
    refine ⟨18435417351704738591109707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49161112937879302909625885 18435417351704738591109707)
    ·
      refine ⟨27653126027557107886664561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18435417351704738591109707 27653126027557107886664561)
      ·
        refine ⟨20739844520667830914998421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27653126027557107886664561 20739844520667830914998421)
        ·
          refine ⟨972180211906304574140551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20739844520667830914998421 972180211906304574140551)
          ·
            refine ⟨1458270317859456861210827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972180211906304574140551 1458270317859456861210827)
            ·
              refine ⟨2187405476789185291816241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458270317859456861210827 2187405476789185291816241)
              ·
                refine ⟨1640554107591888968862181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2187405476789185291816241 1640554107591888968862181)
                ·
                  refine ⟨307603895173479181661659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1640554107591888968862181 307603895173479181661659)
                  ·
                    rfl

theorem cell21_1347877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_1347877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347877 prefixEnd_1347877 := by exact prefixLift 1347877
  have htrace : WordTrace (prefixWord ++ tailWord_1347877) baseStart_1347877 baseEnd_1347877 := by
    simpa [prefixWord, tailWord_1347877, baseEnd_1347877] using wordTrace_append hprefix tailTrace_1347877
  have hstable : (prefixWord ++ tailWord_1347877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347877).length < 2 ^ (prefixWord ++ tailWord_1347877).sum := by decide
  have hdescent : baseEnd_1347877 < baseStart_1347877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347908 : List Nat := [2, 3, 4, 1, 2, 2, 2, 5]
def baseStart_1347908 : Nat := 118140960795 + 1347908 * 2 ^ 59
def prefixEnd_1347908 : Nat := 4983230072969 + 3 ^ 40 * 1347908 * 2
def baseEnd_1347908 : Nat := 102536989931943338881643

theorem tailTrace_1347908 : CollatzResearch.WordTrace tailWord_1347908 prefixEnd_1347908 102536989931943338881643 := by
  unfold tailWord_1347908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24581121800383497602002189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32774829067177996802669585 24581121800383497602002189)
  ·
    refine ⟨9217920675143811600750821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24581121800383497602002189 9217920675143811600750821)
    ·
      refine ⟨1728360126589464675140779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9217920675143811600750821 1728360126589464675140779)
      ·
        refine ⟨2592540189884197012711169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1728360126589464675140779 2592540189884197012711169)
        ·
          refine ⟨1944405142413147759533377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2592540189884197012711169 1944405142413147759533377)
          ·
            refine ⟨1458303856809860819650033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944405142413147759533377 1458303856809860819650033)
            ·
              refine ⟨1093727892607395614737525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458303856809860819650033 1093727892607395614737525)
              ·
                refine ⟨102536989931943338881643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1093727892607395614737525 102536989931943338881643)
                ·
                  rfl

theorem cell21_1347908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 5].length) (baseStart_1347908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347908 prefixEnd_1347908 := by exact prefixLift 1347908
  have htrace : WordTrace (prefixWord ++ tailWord_1347908) baseStart_1347908 baseEnd_1347908 := by
    simpa [prefixWord, tailWord_1347908, baseEnd_1347908] using wordTrace_append hprefix tailTrace_1347908
  have hstable : (prefixWord ++ tailWord_1347908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347908).length < 2 ^ (prefixWord ++ tailWord_1347908).sum := by decide
  have hdescent : baseEnd_1347908 < baseStart_1347908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1347990 : List Nat := [5, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1347990 : Nat := 118140960795 + 1347990 * 2 ^ 59
def prefixEnd_1347990 : Nat := 4983230072969 + 3 ^ 40 * 1347990 * 2
def baseEnd_1347990 : Nat := 307629683313016096278095

theorem tailTrace_1347990 : CollatzResearch.WordTrace tailWord_1347990 prefixEnd_1347990 307629683313016096278095 := by
  unfold tailWord_1347990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072827149154370200530589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32776822924313282138992949 3072827149154370200530589)
  ·
    refine ⟨1152310180932888825198971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3072827149154370200530589 1152310180932888825198971)
    ·
      refine ⟨1728465271399333237798457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152310180932888825198971 1728465271399333237798457)
      ·
        refine ⟨1296348953549499928348843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1728465271399333237798457 1296348953549499928348843)
        ·
          refine ⟨1944523430324249892523265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296348953549499928348843 1944523430324249892523265)
          ·
            refine ⟨1458392572743187419392449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1944523430324249892523265 1458392572743187419392449)
            ·
              refine ⟨1093794429557390564544337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1458392572743187419392449 1093794429557390564544337)
              ·
                refine ⟨820345822168042923408253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1093794429557390564544337 820345822168042923408253)
                ·
                  refine ⟨307629683313016096278095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820345822168042923408253 307629683313016096278095)
                  ·
                    rfl

theorem cell21_1347990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1347990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1347990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1347990 prefixEnd_1347990 := by exact prefixLift 1347990
  have htrace : WordTrace (prefixWord ++ tailWord_1347990) baseStart_1347990 baseEnd_1347990 := by
    simpa [prefixWord, tailWord_1347990, baseEnd_1347990] using wordTrace_append hprefix tailTrace_1347990
  have hstable : (prefixWord ++ tailWord_1347990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1347990).length < 2 ^ (prefixWord ++ tailWord_1347990).sum := by decide
  have hdescent : baseEnd_1347990 < baseStart_1347990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1347990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348023 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 7]
def baseStart_1348023 : Nat := 118140960795 + 1348023 * 2 ^ 59
def prefixEnd_1348023 : Nat := 4983230072969 + 3 ^ 40 * 1348023 * 2
def baseEnd_1348023 : Nat := 307637214362615372228027

theorem tailTrace_1348023 : CollatzResearch.WordTrace tailWord_1348023 prefixEnd_1348023 307637214362615372228027 := by
  unfold tailWord_1348023
  simp only [CollatzResearch.WordTrace]
  refine ⟨49166437995350369844440723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32777625330233579896293815 49166437995350369844440723)
  ·
    refine ⟨73749656993025554766661085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49166437995350369844440723 73749656993025554766661085)
    ·
      refine ⟨27656121372384583037497907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73749656993025554766661085 27656121372384583037497907)
      ·
        refine ⟨41484182058576874556246861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27656121372384583037497907 41484182058576874556246861)
        ·
          refine ⟨15556568271966327958592573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41484182058576874556246861 15556568271966327958592573)
          ·
            refine ⟨5833713101987372984472215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15556568271966327958592573 5833713101987372984472215)
            ·
              refine ⟨8750569652981059476708323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5833713101987372984472215 8750569652981059476708323)
              ·
                refine ⟨13125854479471589215062485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8750569652981059476708323 13125854479471589215062485)
                ·
                  refine ⟨307637214362615372228027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13125854479471589215062485 307637214362615372228027)
                  ·
                    rfl

theorem cell21_1348023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 7].length) (baseStart_1348023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348023 prefixEnd_1348023 := by exact prefixLift 1348023
  have htrace : WordTrace (prefixWord ++ tailWord_1348023) baseStart_1348023 baseEnd_1348023 := by
    simpa [prefixWord, tailWord_1348023, baseEnd_1348023] using wordTrace_append hprefix tailTrace_1348023
  have hstable : (prefixWord ++ tailWord_1348023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348023).length < 2 ^ (prefixWord ++ tailWord_1348023).sum := by decide
  have hdescent : baseEnd_1348023 < baseStart_1348023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348144 : List Nat := [2, 1, 1, 1, 2, 3, 4, 7]
def baseStart_1348144 : Nat := 118140960795 + 1348144 * 2 ^ 59
def prefixEnd_1348144 : Nat := 4983230072969 + 3 ^ 40 * 1348144 * 2
def baseEnd_1348144 : Nat := 102554942737048683570371

theorem tailTrace_1348144 : CollatzResearch.WordTrace tailWord_1348144 prefixEnd_1348144 102554942737048683570371 := by
  unfold tailWord_1348144
  simp only [CollatzResearch.WordTrace]
  refine ⟨24585425613956003754797743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32780567485274671673063657 24585425613956003754797743)
  ·
    refine ⟨36878138420934005632196615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24585425613956003754797743 36878138420934005632196615)
    ·
      refine ⟨55317207631401008448294923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36878138420934005632196615 55317207631401008448294923)
      ·
        refine ⟨82975811447101512672442385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55317207631401008448294923 82975811447101512672442385)
        ·
          refine ⟨62231858585326134504331789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82975811447101512672442385 62231858585326134504331789)
          ·
            refine ⟨23336946969497300439124421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62231858585326134504331789 23336946969497300439124421)
            ·
              refine ⟨4375677556780743832335829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23336946969497300439124421 4375677556780743832335829)
              ·
                refine ⟨102554942737048683570371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4375677556780743832335829 102554942737048683570371)
                ·
                  rfl

theorem cell21_1348144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_1348144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348144 prefixEnd_1348144 := by exact prefixLift 1348144
  have htrace : WordTrace (prefixWord ++ tailWord_1348144) baseStart_1348144 baseEnd_1348144 := by
    simpa [prefixWord, tailWord_1348144, baseEnd_1348144] using wordTrace_append hprefix tailTrace_1348144
  have hstable : (prefixWord ++ tailWord_1348144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348144).length < 2 ^ (prefixWord ++ tailWord_1348144).sum := by decide
  have hdescent : baseEnd_1348144 < baseStart_1348144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348265 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 6]
def baseStart_1348265 : Nat := 118140960795 + 1348265 * 2 ^ 59
def prefixEnd_1348265 : Nat := 4983230072969 + 3 ^ 40 * 1348265 * 2
def baseEnd_1348265 : Nat := 307692442059676729194199

theorem tailTrace_1348265 : CollatzResearch.WordTrace tailWord_1348265 prefixEnd_1348265 307692442059676729194199 := by
  unfold tailWord_1348265
  simp only [CollatzResearch.WordTrace]
  refine ⟨49175264460473645174750249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32783509640315763449833499 49175264460473645174750249)
  ·
    refine ⟨36881448345355233881062687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49175264460473645174750249 36881448345355233881062687)
    ·
      refine ⟨55322172518032850821594031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36881448345355233881062687 55322172518032850821594031)
      ·
        refine ⟨82983258777049276232391047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55322172518032850821594031 82983258777049276232391047)
        ·
          refine ⟨124474888165573914348586571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82983258777049276232391047 124474888165573914348586571)
          ·
            refine ⟨186712332248360871522879857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124474888165573914348586571 186712332248360871522879857)
            ·
              refine ⟨140034249186270653642159893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186712332248360871522879857 140034249186270653642159893)
              ·
                refine ⟨6564105430606436889476245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140034249186270653642159893 6564105430606436889476245)
                ·
                  refine ⟨307692442059676729194199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6564105430606436889476245 307692442059676729194199)
                  ·
                    rfl

theorem cell21_1348265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_1348265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348265 prefixEnd_1348265 := by exact prefixLift 1348265
  have htrace : WordTrace (prefixWord ++ tailWord_1348265) baseStart_1348265 baseEnd_1348265 := by
    simpa [prefixWord, tailWord_1348265, baseEnd_1348265] using wordTrace_append hprefix tailTrace_1348265
  have hstable : (prefixWord ++ tailWord_1348265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348265).length < 2 ^ (prefixWord ++ tailWord_1348265).sum := by decide
  have hdescent : baseEnd_1348265 < baseStart_1348265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348282 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1348282 : Nat := 118140960795 + 1348282 * 2 ^ 59
def prefixEnd_1348282 : Nat := 4983230072969 + 3 ^ 40 * 1348282 * 2
def baseEnd_1348282 : Nat := 307696321691288477410831

theorem tailTrace_1348282 : CollatzResearch.WordTrace tailWord_1348282 prefixEnd_1348282 307696321691288477410831 := by
  unfold tailWord_1348282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12293971125353014269529775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32783923000941371385412733 12293971125353014269529775)
  ·
    refine ⟨18440956688029521404294663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12293971125353014269529775 18440956688029521404294663)
    ·
      refine ⟨27661435032044282106441995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18440956688029521404294663 27661435032044282106441995)
      ·
        refine ⟨41492152548066423159662993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27661435032044282106441995 41492152548066423159662993)
        ·
          refine ⟨31119114411049817369747245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41492152548066423159662993 31119114411049817369747245)
          ·
            refine ⟨11669667904143681513655217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31119114411049817369747245 11669667904143681513655217)
            ·
              refine ⟨8752250928107761135241413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11669667904143681513655217 8752250928107761135241413)
              ·
                refine ⟨1641047049020205212857765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8752250928107761135241413 1641047049020205212857765)
                ·
                  refine ⟨307696321691288477410831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1641047049020205212857765 307696321691288477410831)
                  ·
                    rfl

theorem cell21_1348282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1348282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348282 prefixEnd_1348282 := by exact prefixLift 1348282
  have htrace : WordTrace (prefixWord ++ tailWord_1348282) baseStart_1348282 baseEnd_1348282 := by
    simpa [prefixWord, tailWord_1348282, baseEnd_1348282] using wordTrace_append hprefix tailTrace_1348282
  have hstable : (prefixWord ++ tailWord_1348282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348282).length < 2 ^ (prefixWord ++ tailWord_1348282).sum := by decide
  have hdescent : baseEnd_1348282 < baseStart_1348282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348296 : List Nat := [2, 1, 3, 1, 2, 3, 1, 8]
def baseStart_1348296 : Nat := 118140960795 + 1348296 * 2 ^ 59
def prefixEnd_1348296 : Nat := 4983230072969 + 3 ^ 40 * 1348296 * 2
def baseEnd_1348296 : Nat := 102566505560675854725823

theorem tailTrace_1348296 : CollatzResearch.WordTrace tailWord_1348296 prefixEnd_1348296 102566505560675854725823 := by
  unfold tailWord_1348296
  simp only [CollatzResearch.WordTrace]
  refine ⟨24588197561680668734564371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32784263415574224979419161 24588197561680668734564371)
  ·
    refine ⟨36882296342521003101846557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24588197561680668734564371 36882296342521003101846557)
    ·
      refine ⟨13830861128445376163192459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36882296342521003101846557 13830861128445376163192459)
      ·
        refine ⟨20746291692668064244788689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13830861128445376163192459 20746291692668064244788689)
        ·
          refine ⟨15559718769501048183591517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20746291692668064244788689 15559718769501048183591517)
          ·
            refine ⟨5834894538562893068846819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15559718769501048183591517 5834894538562893068846819)
            ·
              refine ⟨8752341807844339603270229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5834894538562893068846819 8752341807844339603270229)
              ·
                refine ⟨102566505560675854725823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8752341807844339603270229 102566505560675854725823)
                ·
                  rfl

theorem cell21_1348296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_1348296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348296 prefixEnd_1348296 := by exact prefixLift 1348296
  have htrace : WordTrace (prefixWord ++ tailWord_1348296) baseStart_1348296 baseEnd_1348296 := by
    simpa [prefixWord, tailWord_1348296, baseEnd_1348296] using wordTrace_append hprefix tailTrace_1348296
  have hstable : (prefixWord ++ tailWord_1348296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348296).length < 2 ^ (prefixWord ++ tailWord_1348296).sum := by decide
  have hdescent : baseEnd_1348296 < baseStart_1348296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348344 : List Nat := [2, 1, 2, 1, 1, 2, 5, 4, 3]
def baseStart_1348344 : Nat := 118140960795 + 1348344 * 2 ^ 59
def prefixEnd_1348344 : Nat := 4983230072969 + 3 ^ 40 * 1348344 * 2
def baseEnd_1348344 : Nat := 307710470935990147377371

theorem tailTrace_1348344 : CollatzResearch.WordTrace tailWord_1348344 prefixEnd_1348344 307710470935990147377371 := by
  unfold tailWord_1348344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24589072913593720833438043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32785430551458294444584057 24589072913593720833438043)
  ·
    refine ⟨36883609370390581250157065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24589072913593720833438043 36883609370390581250157065)
    ·
      refine ⟨27662707027792935937617799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36883609370390581250157065 27662707027792935937617799)
      ·
        refine ⟨41494060541689403906426699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27662707027792935937617799 41494060541689403906426699)
        ·
          refine ⟨62241090812534105859640049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41494060541689403906426699 62241090812534105859640049)
          ·
            refine ⟨46680818109400579394730037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62241090812534105859640049 46680818109400579394730037)
            ·
              refine ⟨4376326697756304318255941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46680818109400579394730037 4376326697756304318255941)
              ·
                refine ⟨820561255829307059672989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4376326697756304318255941 820561255829307059672989)
                ·
                  refine ⟨307710470935990147377371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820561255829307059672989 307710470935990147377371)
                  ·
                    rfl

theorem cell21_1348344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_1348344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348344 prefixEnd_1348344 := by exact prefixLift 1348344
  have htrace : WordTrace (prefixWord ++ tailWord_1348344) baseStart_1348344 baseEnd_1348344 := by
    simpa [prefixWord, tailWord_1348344, baseEnd_1348344] using wordTrace_append hprefix tailTrace_1348344
  have hstable : (prefixWord ++ tailWord_1348344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348344).length < 2 ^ (prefixWord ++ tailWord_1348344).sum := by decide
  have hdescent : baseEnd_1348344 < baseStart_1348344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348403 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 5]
def baseStart_1348403 : Nat := 118140960795 + 1348403 * 2 ^ 59
def prefixEnd_1348403 : Nat := 4983230072969 + 3 ^ 40 * 1348403 * 2
def baseEnd_1348403 : Nat := 307723935539819155893917

theorem tailTrace_1348403 : CollatzResearch.WordTrace tailWord_1348403 prefixEnd_1348403 307723935539819155893917 := by
  unfold tailWord_1348403
  simp only [CollatzResearch.WordTrace]
  refine ⟨49180297733973694743273863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32786865155982463162182575 49180297733973694743273863)
  ·
    refine ⟨73770446600960542114910795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49180297733973694743273863 73770446600960542114910795)
    ·
      refine ⟨110655669901440813172366193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73770446600960542114910795 110655669901440813172366193)
      ·
        refine ⟨82991752426080609879274645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110655669901440813172366193 82991752426080609879274645)
        ·
          refine ⟨3890238394972528588090999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 82991752426080609879274645 3890238394972528588090999)
          ·
            refine ⟨5835357592458792882136499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3890238394972528588090999 5835357592458792882136499)
            ·
              refine ⟨8753036388688189323204749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5835357592458792882136499 8753036388688189323204749)
              ·
                refine ⟨3282388645758070996201781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8753036388688189323204749 3282388645758070996201781)
                ·
                  refine ⟨307723935539819155893917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3282388645758070996201781 307723935539819155893917)
                  ·
                    rfl

theorem cell21_1348403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 5].length) (baseStart_1348403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348403 prefixEnd_1348403 := by exact prefixLift 1348403
  have htrace : WordTrace (prefixWord ++ tailWord_1348403) baseStart_1348403 baseEnd_1348403 := by
    simpa [prefixWord, tailWord_1348403, baseEnd_1348403] using wordTrace_append hprefix tailTrace_1348403
  have hstable : (prefixWord ++ tailWord_1348403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348403).length < 2 ^ (prefixWord ++ tailWord_1348403).sum := by decide
  have hdescent : baseEnd_1348403 < baseStart_1348403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348513 : List Nat := [1, 2, 3, 4, 1, 2, 1, 4, 3]
def baseStart_1348513 : Nat := 118140960795 + 1348513 * 2 ^ 59
def prefixEnd_1348513 : Nat := 4983230072969 + 3 ^ 40 * 1348513 * 2
def baseEnd_1348513 : Nat := 307749039038483409060359

theorem tailTrace_1348513 : CollatzResearch.WordTrace tailWord_1348513 prefixEnd_1348513 307749039038483409060359 := by
  unfold tailWord_1348513
  simp only [CollatzResearch.WordTrace]
  refine ⟨49184309763575183529778193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32789539842383455686518795 49184309763575183529778193)
  ·
    refine ⟨36888232322681387647333645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49184309763575183529778193 36888232322681387647333645)
    ·
      refine ⟨13833087121005520367750117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36888232322681387647333645 13833087121005520367750117)
      ·
        refine ⟨2593703835188535068953147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13833087121005520367750117 2593703835188535068953147)
        ·
          refine ⟨3890555752782802603429721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2593703835188535068953147 3890555752782802603429721)
          ·
            refine ⟨2917916814587101952572291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3890555752782802603429721 2917916814587101952572291)
            ·
              refine ⟨4376875221880652928858437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2917916814587101952572291 4376875221880652928858437)
              ·
                refine ⟨820664104102622424160957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4376875221880652928858437 820664104102622424160957)
                ·
                  refine ⟨307749039038483409060359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820664104102622424160957 307749039038483409060359)
                  ·
                    rfl

theorem cell21_1348513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_1348513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348513 prefixEnd_1348513 := by exact prefixLift 1348513
  have htrace : WordTrace (prefixWord ++ tailWord_1348513) baseStart_1348513 baseEnd_1348513 := by
    simpa [prefixWord, tailWord_1348513, baseEnd_1348513] using wordTrace_append hprefix tailTrace_1348513
  have hstable : (prefixWord ++ tailWord_1348513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348513).length < 2 ^ (prefixWord ++ tailWord_1348513).sum := by decide
  have hdescent : baseEnd_1348513 < baseStart_1348513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
