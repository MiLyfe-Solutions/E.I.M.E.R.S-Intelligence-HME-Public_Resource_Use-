import V185TrunkScan22Chunk172

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1544654 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1544654 : Nat := 118140960795 + 1544654 * 2 ^ 59
def prefixEnd_1544654 : Nat := 4983230072969 + 3 ^ 40 * 1544654 * 2
def baseEnd_1544654 : Nat := 528766631260069845214181

theorem tailTrace_1544654 : CollatzResearch.WordTrace tailWord_1544654 prefixEnd_1544654 528766631260069845214181 := by
  unfold tailWord_1544654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7042269968248729843206127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37558773163993225830432677 7042269968248729843206127)
  ·
    refine ⟨10563404952373094764809191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7042269968248729843206127 10563404952373094764809191)
    ·
      refine ⟨15845107428559642147213787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563404952373094764809191 15845107428559642147213787)
      ·
        refine ⟨23767661142839463220820681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15845107428559642147213787 23767661142839463220820681)
        ·
          refine ⟨17825745857129597415615511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23767661142839463220820681 17825745857129597415615511)
          ·
            refine ⟨26738618785694396123423267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17825745857129597415615511 26738618785694396123423267)
            ·
              refine ⟨40107928178541594185134901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26738618785694396123423267 40107928178541594185134901)
              ·
                refine ⟨3760118266738274454856397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40107928178541594185134901 3760118266738274454856397)
                ·
                  refine ⟨1410044350026852920571149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3760118266738274454856397 1410044350026852920571149)
                  ·
                    refine ⟨528766631260069845214181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410044350026852920571149 528766631260069845214181)
                    ·
                      rfl

theorem cell22_1544654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1544654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544654 prefixEnd_1544654 := by exact prefixLift 1544654
  have htrace : WordTrace (prefixWord ++ tailWord_1544654) baseStart_1544654 baseEnd_1544654 := by
    simpa [prefixWord, tailWord_1544654, baseEnd_1544654] using wordTrace_append hprefix tailTrace_1544654
  have hstable : (prefixWord ++ tailWord_1544654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544654).length < 2 ^ (prefixWord ++ tailWord_1544654).sum := by decide
  have hdescent : baseEnd_1544654 < baseStart_1544654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544759 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1544759 : Nat := 118140960795 + 1544759 * 2 ^ 59
def prefixEnd_1544759 : Nat := 4983230072969 + 3 ^ 40 * 1544759 * 2
def baseEnd_1544759 : Nat := 528802574905884571338859

theorem tailTrace_1544759 : CollatzResearch.WordTrace tailWord_1544759 prefixEnd_1544759 528802574905884571338859 := by
  unfold tailWord_1544759
  simp only [CollatzResearch.WordTrace]
  refine ⟨56341989410609441678221331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37561326273739627785480887 56341989410609441678221331)
  ·
    refine ⟨84512984115914162517331997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56341989410609441678221331 84512984115914162517331997)
    ·
      refine ⟨31692369043467810943999499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84512984115914162517331997 31692369043467810943999499)
      ·
        refine ⟨47538553565201716415999249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31692369043467810943999499 47538553565201716415999249)
        ·
          refine ⟨35653915173901287311999437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47538553565201716415999249 35653915173901287311999437)
          ·
            refine ⟨13370218190212982741999789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35653915173901287311999437 13370218190212982741999789)
            ·
              refine ⟨5013831821329868528249921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13370218190212982741999789 5013831821329868528249921)
              ·
                refine ⟨3760373865997401396187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013831821329868528249921 3760373865997401396187441)
                ·
                  refine ⟨2820280399498051047140581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760373865997401396187441 2820280399498051047140581)
                  ·
                    refine ⟨528802574905884571338859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820280399498051047140581 528802574905884571338859)
                    ·
                      rfl

theorem cell22_1544759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1544759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544759 prefixEnd_1544759 := by exact prefixLift 1544759
  have htrace : WordTrace (prefixWord ++ tailWord_1544759) baseStart_1544759 baseEnd_1544759 := by
    simpa [prefixWord, tailWord_1544759, baseEnd_1544759] using wordTrace_append hprefix tailTrace_1544759
  have hstable : (prefixWord ++ tailWord_1544759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544759).length < 2 ^ (prefixWord ++ tailWord_1544759).sum := by decide
  have hdescent : baseEnd_1544759 < baseStart_1544759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544761 : List Nat := [1, 2, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_1544761 : Nat := 118140960795 + 1544761 * 2 ^ 59
def prefixEnd_1544761 : Nat := 4983230072969 + 3 ^ 40 * 1544761 * 2
def baseEnd_1544761 : Nat := 528803259546757232788853

theorem tailTrace_1544761 : CollatzResearch.WordTrace tailWord_1544761 prefixEnd_1544761 528803259546757232788853 := by
  unfold tailWord_1544761
  simp only [CollatzResearch.WordTrace]
  refine ⟨56342062356602196019794137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37561374904401464013196091 56342062356602196019794137)
  ·
    refine ⟨42256546767451647014845603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56342062356602196019794137 42256546767451647014845603)
    ·
      refine ⟨63384820151177470522268405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42256546767451647014845603 63384820151177470522268405)
      ·
        refine ⟨5942326889172887861462663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63384820151177470522268405 5942326889172887861462663)
        ·
          refine ⟨8913490333759331792193995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942326889172887861462663 8913490333759331792193995)
          ·
            refine ⟨13370235500638997688290993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913490333759331792193995 13370235500638997688290993)
            ·
              refine ⟨10027676625479248266218245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13370235500638997688290993 10027676625479248266218245)
              ·
                refine ⟨1880189367277359049915921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10027676625479248266218245 1880189367277359049915921)
                ·
                  refine ⟨1410142025458019287436941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880189367277359049915921 1410142025458019287436941)
                  ·
                    refine ⟨528803259546757232788853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410142025458019287436941 528803259546757232788853)
                    ·
                      rfl

theorem cell22_1544761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_1544761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544761 prefixEnd_1544761 := by exact prefixLift 1544761
  have htrace : WordTrace (prefixWord ++ tailWord_1544761) baseStart_1544761 baseEnd_1544761 := by
    simpa [prefixWord, tailWord_1544761, baseEnd_1544761] using wordTrace_append hprefix tailTrace_1544761
  have hstable : (prefixWord ++ tailWord_1544761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544761).length < 2 ^ (prefixWord ++ tailWord_1544761).sum := by decide
  have hdescent : baseEnd_1544761 < baseStart_1544761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544778 : List Nat := [3, 1, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1544778 : Nat := 118140960795 + 1544778 * 2 ^ 59
def prefixEnd_1544778 : Nat := 4983230072969 + 3 ^ 40 * 1544778 * 2
def baseEnd_1544778 : Nat := 528809078994174855113801

theorem tailTrace_1544778 : CollatzResearch.WordTrace tailWord_1544778 prefixEnd_1544778 528809078994174855113801 := by
  unfold tailWord_1544778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085670599385151980790747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37561788265027071948775325 14085670599385151980790747)
  ·
    refine ⟨21128505899077727971186121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14085670599385151980790747 21128505899077727971186121)
    ·
      refine ⟨15846379424308295978389591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21128505899077727971186121 15846379424308295978389591)
      ·
        refine ⟨23769569136462443967584387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846379424308295978389591 23769569136462443967584387)
        ·
          refine ⟨35654353704693665951376581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23769569136462443967584387 35654353704693665951376581)
          ·
            refine ⟨6685191319630062365883109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35654353704693665951376581 6685191319630062365883109)
            ·
              refine ⟨1253473372430636693603083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6685191319630062365883109 1253473372430636693603083)
              ·
                refine ⟨1880210058645955040404625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253473372430636693603083 1880210058645955040404625)
                ·
                  refine ⟨1410157543984466280303469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880210058645955040404625 1410157543984466280303469)
                  ·
                    refine ⟨528809078994174855113801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410157543984466280303469 528809078994174855113801)
                    ·
                      rfl

theorem cell22_1544778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1544778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544778 prefixEnd_1544778 := by exact prefixLift 1544778
  have htrace : WordTrace (prefixWord ++ tailWord_1544778) baseStart_1544778 baseEnd_1544778 := by
    simpa [prefixWord, tailWord_1544778, baseEnd_1544778] using wordTrace_append hprefix tailTrace_1544778
  have hstable : (prefixWord ++ tailWord_1544778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544778).length < 2 ^ (prefixWord ++ tailWord_1544778).sum := by decide
  have hdescent : baseEnd_1544778 < baseStart_1544778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544836 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1544836 : Nat := 118140960795 + 1544836 * 2 ^ 59
def prefixEnd_1544836 : Nat := 4983230072969 + 3 ^ 40 * 1544836 * 2
def baseEnd_1544836 : Nat := 176276311193160679054541

theorem tailTrace_1544836 : CollatzResearch.WordTrace tailWord_1544836 prefixEnd_1544836 176276311193160679054541 := by
  unfold tailWord_1544836
  simp only [CollatzResearch.WordTrace]
  refine ⟨28172398915665241914387181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37563198554220322552516241 28172398915665241914387181)
  ·
    refine ⟨10564649593374465717895193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28172398915665241914387181 10564649593374465717895193)
    ·
      refine ⟨7923487195030849288421395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10564649593374465717895193 7923487195030849288421395)
      ·
        refine ⟨11885230792546273932632093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7923487195030849288421395 11885230792546273932632093)
        ·
          refine ⟨4456961547204852724737035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11885230792546273932632093 4456961547204852724737035)
          ·
            refine ⟨6685442320807279087105553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456961547204852724737035 6685442320807279087105553)
            ·
              refine ⟨5014081740605459315329165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6685442320807279087105553 5014081740605459315329165)
              ·
                refine ⟨1880280652727047243248437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014081740605459315329165 1880280652727047243248437)
                ·
                  refine ⟨176276311193160679054541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1880280652727047243248437 176276311193160679054541)
                  ·
                    rfl

theorem cell22_1544836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1544836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544836 prefixEnd_1544836 := by exact prefixLift 1544836
  have htrace : WordTrace (prefixWord ++ tailWord_1544836) baseStart_1544836 baseEnd_1544836 := by
    simpa [prefixWord, tailWord_1544836, baseEnd_1544836] using wordTrace_append hprefix tailTrace_1544836
  have hstable : (prefixWord ++ tailWord_1544836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544836).length < 2 ^ (prefixWord ++ tailWord_1544836).sum := by decide
  have hdescent : baseEnd_1544836 < baseStart_1544836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544896 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_1544896 : Nat := 118140960795 + 1544896 * 2 ^ 59
def prefixEnd_1544896 : Nat := 4983230072969 + 3 ^ 40 * 1544896 * 2
def baseEnd_1544896 : Nat := 528849472805661880663439

theorem tailTrace_1544896 : CollatzResearch.WordTrace tailWord_1544896 prefixEnd_1544896 528849472805661880663439 := by
  unfold tailWord_1544896
  simp only [CollatzResearch.WordTrace]
  refine ⟨28173493105556557037979271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37564657474075409383972361 28173493105556557037979271)
  ·
    refine ⟨42260239658334835556968907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28173493105556557037979271 42260239658334835556968907)
    ·
      refine ⟨63390359487502253335453361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42260239658334835556968907 63390359487502253335453361)
      ·
        refine ⟨47542769615626690001590021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63390359487502253335453361 47542769615626690001590021)
        ·
          refine ⟨8914269302930004375298129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47542769615626690001590021 8914269302930004375298129)
          ·
            refine ⟨6685701977197503281473597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8914269302930004375298129 6685701977197503281473597)
            ·
              refine ⟨2507138241449063730552599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6685701977197503281473597 2507138241449063730552599)
              ·
                refine ⟨3760707362173595595828899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507138241449063730552599 3760707362173595595828899)
                ·
                  refine ⟨5641061043260393393743349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760707362173595595828899 5641061043260393393743349)
                  ·
                    refine ⟨528849472805661880663439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5641061043260393393743349 528849472805661880663439)
                    ·
                      rfl

theorem cell22_1544896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_1544896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544896 prefixEnd_1544896 := by exact prefixLift 1544896
  have htrace : WordTrace (prefixWord ++ tailWord_1544896) baseStart_1544896 baseEnd_1544896 := by
    simpa [prefixWord, tailWord_1544896, baseEnd_1544896] using wordTrace_append hprefix tailTrace_1544896
  have hstable : (prefixWord ++ tailWord_1544896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544896).length < 2 ^ (prefixWord ++ tailWord_1544896).sum := by decide
  have hdescent : baseEnd_1544896 < baseStart_1544896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544939 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 6]
def baseStart_1544939 : Nat := 118140960795 + 1544939 * 2 ^ 59
def prefixEnd_1544939 : Nat := 4983230072969 + 3 ^ 40 * 1544939 * 2
def baseEnd_1544939 : Nat := 528864192584424101838307

theorem tailTrace_1544939 : CollatzResearch.WordTrace tailWord_1544939 prefixEnd_1544939 528864192584424101838307 := by
  unfold tailWord_1544939
  simp only [CollatzResearch.WordTrace]
  refine ⟨56348554549957332419773871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37565703033304888279849247 56348554549957332419773871)
  ·
    refine ⟨84522831824935998629660807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56348554549957332419773871 84522831824935998629660807)
    ·
      refine ⟨126784247737403997944491211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84522831824935998629660807 126784247737403997944491211)
      ·
        refine ⟨190176371606105996916736817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126784247737403997944491211 190176371606105996916736817)
        ·
          refine ⟨142632278704579497687552613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190176371606105996916736817 142632278704579497687552613)
          ·
            refine ⟨26743552257108655816416115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142632278704579497687552613 26743552257108655816416115)
            ·
              refine ⟨40115328385662983724624173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26743552257108655816416115 40115328385662983724624173)
              ·
                refine ⟨15043248144623618896734065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40115328385662983724624173 15043248144623618896734065)
                ·
                  refine ⟨11282436108467714172550549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15043248144623618896734065 11282436108467714172550549)
                  ·
                    refine ⟨528864192584424101838307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11282436108467714172550549 528864192584424101838307)
                    ·
                      rfl

theorem cell22_1544939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 6].length) (baseStart_1544939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544939 prefixEnd_1544939 := by exact prefixLift 1544939
  have htrace : WordTrace (prefixWord ++ tailWord_1544939) baseStart_1544939 baseEnd_1544939 := by
    simpa [prefixWord, tailWord_1544939, baseEnd_1544939] using wordTrace_append hprefix tailTrace_1544939
  have hstable : (prefixWord ++ tailWord_1544939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544939).length < 2 ^ (prefixWord ++ tailWord_1544939).sum := by decide
  have hdescent : baseEnd_1544939 < baseStart_1544939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544986 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_1544986 : Nat := 118140960795 + 1544986 * 2 ^ 59
def prefixEnd_1544986 : Nat := 4983230072969 + 3 ^ 40 * 1544986 * 2
def baseEnd_1544986 : Nat := 528880281644931645913163

theorem tailTrace_1544986 : CollatzResearch.WordTrace tailWord_1544986 prefixEnd_1544986 528880281644931645913163 := by
  unfold tailWord_1544986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14087567195196764861683703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37566845853858039631156541 14087567195196764861683703)
  ·
    refine ⟨21131350792795147292525555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14087567195196764861683703 21131350792795147292525555)
    ·
      refine ⟨31697026189192720938788333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21131350792795147292525555 31697026189192720938788333)
      ·
        refine ⟨11886384820947270352045625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31697026189192720938788333 11886384820947270352045625)
        ·
          refine ⟨8914788615710452764034219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11886384820947270352045625 8914788615710452764034219)
          ·
            refine ⟨13372182923565679146051329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8914788615710452764034219 13372182923565679146051329)
            ·
              refine ⟨10029137192674259359538497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13372182923565679146051329 10029137192674259359538497)
              ·
                refine ⟨7521852894505694519653873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10029137192674259359538497 7521852894505694519653873)
                ·
                  refine ⟨5641389670879270889740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521852894505694519653873 5641389670879270889740405)
                  ·
                    refine ⟨528880281644931645913163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5641389670879270889740405 528880281644931645913163)
                    ·
                      rfl

theorem cell22_1544986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_1544986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544986 prefixEnd_1544986 := by exact prefixLift 1544986
  have htrace : WordTrace (prefixWord ++ tailWord_1544986) baseStart_1544986 baseEnd_1544986 := by
    simpa [prefixWord, tailWord_1544986, baseEnd_1544986] using wordTrace_append hprefix tailTrace_1544986
  have hstable : (prefixWord ++ tailWord_1544986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544986).length < 2 ^ (prefixWord ++ tailWord_1544986).sum := by decide
  have hdescent : baseEnd_1544986 < baseStart_1544986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544988 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_1544988 : Nat := 118140960795 + 1544988 * 2 ^ 59
def prefixEnd_1544988 : Nat := 4983230072969 + 3 ^ 40 * 1544988 * 2
def baseEnd_1544988 : Nat := 176293655428601435787719

theorem tailTrace_1544988 : CollatzResearch.WordTrace tailWord_1544988 prefixEnd_1544988 176293655428601435787719 := by
  unfold tailWord_1544988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28175170863389906894153809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37566894484519875858871745 28175170863389906894153809)
  ·
    refine ⟨21131378147542430170615357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28175170863389906894153809 21131378147542430170615357)
    ·
      refine ⟨7924266805328411313980759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21131378147542430170615357 7924266805328411313980759)
      ·
        refine ⟨11886400207992616970971139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924266805328411313980759 11886400207992616970971139)
        ·
          refine ⟨17829600311988925456456709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886400207992616970971139 17829600311988925456456709)
          ·
            refine ⟨3343050058497923523085633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17829600311988925456456709 3343050058497923523085633)
            ·
              refine ⟨2507287543873442642314225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3343050058497923523085633 2507287543873442642314225)
              ·
                refine ⟨1880465657905081981735669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507287543873442642314225 1880465657905081981735669)
                ·
                  refine ⟨176293655428601435787719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1880465657905081981735669 176293655428601435787719)
                  ·
                    rfl

theorem cell22_1544988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_1544988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544988 prefixEnd_1544988 := by exact prefixLift 1544988
  have htrace : WordTrace (prefixWord ++ tailWord_1544988) baseStart_1544988 baseEnd_1544988 := by
    simpa [prefixWord, tailWord_1544988, baseEnd_1544988] using wordTrace_append hprefix tailTrace_1544988
  have hstable : (prefixWord ++ tailWord_1544988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544988).length < 2 ^ (prefixWord ++ tailWord_1544988).sum := by decide
  have hdescent : baseEnd_1544988 < baseStart_1544988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544992 : List Nat := [2, 1, 1, 5, 1, 2, 4, 2, 1, 3]
def baseStart_1544992 : Nat := 118140960795 + 1544992 * 2 ^ 59
def prefixEnd_1544992 : Nat := 4983230072969 + 3 ^ 40 * 1544992 * 2
def baseEnd_1544992 : Nat := 528882335567549630263145

theorem tailTrace_1544992 : CollatzResearch.WordTrace tailWord_1544992 prefixEnd_1544992 528882335567549630263145 := by
  unfold tailWord_1544992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28175243809382661235726615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37566991745843548314302153 28175243809382661235726615)
  ·
    refine ⟨42262865714073991853589923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28175243809382661235726615 42262865714073991853589923)
    ·
      refine ⟨63394298571110987780384885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42262865714073991853589923 63394298571110987780384885)
      ·
        refine ⟨5943215491041655104411083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63394298571110987780384885 5943215491041655104411083)
        ·
          refine ⟨8914823236562482656616625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943215491041655104411083 8914823236562482656616625)
          ·
            refine ⟨6686117427421861992462469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8914823236562482656616625 6686117427421861992462469)
            ·
              refine ⟨1253647017641599123586713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6686117427421861992462469 1253647017641599123586713)
              ·
                refine ⟨940235263231199342690035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253647017641599123586713 940235263231199342690035)
                ·
                  refine ⟨1410352894846799014035053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940235263231199342690035 1410352894846799014035053)
                  ·
                    refine ⟨528882335567549630263145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410352894846799014035053 528882335567549630263145)
                    ·
                      rfl

theorem cell22_1544992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_1544992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544992 prefixEnd_1544992 := by exact prefixLift 1544992
  have htrace : WordTrace (prefixWord ++ tailWord_1544992) baseStart_1544992 baseEnd_1544992 := by
    simpa [prefixWord, tailWord_1544992, baseEnd_1544992] using wordTrace_append hprefix tailTrace_1544992
  have hstable : (prefixWord ++ tailWord_1544992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544992).length < 2 ^ (prefixWord ++ tailWord_1544992).sum := by decide
  have hdescent : baseEnd_1544992 < baseStart_1544992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545016 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_1545016 : Nat := 118140960795 + 1545016 * 2 ^ 59
def prefixEnd_1545016 : Nat := 4983230072969 + 3 ^ 40 * 1545016 * 2
def baseEnd_1545016 : Nat := 176296850419340522554357

theorem tailTrace_1545016 : CollatzResearch.WordTrace tailWord_1545016 prefixEnd_1545016 176296850419340522554357 := by
  unfold tailWord_1545016
  simp only [CollatzResearch.WordTrace]
  refine ⟨28175681485339187285163451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37567575313785583046884601 28175681485339187285163451)
  ·
    refine ⟨42263522228008780927745177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28175681485339187285163451 42263522228008780927745177)
    ·
      refine ⟨31697641671006585695808883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42263522228008780927745177 31697641671006585695808883)
      ·
        refine ⟨47546462506509878543713325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31697641671006585695808883 47546462506509878543713325)
        ·
          refine ⟨17829923439941204453892497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47546462506509878543713325 17829923439941204453892497)
          ·
            refine ⟨13372442579955903340419373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17829923439941204453892497 13372442579955903340419373)
            ·
              refine ⟨5014665967483463752657265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13372442579955903340419373 5014665967483463752657265)
              ·
                refine ⟨3760999475612597814492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014665967483463752657265 3760999475612597814492949)
                ·
                  refine ⟨176296850419340522554357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3760999475612597814492949 176296850419340522554357)
                  ·
                    rfl

theorem cell22_1545016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_1545016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545016 prefixEnd_1545016 := by exact prefixLift 1545016
  have htrace : WordTrace (prefixWord ++ tailWord_1545016) baseStart_1545016 baseEnd_1545016 := by
    simpa [prefixWord, tailWord_1545016, baseEnd_1545016] using wordTrace_append hprefix tailTrace_1545016
  have hstable : (prefixWord ++ tailWord_1545016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545016).length < 2 ^ (prefixWord ++ tailWord_1545016).sum := by decide
  have hdescent : baseEnd_1545016 < baseStart_1545016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545033 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 4]
def baseStart_1545033 : Nat := 118140960795 + 1545033 * 2 ^ 59
def prefixEnd_1545033 : Nat := 4983230072969 + 3 ^ 40 * 1545033 * 2
def baseEnd_1545033 : Nat := 176298790235146396662673

theorem tailTrace_1545033 : CollatzResearch.WordTrace tailWord_1545033 prefixEnd_1545033 176298790235146396662673 := by
  unfold tailWord_1545033
  simp only [CollatzResearch.WordTrace]
  refine ⟨56351983011616786473695753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37567988674411190982463835 56351983011616786473695753)
  ·
    refine ⟨42263987258712589855271815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56351983011616786473695753 42263987258712589855271815)
    ·
      refine ⟨63395980888068884782907723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42263987258712589855271815 63395980888068884782907723)
      ·
        refine ⟨95093971332103327174361585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63395980888068884782907723 95093971332103327174361585)
        ·
          refine ⟨71320478499077495380771189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95093971332103327174361585 71320478499077495380771189)
          ·
            refine ⟨6686294859288515191947299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71320478499077495380771189 6686294859288515191947299)
            ·
              refine ⟨10029442288932772787920949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686294859288515191947299 10029442288932772787920949)
              ·
                refine ⟨940260214587447448867589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10029442288932772787920949 940260214587447448867589)
                ·
                  refine ⟨176298790235146396662673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940260214587447448867589 176298790235146396662673)
                  ·
                    rfl

theorem cell22_1545033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_1545033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545033 prefixEnd_1545033 := by exact prefixLift 1545033
  have htrace : WordTrace (prefixWord ++ tailWord_1545033) baseStart_1545033 baseEnd_1545033 := by
    simpa [prefixWord, tailWord_1545033, baseEnd_1545033] using wordTrace_append hprefix tailTrace_1545033
  have hstable : (prefixWord ++ tailWord_1545033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545033).length < 2 ^ (prefixWord ++ tailWord_1545033).sum := by decide
  have hdescent : baseEnd_1545033 < baseStart_1545033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545108 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1545108 : Nat := 118140960795 + 1545108 * 2 ^ 59
def prefixEnd_1545108 : Nat := 4983230072969 + 3 ^ 40 * 1545108 * 2
def baseEnd_1545108 : Nat := 528922044738163994362789

theorem tailTrace_1545108 : CollatzResearch.WordTrace tailWord_1545108 prefixEnd_1545108 528922044738163994362789 := by
  unfold tailWord_1545108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28177359243172537141337989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37569812324230049521783985 28177359243172537141337989)
  ·
    refine ⟨5283254858094850714000873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28177359243172537141337989 5283254858094850714000873)
    ·
      refine ⟨3962441143571138035500655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5283254858094850714000873 3962441143571138035500655)
      ·
        refine ⟨5943661715356707053250983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962441143571138035500655 5943661715356707053250983)
        ·
          refine ⟨8915492573035060579876475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5943661715356707053250983 8915492573035060579876475)
          ·
            refine ⟨13373238859552590869814713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8915492573035060579876475 13373238859552590869814713)
            ·
              refine ⟨10029929144664443152361035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13373238859552590869814713 10029929144664443152361035)
              ·
                refine ⟨15044893716996664728541553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029929144664443152361035 15044893716996664728541553)
                ·
                  refine ⟨11283670287747498546406165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15044893716996664728541553 11283670287747498546406165)
                  ·
                    refine ⟨528922044738163994362789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11283670287747498546406165 528922044738163994362789)
                    ·
                      rfl

theorem cell22_1545108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1545108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545108 prefixEnd_1545108 := by exact prefixLift 1545108
  have htrace : WordTrace (prefixWord ++ tailWord_1545108) baseStart_1545108 baseEnd_1545108 := by
    simpa [prefixWord, tailWord_1545108, baseEnd_1545108] using wordTrace_append hprefix tailTrace_1545108
  have hstable : (prefixWord ++ tailWord_1545108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545108).length < 2 ^ (prefixWord ++ tailWord_1545108).sum := by decide
  have hdescent : baseEnd_1545108 < baseStart_1545108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545116 : List Nat := [2, 2, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1545116 : Nat := 118140960795 + 1545116 * 2 ^ 59
def prefixEnd_1545116 : Nat := 4983230072969 + 3 ^ 40 * 1545116 * 2
def baseEnd_1545116 : Nat := 528924783301654640162765

theorem tailTrace_1545116 : CollatzResearch.WordTrace tailWord_1545116 prefixEnd_1545116 528924783301654640162765 := by
  unfold tailWord_1545116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28177505135158045824483601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37570006846877394432644801 28177505135158045824483601)
  ·
    refine ⟨21133128851368534368362701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28177505135158045824483601 21133128851368534368362701)
    ·
      refine ⟨7924923319263200388136013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21133128851368534368362701 7924923319263200388136013)
      ·
        refine ⟨2971846244723700145551005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7924923319263200388136013 2971846244723700145551005)
        ·
          refine ⟨1114442341771387554581627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2971846244723700145551005 1114442341771387554581627)
          ·
            refine ⟨1671663512657081331872441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114442341771387554581627 1671663512657081331872441)
            ·
              refine ⟨1253747634492810998904331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671663512657081331872441 1253747634492810998904331)
              ·
                refine ⟨1880621451739216498356497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253747634492810998904331 1880621451739216498356497)
                ·
                  refine ⟨1410466088804412373767373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880621451739216498356497 1410466088804412373767373)
                  ·
                    refine ⟨528924783301654640162765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410466088804412373767373 528924783301654640162765)
                    ·
                      rfl

theorem cell22_1545116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1545116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545116 prefixEnd_1545116 := by exact prefixLift 1545116
  have htrace : WordTrace (prefixWord ++ tailWord_1545116) baseStart_1545116 baseEnd_1545116 := by
    simpa [prefixWord, tailWord_1545116, baseEnd_1545116] using wordTrace_append hprefix tailTrace_1545116
  have hstable : (prefixWord ++ tailWord_1545116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545116).length < 2 ^ (prefixWord ++ tailWord_1545116).sum := by decide
  have hdescent : baseEnd_1545116 < baseStart_1545116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545151 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 10]
def baseStart_1545151 : Nat := 118140960795 + 1545151 * 2 ^ 59
def prefixEnd_1545151 : Nat := 4983230072969 + 3 ^ 40 * 1545151 * 2
def baseEnd_1545151 : Nat := 176312254838975405179219

theorem tailTrace_1545151 : CollatzResearch.WordTrace tailWord_1545151 prefixEnd_1545151 176312254838975405179219 := by
  unfold tailWord_1545151
  simp only [CollatzResearch.WordTrace]
  refine ⟨56356286825189292626491307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37570857883459528417660871 56356286825189292626491307)
  ·
    refine ⟨84534430237783938939736961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56356286825189292626491307 84534430237783938939736961)
    ·
      refine ⟨63400822678337954204802721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84534430237783938939736961 63400822678337954204802721)
      ·
        refine ⟨47550617008753465653602041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63400822678337954204802721 47550617008753465653602041)
        ·
          refine ⟨35662962756565099240201531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47550617008753465653602041 35662962756565099240201531)
          ·
            refine ⟨53494444134847648860302297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35662962756565099240201531 53494444134847648860302297)
            ·
              refine ⟨40120833101135736645226723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53494444134847648860302297 40120833101135736645226723)
              ·
                refine ⟨60181249651703604967840085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40120833101135736645226723 60181249651703604967840085)
                ·
                  refine ⟨176312254838975405179219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 60181249651703604967840085 176312254838975405179219)
                  ·
                    rfl

theorem cell22_1545151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_1545151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545151 prefixEnd_1545151 := by exact prefixLift 1545151
  have htrace : WordTrace (prefixWord ++ tailWord_1545151) baseStart_1545151 baseEnd_1545151 := by
    simpa [prefixWord, tailWord_1545151, baseEnd_1545151] using wordTrace_append hprefix tailTrace_1545151
  have hstable : (prefixWord ++ tailWord_1545151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545151).length < 2 ^ (prefixWord ++ tailWord_1545151).sum := by decide
  have hdescent : baseEnd_1545151 < baseStart_1545151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545170 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1545170 : Nat := 118140960795 + 1545170 * 2 ^ 59
def prefixEnd_1545170 : Nat := 4983230072969 + 3 ^ 40 * 1545170 * 2
def baseEnd_1545170 : Nat := 528943268605216499312599

theorem tailTrace_1545170 : CollatzResearch.WordTrace tailWord_1545170 prefixEnd_1545170 528943268605216499312599 := by
  unfold tailWord_1545170
  simp only [CollatzResearch.WordTrace]
  refine ⟨14089244953030114717858241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37571319874746972580955309 14089244953030114717858241)
  ·
    refine ⟨10566933714772586038393681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14089244953030114717858241 10566933714772586038393681)
    ·
      refine ⟨7925200286079439528795261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10566933714772586038393681 7925200286079439528795261)
      ·
        refine ⟨2971950107279789823298223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7925200286079439528795261 2971950107279789823298223)
        ·
          refine ⟨4457925160919684734947335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2971950107279789823298223 4457925160919684734947335)
          ·
            refine ⟨6686887741379527102421003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457925160919684734947335 6686887741379527102421003)
            ·
              refine ⟨10030331612069290653631505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686887741379527102421003 10030331612069290653631505)
              ·
                refine ⟨7522748709051967990223629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10030331612069290653631505 7522748709051967990223629)
                ·
                  refine ⟨2821030765894487996333861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7522748709051967990223629 2821030765894487996333861)
                  ·
                    refine ⟨528943268605216499312599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821030765894487996333861 528943268605216499312599)
                    ·
                      rfl

theorem cell22_1545170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1545170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545170 prefixEnd_1545170 := by exact prefixLift 1545170
  have htrace : WordTrace (prefixWord ++ tailWord_1545170) baseStart_1545170 baseEnd_1545170 := by
    simpa [prefixWord, tailWord_1545170, baseEnd_1545170] using wordTrace_append hprefix tailTrace_1545170
  have hstable : (prefixWord ++ tailWord_1545170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545170).length < 2 ^ (prefixWord ++ tailWord_1545170).sum := by decide
  have hdescent : baseEnd_1545170 < baseStart_1545170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545217 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_1545217 : Nat := 118140960795 + 1545217 * 2 ^ 59
def prefixEnd_1545217 : Nat := 4983230072969 + 3 ^ 40 * 1545217 * 2
def baseEnd_1545217 : Nat := 528959357665724043387455

theorem tailTrace_1545217 : CollatzResearch.WordTrace tailWord_1545217 prefixEnd_1545217 528959357665724043387455 := by
  unfold tailWord_1545217
  simp only [CollatzResearch.WordTrace]
  refine ⟨56358694042950185898393905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37572462695300123932262603 56358694042950185898393905)
  ·
    refine ⟨42269020532212639423795429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56358694042950185898393905 42269020532212639423795429)
    ·
      refine ⟨7925441349789869891961643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42269020532212639423795429 7925441349789869891961643)
      ·
        refine ⟨11888162024684804837942465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925441349789869891961643 11888162024684804837942465)
        ·
          refine ⟨8916121518513603628456849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11888162024684804837942465 8916121518513603628456849)
          ·
            refine ⟨6687091138885202721342637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8916121518513603628456849 6687091138885202721342637)
            ·
              refine ⟨2507659177081951020503489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6687091138885202721342637 2507659177081951020503489)
              ·
                refine ⟨1880744382811463265377617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507659177081951020503489 1880744382811463265377617)
                ·
                  refine ⟨1410558287108597449033213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880744382811463265377617 1410558287108597449033213)
                  ·
                    refine ⟨528959357665724043387455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410558287108597449033213 528959357665724043387455)
                    ·
                      rfl

theorem cell22_1545217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_1545217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545217 prefixEnd_1545217 := by exact prefixLift 1545217
  have htrace : WordTrace (prefixWord ++ tailWord_1545217) baseStart_1545217 baseEnd_1545217 := by
    simpa [prefixWord, tailWord_1545217, baseEnd_1545217] using wordTrace_append hprefix tailTrace_1545217
  have hstable : (prefixWord ++ tailWord_1545217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545217).length < 2 ^ (prefixWord ++ tailWord_1545217).sum := by decide
  have hdescent : baseEnd_1545217 < baseStart_1545217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545303 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 8]
def baseStart_1545303 : Nat := 118140960795 + 1545303 * 2 ^ 59
def prefixEnd_1545303 : Nat := 4983230072969 + 3 ^ 40 * 1545303 * 2
def baseEnd_1545303 : Nat := 176329599074416161912397

theorem tailTrace_1545303 : CollatzResearch.WordTrace tailWord_1545303 prefixEnd_1545303 176329599074416161912397 := by
  unfold tailWord_1545303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56361830720638622586024563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37574553813759081724016375 56361830720638622586024563)
  ·
    refine ⟨84542746080957933879036845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56361830720638622586024563 84542746080957933879036845)
    ·
      refine ⟨31703529780359225204638817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84542746080957933879036845 31703529780359225204638817)
      ·
        refine ⟨23777647335269418903479113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31703529780359225204638817 23777647335269418903479113)
        ·
          refine ⟨17833235501452064177609335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23777647335269418903479113 17833235501452064177609335)
          ·
            refine ⟨26749853252178096266414003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833235501452064177609335 26749853252178096266414003)
            ·
              refine ⟨40124779878267144399621005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26749853252178096266414003 40124779878267144399621005)
              ·
                refine ⟨15046792454350179149857877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40124779878267144399621005 15046792454350179149857877)
                ·
                  refine ⟨176329599074416161912397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15046792454350179149857877 176329599074416161912397)
                  ·
                    rfl

theorem cell22_1545303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 8].length) (baseStart_1545303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545303 prefixEnd_1545303 := by exact prefixLift 1545303
  have htrace : WordTrace (prefixWord ++ tailWord_1545303) baseStart_1545303 baseEnd_1545303 := by
    simpa [prefixWord, tailWord_1545303, baseEnd_1545303] using wordTrace_append hprefix tailTrace_1545303
  have hstable : (prefixWord ++ tailWord_1545303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545303).length < 2 ^ (prefixWord ++ tailWord_1545303).sum := by decide
  have hdescent : baseEnd_1545303 < baseStart_1545303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545305 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_1545305 : Nat := 118140960795 + 1545305 * 2 ^ 59
def prefixEnd_1545305 : Nat := 4983230072969 + 3 ^ 40 * 1545305 * 2
def baseEnd_1545305 : Nat := 528989481864121147187185

theorem tailTrace_1545305 : CollatzResearch.WordTrace tailWord_1545305 prefixEnd_1545305 528989481864121147187185 := by
  unfold tailWord_1545305
  simp only [CollatzResearch.WordTrace]
  refine ⟨56361903666631376927597369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37574602444420917951731579 56361903666631376927597369)
  ·
    refine ⟨42271427749973532695698027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56361903666631376927597369 42271427749973532695698027)
    ·
      refine ⟨63407141624960299043547041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42271427749973532695698027 63407141624960299043547041)
      ·
        refine ⟨47555356218720224282660281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63407141624960299043547041 47555356218720224282660281)
        ·
          refine ⟨35666517164040168211995211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47555356218720224282660281 35666517164040168211995211)
          ·
            refine ⟨53499775746060252317992817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35666517164040168211995211 53499775746060252317992817)
            ·
              refine ⟨40124831809545189238494613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53499775746060252317992817 40124831809545189238494613)
              ·
                refine ⟨1880851491072430745554435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40124831809545189238494613 1880851491072430745554435)
                ·
                  refine ⟨2821277236608646118331653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880851491072430745554435 2821277236608646118331653)
                  ·
                    refine ⟨528989481864121147187185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821277236608646118331653 528989481864121147187185)
                    ·
                      rfl

theorem cell22_1545305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_1545305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545305 prefixEnd_1545305 := by exact prefixLift 1545305
  have htrace : WordTrace (prefixWord ++ tailWord_1545305) baseStart_1545305 baseEnd_1545305 := by
    simpa [prefixWord, tailWord_1545305, baseEnd_1545305] using wordTrace_append hprefix tailTrace_1545305
  have hstable : (prefixWord ++ tailWord_1545305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545305).length < 2 ^ (prefixWord ++ tailWord_1545305).sum := by decide
  have hdescent : baseEnd_1545305 < baseStart_1545305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545367 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 2, 4]
def baseStart_1545367 : Nat := 118140960795 + 1545367 * 2 ^ 59
def prefixEnd_1545367 : Nat := 4983230072969 + 3 ^ 40 * 1545367 * 2
def baseEnd_1545367 : Nat := 529010705731173652136995

theorem tailTrace_1545367 : CollatzResearch.WordTrace tailWord_1545367 prefixEnd_1545367 529010705731173652136995 := by
  unfold tailWord_1545367
  simp only [CollatzResearch.WordTrace]
  refine ⟨56364164992406761516354355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37576109994937841010902903 56364164992406761516354355)
  ·
    refine ⟨84546247488610142274531533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56364164992406761516354355 84546247488610142274531533)
    ·
      refine ⟨31704842808228803352949325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84546247488610142274531533 31704842808228803352949325)
      ·
        refine ⟨11889316053085801257355997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31704842808228803352949325 11889316053085801257355997)
        ·
          refine ⟨4458493519907175471508499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11889316053085801257355997 4458493519907175471508499)
          ·
            refine ⟨6687740279860763207262749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458493519907175471508499 6687740279860763207262749)
            ·
              refine ⟨2507902604947786202723531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6687740279860763207262749 2507902604947786202723531)
              ·
                refine ⟨3761853907421679304085297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507902604947786202723531 3761853907421679304085297)
                ·
                  refine ⟨2821390430566259478063973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3761853907421679304085297 2821390430566259478063973)
                  ·
                    refine ⟨529010705731173652136995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821390430566259478063973 529010705731173652136995)
                    ·
                      rfl

theorem cell22_1545367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_1545367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545367 prefixEnd_1545367 := by exact prefixLift 1545367
  have htrace : WordTrace (prefixWord ++ tailWord_1545367) baseStart_1545367 baseEnd_1545367 := by
    simpa [prefixWord, tailWord_1545367, baseEnd_1545367] using wordTrace_append hprefix tailTrace_1545367
  have hstable : (prefixWord ++ tailWord_1545367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545367).length < 2 ^ (prefixWord ++ tailWord_1545367).sum := by decide
  have hdescent : baseEnd_1545367 < baseStart_1545367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545386 : List Nat := [3, 1, 5, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1545386 : Nat := 118140960795 + 1545386 * 2 ^ 59
def prefixEnd_1545386 : Nat := 4983230072969 + 3 ^ 40 * 1545386 * 2
def baseEnd_1545386 : Nat := 529017209819463935911937

theorem tailTrace_1545386 : CollatzResearch.WordTrace tailWord_1545386 prefixEnd_1545386 529017209819463935911937 := by
  unfold tailWord_1545386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091214494834481940324003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37576571986225285174197341 14091214494834481940324003)
  ·
    refine ⟨21136821742251722910486005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14091214494834481940324003 21136821742251722910486005)
    ·
      refine ⟨1981577038336099022858063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21136821742251722910486005 1981577038336099022858063)
      ·
        refine ⟨2972365557504148534287095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981577038336099022858063 2972365557504148534287095)
        ·
          refine ⟨4458548336256222801430643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972365557504148534287095 4458548336256222801430643)
          ·
            refine ⟨6687822504384334202145965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458548336256222801430643 6687822504384334202145965)
            ·
              refine ⟨2507933439144125325804737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6687822504384334202145965 2507933439144125325804737)
              ·
                refine ⟨1880950079358093994353553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2507933439144125325804737 1880950079358093994353553)
                ·
                  refine ⟨1410712559518570495765165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1880950079358093994353553 1410712559518570495765165)
                  ·
                    refine ⟨529017209819463935911937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1410712559518570495765165 529017209819463935911937)
                    ·
                      rfl

theorem cell22_1545386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1545386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545386 prefixEnd_1545386 := by exact prefixLift 1545386
  have htrace : WordTrace (prefixWord ++ tailWord_1545386) baseStart_1545386 baseEnd_1545386 := by
    simpa [prefixWord, tailWord_1545386, baseEnd_1545386] using wordTrace_append hprefix tailTrace_1545386
  have hstable : (prefixWord ++ tailWord_1545386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545386).length < 2 ^ (prefixWord ++ tailWord_1545386).sum := by decide
  have hdescent : baseEnd_1545386 < baseStart_1545386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545506 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 4]
def baseStart_1545506 : Nat := 118140960795 + 1545506 * 2 ^ 59
def prefixEnd_1545506 : Nat := 4983230072969 + 3 ^ 40 * 1545506 * 2
def baseEnd_1545506 : Nat := 176352762757274540970523

theorem tailTrace_1545506 : CollatzResearch.WordTrace tailWord_1545506 prefixEnd_1545506 176352762757274540970523 := by
  unfold tailWord_1545506
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092308684725797063916093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37579489825935458837109581 14092308684725797063916093)
  ·
    refine ⟨5284615756772173898968535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14092308684725797063916093 5284615756772173898968535)
    ·
      refine ⟨7926923635158260848452803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5284615756772173898968535 7926923635158260848452803)
      ·
        refine ⟨11890385452737391272679205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926923635158260848452803 11890385452737391272679205)
        ·
          refine ⟨2229447272388260863627351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11890385452737391272679205 2229447272388260863627351)
          ·
            refine ⟨3344170908582391295441027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229447272388260863627351 3344170908582391295441027)
            ·
              refine ⟨5016256362873586943161541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344170908582391295441027 5016256362873586943161541)
              ·
                refine ⟨940548068038797551842789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5016256362873586943161541 940548068038797551842789)
                ·
                  refine ⟨176352762757274540970523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940548068038797551842789 176352762757274540970523)
                  ·
                    rfl

theorem cell22_1545506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_1545506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545506 prefixEnd_1545506 := by exact prefixLift 1545506
  have htrace : WordTrace (prefixWord ++ tailWord_1545506) baseStart_1545506 baseEnd_1545506 := by
    simpa [prefixWord, tailWord_1545506, baseEnd_1545506] using wordTrace_append hprefix tailTrace_1545506
  have hstable : (prefixWord ++ tailWord_1545506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545506).length < 2 ^ (prefixWord ++ tailWord_1545506).sum := by decide
  have hdescent : baseEnd_1545506 < baseStart_1545506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545534 : List Nat := [4, 2, 1, 2, 1, 1, 5, 6]
def baseStart_1545534 : Nat := 118140960795 + 1545534 * 2 ^ 59
def prefixEnd_1545534 : Nat := 4983230072969 + 3 ^ 40 * 1545534 * 2
def baseEnd_1545534 : Nat := 58785319249337875912387

theorem tailTrace_1545534 : CollatzResearch.WordTrace tailWord_1545534 prefixEnd_1545534 58785319249337875912387 := by
  unfold tailWord_1545534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046281997850218629710457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37580170655201166025122437 7046281997850218629710457)
  ·
    refine ⟨5284711498387663972282843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7046281997850218629710457 5284711498387663972282843)
    ·
      refine ⟨7927067247581495958424265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5284711498387663972282843 7927067247581495958424265)
      ·
        refine ⟨5945300435686121968818199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7927067247581495958424265 5945300435686121968818199)
        ·
          refine ⟨8917950653529182953227299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945300435686121968818199 8917950653529182953227299)
          ·
            refine ⟨13376925980293774429840949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917950653529182953227299 13376925980293774429840949)
            ·
              refine ⟨1254086810652541352797589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13376925980293774429840949 1254086810652541352797589)
              ·
                refine ⟨58785319249337875912387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1254086810652541352797589 58785319249337875912387)
                ·
                  rfl

theorem cell22_1545534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_1545534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545534 prefixEnd_1545534 := by exact prefixLift 1545534
  have htrace : WordTrace (prefixWord ++ tailWord_1545534) baseStart_1545534 baseEnd_1545534 := by
    simpa [prefixWord, tailWord_1545534, baseEnd_1545534] using wordTrace_append hprefix tailTrace_1545534
  have hstable : (prefixWord ++ tailWord_1545534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545534).length < 2 ^ (prefixWord ++ tailWord_1545534).sum := by decide
  have hdescent : baseEnd_1545534 < baseStart_1545534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545542 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1545542 : Nat := 118140960795 + 1545542 * 2 ^ 59
def prefixEnd_1545542 : Nat := 4983230072969 + 3 ^ 40 * 1545542 * 2
def baseEnd_1545542 : Nat := 529070611807531529011459

theorem tailTrace_1545542 : CollatzResearch.WordTrace tailWord_1545542 prefixEnd_1545542 529070611807531529011459 := by
  unfold tailWord_1545542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761579617711648950124215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37580365177848510935983253 1761579617711648950124215)
  ·
    refine ⟨2642369426567473425186323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1761579617711648950124215 2642369426567473425186323)
    ·
      refine ⟨3963554139851210137779485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642369426567473425186323 3963554139851210137779485)
      ·
        refine ⟨1486332802444203801667307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3963554139851210137779485 1486332802444203801667307)
        ·
          refine ⟨2229499203666305702500961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486332802444203801667307 2229499203666305702500961)
          ·
            refine ⟨1672124402749729276875721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229499203666305702500961 1672124402749729276875721)
            ·
              refine ⟨1254093302062296957656791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672124402749729276875721 1254093302062296957656791)
              ·
                refine ⟨1881139953093445436485187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254093302062296957656791 1881139953093445436485187)
                ·
                  refine ⟨2821709929640168154727781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881139953093445436485187 2821709929640168154727781)
                  ·
                    refine ⟨529070611807531529011459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2821709929640168154727781 529070611807531529011459)
                    ·
                      rfl

theorem cell22_1545542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1545542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545542 prefixEnd_1545542 := by exact prefixLift 1545542
  have htrace : WordTrace (prefixWord ++ tailWord_1545542) baseStart_1545542 baseEnd_1545542 := by
    simpa [prefixWord, tailWord_1545542, baseEnd_1545542] using wordTrace_append hprefix tailTrace_1545542
  have hstable : (prefixWord ++ tailWord_1545542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545542).length < 2 ^ (prefixWord ++ tailWord_1545542).sum := by decide
  have hdescent : baseEnd_1545542 < baseStart_1545542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545630 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1545630 : Nat := 118140960795 + 1545630 * 2 ^ 59
def prefixEnd_1545630 : Nat := 4983230072969 + 3 ^ 40 * 1545630 * 2
def baseEnd_1545630 : Nat := 176366912001976210937063

theorem tailTrace_1545630 : CollatzResearch.WordTrace tailWord_1545630 prefixEnd_1545630 176366912001976210937063 := by
  unfold tailWord_1545630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046719673806744679147293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37582504926969304955452229 7046719673806744679147293)
  ·
    refine ⟨2642519877677529254680235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7046719673806744679147293 2642519877677529254680235)
    ·
      refine ⟨3963779816516293882020353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642519877677529254680235 3963779816516293882020353)
      ·
        refine ⟨2972834862387220411515265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3963779816516293882020353 2972834862387220411515265)
        ·
          refine ⟨2229626146790415308636449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2972834862387220411515265 2229626146790415308636449)
          ·
            refine ⟨1672219610092811481477337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229626146790415308636449 1672219610092811481477337)
            ·
              refine ⟨1254164707569608611108003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672219610092811481477337 1254164707569608611108003)
              ·
                refine ⟨1881247061354412916662005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254164707569608611108003 1881247061354412916662005)
                ·
                  refine ⟨176366912001976210937063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1881247061354412916662005 176366912001976210937063)
                  ·
                    rfl

theorem cell22_1545630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1545630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545630 prefixEnd_1545630 := by exact prefixLift 1545630
  have htrace : WordTrace (prefixWord ++ tailWord_1545630) baseStart_1545630 baseEnd_1545630 := by
    simpa [prefixWord, tailWord_1545630, baseEnd_1545630] using wordTrace_append hprefix tailTrace_1545630
  have hstable : (prefixWord ++ tailWord_1545630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545630).length < 2 ^ (prefixWord ++ tailWord_1545630).sum := by decide
  have hdescent : baseEnd_1545630 < baseStart_1545630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545637 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_1545637 : Nat := 118140960795 + 1545637 * 2 ^ 59
def prefixEnd_1545637 : Nat := 4983230072969 + 3 ^ 40 * 1545637 * 2
def baseEnd_1545637 : Nat := 529103132248982947886167

theorem tailTrace_1545637 : CollatzResearch.WordTrace tailWord_1545637 prefixEnd_1545637 529103132248982947886167 := by
  unfold tailWord_1545637
  simp only [CollatzResearch.WordTrace]
  refine ⟨56374012701428597628683165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37582675134285731752455443 56374012701428597628683165)
  ·
    refine ⟨21140254763035724110756187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56374012701428597628683165 21140254763035724110756187)
    ·
      refine ⟨31710382144553586166134281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21140254763035724110756187 31710382144553586166134281)
      ·
        refine ⟨23782786608415189624600711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31710382144553586166134281 23782786608415189624600711)
        ·
          refine ⟨35674179912622784436901067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23782786608415189624600711 35674179912622784436901067)
          ·
            refine ⟨53511269868934176655351601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35674179912622784436901067 53511269868934176655351601)
            ·
              refine ⟨40133452401700632491513701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53511269868934176655351601 40133452401700632491513701)
              ·
                refine ⟨7525022325318868592158819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40133452401700632491513701 7525022325318868592158819)
                ·
                  refine ⟨11287533487978302888238229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7525022325318868592158819 11287533487978302888238229)
                  ·
                    refine ⟨529103132248982947886167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11287533487978302888238229 529103132248982947886167)
                    ·
                      rfl

theorem cell22_1545637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_1545637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545637 prefixEnd_1545637 := by exact prefixLift 1545637
  have htrace : WordTrace (prefixWord ++ tailWord_1545637) baseStart_1545637 baseEnd_1545637 := by
    simpa [prefixWord, tailWord_1545637, baseEnd_1545637] using wordTrace_append hprefix tailTrace_1545637
  have hstable : (prefixWord ++ tailWord_1545637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545637).length < 2 ^ (prefixWord ++ tailWord_1545637).sum := by decide
  have hdescent : baseEnd_1545637 < baseStart_1545637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545639 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1545639 : Nat := 118140960795 + 1545639 * 2 ^ 59
def prefixEnd_1545639 : Nat := 4983230072969 + 3 ^ 40 * 1545639 * 2
def baseEnd_1545639 : Nat := 529103816889855609336161

theorem tailTrace_1545639 : CollatzResearch.WordTrace tailWord_1545639 prefixEnd_1545639 529103816889855609336161 := by
  unfold tailWord_1545639
  simp only [CollatzResearch.WordTrace]
  refine ⟨56374085647421351970255971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37582723764947567980170647 56374085647421351970255971)
  ·
    refine ⟨84561128471132027955383957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56374085647421351970255971 84561128471132027955383957)
    ·
      refine ⟨3963802897084313810408623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84561128471132027955383957 3963802897084313810408623)
      ·
        refine ⟨5945704345626470715612935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963802897084313810408623 5945704345626470715612935)
        ·
          refine ⟨8918556518439706073419403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945704345626470715612935 8918556518439706073419403)
          ·
            refine ⟨13377834777659559110129105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8918556518439706073419403 13377834777659559110129105)
            ·
              refine ⟨10033376083244669332596829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13377834777659559110129105 10033376083244669332596829)
              ·
                refine ⟨3762516031216750999723811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10033376083244669332596829 3762516031216750999723811)
                ·
                  refine ⟨5643774046825126499585717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762516031216750999723811 5643774046825126499585717)
                  ·
                    refine ⟨529103816889855609336161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5643774046825126499585717 529103816889855609336161)
                    ·
                      rfl

theorem cell22_1545639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1545639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545639 prefixEnd_1545639 := by exact prefixLift 1545639
  have htrace : WordTrace (prefixWord ++ tailWord_1545639) baseStart_1545639 baseEnd_1545639 := by
    simpa [prefixWord, tailWord_1545639, baseEnd_1545639] using wordTrace_append hprefix tailTrace_1545639
  have hstable : (prefixWord ++ tailWord_1545639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545639).length < 2 ^ (prefixWord ++ tailWord_1545639).sum := by decide
  have hdescent : baseEnd_1545639 < baseStart_1545639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545686 : List Nat := [5, 2, 1, 1, 1, 2, 3, 7]
def baseStart_1545686 : Nat := 118140960795 + 1545686 * 2 ^ 59
def prefixEnd_1545686 : Nat := 4983230072969 + 3 ^ 40 * 1545686 * 2
def baseEnd_1545686 : Nat := 58791100661151461490113

theorem tailTrace_1545686 : CollatzResearch.WordTrace tailWord_1545686 prefixEnd_1545686 58791100661151461490113 := by
  unfold tailWord_1545686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523487492390692437326057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37583866585500719331477941 3523487492390692437326057)
  ·
    refine ⟨2642615619293019327994543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3523487492390692437326057 2642615619293019327994543)
    ·
      refine ⟨3963923428939528991991815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2642615619293019327994543 3963923428939528991991815)
      ·
        refine ⟨5945885143409293487987723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963923428939528991991815 5945885143409293487987723)
        ·
          refine ⟨8918827715113940231981585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945885143409293487987723 8918827715113940231981585)
          ·
            refine ⟨6689120786335455173986189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918827715113940231981585 6689120786335455173986189)
            ·
              refine ⟨2508420294875795690244821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6689120786335455173986189 2508420294875795690244821)
              ·
                refine ⟨58791100661151461490113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2508420294875795690244821 58791100661151461490113)
                ·
                  rfl

theorem cell22_1545686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_1545686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545686 prefixEnd_1545686 := by exact prefixLift 1545686
  have htrace : WordTrace (prefixWord ++ tailWord_1545686) baseStart_1545686 baseEnd_1545686 := by
    simpa [prefixWord, tailWord_1545686, baseEnd_1545686] using wordTrace_append hprefix tailTrace_1545686
  have hstable : (prefixWord ++ tailWord_1545686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545686).length < 2 ^ (prefixWord ++ tailWord_1545686).sum := by decide
  have hdescent : baseEnd_1545686 < baseStart_1545686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545701 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_1545701 : Nat := 118140960795 + 1545701 * 2 ^ 59
def prefixEnd_1545701 : Nat := 4983230072969 + 3 ^ 40 * 1545701 * 2
def baseEnd_1545701 : Nat := 529125040756908114285971

theorem tailTrace_1545701 : CollatzResearch.WordTrace tailWord_1545701 prefixEnd_1545701 529125040756908114285971 := by
  unfold tailWord_1545701
  simp only [CollatzResearch.WordTrace]
  refine ⟨56376346973196736559012957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37584231315464491039341971 56376346973196736559012957)
  ·
    refine ⟨21141130114948776209629859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56376346973196736559012957 21141130114948776209629859)
    ·
      refine ⟨31711695172423164314444789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21141130114948776209629859 31711695172423164314444789)
      ·
        refine ⟨2972971422414671654479199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31711695172423164314444789 2972971422414671654479199)
        ·
          refine ⟨4459457133622007481718799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2972971422414671654479199 4459457133622007481718799)
          ·
            refine ⟨6689185700433011222578199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459457133622007481718799 6689185700433011222578199)
            ·
              refine ⟨10033778550649516833867299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689185700433011222578199 10033778550649516833867299)
              ·
                refine ⟨15050667825974275250800949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10033778550649516833867299 15050667825974275250800949)
                ·
                  refine ⟨1411000108685088304762589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15050667825974275250800949 1411000108685088304762589)
                  ·
                    refine ⟨529125040756908114285971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411000108685088304762589 529125040756908114285971)
                    ·
                      rfl

theorem cell22_1545701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_1545701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545701 prefixEnd_1545701 := by exact prefixLift 1545701
  have htrace : WordTrace (prefixWord ++ tailWord_1545701) baseStart_1545701 baseEnd_1545701 := by
    simpa [prefixWord, tailWord_1545701, baseEnd_1545701] using wordTrace_append hprefix tailTrace_1545701
  have hstable : (prefixWord ++ tailWord_1545701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545701).length < 2 ^ (prefixWord ++ tailWord_1545701).sum := by decide
  have hdescent : baseEnd_1545701 < baseStart_1545701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545759 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 6]
def baseStart_1545759 : Nat := 118140960795 + 1545759 * 2 ^ 59
def prefixEnd_1545759 : Nat := 4983230072969 + 3 ^ 40 * 1545759 * 2
def baseEnd_1545759 : Nat := 176381631780738432111931

theorem tailTrace_1545759 : CollatzResearch.WordTrace tailWord_1545759 prefixEnd_1545759 176381631780738432111931 := by
  unfold tailWord_1545759
  simp only [CollatzResearch.WordTrace]
  refine ⟨56378462406986612464624331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37585641604657741643082887 56378462406986612464624331)
  ·
    refine ⟨84567693610479918696936497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56378462406986612464624331 84567693610479918696936497)
    ·
      refine ⟨63425770207859939022702373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84567693610479918696936497 63425770207859939022702373)
      ·
        refine ⟨11892331913973738566756695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63425770207859939022702373 11892331913973738566756695)
        ·
          refine ⟨17838497870960607850135043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11892331913973738566756695 17838497870960607850135043)
          ·
            refine ⟨26757746806440911775202565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17838497870960607850135043 26757746806440911775202565)
            ·
              refine ⟨5017077526207670957850481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26757746806440911775202565 5017077526207670957850481)
              ·
                refine ⟨3762808144655753218387861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5017077526207670957850481 3762808144655753218387861)
                ·
                  refine ⟨176381631780738432111931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3762808144655753218387861 176381631780738432111931)
                  ·
                    rfl

theorem cell22_1545759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_1545759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545759 prefixEnd_1545759 := by exact prefixLift 1545759
  have htrace : WordTrace (prefixWord ++ tailWord_1545759) baseStart_1545759 baseEnd_1545759 := by
    simpa [prefixWord, tailWord_1545759, baseEnd_1545759] using wordTrace_append hprefix tailTrace_1545759
  have hstable : (prefixWord ++ tailWord_1545759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545759).length < 2 ^ (prefixWord ++ tailWord_1545759).sum := by decide
  have hdescent : baseEnd_1545759 < baseStart_1545759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545761 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_1545761 : Nat := 118140960795 + 1545761 * 2 ^ 59
def prefixEnd_1545761 : Nat := 4983230072969 + 3 ^ 40 * 1545761 * 2
def baseEnd_1545761 : Nat := 529145579983087957785787

theorem tailTrace_1545761 : CollatzResearch.WordTrace tailWord_1545761 prefixEnd_1545761 529145579983087957785787 := by
  unfold tailWord_1545761
  simp only [CollatzResearch.WordTrace]
  refine ⟨56378535352979366806197137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37585690235319577870798091 56378535352979366806197137)
  ·
    refine ⟨42283901514734525104647853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56378535352979366806197137 42283901514734525104647853)
    ·
      refine ⟨15856463068025446914242945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42283901514734525104647853 15856463068025446914242945)
      ·
        refine ⟨11892347301019085185682209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15856463068025446914242945 11892347301019085185682209)
        ·
          refine ⟨8919260475764313889261657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11892347301019085185682209 8919260475764313889261657)
          ·
            refine ⟨6689445356823235416946243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919260475764313889261657 6689445356823235416946243)
            ·
              refine ⟨10034168035234853125419365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689445356823235416946243 10034168035234853125419365)
              ·
                refine ⟨1881406506606534961016131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10034168035234853125419365 1881406506606534961016131)
                ·
                  refine ⟨2822109759909802441524197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881406506606534961016131 2822109759909802441524197)
                  ·
                    refine ⟨529145579983087957785787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822109759909802441524197 529145579983087957785787)
                    ·
                      rfl

theorem cell22_1545761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_1545761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545761 prefixEnd_1545761 := by exact prefixLift 1545761
  have htrace : WordTrace (prefixWord ++ tailWord_1545761) baseStart_1545761 baseEnd_1545761 := by
    simpa [prefixWord, tailWord_1545761, baseEnd_1545761] using wordTrace_append hprefix tailTrace_1545761
  have hstable : (prefixWord ++ tailWord_1545761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545761).length < 2 ^ (prefixWord ++ tailWord_1545761).sum := by decide
  have hdescent : baseEnd_1545761 < baseStart_1545761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545791 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 4, 3]
def baseStart_1545791 : Nat := 118140960795 + 1545791 * 2 ^ 59
def prefixEnd_1545791 : Nat := 4983230072969 + 3 ^ 40 * 1545791 * 2
def baseEnd_1545791 : Nat := 529155849596177879535695

theorem tailTrace_1545791 : CollatzResearch.WordTrace tailWord_1545791 prefixEnd_1545791 529155849596177879535695 := by
  unfold tailWord_1545791
  simp only [CollatzResearch.WordTrace]
  refine ⟨56379629542870681929789227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37586419695247121286526151 56379629542870681929789227)
  ·
    refine ⟨84569444314306022894683841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56379629542870681929789227 84569444314306022894683841)
    ·
      refine ⟨63427083235729517171012881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84569444314306022894683841 63427083235729517171012881)
      ·
        refine ⟨47570312426797137878259661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63427083235729517171012881 47570312426797137878259661)
        ·
          refine ⟨17838867160048926704347373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47570312426797137878259661 17838867160048926704347373)
          ·
            refine ⟨6689575185018347514130265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17838867160048926704347373 6689575185018347514130265)
            ·
              refine ⟨5017181388763760635597699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689575185018347514130265 5017181388763760635597699)
              ·
                refine ⟨7525772083145640953396549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017181388763760635597699 7525772083145640953396549)
                ·
                  refine ⟨1411082265589807678761853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7525772083145640953396549 1411082265589807678761853)
                  ·
                    refine ⟨529155849596177879535695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411082265589807678761853 529155849596177879535695)
                    ·
                      rfl

theorem cell22_1545791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 3].length) (baseStart_1545791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545791 prefixEnd_1545791 := by exact prefixLift 1545791
  have htrace : WordTrace (prefixWord ++ tailWord_1545791) baseStart_1545791 baseEnd_1545791 := by
    simpa [prefixWord, tailWord_1545791, baseEnd_1545791] using wordTrace_append hprefix tailTrace_1545791
  have hstable : (prefixWord ++ tailWord_1545791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545791).length < 2 ^ (prefixWord ++ tailWord_1545791).sum := by decide
  have hdescent : baseEnd_1545791 < baseStart_1545791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545804 : List Nat := [2, 2, 1, 3, 1, 3, 1, 9]
def baseStart_1545804 : Nat := 118140960795 + 1545804 * 2 ^ 59
def prefixEnd_1545804 : Nat := 4983230072969 + 3 ^ 40 * 1545804 * 2
def baseEnd_1545804 : Nat := 58795588862427797662295

theorem tailTrace_1545804 : CollatzResearch.WordTrace tailWord_1545804 prefixEnd_1545804 58795588862427797662295 := by
  unfold tailWord_1545804
  simp only [CollatzResearch.WordTrace]
  refine ⟨28190051845911792575006233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37586735794549056766674977 28190051845911792575006233)
  ·
    refine ⟨21142538884433844431254675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28190051845911792575006233 21142538884433844431254675)
    ·
      refine ⟨31713808326650766646882013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21142538884433844431254675 31713808326650766646882013)
      ·
        refine ⟨11892678122494037492580755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31713808326650766646882013 11892678122494037492580755)
        ·
          refine ⟨17839017183741056238871133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11892678122494037492580755 17839017183741056238871133)
          ·
            refine ⟨6689631443902896089576675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17839017183741056238871133 6689631443902896089576675)
            ·
              refine ⟨10034447165854344134365013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689631443902896089576675 10034447165854344134365013)
              ·
                refine ⟨58795588862427797662295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10034447165854344134365013 58795588862427797662295)
                ·
                  rfl

theorem cell22_1545804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_1545804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545804 prefixEnd_1545804 := by exact prefixLift 1545804
  have htrace : WordTrace (prefixWord ++ tailWord_1545804) baseStart_1545804 baseEnd_1545804 := by
    simpa [prefixWord, tailWord_1545804, baseEnd_1545804] using wordTrace_append hprefix tailTrace_1545804
  have hstable : (prefixWord ++ tailWord_1545804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545804).length < 2 ^ (prefixWord ++ tailWord_1545804).sum := by decide
  have hdescent : baseEnd_1545804 < baseStart_1545804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545911 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 6]
def baseStart_1545911 : Nat := 118140960795 + 1545911 * 2 ^ 59
def prefixEnd_1545911 : Nat := 4983230072969 + 3 ^ 40 * 1545911 * 2
def baseEnd_1545911 : Nat := 176398976016179188845109

theorem tailTrace_1545911 : CollatzResearch.WordTrace tailWord_1545911 prefixEnd_1545911 176398976016179188845109 := by
  unfold tailWord_1545911
  simp only [CollatzResearch.WordTrace]
  refine ⟨56384006302435942424157587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37589337534957294949438391 56384006302435942424157587)
  ·
    refine ⟨84576009453653913636236381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56384006302435942424157587 84576009453653913636236381)
    ·
      refine ⟨31716003545120217613588643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84576009453653913636236381 31716003545120217613588643)
      ·
        refine ⟨47574005317680326420382965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31716003545120217613588643 47574005317680326420382965)
        ·
          refine ⟨4460062998532530601910903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47574005317680326420382965 4460062998532530601910903)
          ·
            refine ⟨6690094497798795902866355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460062998532530601910903 6690094497798795902866355)
            ·
              refine ⟨10035141746698193854299533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690094497798795902866355 10035141746698193854299533)
              ·
                refine ⟨3763178155011822695362325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10035141746698193854299533 3763178155011822695362325)
                ·
                  refine ⟨176398976016179188845109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3763178155011822695362325 176398976016179188845109)
                  ·
                    rfl

theorem cell22_1545911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_1545911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545911 prefixEnd_1545911 := by exact prefixLift 1545911
  have htrace : WordTrace (prefixWord ++ tailWord_1545911) baseStart_1545911 baseEnd_1545911 := by
    simpa [prefixWord, tailWord_1545911, baseEnd_1545911] using wordTrace_append hprefix tailTrace_1545911
  have hstable : (prefixWord ++ tailWord_1545911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545911).length < 2 ^ (prefixWord ++ tailWord_1545911).sum := by decide
  have hdescent : baseEnd_1545911 < baseStart_1545911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545930 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_1545930 : Nat := 118140960795 + 1545930 * 2 ^ 59
def prefixEnd_1545930 : Nat := 4983230072969 + 3 ^ 40 * 1545930 * 2
def baseEnd_1545930 : Nat := 529203432136827850310269

theorem tailTrace_1545930 : CollatzResearch.WordTrace tailWord_1545930 prefixEnd_1545930 529203432136827850310269 := by
  unfold tailWord_1545930
  simp only [CollatzResearch.WordTrace]
  refine ⟨14096174822341777167274811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37589799526244739112732829 14096174822341777167274811)
  ·
    refine ⟨21144262233512665750912217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14096174822341777167274811 21144262233512665750912217)
    ·
      refine ⟨15858196675134499313184163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21144262233512665750912217 15858196675134499313184163)
      ·
        refine ⟨23787295012701748969776245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15858196675134499313184163 23787295012701748969776245)
        ·
          refine ⟨2230058907440788965916523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23787295012701748969776245 2230058907440788965916523)
          ·
            refine ⟨3345088361161183448874785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230058907440788965916523 3345088361161183448874785)
            ·
              refine ⟨2508816270870887586656089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3345088361161183448874785 2508816270870887586656089)
              ·
                refine ⟨1881612203153165689992067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508816270870887586656089 1881612203153165689992067)
                ·
                  refine ⟨2822418304729748534988101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881612203153165689992067 2822418304729748534988101)
                  ·
                    refine ⟨529203432136827850310269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822418304729748534988101 529203432136827850310269)
                    ·
                      rfl

theorem cell22_1545930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_1545930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545930 prefixEnd_1545930 := by exact prefixLift 1545930
  have htrace : WordTrace (prefixWord ++ tailWord_1545930) baseStart_1545930 baseEnd_1545930 := by
    simpa [prefixWord, tailWord_1545930, baseEnd_1545930] using wordTrace_append hprefix tailTrace_1545930
  have hstable : (prefixWord ++ tailWord_1545930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545930).length < 2 ^ (prefixWord ++ tailWord_1545930).sum := by decide
  have hdescent : baseEnd_1545930 < baseStart_1545930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1545945 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 4]
def baseStart_1545945 : Nat := 118140960795 + 1545945 * 2 ^ 59
def prefixEnd_1545945 : Nat := 4983230072969 + 3 ^ 40 * 1545945 * 2
def baseEnd_1545945 : Nat := 176402855647790937061741

theorem tailTrace_1545945 : CollatzResearch.WordTrace tailWord_1545945 prefixEnd_1545945 176402855647790937061741 := by
  unfold tailWord_1545945
  simp only [CollatzResearch.WordTrace]
  refine ⟨56385246384312766230895289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37590164256208510820596859 56385246384312766230895289)
  ·
    refine ⟨42288934788234574673171467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56385246384312766230895289 42288934788234574673171467)
    ·
      refine ⟨63433402182351862009757201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42288934788234574673171467 63433402182351862009757201)
      ·
        refine ⟨47575051636763896507317901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63433402182351862009757201 47575051636763896507317901)
        ·
          refine ⟨17840644363786461190244213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47575051636763896507317901 17840644363786461190244213)
          ·
            refine ⟨1672560409104980736585395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17840644363786461190244213 1672560409104980736585395)
            ·
              refine ⟨2508840613657471104878093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1672560409104980736585395 2508840613657471104878093)
              ·
                refine ⟨940815230121551664329285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2508840613657471104878093 940815230121551664329285)
                ·
                  refine ⟨176402855647790937061741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940815230121551664329285 176402855647790937061741)
                  ·
                    rfl

theorem cell22_1545945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_1545945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1545945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1545945 prefixEnd_1545945 := by exact prefixLift 1545945
  have htrace : WordTrace (prefixWord ++ tailWord_1545945) baseStart_1545945 baseEnd_1545945 := by
    simpa [prefixWord, tailWord_1545945, baseEnd_1545945] using wordTrace_append hprefix tailTrace_1545945
  have hstable : (prefixWord ++ tailWord_1545945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1545945).length < 2 ^ (prefixWord ++ tailWord_1545945).sum := by decide
  have hdescent : baseEnd_1545945 < baseStart_1545945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1545945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546033 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1546033 : Nat := 118140960795 + 1546033 * 2 ^ 59
def prefixEnd_1546033 : Nat := 4983230072969 + 3 ^ 40 * 1546033 * 2
def baseEnd_1546033 : Nat := 529238691141769914984953

theorem tailTrace_1546033 : CollatzResearch.WordTrace tailWord_1546033 prefixEnd_1546033 529238691141769914984953 := by
  unfold tailWord_1546033
  simp only [CollatzResearch.WordTrace]
  refine ⟨56388456007993957260098753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37592304005329304840065835 56388456007993957260098753)
  ·
    refine ⟨42291342005995467945074065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56388456007993957260098753 42291342005995467945074065)
    ·
      refine ⟨31718506504496600958805549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42291342005995467945074065 31718506504496600958805549)
      ·
        refine ⟨11894439939186225359552081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31718506504496600958805549 11894439939186225359552081)
        ·
          refine ⟨8920829954389669019664061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11894439939186225359552081 8920829954389669019664061)
          ·
            refine ⟨3345311232896125882374023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8920829954389669019664061 3345311232896125882374023)
            ·
              refine ⟨5017966849344188823561035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345311232896125882374023 5017966849344188823561035)
              ·
                refine ⟨7526950274016283235341553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017966849344188823561035 7526950274016283235341553)
                ·
                  refine ⟨5645212705512212426506165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7526950274016283235341553 5645212705512212426506165)
                  ·
                    refine ⟨529238691141769914984953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5645212705512212426506165 529238691141769914984953)
                    ·
                      rfl

theorem cell22_1546033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1546033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546033 prefixEnd_1546033 := by exact prefixLift 1546033
  have htrace : WordTrace (prefixWord ++ tailWord_1546033) baseStart_1546033 baseEnd_1546033 := by
    simpa [prefixWord, tailWord_1546033, baseEnd_1546033] using wordTrace_append hprefix tailTrace_1546033
  have hstable : (prefixWord ++ tailWord_1546033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546033).length < 2 ^ (prefixWord ++ tailWord_1546033).sum := by decide
  have hdescent : baseEnd_1546033 < baseStart_1546033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546065 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_1546065 : Nat := 118140960795 + 1546065 * 2 ^ 59
def prefixEnd_1546065 : Nat := 4983230072969 + 3 ^ 40 * 1546065 * 2
def baseEnd_1546065 : Nat := 529249645395732498184855

theorem tailTrace_1546065 : CollatzResearch.WordTrace tailWord_1546065 prefixEnd_1546065 529249645395732498184855 := by
  unfold tailWord_1546065
  simp only [CollatzResearch.WordTrace]
  refine ⟨56389623143878026725263649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37593082095918684483509099 56389623143878026725263649)
  ·
    refine ⟨42292217357908520043947737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56389623143878026725263649 42292217357908520043947737)
    ·
      refine ⟨31719163018431390032960803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42292217357908520043947737 31719163018431390032960803)
      ·
        refine ⟨47578744527647085049441205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31719163018431390032960803 47578744527647085049441205)
        ·
          refine ⟨4460507299466914223385113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47578744527647085049441205 4460507299466914223385113)
          ·
            refine ⟨3345380474600185667538835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4460507299466914223385113 3345380474600185667538835)
            ·
              refine ⟨5018070711900278501308253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345380474600185667538835 5018070711900278501308253)
              ·
                refine ⟨1881776516962604437990595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5018070711900278501308253 1881776516962604437990595)
                ·
                  refine ⟨2822664775443906656985893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881776516962604437990595 2822664775443906656985893)
                  ·
                    refine ⟨529249645395732498184855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2822664775443906656985893 529249645395732498184855)
                    ·
                      rfl

theorem cell22_1546065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_1546065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546065 prefixEnd_1546065 := by exact prefixLift 1546065
  have htrace : WordTrace (prefixWord ++ tailWord_1546065) baseStart_1546065 baseEnd_1546065 := by
    simpa [prefixWord, tailWord_1546065, baseEnd_1546065] using wordTrace_append hprefix tailTrace_1546065
  have hstable : (prefixWord ++ tailWord_1546065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546065).length < 2 ^ (prefixWord ++ tailWord_1546065).sum := by decide
  have hdescent : baseEnd_1546065 < baseStart_1546065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546080 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_1546080 : Nat := 118140960795 + 1546080 * 2 ^ 59
def prefixEnd_1546080 : Nat := 4983230072969 + 3 ^ 40 * 1546080 * 2
def baseEnd_1546080 : Nat := 176418260067425819686603

theorem tailTrace_1546080 : CollatzResearch.WordTrace tailWord_1546080 prefixEnd_1546080 176418260067425819686603 := by
  unfold tailWord_1546080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28195085119411842143529847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37593446825882456191373129 28195085119411842143529847)
  ·
    refine ⟨42292627679117763215294771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28195085119411842143529847 42292627679117763215294771)
    ·
      refine ⟨63438941518676644822942157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42292627679117763215294771 63438941518676644822942157)
      ·
        refine ⟨23789603069503741808603309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63438941518676644822942157 23789603069503741808603309)
        ·
          refine ⟨8921101151063903178226241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23789603069503741808603309 8921101151063903178226241)
          ·
            refine ⟨6690825863297927383669681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921101151063903178226241 6690825863297927383669681)
            ·
              refine ⟨5018119397473445537752261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690825863297927383669681 5018119397473445537752261)
              ·
                refine ⟨940897387026271038328549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5018119397473445537752261 940897387026271038328549)
                ·
                  refine ⟨176418260067425819686603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940897387026271038328549 176418260067425819686603)
                  ·
                    rfl

theorem cell22_1546080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_1546080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546080 prefixEnd_1546080 := by exact prefixLift 1546080
  have htrace : WordTrace (prefixWord ++ tailWord_1546080) baseStart_1546080 baseEnd_1546080 := by
    simpa [prefixWord, tailWord_1546080, baseEnd_1546080] using wordTrace_append hprefix tailTrace_1546080
  have hstable : (prefixWord ++ tailWord_1546080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546080).length < 2 ^ (prefixWord ++ tailWord_1546080).sum := by decide
  have hdescent : baseEnd_1546080 < baseStart_1546080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546091 : List Nat := [1, 1, 1, 1, 2, 2, 3, 11]
def baseStart_1546091 : Nat := 118140960795 + 1546091 * 2 ^ 59
def prefixEnd_1546091 : Nat := 4983230072969 + 3 ^ 40 * 1546091 * 2
def baseEnd_1546091 : Nat := 58806505080786344114975

theorem tailTrace_1546091 : CollatzResearch.WordTrace tailWord_1546091 prefixEnd_1546091 58806505080786344114975 := by
  unfold tailWord_1546091
  simp only [CollatzResearch.WordTrace]
  refine ⟨56390571441783833165710127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37593714294522555443806751 56390571441783833165710127)
  ·
    refine ⟨84585857162675749748565191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56390571441783833165710127 84585857162675749748565191)
    ·
      refine ⟨126878785744013624622847787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84585857162675749748565191 126878785744013624622847787)
      ·
        refine ⟨190318178616020436934271681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126878785744013624622847787 190318178616020436934271681)
        ·
          refine ⟨142738633962015327700703761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190318178616020436934271681 142738633962015327700703761)
          ·
            refine ⟨107053975471511495775527821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142738633962015327700703761 107053975471511495775527821)
            ·
              refine ⟨40145240801816810915822933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107053975471511495775527821 40145240801816810915822933)
              ·
                refine ⟨58806505080786344114975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 40145240801816810915822933 58806505080786344114975)
                ·
                  rfl

theorem cell22_1546091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 11].length) (baseStart_1546091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546091 prefixEnd_1546091 := by exact prefixLift 1546091
  have htrace : WordTrace (prefixWord ++ tailWord_1546091) baseStart_1546091 baseEnd_1546091 := by
    simpa [prefixWord, tailWord_1546091, baseEnd_1546091] using wordTrace_append hprefix tailTrace_1546091
  have hstable : (prefixWord ++ tailWord_1546091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546091).length < 2 ^ (prefixWord ++ tailWord_1546091).sum := by decide
  have hdescent : baseEnd_1546091 < baseStart_1546091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546093 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1546093 : Nat := 118140960795 + 1546093 * 2 ^ 59
def prefixEnd_1546093 : Nat := 4983230072969 + 3 ^ 40 * 1546093 * 2
def baseEnd_1546093 : Nat := 529259230367949758484769

theorem tailTrace_1546093 : CollatzResearch.WordTrace tailWord_1546093 prefixEnd_1546093 529259230367949758484769 := by
  unfold tailWord_1546093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56390644387776587507282933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37593762925184391671521955 56390644387776587507282933)
  ·
    refine ⟨5286622911354055078807775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56390644387776587507282933 5286622911354055078807775)
    ·
      refine ⟨7929934367031082618211663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5286622911354055078807775 7929934367031082618211663)
      ·
        refine ⟨11894901550546623927317495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7929934367031082618211663 11894901550546623927317495)
        ·
          refine ⟨17842352325819935890976243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894901550546623927317495 17842352325819935890976243)
          ·
            refine ⟨26763528488729903836464365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17842352325819935890976243 26763528488729903836464365)
            ·
              refine ⟨10036323183273713938674137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26763528488729903836464365 10036323183273713938674137)
              ·
                refine ⟨7527242387455285454005603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036323183273713938674137 7527242387455285454005603)
                ·
                  refine ⟨11290863581182928181008405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7527242387455285454005603 11290863581182928181008405)
                  ·
                    refine ⟨529259230367949758484769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11290863581182928181008405 529259230367949758484769)
                    ·
                      rfl

theorem cell22_1546093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1546093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546093 prefixEnd_1546093 := by exact prefixLift 1546093
  have htrace : WordTrace (prefixWord ++ tailWord_1546093) baseStart_1546093 baseEnd_1546093 := by
    simpa [prefixWord, tailWord_1546093, baseEnd_1546093] using wordTrace_append hprefix tailTrace_1546093
  have hstable : (prefixWord ++ tailWord_1546093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546093).length < 2 ^ (prefixWord ++ tailWord_1546093).sum := by decide
  have hdescent : baseEnd_1546093 < baseStart_1546093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546146 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_1546146 : Nat := 118140960795 + 1546146 * 2 ^ 59
def prefixEnd_1546146 : Nat := 4983230072969 + 3 ^ 40 * 1546146 * 2
def baseEnd_1546146 : Nat := 529277373351075286909607

theorem tailTrace_1546146 : CollatzResearch.WordTrace tailWord_1546146 prefixEnd_1546146 529277373351075286909607 := by
  unfold tailWord_1546146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14098144364146144389740573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37595051637723051705974861 14098144364146144389740573)
  ·
    refine ⟨5286804136554804146152715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14098144364146144389740573 5286804136554804146152715)
    ·
      refine ⟨7930206204832206219229073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5286804136554804146152715 7930206204832206219229073)
      ·
        refine ⟨5947654653624154664421805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7930206204832206219229073 5947654653624154664421805)
        ·
          refine ⟨2230370495109057999158177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5947654653624154664421805 2230370495109057999158177)
          ·
            refine ⟨1672777871331793499368633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2230370495109057999158177 1672777871331793499368633)
            ·
              refine ⟨1254583403498845124526475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672777871331793499368633 1254583403498845124526475)
              ·
                refine ⟨1881875105248267686789713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254583403498845124526475 1881875105248267686789713)
                ·
                  refine ⟨1411406328936200765092285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1881875105248267686789713 1411406328936200765092285)
                  ·
                    refine ⟨529277373351075286909607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411406328936200765092285 529277373351075286909607)
                    ·
                      rfl

theorem cell22_1546146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_1546146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546146 prefixEnd_1546146 := by exact prefixLift 1546146
  have htrace : WordTrace (prefixWord ++ tailWord_1546146) baseStart_1546146 baseEnd_1546146 := by
    simpa [prefixWord, tailWord_1546146, baseEnd_1546146] using wordTrace_append hprefix tailTrace_1546146
  have hstable : (prefixWord ++ tailWord_1546146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546146).length < 2 ^ (prefixWord ++ tailWord_1546146).sum := by decide
  have hdescent : baseEnd_1546146 < baseStart_1546146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546247 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 4, 3]
def baseStart_1546247 : Nat := 118140960795 + 1546247 * 2 ^ 59
def prefixEnd_1546247 : Nat := 4983230072969 + 3 ^ 40 * 1546247 * 2
def baseEnd_1546247 : Nat := 529311947715144690134297

theorem tailTrace_1546247 : CollatzResearch.WordTrace tailWord_1546247 prefixEnd_1546247 529311947715144690134297 := by
  unfold tailWord_1546247
  simp only [CollatzResearch.WordTrace]
  refine ⟨56396261229218671808388995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37597507486145781205592663 56396261229218671808388995)
  ·
    refine ⟨84594391843828007712583493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56396261229218671808388995 84594391843828007712583493)
    ·
      refine ⟨15861448470717751446109405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84594391843828007712583493 15861448470717751446109405)
      ·
        refine ⟨5948043176519156792291027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15861448470717751446109405 5948043176519156792291027)
        ·
          refine ⟨8922064764778735188436541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948043176519156792291027 8922064764778735188436541)
          ·
            refine ⟨3345774286792025695663703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8922064764778735188436541 3345774286792025695663703)
            ·
              refine ⟨5018661430188038543495555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345774286792025695663703 5018661430188038543495555)
              ·
                refine ⟨7527992145282057815243333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018661430188038543495555 7527992145282057815243333)
                ·
                  refine ⟨1411498527240385840358125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7527992145282057815243333 1411498527240385840358125)
                  ·
                    refine ⟨529311947715144690134297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411498527240385840358125 529311947715144690134297)
                    ·
                      rfl

theorem cell22_1546247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_1546247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546247 prefixEnd_1546247 := by exact prefixLift 1546247
  have htrace : WordTrace (prefixWord ++ tailWord_1546247) baseStart_1546247 baseEnd_1546247 := by
    simpa [prefixWord, tailWord_1546247, baseEnd_1546247] using wordTrace_append hprefix tailTrace_1546247
  have hstable : (prefixWord ++ tailWord_1546247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546247).length < 2 ^ (prefixWord ++ tailWord_1546247).sum := by decide
  have hdescent : baseEnd_1546247 < baseStart_1546247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546264 : List Nat := [2, 1, 2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_1546264 : Nat := 118140960795 + 1546264 * 2 ^ 59
def prefixEnd_1546264 : Nat := 4983230072969 + 3 ^ 40 * 1546264 * 2
def baseEnd_1546264 : Nat := 529317767162562312459245

theorem tailTrace_1546264 : CollatzResearch.WordTrace tailWord_1546264 prefixEnd_1546264 529317767162562312459245 := by
  unfold tailWord_1546264
  simp only [CollatzResearch.WordTrace]
  refine ⟨28198440635078541855878923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37597920846771389141171897 28198440635078541855878923)
  ·
    refine ⟨42297660952617812783818385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28198440635078541855878923 42297660952617812783818385)
    ·
      refine ⟨31723245714463359587863789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42297660952617812783818385 31723245714463359587863789)
      ·
        refine ⟨11896217142923759845448921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31723245714463359587863789 11896217142923759845448921)
        ·
          refine ⟨8922162857192819884086691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11896217142923759845448921 8922162857192819884086691)
          ·
            refine ⟨13383244285789229826130037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8922162857192819884086691 13383244285789229826130037)
            ·
              refine ⟨1254679151792740296199691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13383244285789229826130037 1254679151792740296199691)
              ·
                refine ⟨1882018727689110444299537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254679151792740296199691 1882018727689110444299537)
                ·
                  refine ⟨1411514045766832833224653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882018727689110444299537 1411514045766832833224653)
                  ·
                    refine ⟨529317767162562312459245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411514045766832833224653 529317767162562312459245)
                    ·
                      rfl

theorem cell22_1546264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_1546264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546264 prefixEnd_1546264 := by exact prefixLift 1546264
  have htrace : WordTrace (prefixWord ++ tailWord_1546264) baseStart_1546264 baseEnd_1546264 := by
    simpa [prefixWord, tailWord_1546264, baseEnd_1546264] using wordTrace_append hprefix tailTrace_1546264
  have hstable : (prefixWord ++ tailWord_1546264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546264).length < 2 ^ (prefixWord ++ tailWord_1546264).sum := by decide
  have hdescent : baseEnd_1546264 < baseStart_1546264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546277 : List Nat := [1, 3, 1, 2, 2, 5, 2, 6]
def baseStart_1546277 : Nat := 118140960795 + 1546277 * 2 ^ 59
def prefixEnd_1546277 : Nat := 4983230072969 + 3 ^ 40 * 1546277 * 2
def baseEnd_1546277 : Nat := 58813579703137179098245

theorem tailTrace_1546277 : CollatzResearch.WordTrace tailWord_1546277 prefixEnd_1546277 58813579703137179098245 := by
  unfold tailWord_1546277
  simp only [CollatzResearch.WordTrace]
  refine ⟨56397355419109986931981085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37598236946073324621320723 56397355419109986931981085)
  ·
    refine ⟨21149008282166245099492907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56397355419109986931981085 21149008282166245099492907)
    ·
      refine ⟨31723512423249367649239361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21149008282166245099492907 31723512423249367649239361)
      ·
        refine ⟨23792634317437025736929521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31723512423249367649239361 23792634317437025736929521)
        ·
          refine ⟨17844475738077769302697141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23792634317437025736929521 17844475738077769302697141)
          ·
            refine ⟨1672919600444790872127857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17844475738077769302697141 1672919600444790872127857)
            ·
              refine ⟨1254689700333593154095893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672919600444790872127857 1254689700333593154095893)
              ·
                refine ⟨58813579703137179098245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1254689700333593154095893 58813579703137179098245)
                ·
                  rfl

theorem cell22_1546277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 6].length) (baseStart_1546277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546277 prefixEnd_1546277 := by exact prefixLift 1546277
  have htrace : WordTrace (prefixWord ++ tailWord_1546277) baseStart_1546277 baseEnd_1546277 := by
    simpa [prefixWord, tailWord_1546277, baseEnd_1546277] using wordTrace_append hprefix tailTrace_1546277
  have hstable : (prefixWord ++ tailWord_1546277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546277).length < 2 ^ (prefixWord ++ tailWord_1546277).sum := by decide
  have hdescent : baseEnd_1546277 < baseStart_1546277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546397 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1546397 : Nat := 118140960795 + 1546397 * 2 ^ 59
def prefixEnd_1546397 : Nat := 4983230072969 + 3 ^ 40 * 1546397 * 2
def baseEnd_1546397 : Nat := 529363295780594298883837

theorem tailTrace_1546397 : CollatzResearch.WordTrace tailWord_1546397 prefixEnd_1546397 529363295780594298883837 := by
  unfold tailWord_1546397
  simp only [CollatzResearch.WordTrace]
  refine ⟨56401732178675247426349445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37601154785783498284232963 56401732178675247426349445)
  ·
    refine ⟨10575324783501608892440521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56401732178675247426349445 10575324783501608892440521)
    ·
      refine ⟨7931493587626206669330391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10575324783501608892440521 7931493587626206669330391)
      ·
        refine ⟨11897240381439310003995587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7931493587626206669330391 11897240381439310003995587)
        ·
          refine ⟨17845860572158965005993381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11897240381439310003995587 17845860572158965005993381)
          ·
            refine ⟨3346098857279805938623759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17845860572158965005993381 3346098857279805938623759)
            ·
              refine ⟨5019148285919708907935639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346098857279805938623759 5019148285919708907935639)
              ·
                refine ⟨7528722428879563361903459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5019148285919708907935639 7528722428879563361903459)
                ·
                  refine ⟨11293083643319345042855189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528722428879563361903459 11293083643319345042855189)
                  ·
                    refine ⟨529363295780594298883837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11293083643319345042855189 529363295780594298883837)
                    ·
                      rfl

theorem cell22_1546397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1546397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546397 prefixEnd_1546397 := by exact prefixLift 1546397
  have htrace : WordTrace (prefixWord ++ tailWord_1546397) baseStart_1546397 baseEnd_1546397 := by
    simpa [prefixWord, tailWord_1546397, baseEnd_1546397] using wordTrace_append hprefix tailTrace_1546397
  have hstable : (prefixWord ++ tailWord_1546397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546397).length < 2 ^ (prefixWord ++ tailWord_1546397).sum := by decide
  have hdescent : baseEnd_1546397 < baseStart_1546397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546433 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1546433 : Nat := 118140960795 + 1546433 * 2 ^ 59
def prefixEnd_1546433 : Nat := 4983230072969 + 3 ^ 40 * 1546433 * 2
def baseEnd_1546433 : Nat := 529375619316302204983727

theorem tailTrace_1546433 : CollatzResearch.WordTrace tailWord_1546433 prefixEnd_1546433 529375619316302204983727 := by
  unfold tailWord_1546433
  simp only [CollatzResearch.WordTrace]
  refine ⟨56403045206544825574659953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37602030137696550383106635 56403045206544825574659953)
  ·
    refine ⟨42302283904908619180994965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56403045206544825574659953 42302283904908619180994965)
    ·
      refine ⟨1982919558042591524109139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42302283904908619180994965 1982919558042591524109139)
      ·
        refine ⟨2974379337063887286163709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982919558042591524109139 2974379337063887286163709)
        ·
          refine ⟨1115392251398957732311391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2974379337063887286163709 1115392251398957732311391)
          ·
            refine ⟨1673088377098436598467087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115392251398957732311391 1673088377098436598467087)
            ·
              refine ⟨2509632565647654897700631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673088377098436598467087 2509632565647654897700631)
              ·
                refine ⟨3764448848471482346550947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509632565647654897700631 3764448848471482346550947)
                ·
                  refine ⟨5646673272707223519826421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764448848471482346550947 5646673272707223519826421)
                  ·
                    refine ⟨529375619316302204983727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5646673272707223519826421 529375619316302204983727)
                    ·
                      rfl

theorem cell22_1546433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1546433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546433 prefixEnd_1546433 := by exact prefixLift 1546433
  have htrace : WordTrace (prefixWord ++ tailWord_1546433) baseStart_1546433 baseEnd_1546433 := by
    simpa [prefixWord, tailWord_1546433, baseEnd_1546433] using wordTrace_append hprefix tailTrace_1546433
  have hstable : (prefixWord ++ tailWord_1546433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546433).length < 2 ^ (prefixWord ++ tailWord_1546433).sum := by decide
  have hdescent : baseEnd_1546433 < baseStart_1546433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546504 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_1546504 : Nat := 118140960795 + 1546504 * 2 ^ 59
def prefixEnd_1546504 : Nat := 4983230072969 + 3 ^ 40 * 1546504 * 2
def baseEnd_1546504 : Nat := 529399924067281686458509

theorem tailTrace_1546504 : CollatzResearch.WordTrace tailWord_1546504 prefixEnd_1546504 529399924067281686458509 := by
  unfold tailWord_1546504
  simp only [CollatzResearch.WordTrace]
  refine ⟨28202817394643802350247283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37603756526191736466996377 28202817394643802350247283)
  ·
    refine ⟨42304226091965703525370925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28202817394643802350247283 42304226091965703525370925)
    ·
      refine ⟨15864084784487138822014097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42304226091965703525370925 15864084784487138822014097)
      ·
        refine ⟨11898063588365354116510573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15864084784487138822014097 11898063588365354116510573)
        ·
          refine ⟨4461773845637007793691465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11898063588365354116510573 4461773845637007793691465)
          ·
            refine ⟨3346330384227755845268599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4461773845637007793691465 3346330384227755845268599)
            ·
              refine ⟨5019495576341633767902899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346330384227755845268599 5019495576341633767902899)
              ·
                refine ⟨7529243364512450651854349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5019495576341633767902899 7529243364512450651854349)
                ·
                  refine ⟨2823466261692168994445381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7529243364512450651854349 2823466261692168994445381)
                  ·
                    refine ⟨529399924067281686458509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2823466261692168994445381 529399924067281686458509)
                    ·
                      rfl

theorem cell22_1546504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_1546504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546504 prefixEnd_1546504 := by exact prefixLift 1546504
  have htrace : WordTrace (prefixWord ++ tailWord_1546504) baseStart_1546504 baseEnd_1546504 := by
    simpa [prefixWord, tailWord_1546504, baseEnd_1546504] using wordTrace_append hprefix tailTrace_1546504
  have hstable : (prefixWord ++ tailWord_1546504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546504).length < 2 ^ (prefixWord ++ tailWord_1546504).sum := by decide
  have hdescent : baseEnd_1546504 < baseStart_1546504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546517 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1546517 : Nat := 118140960795 + 1546517 * 2 ^ 59
def prefixEnd_1546517 : Nat := 4983230072969 + 3 ^ 40 * 1546517 * 2
def baseEnd_1546517 : Nat := 529404374232953985883469

theorem tailTrace_1546517 : CollatzResearch.WordTrace tailWord_1546517 prefixEnd_1546517 529404374232953985883469 := by
  unfold tailWord_1546517
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406108938240507920717805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37604072625493671947145203 56406108938240507920717805)
  ·
    refine ⟨21152290851840190470269177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56406108938240507920717805 21152290851840190470269177)
    ·
      refine ⟨15864218138880142852701883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21152290851840190470269177 15864218138880142852701883)
      ·
        refine ⟨23796327208320214279052825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15864218138880142852701883 23796327208320214279052825)
        ·
          refine ⟨17847245406240160709289619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23796327208320214279052825 17847245406240160709289619)
          ·
            refine ⟨26770868109360241063934429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17847245406240160709289619 26770868109360241063934429)
            ·
              refine ⟨10039075541010090398975411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26770868109360241063934429 10039075541010090398975411)
              ·
                refine ⟨15058613311515135598463117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039075541010090398975411 15058613311515135598463117)
                ·
                  refine ⟨5646979991818175849423669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15058613311515135598463117 5646979991818175849423669)
                  ·
                    refine ⟨529404374232953985883469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5646979991818175849423669 529404374232953985883469)
                    ·
                      rfl

theorem cell22_1546517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1546517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546517 prefixEnd_1546517 := by exact prefixLift 1546517
  have htrace : WordTrace (prefixWord ++ tailWord_1546517) baseStart_1546517 baseEnd_1546517 := by
    simpa [prefixWord, tailWord_1546517, baseEnd_1546517] using wordTrace_append hprefix tailTrace_1546517
  have hstable : (prefixWord ++ tailWord_1546517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546517).length < 2 ^ (prefixWord ++ tailWord_1546517).sum := by decide
  have hdescent : baseEnd_1546517 < baseStart_1546517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546596 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1546596 : Nat := 118140960795 + 1546596 * 2 ^ 59
def prefixEnd_1546596 : Nat := 4983230072969 + 3 ^ 40 * 1546596 * 2
def baseEnd_1546596 : Nat := 529431417547424113158227

theorem tailTrace_1546596 : CollatzResearch.WordTrace tailWord_1546596 prefixEnd_1546596 529431417547424113158227 := by
  unfold tailWord_1546596
  simp only [CollatzResearch.WordTrace]
  refine ⟨28204495152477152206421821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37605993536636202941895761 28204495152477152206421821)
  ·
    refine ⟨10576685682178932077408183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28204495152477152206421821 10576685682178932077408183)
    ·
      refine ⟨15865028523268398116112275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576685682178932077408183 15865028523268398116112275)
      ·
        refine ⟨23797542784902597174168413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15865028523268398116112275 23797542784902597174168413)
        ·
          refine ⟨8924078544338473940313155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23797542784902597174168413 8924078544338473940313155)
          ·
            refine ⟨13386117816507710910469733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8924078544338473940313155 13386117816507710910469733)
            ·
              refine ⟨2509897090595195795713075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13386117816507710910469733 2509897090595195795713075)
              ·
                refine ⟨3764845635892793693569613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509897090595195795713075 3764845635892793693569613)
                ·
                  refine ⟨1411817113459797635088605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3764845635892793693569613 1411817113459797635088605)
                  ·
                    refine ⟨529431417547424113158227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411817113459797635088605 529431417547424113158227)
                    ·
                      rfl

theorem cell22_1546596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1546596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546596 prefixEnd_1546596 := by exact prefixLift 1546596
  have htrace : WordTrace (prefixWord ++ tailWord_1546596) baseStart_1546596 baseEnd_1546596 := by
    simpa [prefixWord, tailWord_1546596, baseEnd_1546596] using wordTrace_append hprefix tailTrace_1546596
  have hstable : (prefixWord ++ tailWord_1546596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546596).length < 2 ^ (prefixWord ++ tailWord_1546596).sum := by decide
  have hdescent : baseEnd_1546596 < baseStart_1546596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546607 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1546607 : Nat := 118140960795 + 1546607 * 2 ^ 59
def prefixEnd_1546607 : Nat := 4983230072969 + 3 ^ 40 * 1546607 * 2
def baseEnd_1546607 : Nat := 529435183072223751133193

theorem tailTrace_1546607 : CollatzResearch.WordTrace tailWord_1546607 prefixEnd_1546607 529435183072223751133193 := by
  unfold tailWord_1546607
  simp only [CollatzResearch.WordTrace]
  refine ⟨56409391507914453291494075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37606261005276302194329383 56409391507914453291494075)
  ·
    refine ⟨84614087261871679937241113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56409391507914453291494075 84614087261871679937241113)
    ·
      refine ⟨63460565446403759952930835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84614087261871679937241113 63460565446403759952930835)
      ·
        refine ⟨95190848169605639929396253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63460565446403759952930835 95190848169605639929396253)
        ·
          refine ⟨35696568063602114973523595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95190848169605639929396253 35696568063602114973523595)
          ·
            refine ⟨53544852095403172460285393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35696568063602114973523595 53544852095403172460285393)
            ·
              refine ⟨40158639071552379345214045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53544852095403172460285393 40158639071552379345214045)
              ·
                refine ⟨15059489651832142254455267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40158639071552379345214045 15059489651832142254455267)
                ·
                  refine ⟨22589234477748213381682901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15059489651832142254455267 22589234477748213381682901)
                  ·
                    refine ⟨529435183072223751133193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22589234477748213381682901 529435183072223751133193)
                    ·
                      rfl

theorem cell22_1546607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1546607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546607 prefixEnd_1546607 := by exact prefixLift 1546607
  have htrace : WordTrace (prefixWord ++ tailWord_1546607) baseStart_1546607 baseEnd_1546607 := by
    simpa [prefixWord, tailWord_1546607, baseEnd_1546607] using wordTrace_append hprefix tailTrace_1546607
  have hstable : (prefixWord ++ tailWord_1546607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546607).length < 2 ^ (prefixWord ++ tailWord_1546607).sum := by decide
  have hdescent : baseEnd_1546607 < baseStart_1546607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546673 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_1546673 : Nat := 118140960795 + 1546673 * 2 ^ 59
def prefixEnd_1546673 : Nat := 4983230072969 + 3 ^ 40 * 1546673 * 2
def baseEnd_1546673 : Nat := 529457776221021578982991

theorem tailTrace_1546673 : CollatzResearch.WordTrace tailWord_1546673 prefixEnd_1546673 529457776221021578982991 := by
  unfold tailWord_1546673
  simp only [CollatzResearch.WordTrace]
  refine ⟨56411798725675346563396673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37607865817116897708931115 56411798725675346563396673)
  ·
    refine ⟨42308849044256509922547505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56411798725675346563396673 42308849044256509922547505)
    ·
      refine ⟨31731636783192382441910629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42308849044256509922547505 31731636783192382441910629)
      ·
        refine ⟨5949681896848571707858243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31731636783192382441910629 5949681896848571707858243)
        ·
          refine ⟨8924522845272857561787365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949681896848571707858243 8924522845272857561787365)
          ·
            refine ⟨1673348033488660792835131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8924522845272857561787365 1673348033488660792835131)
            ·
              refine ⟨2510022050232991189252697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673348033488660792835131 2510022050232991189252697)
              ·
                refine ⟨1882516537674743391939523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510022050232991189252697 1882516537674743391939523)
                ·
                  refine ⟨2823774806512115087909285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882516537674743391939523 2823774806512115087909285)
                  ·
                    refine ⟨529457776221021578982991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2823774806512115087909285 529457776221021578982991)
                    ·
                      rfl

theorem cell22_1546673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_1546673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546673 prefixEnd_1546673 := by exact prefixLift 1546673
  have htrace : WordTrace (prefixWord ++ tailWord_1546673) baseStart_1546673 baseEnd_1546673 := by
    simpa [prefixWord, tailWord_1546673, baseEnd_1546673] using wordTrace_append hprefix tailTrace_1546673
  have hstable : (prefixWord ++ tailWord_1546673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546673).length < 2 ^ (prefixWord ++ tailWord_1546673).sum := by decide
  have hdescent : baseEnd_1546673 < baseStart_1546673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546686 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_1546686 : Nat := 118140960795 + 1546686 * 2 ^ 59
def prefixEnd_1546686 : Nat := 4983230072969 + 3 ^ 40 * 1546686 * 2
def baseEnd_1546686 : Nat := 529462226386693878407951

theorem tailTrace_1546686 : CollatzResearch.WordTrace tailWord_1546686 prefixEnd_1546686 529462226386693878407951 := by
  unfold tailWord_1546686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051534109328531222952489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37608181916418833189079941 7051534109328531222952489)
  ·
    refine ⟨5288650581996398417214367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7051534109328531222952489 5288650581996398417214367)
    ·
      refine ⟨7932975872994597625821551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288650581996398417214367 7932975872994597625821551)
      ·
        refine ⟨11899463809491896438732327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932975872994597625821551 11899463809491896438732327)
        ·
          refine ⟨17849195714237844658098491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11899463809491896438732327 17849195714237844658098491)
          ·
            refine ⟨26773793571356766987147737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849195714237844658098491 26773793571356766987147737)
            ·
              refine ⟨20080345178517575240360803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26773793571356766987147737 20080345178517575240360803)
              ·
                refine ⟨30120517767776362860541205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20080345178517575240360803 30120517767776362860541205)
                ·
                  refine ⟨1411899270364517009087869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30120517767776362860541205 1411899270364517009087869)
                  ·
                    refine ⟨529462226386693878407951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411899270364517009087869 529462226386693878407951)
                    ·
                      rfl

theorem cell22_1546686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_1546686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546686 prefixEnd_1546686 := by exact prefixLift 1546686
  have htrace : WordTrace (prefixWord ++ tailWord_1546686) baseStart_1546686 baseEnd_1546686 := by
    simpa [prefixWord, tailWord_1546686, baseEnd_1546686] using wordTrace_append hprefix tailTrace_1546686
  have hstable : (prefixWord ++ tailWord_1546686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546686).length < 2 ^ (prefixWord ++ tailWord_1546686).sum := by decide
  have hdescent : baseEnd_1546686 < baseStart_1546686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546731 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 3, 3]
def baseStart_1546731 : Nat := 118140960795 + 1546731 * 2 ^ 59
def prefixEnd_1546731 : Nat := 4983230072969 + 3 ^ 40 * 1546731 * 2
def baseEnd_1546731 : Nat := 529477630806328761032813

theorem tailTrace_1546731 : CollatzResearch.WordTrace tailWord_1546731 prefixEnd_1546731 529477630806328761032813 := by
  unfold tailWord_1546731
  simp only [CollatzResearch.WordTrace]
  refine ⟨56413914159465222469008047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37609276106310148312672031 56413914159465222469008047)
  ·
    refine ⟨84620871239197833703512071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56413914159465222469008047 84620871239197833703512071)
    ·
      refine ⟨126931306858796750555268107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84620871239197833703512071 126931306858796750555268107)
      ·
        refine ⟨190396960288195125832902161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126931306858796750555268107 190396960288195125832902161)
        ·
          refine ⟨142797720216146344374676621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190396960288195125832902161 142797720216146344374676621)
          ·
            refine ⟨53549145081054879140503733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142797720216146344374676621 53549145081054879140503733)
            ·
              refine ⟨5020232351348894919422225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53549145081054879140503733 5020232351348894919422225)
              ·
                refine ⟨3765174263511671189566669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020232351348894919422225 3765174263511671189566669)
                ·
                  refine ⟨1411940348816876696087501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3765174263511671189566669 1411940348816876696087501)
                  ·
                    refine ⟨529477630806328761032813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411940348816876696087501 529477630806328761032813)
                    ·
                      rfl

theorem cell22_1546731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 3, 3].length) (baseStart_1546731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546731 prefixEnd_1546731 := by exact prefixLift 1546731
  have htrace : WordTrace (prefixWord ++ tailWord_1546731) baseStart_1546731 baseEnd_1546731 := by
    simpa [prefixWord, tailWord_1546731, baseEnd_1546731] using wordTrace_append hprefix tailTrace_1546731
  have hstable : (prefixWord ++ tailWord_1546731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546731).length < 2 ^ (prefixWord ++ tailWord_1546731).sum := by decide
  have hdescent : baseEnd_1546731 < baseStart_1546731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546733 : List Nat := [1, 5, 1, 3, 1, 2, 3, 6]
def baseStart_1546733 : Nat := 118140960795 + 1546733 * 2 ^ 59
def prefixEnd_1546733 : Nat := 4983230072969 + 3 ^ 40 * 1546733 * 2
def baseEnd_1546733 : Nat := 58830923938577935831423

theorem tailTrace_1546733 : CollatzResearch.WordTrace tailWord_1546733 prefixEnd_1546733 58830923938577935831423 := by
  unfold tailWord_1546733
  simp only [CollatzResearch.WordTrace]
  refine ⟨56413987105457976810580853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37609324736971984540387235 56413987105457976810580853)
  ·
    refine ⟨5288811291136685325991955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56413987105457976810580853 5288811291136685325991955)
    ·
      refine ⟨7933216936705027988987933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288811291136685325991955 7933216936705027988987933)
      ·
        refine ⟨2974956351264385495870475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7933216936705027988987933 2974956351264385495870475)
        ·
          refine ⟨4462434526896578243805713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974956351264385495870475 4462434526896578243805713)
          ·
            refine ⟨3346825895172433682854285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4462434526896578243805713 3346825895172433682854285)
            ·
              refine ⟨1255059710689662631070357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3346825895172433682854285 1255059710689662631070357)
              ·
                refine ⟨58830923938577935831423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1255059710689662631070357 58830923938577935831423)
                ·
                  rfl

theorem cell22_1546733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 6].length) (baseStart_1546733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546733 prefixEnd_1546733 := by exact prefixLift 1546733
  have htrace : WordTrace (prefixWord ++ tailWord_1546733) baseStart_1546733 baseEnd_1546733 := by
    simpa [prefixWord, tailWord_1546733, baseEnd_1546733] using wordTrace_append hprefix tailTrace_1546733
  have hstable : (prefixWord ++ tailWord_1546733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546733).length < 2 ^ (prefixWord ++ tailWord_1546733).sum := by decide
  have hdescent : baseEnd_1546733 < baseStart_1546733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546744 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_1546744 : Nat := 118140960795 + 1546744 * 2 ^ 59
def prefixEnd_1546744 : Nat := 4983230072969 + 3 ^ 40 * 1546744 * 2
def baseEnd_1546744 : Nat := 176494026990667020152591

theorem tailTrace_1546744 : CollatzResearch.WordTrace tailWord_1546744 prefixEnd_1546744 176494026990667020152591 := by
  unfold tailWord_1546744
  simp only [CollatzResearch.WordTrace]
  refine ⟨28207194154209062844615643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37609592205612083792820857 28207194154209062844615643)
  ·
    refine ⟨42310791231313594266923465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28207194154209062844615643 42310791231313594266923465)
    ·
      refine ⟨31733093423485195700192599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42310791231313594266923465 31733093423485195700192599)
      ·
        refine ⟨47599640135227793550288899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31733093423485195700192599 47599640135227793550288899)
        ·
          refine ⟨71399460202841690325433349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47599640135227793550288899 71399460202841690325433349)
          ·
            refine ⟨13387398788032816936018753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71399460202841690325433349 13387398788032816936018753)
            ·
              refine ⟨10040549091024612702014065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13387398788032816936018753 10040549091024612702014065)
              ·
                refine ⟨7530411818268459526510549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10040549091024612702014065 7530411818268459526510549)
                ·
                  refine ⟨176494026990667020152591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7530411818268459526510549 176494026990667020152591)
                  ·
                    rfl

theorem cell22_1546744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_1546744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546744 prefixEnd_1546744 := by exact prefixLift 1546744
  have htrace : WordTrace (prefixWord ++ tailWord_1546744) baseStart_1546744 baseEnd_1546744 := by
    simpa [prefixWord, tailWord_1546744, baseEnd_1546744] using wordTrace_append hprefix tailTrace_1546744
  have hstable : (prefixWord ++ tailWord_1546744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546744).length < 2 ^ (prefixWord ++ tailWord_1546744).sum := by decide
  have hdescent : baseEnd_1546744 < baseStart_1546744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546754 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_1546754 : Nat := 118140960795 + 1546754 * 2 ^ 59
def prefixEnd_1546754 : Nat := 4983230072969 + 3 ^ 40 * 1546754 * 2
def baseEnd_1546754 : Nat := 529485504176364367707743

theorem tailTrace_1546754 : CollatzResearch.WordTrace tailWord_1546754 prefixEnd_1546754 529485504176364367707743 := by
  unfold tailWord_1546754
  simp only [CollatzResearch.WordTrace]
  refine ⟨14103688259595474349273829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37609835358921264931396877 14103688259595474349273829)
  ·
    refine ⟨2644441548674151440488843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14103688259595474349273829 2644441548674151440488843)
    ·
      refine ⟨3966662323011227160733265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644441548674151440488843 3966662323011227160733265)
      ·
        refine ⟨2974996742258420370549949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3966662323011227160733265 2974996742258420370549949)
        ·
          refine ⟨1115623778346907638956231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2974996742258420370549949 1115623778346907638956231)
          ·
            refine ⟨1673435667520361458434347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115623778346907638956231 1673435667520361458434347)
            ·
              refine ⟨2510153501280542187651521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673435667520361458434347 2510153501280542187651521)
              ·
                refine ⟨1882615125960406640738641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510153501280542187651521 1882615125960406640738641)
                ·
                  refine ⟨1411961344470304980553981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1882615125960406640738641 1411961344470304980553981)
                  ·
                    refine ⟨529485504176364367707743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1411961344470304980553981 529485504176364367707743)
                    ·
                      rfl

theorem cell22_1546754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_1546754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546754 prefixEnd_1546754 := by exact prefixLift 1546754
  have htrace : WordTrace (prefixWord ++ tailWord_1546754) baseStart_1546754 baseEnd_1546754 := by
    simpa [prefixWord, tailWord_1546754, baseEnd_1546754] using wordTrace_append hprefix tailTrace_1546754
  have hstable : (prefixWord ++ tailWord_1546754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546754).length < 2 ^ (prefixWord ++ tailWord_1546754).sum := by decide
  have hdescent : baseEnd_1546754 < baseStart_1546754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546776 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1546776 : Nat := 118140960795 + 1546776 * 2 ^ 59
def prefixEnd_1546776 : Nat := 4983230072969 + 3 ^ 40 * 1546776 * 2
def baseEnd_1546776 : Nat := 529493035225963643657675

theorem tailTrace_1546776 : CollatzResearch.WordTrace tailWord_1546776 prefixEnd_1546776 529493035225963643657675 := by
  unfold tailWord_1546776
  simp only [CollatzResearch.WordTrace]
  refine ⟨28207777722151097577198091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37610370296201463436264121 28207777722151097577198091)
  ·
    refine ⟨42311666583226646365797137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28207777722151097577198091 42311666583226646365797137)
    ·
      refine ⟨31733749937419984774347853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42311666583226646365797137 31733749937419984774347853)
      ·
        refine ⟨11900156226532494290380445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31733749937419984774347853 11900156226532494290380445)
        ·
          refine ⟨4462558584949685358892667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11900156226532494290380445 4462558584949685358892667)
          ·
            refine ⟨6693837877424528038339001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462558584949685358892667 6693837877424528038339001)
            ·
              refine ⟨5020378408068396028754251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6693837877424528038339001 5020378408068396028754251)
              ·
                refine ⟨7530567612102594043131377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020378408068396028754251 7530567612102594043131377)
                ·
                  refine ⟨5647925709076945532348533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7530567612102594043131377 5647925709076945532348533)
                  ·
                    refine ⟨529493035225963643657675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5647925709076945532348533 529493035225963643657675)
                    ·
                      rfl

theorem cell22_1546776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1546776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546776 prefixEnd_1546776 := by exact prefixLift 1546776
  have htrace : WordTrace (prefixWord ++ tailWord_1546776) baseStart_1546776 baseEnd_1546776 := by
    simpa [prefixWord, tailWord_1546776, baseEnd_1546776] using wordTrace_append hprefix tailTrace_1546776
  have hstable : (prefixWord ++ tailWord_1546776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546776).length < 2 ^ (prefixWord ++ tailWord_1546776).sum := by decide
  have hdescent : baseEnd_1546776 < baseStart_1546776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546823 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 6]
def baseStart_1546823 : Nat := 118140960795 + 1546823 * 2 ^ 59
def prefixEnd_1546823 : Nat := 4983230072969 + 3 ^ 40 * 1546823 * 2
def baseEnd_1546823 : Nat := 176503041428823729244177

theorem tailTrace_1546823 : CollatzResearch.WordTrace tailWord_1546823 prefixEnd_1546823 176503041428823729244177 := by
  unfold tailWord_1546823
  simp only [CollatzResearch.WordTrace]
  refine ⟨56417269675131922181357123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37611513116754614787571415 56417269675131922181357123)
  ·
    refine ⟨84625904512697883272035685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56417269675131922181357123 84625904512697883272035685)
    ·
      refine ⟨15867357096130853113506691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84625904512697883272035685 15867357096130853113506691)
      ·
        refine ⟨23801035644196279670260037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15867357096130853113506691 23801035644196279670260037)
        ·
          refine ⟨4462694183286802438173757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23801035644196279670260037 4462694183286802438173757)
          ·
            refine ⟨1673510318732550914315159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4462694183286802438173757 1673510318732550914315159)
            ·
              refine ⟨2510265478098826371472739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673510318732550914315159 2510265478098826371472739)
              ·
                refine ⟨3765398217148239557209109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510265478098826371472739 3765398217148239557209109)
                ·
                  refine ⟨176503041428823729244177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3765398217148239557209109 176503041428823729244177)
                  ·
                    rfl

theorem cell22_1546823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 6].length) (baseStart_1546823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546823 prefixEnd_1546823 := by exact prefixLift 1546823
  have htrace : WordTrace (prefixWord ++ tailWord_1546823) baseStart_1546823 baseEnd_1546823 := by
    simpa [prefixWord, tailWord_1546823, baseEnd_1546823] using wordTrace_append hprefix tailTrace_1546823
  have hstable : (prefixWord ++ tailWord_1546823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546823).length < 2 ^ (prefixWord ++ tailWord_1546823).sum := by decide
  have hdescent : baseEnd_1546823 < baseStart_1546823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546881 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1546881 : Nat := 118140960795 + 1546881 * 2 ^ 59
def prefixEnd_1546881 : Nat := 4983230072969 + 3 ^ 40 * 1546881 * 2
def baseEnd_1546881 : Nat := 529528978871778369782353

theorem tailTrace_1546881 : CollatzResearch.WordTrace tailWord_1546881 prefixEnd_1546881 529528978871778369782353 := by
  unfold tailWord_1546881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56419385108921798086968497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37612923405947865391312331 56419385108921798086968497)
  ·
    refine ⟨42314538831691348565226373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56419385108921798086968497 42314538831691348565226373)
    ·
      refine ⟨7933976030942127855979945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42314538831691348565226373 7933976030942127855979945)
      ·
        refine ⟨5950482023206595891984959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7933976030942127855979945 5950482023206595891984959)
        ·
          refine ⟨8925723034809893837977439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950482023206595891984959 8925723034809893837977439)
          ·
            refine ⟨13388584552214840756966159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925723034809893837977439 13388584552214840756966159)
            ·
              refine ⟨20082876828322261135449239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13388584552214840756966159 20082876828322261135449239)
              ·
                refine ⟨30124315242483391703173859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20082876828322261135449239 30124315242483391703173859)
                ·
                  refine ⟨45186472863725087554760789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30124315242483391703173859 45186472863725087554760789)
                  ·
                    refine ⟨529528978871778369782353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45186472863725087554760789 529528978871778369782353)
                    ·
                      rfl

theorem cell22_1546881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1546881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546881 prefixEnd_1546881 := by exact prefixLift 1546881
  have htrace : WordTrace (prefixWord ++ tailWord_1546881) baseStart_1546881 baseEnd_1546881 := by
    simpa [prefixWord, tailWord_1546881, baseEnd_1546881] using wordTrace_append hprefix tailTrace_1546881
  have hstable : (prefixWord ++ tailWord_1546881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546881).length < 2 ^ (prefixWord ++ tailWord_1546881).sum := by decide
  have hdescent : baseEnd_1546881 < baseStart_1546881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546900 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1546900 : Nat := 118140960795 + 1546900 * 2 ^ 59
def prefixEnd_1546900 : Nat := 4983230072969 + 3 ^ 40 * 1546900 * 2
def baseEnd_1546900 : Nat := 529535482960068653557295

theorem tailTrace_1546900 : CollatzResearch.WordTrace tailWord_1546900 prefixEnd_1546900 529535482960068653557295 := by
  unfold tailWord_1546900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28210039047926482165955077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37613385397235309554606769 28210039047926482165955077)
  ·
    refine ⟨5289382321486215406116577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28210039047926482165955077 5289382321486215406116577)
    ·
      refine ⟨3967036741114661554587433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5289382321486215406116577 3967036741114661554587433)
      ·
        refine ⟨2975277555835996165940575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3967036741114661554587433 2975277555835996165940575)
        ·
          refine ⟨4462916333753994248910863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975277555835996165940575 4462916333753994248910863)
          ·
            refine ⟨6694374500630991373366295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462916333753994248910863 6694374500630991373366295)
            ·
              refine ⟨10041561750946487060049443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694374500630991373366295 10041561750946487060049443)
              ·
                refine ⟨15062342626419730590074165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041561750946487060049443 15062342626419730590074165)
                ·
                  refine ⟨1412094621226849742819453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15062342626419730590074165 1412094621226849742819453)
                  ·
                    refine ⟨529535482960068653557295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412094621226849742819453 529535482960068653557295)
                    ·
                      rfl

theorem cell22_1546900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1546900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546900 prefixEnd_1546900 := by exact prefixLift 1546900
  have htrace : WordTrace (prefixWord ++ tailWord_1546900) baseStart_1546900 baseEnd_1546900 := by
    simpa [prefixWord, tailWord_1546900, baseEnd_1546900] using wordTrace_append hprefix tailTrace_1546900
  have hstable : (prefixWord ++ tailWord_1546900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546900).length < 2 ^ (prefixWord ++ tailWord_1546900).sum := by decide
  have hdescent : baseEnd_1546900 < baseStart_1546900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546934 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1546934 : Nat := 118140960795 + 1546934 * 2 ^ 59
def prefixEnd_1546934 : Nat := 4983230072969 + 3 ^ 40 * 1546934 * 2
def baseEnd_1546934 : Nat := 529547121854903898207191

theorem tailTrace_1546934 : CollatzResearch.WordTrace tailWord_1546934 prefixEnd_1546934 529547121854903898207191 := by
  unfold tailWord_1546934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526332386108111758665491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37614212118486525425765237 3526332386108111758665491)
  ·
    refine ⟨5289498579162167637998237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3526332386108111758665491 5289498579162167637998237)
    ·
      refine ⟨1983561967185812864249339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5289498579162167637998237 1983561967185812864249339)
      ·
        refine ⟨2975342950778719296374009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983561967185812864249339 2975342950778719296374009)
        ·
          refine ⟨2231507213084039472280507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2975342950778719296374009 2231507213084039472280507)
          ·
            refine ⟨3347260819626059208420761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231507213084039472280507 3347260819626059208420761)
            ·
              refine ⟨2510445614719544406315571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347260819626059208420761 2510445614719544406315571)
              ·
                refine ⟨3765668422079316609473357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510445614719544406315571 3765668422079316609473357)
                ·
                  refine ⟨1412125658279743728552509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3765668422079316609473357 1412125658279743728552509)
                  ·
                    refine ⟨529547121854903898207191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412125658279743728552509 529547121854903898207191)
                    ·
                      rfl

theorem cell22_1546934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1546934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546934 prefixEnd_1546934 := by exact prefixLift 1546934
  have htrace : WordTrace (prefixWord ++ tailWord_1546934) baseStart_1546934 baseEnd_1546934 := by
    simpa [prefixWord, tailWord_1546934, baseEnd_1546934] using wordTrace_append hprefix tailTrace_1546934
  have hstable : (prefixWord ++ tailWord_1546934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546934).length < 2 ^ (prefixWord ++ tailWord_1546934).sum := by decide
  have hdescent : baseEnd_1546934 < baseStart_1546934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546958 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1546958 : Nat := 118140960795 + 1546958 * 2 ^ 59
def prefixEnd_1546958 : Nat := 4983230072969 + 3 ^ 40 * 1546958 * 2
def baseEnd_1546958 : Nat := 176518445848458611869039

theorem tailTrace_1546958 : CollatzResearch.WordTrace tailWord_1546958 prefixEnd_1546958 176518445848458611869039 := by
  unfold tailWord_1546958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052774191205355029690191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37614795686428560158347685 7052774191205355029690191)
  ·
    refine ⟨10579161286808032544535287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7052774191205355029690191 10579161286808032544535287)
    ·
      refine ⟨15868741930212048816802931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10579161286808032544535287 15868741930212048816802931)
      ·
        refine ⟨23803112895318073225204397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15868741930212048816802931 23803112895318073225204397)
        ·
          refine ⟨8926167335744277459451649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23803112895318073225204397 8926167335744277459451649)
          ·
            refine ⟨6694625501808208094588737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8926167335744277459451649 6694625501808208094588737)
            ·
              refine ⟨5020969126356156070941553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6694625501808208094588737 5020969126356156070941553)
              ·
                refine ⟨3765726844767117053206165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5020969126356156070941553 3765726844767117053206165)
                ·
                  refine ⟨176518445848458611869039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3765726844767117053206165 176518445848458611869039)
                  ·
                    rfl

theorem cell22_1546958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1546958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546958 prefixEnd_1546958 := by exact prefixLift 1546958
  have htrace : WordTrace (prefixWord ++ tailWord_1546958) baseStart_1546958 baseEnd_1546958 := by
    simpa [prefixWord, tailWord_1546958, baseEnd_1546958] using wordTrace_append hprefix tailTrace_1546958
  have hstable : (prefixWord ++ tailWord_1546958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546958).length < 2 ^ (prefixWord ++ tailWord_1546958).sum := by decide
  have hdescent : baseEnd_1546958 < baseStart_1546958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546975 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 4]
def baseStart_1546975 : Nat := 118140960795 + 1546975 * 2 ^ 59
def prefixEnd_1546975 : Nat := 4983230072969 + 3 ^ 40 * 1546975 * 2
def baseEnd_1546975 : Nat := 176520385664264485977355

theorem tailTrace_1546975 : CollatzResearch.WordTrace tailWord_1546975 prefixEnd_1546975 176520385664264485977355 := by
  unfold tailWord_1546975
  simp only [CollatzResearch.WordTrace]
  refine ⟨56422813570581252140890379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37615209047054168093926919 56422813570581252140890379)
  ·
    refine ⟨84634220355871878211335569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56422813570581252140890379 84634220355871878211335569)
    ·
      refine ⟨63475665266903908658501677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84634220355871878211335569 63475665266903908658501677)
      ·
        refine ⟨23803374475088965746938129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63475665266903908658501677 23803374475088965746938129)
        ·
          refine ⟨17852530856316724310203597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23803374475088965746938129 17852530856316724310203597)
          ·
            refine ⟨6694699071118771616326349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17852530856316724310203597 6694699071118771616326349)
            ·
              refine ⟨2510512151669539356122381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6694699071118771616326349 2510512151669539356122381)
              ·
                refine ⟨941442056876077258545893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510512151669539356122381 941442056876077258545893)
                ·
                  refine ⟨176520385664264485977355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941442056876077258545893 176520385664264485977355)
                  ·
                    rfl

theorem cell22_1546975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 4].length) (baseStart_1546975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546975 prefixEnd_1546975 := by exact prefixLift 1546975
  have htrace : WordTrace (prefixWord ++ tailWord_1546975) baseStart_1546975 baseEnd_1546975 := by
    simpa [prefixWord, tailWord_1546975, baseEnd_1546975] using wordTrace_append hprefix tailTrace_1546975
  have hstable : (prefixWord ++ tailWord_1546975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546975).length < 2 ^ (prefixWord ++ tailWord_1546975).sum := by decide
  have hdescent : baseEnd_1546975 < baseStart_1546975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1546990 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1546990 : Nat := 118140960795 + 1546990 * 2 ^ 59
def prefixEnd_1546990 : Nat := 4983230072969 + 3 ^ 40 * 1546990 * 2
def baseEnd_1546990 : Nat := 529566291799338418807019

theorem tailTrace_1546990 : CollatzResearch.WordTrace tailWord_1546990 prefixEnd_1546990 529566291799338418807019 := by
  unfold tailWord_1546990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052920083190863712835803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37615573777017939801790949 7052920083190863712835803)
  ·
    refine ⟨10579380124786295569253705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7052920083190863712835803 10579380124786295569253705)
    ·
      refine ⟨7934535093589721676940279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10579380124786295569253705 7934535093589721676940279)
      ·
        refine ⟨11901802640384582515410419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7934535093589721676940279 11901802640384582515410419)
        ·
          refine ⟨17852703960576873773115629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11901802640384582515410419 17852703960576873773115629)
          ·
            refine ⟨6694763985216327664918361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17852703960576873773115629 6694763985216327664918361)
            ·
              refine ⟨5021072988912245748688771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6694763985216327664918361 5021072988912245748688771)
              ·
                refine ⟨7531609483368368623033157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021072988912245748688771 7531609483368368623033157)
                ·
                  refine ⟨1412176778131569116818717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7531609483368368623033157 1412176778131569116818717)
                  ·
                    refine ⟨529566291799338418807019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412176778131569116818717 529566291799338418807019)
                    ·
                      rfl

theorem cell22_1546990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1546990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1546990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1546990 prefixEnd_1546990 := by exact prefixLift 1546990
  have htrace : WordTrace (prefixWord ++ tailWord_1546990) baseStart_1546990 baseEnd_1546990 := by
    simpa [prefixWord, tailWord_1546990, baseEnd_1546990] using wordTrace_append hprefix tailTrace_1546990
  have hstable : (prefixWord ++ tailWord_1546990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1546990).length < 2 ^ (prefixWord ++ tailWord_1546990).sum := by decide
  have hdescent : baseEnd_1546990 < baseStart_1546990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1546990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547052 : List Nat := [2, 2, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_1547052 : Nat := 118140960795 + 1547052 * 2 ^ 59
def prefixEnd_1547052 : Nat := 4983230072969 + 3 ^ 40 * 1547052 * 2
def baseEnd_1547052 : Nat := 529587515666390923756829

theorem tailTrace_1547052 : CollatzResearch.WordTrace tailWord_1547052 prefixEnd_1547052 529587515666390923756829 := by
  unfold tailWord_1547052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212810995651147145721705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37617081327534862860962273 28212810995651147145721705)
  ·
    refine ⟨21159608246738360359291279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28212810995651147145721705 21159608246738360359291279)
    ·
      refine ⟨31739412370107540538936919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21159608246738360359291279 31739412370107540538936919)
      ·
        refine ⟨47609118555161310808405379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739412370107540538936919 47609118555161310808405379)
        ·
          refine ⟨71413677832741966212608069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47609118555161310808405379 71413677832741966212608069)
          ·
            refine ⟨13390064593639118664864013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71413677832741966212608069 13390064593639118664864013)
            ·
              refine ⟨5021274222614669499324005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13390064593639118664864013 5021274222614669499324005)
              ·
                refine ⟨941488916740250531123251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5021274222614669499324005 941488916740250531123251)
                ·
                  refine ⟨1412233375110375796684877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941488916740250531123251 1412233375110375796684877)
                  ·
                    refine ⟨529587515666390923756829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412233375110375796684877 529587515666390923756829)
                    ·
                      rfl

theorem cell22_1547052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_1547052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547052 prefixEnd_1547052 := by exact prefixLift 1547052
  have htrace : WordTrace (prefixWord ++ tailWord_1547052) baseStart_1547052 baseEnd_1547052 := by
    simpa [prefixWord, tailWord_1547052, baseEnd_1547052] using wordTrace_append hprefix tailTrace_1547052
  have hstable : (prefixWord ++ tailWord_1547052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547052).length < 2 ^ (prefixWord ++ tailWord_1547052).sum := by decide
  have hdescent : baseEnd_1547052 < baseStart_1547052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547063 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1547063 : Nat := 118140960795 + 1547063 * 2 ^ 59
def prefixEnd_1547063 : Nat := 4983230072969 + 3 ^ 40 * 1547063 * 2
def baseEnd_1547063 : Nat := 529591281191190561731795

theorem tailTrace_1547063 : CollatzResearch.WordTrace tailWord_1547063 prefixEnd_1547063 529591281191190561731795 := by
  unfold tailWord_1547063
  simp only [CollatzResearch.WordTrace]
  refine ⟨56426023194262443170093843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37617348796174962113395895 56426023194262443170093843)
  ·
    refine ⟨84639034791393664755140765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56426023194262443170093843 84639034791393664755140765)
    ·
      refine ⟨31739638046772624283177787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84639034791393664755140765 31739638046772624283177787)
      ·
        refine ⟨47609457070158936424766681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31739638046772624283177787 47609457070158936424766681)
        ·
          refine ⟨35707092802619202318575011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47609457070158936424766681 35707092802619202318575011)
          ·
            refine ⟨53560639203928803477862517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35707092802619202318575011 53560639203928803477862517)
            ·
              refine ⟨5021309925368325326049611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53560639203928803477862517 5021309925368325326049611)
              ·
                refine ⟨7531964888052487989074417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021309925368325326049611 7531964888052487989074417)
                ·
                  refine ⟨5648973666039365991805813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7531964888052487989074417 5648973666039365991805813)
                  ·
                    refine ⟨529591281191190561731795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5648973666039365991805813 529591281191190561731795)
                    ·
                      rfl

theorem cell22_1547063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1547063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547063 prefixEnd_1547063 := by exact prefixLift 1547063
  have htrace : WordTrace (prefixWord ++ tailWord_1547063) baseStart_1547063 baseEnd_1547063 := by
    simpa [prefixWord, tailWord_1547063, baseEnd_1547063] using wordTrace_append hprefix tailTrace_1547063
  have hstable : (prefixWord ++ tailWord_1547063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547063).length < 2 ^ (prefixWord ++ tailWord_1547063).sum := by decide
  have hdescent : baseEnd_1547063 < baseStart_1547063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547093 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 8]
def baseStart_1547093 : Nat := 118140960795 + 1547093 * 2 ^ 59
def prefixEnd_1547093 : Nat := 4983230072969 + 3 ^ 40 * 1547093 * 2
def baseEnd_1547093 : Nat := 176533850268093494493901

theorem tailTrace_1547093 : CollatzResearch.WordTrace tailWord_1547093 prefixEnd_1547093 176533850268093494493901 := by
  unfold tailWord_1547093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56427117384153758293685933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37618078256102505529123955 56427117384153758293685933)
  ·
    refine ⟨21160169019057659360132225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56427117384153758293685933 21160169019057659360132225)
    ·
      refine ⟨15870126764293244520099169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21160169019057659360132225 15870126764293244520099169)
      ·
        refine ⟨11902595073219933390074377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15870126764293244520099169 11902595073219933390074377)
        ·
          refine ⟨8926946304914950042555783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11902595073219933390074377 8926946304914950042555783)
          ·
            refine ⟨13390419457372425063833675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926946304914950042555783 13390419457372425063833675)
            ·
              refine ⟨20085629186058637595750513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13390419457372425063833675 20085629186058637595750513)
              ·
                refine ⟨15064221889543978196812885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20085629186058637595750513 15064221889543978196812885)
                ·
                  refine ⟨176533850268093494493901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15064221889543978196812885 176533850268093494493901)
                  ·
                    rfl

theorem cell22_1547093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_1547093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547093 prefixEnd_1547093 := by exact prefixLift 1547093
  have htrace : WordTrace (prefixWord ++ tailWord_1547093) baseStart_1547093 baseEnd_1547093 := by
    simpa [prefixWord, tailWord_1547093, baseEnd_1547093] using wordTrace_append hprefix tailTrace_1547093
  have hstable : (prefixWord ++ tailWord_1547093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547093).length < 2 ^ (prefixWord ++ tailWord_1547093).sum := by decide
  have hdescent : baseEnd_1547093 < baseStart_1547093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547123 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_1547123 : Nat := 118140960795 + 1547123 * 2 ^ 59
def prefixEnd_1547123 : Nat := 4983230072969 + 3 ^ 40 * 1547123 * 2
def baseEnd_1547123 : Nat := 529611820417370405231611

theorem tailTrace_1547123 : CollatzResearch.WordTrace tailWord_1547123 prefixEnd_1547123 529611820417370405231611 := by
  unfold tailWord_1547123
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428211574045073417278023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37618807716030048944852015 56428211574045073417278023)
  ·
    refine ⟨84642317361067610125917035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428211574045073417278023 84642317361067610125917035)
    ·
      refine ⟨126963476041601415188875553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84642317361067610125917035 126963476041601415188875553)
      ·
        refine ⟨95222607031201061391656665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126963476041601415188875553 95222607031201061391656665)
        ·
          refine ⟨71416955273400796043742499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95222607031201061391656665 71416955273400796043742499)
          ·
            refine ⟨107125432910101194065613749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71416955273400796043742499 107125432910101194065613749)
            ·
              refine ⟨10043009335321986943651289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107125432910101194065613749 10043009335321986943651289)
              ·
                refine ⟨7532257001491490207738467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10043009335321986943651289 7532257001491490207738467)
                ·
                  refine ⟨11298385502237235311607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532257001491490207738467 11298385502237235311607701)
                  ·
                    refine ⟨529611820417370405231611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11298385502237235311607701 529611820417370405231611)
                    ·
                      rfl

theorem cell22_1547123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_1547123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547123 prefixEnd_1547123 := by exact prefixLift 1547123
  have htrace : WordTrace (prefixWord ++ tailWord_1547123) baseStart_1547123 baseEnd_1547123 := by
    simpa [prefixWord, tailWord_1547123, baseEnd_1547123] using wordTrace_append hprefix tailTrace_1547123
  have hstable : (prefixWord ++ tailWord_1547123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547123).length < 2 ^ (prefixWord ++ tailWord_1547123).sum := by decide
  have hdescent : baseEnd_1547123 < baseStart_1547123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547140 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1547140 : Nat := 118140960795 + 1547140 * 2 ^ 59
def prefixEnd_1547140 : Nat := 4983230072969 + 3 ^ 40 * 1547140 * 2
def baseEnd_1547140 : Nat := 529617639864788027556559

theorem tailTrace_1547140 : CollatzResearch.WordTrace tailWord_1547140 prefixEnd_1547140 529617639864788027556559 := by
  unfold tailWord_1547140
  simp only [CollatzResearch.WordTrace]
  refine ⟨28214415807491742660323437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37619221076655656880431249 28214415807491742660323437)
  ·
    refine ⟨10580405927809403497621289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28214415807491742660323437 10580405927809403497621289)
    ·
      refine ⟨7935304445857052623215967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10580405927809403497621289 7935304445857052623215967)
      ·
        refine ⟨11902956668785578934823951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935304445857052623215967 11902956668785578934823951)
        ·
          refine ⟨17854435003178368402235927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11902956668785578934823951 17854435003178368402235927)
          ·
            refine ⟨26781652504767552603353891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17854435003178368402235927 26781652504767552603353891)
            ·
              refine ⟨40172478757151328905030837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26781652504767552603353891 40172478757151328905030837)
              ·
                refine ⟨3766169883482937084846641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40172478757151328905030837 3766169883482937084846641)
                ·
                  refine ⟨2824627412612202813634981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3766169883482937084846641 2824627412612202813634981)
                  ·
                    refine ⟨529617639864788027556559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2824627412612202813634981 529617639864788027556559)
                    ·
                      rfl

theorem cell22_1547140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1547140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547140 prefixEnd_1547140 := by exact prefixLift 1547140
  have htrace : WordTrace (prefixWord ++ tailWord_1547140) baseStart_1547140 baseEnd_1547140 := by
    simpa [prefixWord, tailWord_1547140, baseEnd_1547140] using wordTrace_append hprefix tailTrace_1547140
  have hstable : (prefixWord ++ tailWord_1547140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547140).length < 2 ^ (prefixWord ++ tailWord_1547140).sum := by decide
  have hdescent : baseEnd_1547140 < baseStart_1547140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547144 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_1547144 : Nat := 118140960795 + 1547144 * 2 ^ 59
def prefixEnd_1547144 : Nat := 4983230072969 + 3 ^ 40 * 1547144 * 2
def baseEnd_1547144 : Nat := 176539669715511116818849

theorem tailTrace_1547144 : CollatzResearch.WordTrace tailWord_1547144 prefixEnd_1547144 176539669715511116818849 := by
  unfold tailWord_1547144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28214488753484497001896243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37619318337979329335861657 28214488753484497001896243)
  ·
    refine ⟨42321733130226745502844365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28214488753484497001896243 42321733130226745502844365)
    ·
      refine ⟨15870649923835029563566637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42321733130226745502844365 15870649923835029563566637)
      ·
        refine ⟨5951493721438136086337489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15870649923835029563566637 5951493721438136086337489)
        ·
          refine ⟨4463620291078602064753117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951493721438136086337489 4463620291078602064753117)
          ·
            refine ⟨1673857609154475774282419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4463620291078602064753117 1673857609154475774282419)
            ·
              refine ⟨2510786413731713661423629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673857609154475774282419 2510786413731713661423629)
              ·
                refine ⟨941544905149392623033861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510786413731713661423629 941544905149392623033861)
                ·
                  refine ⟨176539669715511116818849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941544905149392623033861 176539669715511116818849)
                  ·
                    rfl

theorem cell22_1547144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_1547144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547144 prefixEnd_1547144 := by exact prefixLift 1547144
  have htrace : WordTrace (prefixWord ++ tailWord_1547144) baseStart_1547144 baseEnd_1547144 := by
    simpa [prefixWord, tailWord_1547144, baseEnd_1547144] using wordTrace_append hprefix tailTrace_1547144
  have hstable : (prefixWord ++ tailWord_1547144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547144).length < 2 ^ (prefixWord ++ tailWord_1547144).sum := by decide
  have hdescent : baseEnd_1547144 < baseStart_1547144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547183 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 9]
def baseStart_1547183 : Nat := 118140960795 + 1547183 * 2 ^ 59
def prefixEnd_1547183 : Nat := 4983230072969 + 3 ^ 40 * 1547183 * 2
def baseEnd_1547183 : Nat := 176544119881183416243809

theorem tailTrace_1547183 : CollatzResearch.WordTrace tailWord_1547183 prefixEnd_1547183 176544119881183416243809 := by
  unfold tailWord_1547183
  simp only [CollatzResearch.WordTrace]
  refine ⟨56430399953827703664462203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37620266635885135776308135 56430399953827703664462203)
  ·
    refine ⟨84645599930741555496693305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56430399953827703664462203 84645599930741555496693305)
    ·
      refine ⟨63484199948056166622519979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84645599930741555496693305 63484199948056166622519979)
      ·
        refine ⟨95226299922084249933779969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63484199948056166622519979 95226299922084249933779969)
        ·
          refine ⟨71419724941563187450334977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95226299922084249933779969 71419724941563187450334977)
          ·
            refine ⟨53564793706172390587751233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71419724941563187450334977 53564793706172390587751233)
            ·
              refine ⟨40173595279629292940813425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53564793706172390587751233 40173595279629292940813425)
              ·
                refine ⟨30130196459721969705610069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40173595279629292940813425 30130196459721969705610069)
                ·
                  refine ⟨176544119881183416243809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30130196459721969705610069 176544119881183416243809)
                  ·
                    rfl

theorem cell22_1547183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_1547183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547183 prefixEnd_1547183 := by exact prefixLift 1547183
  have htrace : WordTrace (prefixWord ++ tailWord_1547183) baseStart_1547183 baseEnd_1547183 := by
    simpa [prefixWord, tailWord_1547183, baseEnd_1547183] using wordTrace_append hprefix tailTrace_1547183
  have hstable : (prefixWord ++ tailWord_1547183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547183).length < 2 ^ (prefixWord ++ tailWord_1547183).sum := by decide
  have hdescent : baseEnd_1547183 < baseStart_1547183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547206 : List Nat := [6, 1, 3, 1, 1, 10]
def baseStart_1547206 : Nat := 118140960795 + 1547206 * 2 ^ 59
def prefixEnd_1547206 : Nat := 4983230072969 + 3 ^ 40 * 1547206 * 2
def baseEnd_1547206 : Nat := 6538768308809701918597

theorem tailTrace_1547206 : CollatzResearch.WordTrace tailWord_1547206 prefixEnd_1547206 6538768308809701918597 := by
  unfold tailWord_1547206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763476213523261831017171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37620825888496252395032981 1763476213523261831017171)
  ·
    refine ⟨2645214320284892746525757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1763476213523261831017171 2645214320284892746525757)
    ·
      refine ⟨991955370106834779947159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2645214320284892746525757 991955370106834779947159)
      ·
        refine ⟨1487933055160252169920739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991955370106834779947159 1487933055160252169920739)
        ·
          refine ⟨2231899582740378254881109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487933055160252169920739 2231899582740378254881109)
          ·
            refine ⟨6538768308809701918597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2231899582740378254881109 6538768308809701918597)
            ·
              rfl

theorem cell22_1547206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 10].length) (baseStart_1547206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547206 prefixEnd_1547206 := by exact prefixLift 1547206
  have htrace : WordTrace (prefixWord ++ tailWord_1547206) baseStart_1547206 baseEnd_1547206 := by
    simpa [prefixWord, tailWord_1547206, baseEnd_1547206] using wordTrace_append hprefix tailTrace_1547206
  have hstable : (prefixWord ++ tailWord_1547206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547206).length < 2 ^ (prefixWord ++ tailWord_1547206).sum := by decide
  have hdescent : baseEnd_1547206 < baseStart_1547206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547221 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_1547221 : Nat := 118140960795 + 1547221 * 2 ^ 59
def prefixEnd_1547221 : Nat := 4983230072969 + 3 ^ 40 * 1547221 * 2
def baseEnd_1547221 : Nat := 529645367820130816281311

theorem tailTrace_1547221 : CollatzResearch.WordTrace tailWord_1547221 prefixEnd_1547221 529645367820130816281311 := by
  unfold tailWord_1547221
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431785927690036154345517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37621190618460024102897011 56431785927690036154345517)
  ·
    refine ⟨21161919722883763557879569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56431785927690036154345517 21161919722883763557879569)
    ·
      refine ⟨15871439792162822668409677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21161919722883763557879569 15871439792162822668409677)
      ·
        refine ⟨5951789922061058500653629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15871439792162822668409677 5951789922061058500653629)
        ·
          refine ⟨2231921220772896937745111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5951789922061058500653629 2231921220772896937745111)
          ·
            refine ⟨3347881831159345406617667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231921220772896937745111 3347881831159345406617667)
            ·
              refine ⟨5021822746739018109926501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347881831159345406617667 5021822746739018109926501)
              ·
                refine ⟨941591765013565895611219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5021822746739018109926501 941591765013565895611219)
                ·
                  refine ⟨1412387647520348843416829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941591765013565895611219 1412387647520348843416829)
                  ·
                    refine ⟨529645367820130816281311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412387647520348843416829 529645367820130816281311)
                    ·
                      rfl

theorem cell22_1547221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_1547221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547221 prefixEnd_1547221 := by exact prefixLift 1547221
  have htrace : WordTrace (prefixWord ++ tailWord_1547221) baseStart_1547221 baseEnd_1547221 := by
    simpa [prefixWord, tailWord_1547221, baseEnd_1547221] using wordTrace_append hprefix tailTrace_1547221
  have hstable : (prefixWord ++ tailWord_1547221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547221).length < 2 ^ (prefixWord ++ tailWord_1547221).sum := by decide
  have hdescent : baseEnd_1547221 < baseStart_1547221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547234 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_1547234 : Nat := 118140960795 + 1547234 * 2 ^ 59
def prefixEnd_1547234 : Nat := 4983230072969 + 3 ^ 40 * 1547234 * 2
def baseEnd_1547234 : Nat := 176549939328601038568757

theorem tailTrace_1547234 : CollatzResearch.WordTrace tailWord_1547234 prefixEnd_1547234 176549939328601038568757 := by
  unfold tailWord_1547234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108065019160734843642189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37621506717761959583045837 14108065019160734843642189)
  ·
    refine ⟨5290524382185275566365821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14108065019160734843642189 5290524382185275566365821)
    ·
      refine ⟨1983946643319478337387183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5290524382185275566365821 1983946643319478337387183)
      ·
        refine ⟨2975919964979217506080775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983946643319478337387183 2975919964979217506080775)
        ·
          refine ⟨4463879947468826259121163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975919964979217506080775 4463879947468826259121163)
          ·
            refine ⟨6695819921203239388681745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463879947468826259121163 6695819921203239388681745)
            ·
              refine ⟨5021864940902429541511309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6695819921203239388681745 5021864940902429541511309)
              ·
                refine ⟨1883199352838411078066741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021864940902429541511309 1883199352838411078066741)
                ·
                  refine ⟨176549939328601038568757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883199352838411078066741 176549939328601038568757)
                  ·
                    rfl

theorem cell22_1547234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_1547234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547234 prefixEnd_1547234 := by exact prefixLift 1547234
  have htrace : WordTrace (prefixWord ++ tailWord_1547234) baseStart_1547234 baseEnd_1547234 := by
    simpa [prefixWord, tailWord_1547234, baseEnd_1547234] using wordTrace_append hprefix tailTrace_1547234
  have hstable : (prefixWord ++ tailWord_1547234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547234).length < 2 ^ (prefixWord ++ tailWord_1547234).sum := by decide
  have hdescent : baseEnd_1547234 < baseStart_1547234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547290 : List Nat := [3, 1, 1, 3, 1, 2, 2, 9]
def baseStart_1547290 : Nat := 118140960795 + 1547290 * 2 ^ 59
def prefixEnd_1547290 : Nat := 4983230072969 + 3 ^ 40 * 1547290 * 2
def baseEnd_1547290 : Nat := 58852109770026404034011

theorem tailTrace_1547290 : CollatzResearch.WordTrace tailWord_1547290 prefixEnd_1547290 58852109770026404034011 := by
  unfold tailWord_1547290
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108575641110015234651831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37622868376293373959071549 14108575641110015234651831)
  ·
    refine ⟨21162863461665022851977747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14108575641110015234651831 21162863461665022851977747)
    ·
      refine ⟨31744295192497534277966621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21162863461665022851977747 31744295192497534277966621)
      ·
        refine ⟨11904110697186575354237483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31744295192497534277966621 11904110697186575354237483)
        ·
          refine ⟨17856166045779863031356225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904110697186575354237483 17856166045779863031356225)
          ·
            refine ⟨13392124534334897273517169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17856166045779863031356225 13392124534334897273517169)
            ·
              refine ⟨10044093400751172955137877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13392124534334897273517169 10044093400751172955137877)
              ·
                refine ⟨58852109770026404034011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10044093400751172955137877 58852109770026404034011)
                ·
                  rfl

theorem cell22_1547290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_1547290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547290 prefixEnd_1547290 := by exact prefixLift 1547290
  have htrace : WordTrace (prefixWord ++ tailWord_1547290) baseStart_1547290 baseEnd_1547290 := by
    simpa [prefixWord, tailWord_1547290, baseEnd_1547290] using wordTrace_append hprefix tailTrace_1547290
  have hstable : (prefixWord ++ tailWord_1547290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547290).length < 2 ^ (prefixWord ++ tailWord_1547290).sum := by decide
  have hdescent : baseEnd_1547290 < baseStart_1547290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547322 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_1547322 : Nat := 118140960795 + 1547322 * 2 ^ 59
def prefixEnd_1547322 : Nat := 4983230072969 + 3 ^ 40 * 1547322 * 2
def baseEnd_1547322 : Nat := 529679942184200219506001

theorem tailTrace_1547322 : CollatzResearch.WordTrace tailWord_1547322 prefixEnd_1547322 529679942184200219506001 := by
  unfold tailWord_1547322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14108867425081032600943055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37623646466882753602514813 14108867425081032600943055)
  ·
    refine ⟨21163301137621548901414583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14108867425081032600943055 21163301137621548901414583)
    ·
      refine ⟨31744951706432323352121875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21163301137621548901414583 31744951706432323352121875)
      ·
        refine ⟨47617427559648485028182813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31744951706432323352121875 47617427559648485028182813)
        ·
          refine ⟨17856535334868181885568555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47617427559648485028182813 17856535334868181885568555)
          ·
            refine ⟨26784803002302272828352833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17856535334868181885568555 26784803002302272828352833)
            ·
              refine ⟨20088602251726704621264625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26784803002302272828352833 20088602251726704621264625)
              ·
                refine ⟨15066451688795028465948469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20088602251726704621264625 15066451688795028465948469)
                ·
                  refine ⟨1412479845824533918682669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15066451688795028465948469 1412479845824533918682669)
                  ·
                    refine ⟨529679942184200219506001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412479845824533918682669 529679942184200219506001)
                    ·
                      rfl

theorem cell22_1547322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_1547322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547322 prefixEnd_1547322 := by exact prefixLift 1547322
  have htrace : WordTrace (prefixWord ++ tailWord_1547322) baseStart_1547322 baseEnd_1547322 := by
    simpa [prefixWord, tailWord_1547322, baseEnd_1547322] using wordTrace_append hprefix tailTrace_1547322
  have hstable : (prefixWord ++ tailWord_1547322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547322).length < 2 ^ (prefixWord ++ tailWord_1547322).sum := by decide
  have hdescent : baseEnd_1547322 < baseStart_1547322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547352 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_1547352 : Nat := 118140960795 + 1547352 * 2 ^ 59
def prefixEnd_1547352 : Nat := 4983230072969 + 3 ^ 40 * 1547352 * 2
def baseEnd_1547352 : Nat := 176563403932430047085303

theorem tailTrace_1547352 : CollatzResearch.WordTrace tailWord_1547352 prefixEnd_1547352 176563403932430047085303 := by
  unfold tailWord_1547352
  simp only [CollatzResearch.WordTrace]
  refine ⟨28218281945107722763682155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37624375926810297018242873 28218281945107722763682155)
  ·
    refine ⟨42327422917661584145523233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28218281945107722763682155 42327422917661584145523233)
    ·
      refine ⟨31745567188246188109142425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42327422917661584145523233 31745567188246188109142425)
      ·
        refine ⟨23809175391184641081856819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31745567188246188109142425 23809175391184641081856819)
        ·
          refine ⟨35713763086776961622785229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23809175391184641081856819 35713763086776961622785229)
          ·
            refine ⟨13392661157541360608544461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35713763086776961622785229 13392661157541360608544461)
            ·
              refine ⟨5022247934078010228204173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13392661157541360608544461 5022247934078010228204173)
              ·
                refine ⟨1883342975279253835576565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5022247934078010228204173 1883342975279253835576565)
                ·
                  refine ⟨176563403932430047085303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883342975279253835576565 176563403932430047085303)
                  ·
                    rfl

theorem cell22_1547352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_1547352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547352 prefixEnd_1547352 := by exact prefixLift 1547352
  have htrace : WordTrace (prefixWord ++ tailWord_1547352) baseStart_1547352 baseEnd_1547352 := by
    simpa [prefixWord, tailWord_1547352, baseEnd_1547352] using wordTrace_append hprefix tailTrace_1547352
  have hstable : (prefixWord ++ tailWord_1547352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547352).length < 2 ^ (prefixWord ++ tailWord_1547352).sum := by decide
  have hdescent : baseEnd_1547352 < baseStart_1547352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547431 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 4]
def baseStart_1547431 : Nat := 118140960795 + 1547431 * 2 ^ 59
def prefixEnd_1547431 : Nat := 4983230072969 + 3 ^ 40 * 1547431 * 2
def baseEnd_1547431 : Nat := 176572418370586756176889

theorem tailTrace_1547431 : CollatzResearch.WordTrace tailWord_1547431 prefixEnd_1547431 176572418370586756176889 := by
  unfold tailWord_1547431
  simp only [CollatzResearch.WordTrace]
  refine ⟨56439445256929242019490147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37626296837952828012993431 56439445256929242019490147)
  ·
    refine ⟨84659167885393863029235221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56439445256929242019490147 84659167885393863029235221)
    ·
      refine ⟨3968398494627837329495401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84659167885393863029235221 3968398494627837329495401)
      ·
        refine ⟨2976298870970877997121551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3968398494627837329495401 2976298870970877997121551)
        ·
          refine ⟨4464448306456316995682327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976298870970877997121551 4464448306456316995682327)
          ·
            refine ⟨6696672459684475493523491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464448306456316995682327 6696672459684475493523491)
            ·
              refine ⟨10045008689526713240285237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696672459684475493523491 10045008689526713240285237)
              ·
                refine ⟨941719564643129366276741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10045008689526713240285237 941719564643129366276741)
                ·
                  refine ⟨176572418370586756176889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 941719564643129366276741 176572418370586756176889)
                  ·
                    rfl

theorem cell22_1547431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 4].length) (baseStart_1547431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547431 prefixEnd_1547431 := by exact prefixLift 1547431
  have htrace : WordTrace (prefixWord ++ tailWord_1547431) baseStart_1547431 baseEnd_1547431 := by
    simpa [prefixWord, tailWord_1547431, baseEnd_1547431] using wordTrace_append hprefix tailTrace_1547431
  have hstable : (prefixWord ++ tailWord_1547431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547431).length < 2 ^ (prefixWord ++ tailWord_1547431).sum := by decide
  have hdescent : baseEnd_1547431 < baseStart_1547431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547442 : List Nat := [3, 2, 1, 1, 1, 5, 9]
def baseStart_1547442 : Nat := 118140960795 + 1547442 * 2 ^ 59
def prefixEnd_1547442 : Nat := 4983230072969 + 3 ^ 40 * 1547442 * 2
def baseEnd_1547442 : Nat := 19619297060613329870579

theorem tailTrace_1547442 : CollatzResearch.WordTrace tailWord_1547442 prefixEnd_1547442 19619297060613329870579 := by
  unfold tailWord_1547442
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109961614972347724535145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37626564306592927265427053 14109961614972347724535145)
  ·
    refine ⟨10582471211229260793401359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14109961614972347724535145 10582471211229260793401359)
    ·
      refine ⟨15873706816843891190102039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10582471211229260793401359 15873706816843891190102039)
      ·
        refine ⟨23810560225265836785153059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15873706816843891190102039 23810560225265836785153059)
        ·
          refine ⟨35715840337898755177729589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23810560225265836785153059 35715840337898755177729589)
          ·
            refine ⟨3348360031678008297912149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35715840337898755177729589 3348360031678008297912149)
            ·
              refine ⟨19619297060613329870579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3348360031678008297912149 19619297060613329870579)
              ·
                rfl

theorem cell22_1547442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 9].length) (baseStart_1547442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547442 prefixEnd_1547442 := by exact prefixLift 1547442
  have htrace : WordTrace (prefixWord ++ tailWord_1547442) baseStart_1547442 baseEnd_1547442 := by
    simpa [prefixWord, tailWord_1547442, baseEnd_1547442] using wordTrace_append hprefix tailTrace_1547442
  have hstable : (prefixWord ++ tailWord_1547442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547442).length < 2 ^ (prefixWord ++ tailWord_1547442).sum := by decide
  have hdescent : baseEnd_1547442 < baseStart_1547442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547476 : List Nat := [2, 4, 1, 4, 1, 1, 1, 8]
def baseStart_1547476 : Nat := 118140960795 + 1547476 * 2 ^ 59
def prefixEnd_1547476 : Nat := 4983230072969 + 3 ^ 40 * 1547476 * 2
def baseEnd_1547476 : Nat := 58859184392377239017281

theorem tailTrace_1547476 : CollatzResearch.WordTrace tailWord_1547476 prefixEnd_1547476 58859184392377239017281 := by
  unfold tailWord_1547476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28220543270883107352439141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37627391027844143136585521 28220543270883107352439141)
  ·
    refine ⟨5291351863290582628582339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28220543270883107352439141 5291351863290582628582339)
    ·
      refine ⟨7937027794935873942873509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5291351863290582628582339 7937027794935873942873509)
      ·
        refine ⟨1488192711550476364288783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7937027794935873942873509 1488192711550476364288783)
        ·
          refine ⟨2232289067325714546433175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488192711550476364288783 2232289067325714546433175)
          ·
            refine ⟨3348433600988571819649763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232289067325714546433175 3348433600988571819649763)
            ·
              refine ⟨5022650401482857729474645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348433600988571819649763 5022650401482857729474645)
              ·
                refine ⟨58859184392377239017281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5022650401482857729474645 58859184392377239017281)
                ·
                  rfl

theorem cell22_1547476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_1547476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547476 prefixEnd_1547476 := by exact prefixLift 1547476
  have htrace : WordTrace (prefixWord ++ tailWord_1547476) baseStart_1547476 baseEnd_1547476 := by
    simpa [prefixWord, tailWord_1547476, baseEnd_1547476] using wordTrace_append hprefix tailTrace_1547476
  have hstable : (prefixWord ++ tailWord_1547476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547476).length < 2 ^ (prefixWord ++ tailWord_1547476).sum := by decide
  have hdescent : baseEnd_1547476 < baseStart_1547476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547487 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 7]
def baseStart_1547487 : Nat := 118140960795 + 1547487 * 2 ^ 59
def prefixEnd_1547487 : Nat := 4983230072969 + 3 ^ 40 * 1547487 * 2
def baseEnd_1547487 : Nat := 176578808352064929710165

theorem tailTrace_1547487 : CollatzResearch.WordTrace tailWord_1547487 prefixEnd_1547487 176578808352064929710165 := by
  unfold tailWord_1547487
  simp only [CollatzResearch.WordTrace]
  refine ⟨56441487744726363583528715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37627658496484242389019143 56441487744726363583528715)
  ·
    refine ⟨84662231617089545375293073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56441487744726363583528715 84662231617089545375293073)
    ·
      refine ⟨63496673712817159031469805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84662231617089545375293073 63496673712817159031469805)
      ·
        refine ⟨23811252642306434636801177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63496673712817159031469805 23811252642306434636801177)
        ·
          refine ⟨17858439481729825977600883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23811252642306434636801177 17858439481729825977600883)
          ·
            refine ⟨26787659222594738966401325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858439481729825977600883 26787659222594738966401325)
            ·
              refine ⟨10045372208473027112400497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26787659222594738966401325 10045372208473027112400497)
              ·
                refine ⟨7534029156354770334300373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10045372208473027112400497 7534029156354770334300373)
                ·
                  refine ⟨176578808352064929710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7534029156354770334300373 176578808352064929710165)
                  ·
                    rfl

theorem cell22_1547487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_1547487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547487 prefixEnd_1547487 := by exact prefixLift 1547487
  have htrace : WordTrace (prefixWord ++ tailWord_1547487) baseStart_1547487 baseEnd_1547487 := by
    simpa [prefixWord, tailWord_1547487, baseEnd_1547487] using wordTrace_append hprefix tailTrace_1547487
  have hstable : (prefixWord ++ tailWord_1547487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547487).length < 2 ^ (prefixWord ++ tailWord_1547487).sum := by decide
  have hdescent : baseEnd_1547487 < baseStart_1547487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547517 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1547517 : Nat := 118140960795 + 1547517 * 2 ^ 59
def prefixEnd_1547517 : Nat := 4983230072969 + 3 ^ 40 * 1547517 * 2
def baseEnd_1547517 : Nat := 529746694669284710880403

theorem tailTrace_1547517 : CollatzResearch.WordTrace tailWord_1547517 prefixEnd_1547517 529746694669284710880403 := by
  unfold tailWord_1547517
  simp only [CollatzResearch.WordTrace]
  refine ⟨56442581934617678707120805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37628387956411785804747203 56442581934617678707120805)
  ·
    refine ⟨10582984112740814757585151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56442581934617678707120805 10582984112740814757585151)
    ·
      refine ⟨15874476169111222136377727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10582984112740814757585151 15874476169111222136377727)
      ·
        refine ⟨23811714253666833204566591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15874476169111222136377727 23811714253666833204566591)
        ·
          refine ⟨35717571380500249806849887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23811714253666833204566591 35717571380500249806849887)
          ·
            refine ⟨53576357070750374710274831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35717571380500249806849887 53576357070750374710274831)
            ·
              refine ⟨80364535606125562065412247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53576357070750374710274831 80364535606125562065412247)
              ·
                refine ⟨120546803409188343098118371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80364535606125562065412247 120546803409188343098118371)
                ·
                  refine ⟨180820205113782514647177557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120546803409188343098118371 180820205113782514647177557)
                  ·
                    refine ⟨529746694669284710880403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 180820205113782514647177557 529746694669284710880403)
                    ·
                      rfl

theorem cell22_1547517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1547517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547517 prefixEnd_1547517 := by exact prefixLift 1547517
  have htrace : WordTrace (prefixWord ++ tailWord_1547517) baseStart_1547517 baseEnd_1547517 := by
    simpa [prefixWord, tailWord_1547517, baseEnd_1547517] using wordTrace_append hprefix tailTrace_1547517
  have hstable : (prefixWord ++ tailWord_1547517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547517).length < 2 ^ (prefixWord ++ tailWord_1547517).sum := by decide
  have hdescent : baseEnd_1547517 < baseStart_1547517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547521 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 5]
def baseStart_1547521 : Nat := 118140960795 + 1547521 * 2 ^ 59
def prefixEnd_1547521 : Nat := 4983230072969 + 3 ^ 40 * 1547521 * 2
def baseEnd_1547521 : Nat := 176582687983676677926797

theorem tailTrace_1547521 : CollatzResearch.WordTrace tailWord_1547521 prefixEnd_1547521 176582687983676677926797 := by
  unfold tailWord_1547521
  simp only [CollatzResearch.WordTrace]
  refine ⟨56442727826603187390266417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37628485217735458260177611 56442727826603187390266417)
  ·
    refine ⟨42332045869952390542699813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56442727826603187390266417 42332045869952390542699813)
    ·
      refine ⟨7937258600616073226756215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42332045869952390542699813 7937258600616073226756215)
      ·
        refine ⟨11905887900924109840134323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7937258600616073226756215 11905887900924109840134323)
        ·
          refine ⟨17858831851386164760201485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11905887900924109840134323 17858831851386164760201485)
          ·
            refine ⟨6697061944269811785075557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17858831851386164760201485 6697061944269811785075557)
            ·
              refine ⟨1255699114550589709701667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6697061944269811785075557 1255699114550589709701667)
              ·
                refine ⟨1883548671825884564552501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255699114550589709701667 1883548671825884564552501)
                ·
                  refine ⟨176582687983676677926797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1883548671825884564552501 176582687983676677926797)
                  ·
                    rfl

theorem cell22_1547521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_1547521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547521 prefixEnd_1547521 := by exact prefixLift 1547521
  have htrace : WordTrace (prefixWord ++ tailWord_1547521) baseStart_1547521 baseEnd_1547521 := by
    simpa [prefixWord, tailWord_1547521, baseEnd_1547521] using wordTrace_append hprefix tailTrace_1547521
  have hstable : (prefixWord ++ tailWord_1547521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547521).length < 2 ^ (prefixWord ++ tailWord_1547521).sum := by decide
  have hdescent : baseEnd_1547521 < baseStart_1547521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547596 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1547596 : Nat := 118140960795 + 1547596 * 2 ^ 59
def prefixEnd_1547596 : Nat := 4983230072969 + 3 ^ 40 * 1547596 * 2
def baseEnd_1547596 : Nat := 529773737983754838155161

theorem tailTrace_1547596 : CollatzResearch.WordTrace tailWord_1547596 prefixEnd_1547596 529773737983754838155161 := by
  unfold tailWord_1547596
  simp only [CollatzResearch.WordTrace]
  refine ⟨28222731650665737599623321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37630308867554316799497761 28222731650665737599623321)
  ·
    refine ⟨21167048737999303199717491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28222731650665737599623321 21167048737999303199717491)
    ·
      refine ⟨31750573106998954799576237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21167048737999303199717491 31750573106998954799576237)
      ·
        refine ⟨11906464915124608049841089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31750573106998954799576237 11906464915124608049841089)
        ·
          refine ⟨8929848686343456037380817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11906464915124608049841089 8929848686343456037380817)
          ·
            refine ⟨6697386514757592028035613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8929848686343456037380817 6697386514757592028035613)
            ·
              refine ⟨2511519943034097010513355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6697386514757592028035613 2511519943034097010513355)
              ·
                refine ⟨3767279914551145515770033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511519943034097010513355 3767279914551145515770033)
                ·
                  refine ⟨2825459935913359136827525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3767279914551145515770033 2825459935913359136827525)
                  ·
                    refine ⟨529773737983754838155161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2825459935913359136827525 529773737983754838155161)
                    ·
                      rfl

theorem cell22_1547596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1547596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547596 prefixEnd_1547596 := by exact prefixLift 1547596
  have htrace : WordTrace (prefixWord ++ tailWord_1547596) baseStart_1547596 baseEnd_1547596 := by
    simpa [prefixWord, tailWord_1547596, baseEnd_1547596] using wordTrace_append hprefix tailTrace_1547596
  have hstable : (prefixWord ++ tailWord_1547596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547596).length < 2 ^ (prefixWord ++ tailWord_1547596).sum := by decide
  have hdescent : baseEnd_1547596 < baseStart_1547596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547677 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_1547677 : Nat := 118140960795 + 1547677 * 2 ^ 59
def prefixEnd_1547677 : Nat := 4983230072969 + 3 ^ 40 * 1547677 * 2
def baseEnd_1547677 : Nat := 529801465939097626879913

theorem tailTrace_1547677 : CollatzResearch.WordTrace tailWord_1547677 prefixEnd_1547677 529801465939097626879913 := by
  unfold tailWord_1547677
  simp only [CollatzResearch.WordTrace]
  refine ⟨56448417614038026032945285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37632278409358684021963523 56448417614038026032945285)
  ·
    refine ⟨10584078302632129881177241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56448417614038026032945285 10584078302632129881177241)
    ·
      refine ⟨7938058726974097410882931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10584078302632129881177241 7938058726974097410882931)
      ·
        refine ⟨11907088090461146116324397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7938058726974097410882931 11907088090461146116324397)
        ·
          refine ⟨4465158033922929793621649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11907088090461146116324397 4465158033922929793621649)
          ·
            refine ⟨3348868525442197345216237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465158033922929793621649 3348868525442197345216237)
            ·
              refine ⟨1255825697040824004456089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3348868525442197345216237 1255825697040824004456089)
              ·
                refine ⟨941869272780618003342067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255825697040824004456089 941869272780618003342067)
                ·
                  refine ⟨1412803909170927005013101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941869272780618003342067 1412803909170927005013101)
                  ·
                    refine ⟨529801465939097626879913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412803909170927005013101 529801465939097626879913)
                    ·
                      rfl

theorem cell22_1547677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_1547677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547677 prefixEnd_1547677 := by exact prefixLift 1547677
  have htrace : WordTrace (prefixWord ++ tailWord_1547677) baseStart_1547677 baseEnd_1547677 := by
    simpa [prefixWord, tailWord_1547677, baseEnd_1547677] using wordTrace_append hprefix tailTrace_1547677
  have hstable : (prefixWord ++ tailWord_1547677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547677).length < 2 ^ (prefixWord ++ tailWord_1547677).sum := by decide
  have hdescent : baseEnd_1547677 < baseStart_1547677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547699 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_1547699 : Nat := 118140960795 + 1547699 * 2 ^ 59
def prefixEnd_1547699 : Nat := 4983230072969 + 3 ^ 40 * 1547699 * 2
def baseEnd_1547699 : Nat := 529808996988696902829845

theorem tailTrace_1547699 : CollatzResearch.WordTrace tailWord_1547699 prefixEnd_1547699 529808996988696902829845 := by
  unfold tailWord_1547699
  simp only [CollatzResearch.WordTrace]
  refine ⟨56449220019958323790246151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37632813346638882526830767 56449220019958323790246151)
  ·
    refine ⟨84673830029937485685369227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56449220019958323790246151 84673830029937485685369227)
    ·
      refine ⟨127010745044906228528053841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84673830029937485685369227 127010745044906228528053841)
      ·
        refine ⟨95258058783679671396040381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127010745044906228528053841 95258058783679671396040381)
        ·
          refine ⟨35721772043879876773515143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95258058783679671396040381 35721772043879876773515143)
          ·
            refine ⟨53582658065819815160272715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35721772043879876773515143 53582658065819815160272715)
            ·
              refine ⟨80373987098729722740409073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53582658065819815160272715 80373987098729722740409073)
              ·
                refine ⟨60280490324047292055306805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80373987098729722740409073 60280490324047292055306805)
                ·
                  refine ⟨5651295967879433630185013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60280490324047292055306805 5651295967879433630185013)
                  ·
                    refine ⟨529808996988696902829845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5651295967879433630185013 529808996988696902829845)
                    ·
                      rfl

theorem cell22_1547699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_1547699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547699 prefixEnd_1547699 := by exact prefixLift 1547699
  have htrace : WordTrace (prefixWord ++ tailWord_1547699) baseStart_1547699 baseEnd_1547699 := by
    simpa [prefixWord, tailWord_1547699, baseEnd_1547699] using wordTrace_append hprefix tailTrace_1547699
  have hstable : (prefixWord ++ tailWord_1547699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547699).length < 2 ^ (prefixWord ++ tailWord_1547699).sum := by decide
  have hdescent : baseEnd_1547699 < baseStart_1547699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547765 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1547765 : Nat := 118140960795 + 1547765 * 2 ^ 59
def prefixEnd_1547765 : Nat := 4983230072969 + 3 ^ 40 * 1547765 * 2
def baseEnd_1547765 : Nat := 529831590137494730679643

theorem tailTrace_1547765 : CollatzResearch.WordTrace tailWord_1547765 prefixEnd_1547765 529831590137494730679643 := by
  unfold tailWord_1547765
  simp only [CollatzResearch.WordTrace]
  refine ⟨56451627237719217062148749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37634418158479478041432499 56451627237719217062148749)
  ·
    refine ⟨21169360214144706398305781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56451627237719217062148749 21169360214144706398305781)
    ·
      refine ⟨1984627520076066224841167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21169360214144706398305781 1984627520076066224841167)
      ·
        refine ⟨2976941280114099337261751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1984627520076066224841167 2976941280114099337261751)
        ·
          refine ⟨4465411920171149005892627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2976941280114099337261751 4465411920171149005892627)
          ·
            refine ⟨6698117880256723508838941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465411920171149005892627 6698117880256723508838941)
            ·
              refine ⟨2511794205096271315814603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6698117880256723508838941 2511794205096271315814603)
              ·
                refine ⟨3767691307644406973721905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511794205096271315814603 3767691307644406973721905)
                ·
                  refine ⟨2825768480733305230291429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3767691307644406973721905 2825768480733305230291429)
                  ·
                    refine ⟨529831590137494730679643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2825768480733305230291429 529831590137494730679643)
                    ·
                      rfl

theorem cell22_1547765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1547765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547765 prefixEnd_1547765 := by exact prefixLift 1547765
  have htrace : WordTrace (prefixWord ++ tailWord_1547765) baseStart_1547765 baseEnd_1547765 := by
    simpa [prefixWord, tailWord_1547765, baseEnd_1547765] using wordTrace_append hprefix tailTrace_1547765
  have hstable : (prefixWord ++ tailWord_1547765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547765).length < 2 ^ (prefixWord ++ tailWord_1547765).sum := by decide
  have hdescent : baseEnd_1547765 < baseStart_1547765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547795 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 1, 3]
def baseStart_1547795 : Nat := 118140960795 + 1547795 * 2 ^ 59
def prefixEnd_1547795 : Nat := 4983230072969 + 3 ^ 40 * 1547795 * 2
def baseEnd_1547795 : Nat := 529841859750584652429551

theorem tailTrace_1547795 : CollatzResearch.WordTrace tailWord_1547795 prefixEnd_1547795 529841859750584652429551 := by
  unfold tailWord_1547795
  simp only [CollatzResearch.WordTrace]
  refine ⟨56452721427610532185740839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37635147618407021457160559 56452721427610532185740839)
  ·
    refine ⟨84679082141415798278611259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56452721427610532185740839 84679082141415798278611259)
    ·
      refine ⟨127018623212123697417916889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84679082141415798278611259 127018623212123697417916889)
      ·
        refine ⟨95263967409092773063437667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127018623212123697417916889 95263967409092773063437667)
        ·
          refine ⟨142895951113639159595156501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95263967409092773063437667 142895951113639159595156501)
          ·
            refine ⟨6698247708451835606022961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142895951113639159595156501 6698247708451835606022961)
            ·
              refine ⟨5023685781338876704517221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6698247708451835606022961 5023685781338876704517221)
              ·
                refine ⟨941941084001039382096979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5023685781338876704517221 941941084001039382096979)
                ·
                  refine ⟨1412911626001559073145469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941941084001039382096979 1412911626001559073145469)
                  ·
                    refine ⟨529841859750584652429551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412911626001559073145469 529841859750584652429551)
                    ·
                      rfl

theorem cell22_1547795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 3].length) (baseStart_1547795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547795 prefixEnd_1547795 := by exact prefixLift 1547795
  have htrace : WordTrace (prefixWord ++ tailWord_1547795) baseStart_1547795 baseEnd_1547795 := by
    simpa [prefixWord, tailWord_1547795, baseEnd_1547795] using wordTrace_append hprefix tailTrace_1547795
  have hstable : (prefixWord ++ tailWord_1547795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547795).length < 2 ^ (prefixWord ++ tailWord_1547795).sum := by decide
  have hdescent : baseEnd_1547795 < baseStart_1547795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547846 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1547846 : Nat := 118140960795 + 1547846 * 2 ^ 59
def prefixEnd_1547846 : Nat := 4983230072969 + 3 ^ 40 * 1547846 * 2
def baseEnd_1547846 : Nat := 529859318092837519404395

theorem tailTrace_1547846 : CollatzResearch.WordTrace tailWord_1547846 prefixEnd_1547846 529859318092837519404395 := by
  unfold tailWord_1547846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764205673450805246745231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37636387700283845263898261 1764205673450805246745231)
  ·
    refine ⟨2646308510176207870117847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764205673450805246745231 2646308510176207870117847)
    ·
      refine ⟨3969462765264311805176771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2646308510176207870117847 3969462765264311805176771)
      ·
        refine ⟨5954194147896467707765157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3969462765264311805176771 5954194147896467707765157)
        ·
          refine ⟨1116411402730587695205967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5954194147896467707765157 1116411402730587695205967)
          ·
            refine ⟨1674617104095881542808951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116411402730587695205967 1674617104095881542808951)
            ·
              refine ⟨2511925656143822314213427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674617104095881542808951 2511925656143822314213427)
              ·
                refine ⟨3767888484215733471320141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511925656143822314213427 3767888484215733471320141)
                ·
                  refine ⟨1412958181580900051745053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3767888484215733471320141 1412958181580900051745053)
                  ·
                    refine ⟨529859318092837519404395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1412958181580900051745053 529859318092837519404395)
                    ·
                      rfl

theorem cell22_1547846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1547846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547846 prefixEnd_1547846 := by exact prefixLift 1547846
  have htrace : WordTrace (prefixWord ++ tailWord_1547846) baseStart_1547846 baseEnd_1547846 := by
    simpa [prefixWord, tailWord_1547846, baseEnd_1547846] using wordTrace_append hprefix tailTrace_1547846
  have hstable : (prefixWord ++ tailWord_1547846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547846).length < 2 ^ (prefixWord ++ tailWord_1547846).sum := by decide
  have hdescent : baseEnd_1547846 < baseStart_1547846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547866 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_1547866 : Nat := 118140960795 + 1547866 * 2 ^ 59
def prefixEnd_1547866 : Nat := 4983230072969 + 3 ^ 40 * 1547866 * 2
def baseEnd_1547866 : Nat := 529866164501564133904333

theorem tailTrace_1547866 : CollatzResearch.WordTrace tailWord_1547866 prefixEnd_1547866 529866164501564133904333 := by
  unfold tailWord_1547866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113827752588327827893863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37636874006902207541050301 14113827752588327827893863)
  ·
    refine ⟨21170741628882491741840795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14113827752588327827893863 21170741628882491741840795)
    ·
      refine ⟨31756112443323737612761193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21170741628882491741840795 31756112443323737612761193)
      ·
        refine ⟨23817084332492803209570895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31756112443323737612761193 23817084332492803209570895)
        ·
          refine ⟨35725626498739204814356343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23817084332492803209570895 35725626498739204814356343)
          ·
            refine ⟨53588439748108807221534515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35725626498739204814356343 53588439748108807221534515)
            ·
              refine ⟨80382659622163210832301773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53588439748108807221534515 80382659622163210832301773)
              ·
                refine ⟨30143497358311204062113165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80382659622163210832301773 30143497358311204062113165)
                ·
                  refine ⟨11303811509366701523292437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30143497358311204062113165 11303811509366701523292437)
                  ·
                    refine ⟨529866164501564133904333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11303811509366701523292437 529866164501564133904333)
                    ·
                      rfl

theorem cell22_1547866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_1547866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547866 prefixEnd_1547866 := by exact prefixLift 1547866
  have htrace : WordTrace (prefixWord ++ tailWord_1547866) baseStart_1547866 baseEnd_1547866 := by
    simpa [prefixWord, tailWord_1547866, baseEnd_1547866] using wordTrace_append hprefix tailTrace_1547866
  have hstable : (prefixWord ++ tailWord_1547866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547866).length < 2 ^ (prefixWord ++ tailWord_1547866).sum := by decide
  have hdescent : baseEnd_1547866 < baseStart_1547866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547881 : List Nat := [1, 2, 1, 1, 1, 4, 4, 8]
def baseStart_1547881 : Nat := 118140960795 + 1547881 * 2 ^ 59
def prefixEnd_1547881 : Nat := 4983230072969 + 3 ^ 40 * 1547881 * 2
def baseEnd_1547881 : Nat := 58874588812012121642143

theorem tailTrace_1547881 : CollatzResearch.WordTrace tailWord_1547881 prefixEnd_1547881 58874588812012121642143 := by
  unfold tailWord_1547881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56455858105298968873371497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37637238736865979248914331 56455858105298968873371497)
  ·
    refine ⟨42341893578974226655028623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56455858105298968873371497 42341893578974226655028623)
    ·
      refine ⟨63512840368461339982542935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42341893578974226655028623 63512840368461339982542935)
      ·
        refine ⟨95269260552692009973814403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63512840368461339982542935 95269260552692009973814403)
        ·
          refine ⟨142903890829038014960721605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95269260552692009973814403 142903890829038014960721605)
          ·
            refine ⟨26794479530444627805135301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142903890829038014960721605 26794479530444627805135301)
            ·
              refine ⟨5023964911958367713462869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26794479530444627805135301 5023964911958367713462869)
              ·
                refine ⟨58874588812012121642143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5023964911958367713462869 58874588812012121642143)
                ·
                  rfl

theorem cell22_1547881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 8].length) (baseStart_1547881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547881 prefixEnd_1547881 := by exact prefixLift 1547881
  have htrace : WordTrace (prefixWord ++ tailWord_1547881) baseStart_1547881 baseEnd_1547881 := by
    simpa [prefixWord, tailWord_1547881, baseEnd_1547881] using wordTrace_append hprefix tailTrace_1547881
  have hstable : (prefixWord ++ tailWord_1547881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547881).length < 2 ^ (prefixWord ++ tailWord_1547881).sum := by decide
  have hdescent : baseEnd_1547881 < baseStart_1547881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1547885 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1547885 : Nat := 118140960795 + 1547885 * 2 ^ 59
def prefixEnd_1547885 : Nat := 4983230072969 + 3 ^ 40 * 1547885 * 2
def baseEnd_1547885 : Nat := 529872668589854417679275

theorem tailTrace_1547885 : CollatzResearch.WordTrace tailWord_1547885 prefixEnd_1547885 529872668589854417679275 := by
  unfold tailWord_1547885
  simp only [CollatzResearch.WordTrace]
  refine ⟨56456003997284477556517109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37637335998189651704344739 56456003997284477556517109)
  ·
    refine ⟨5292750374745419770923479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56456003997284477556517109 5292750374745419770923479)
    ·
      refine ⟨7939125562118129656385219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5292750374745419770923479 7939125562118129656385219)
      ·
        refine ⟨11908688343177194484577829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939125562118129656385219 11908688343177194484577829)
        ·
          refine ⟨2232879064345723965858343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11908688343177194484577829 2232879064345723965858343)
          ·
            refine ⟨3349318596518585948787515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2232879064345723965858343 3349318596518585948787515)
            ·
              refine ⟨5023977894777878923181273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3349318596518585948787515 5023977894777878923181273)
              ·
                refine ⟨3767983421083409192385955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5023977894777878923181273 3767983421083409192385955)
                ·
                  refine ⟨5651975131625113788578933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767983421083409192385955 5651975131625113788578933)
                  ·
                    refine ⟨529872668589854417679275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5651975131625113788578933 529872668589854417679275)
                    ·
                      rfl

theorem cell22_1547885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1547885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1547885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1547885 prefixEnd_1547885 := by exact prefixLift 1547885
  have htrace : WordTrace (prefixWord ++ tailWord_1547885) baseStart_1547885 baseEnd_1547885 := by
    simpa [prefixWord, tailWord_1547885, baseEnd_1547885] using wordTrace_append hprefix tailTrace_1547885
  have hstable : (prefixWord ++ tailWord_1547885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1547885).length < 2 ^ (prefixWord ++ tailWord_1547885).sum := by decide
  have hdescent : baseEnd_1547885 < baseStart_1547885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1547885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548022 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1548022 : Nat := 118140960795 + 1548022 * 2 ^ 59
def prefixEnd_1548022 : Nat := 4983230072969 + 3 ^ 40 * 1548022 * 2
def baseEnd_1548022 : Nat := 176639855496543909001285

theorem tailTrace_1548022 : CollatzResearch.WordTrace tailWord_1548022 prefixEnd_1548022 176639855496543909001285 := by
  unfold tailWord_1548022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3528812549861759372140895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37640667198525433302836213 3528812549861759372140895)
  ·
    refine ⟨5293218824792639058211343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3528812549861759372140895 5293218824792639058211343)
    ·
      refine ⟨7939828237188958587317015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293218824792639058211343 7939828237188958587317015)
      ·
        refine ⟨11909742355783437880975523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939828237188958587317015 11909742355783437880975523)
        ·
          refine ⟨17864613533675156821463285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909742355783437880975523 17864613533675156821463285)
          ·
            refine ⟨1674807518782045952012183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17864613533675156821463285 1674807518782045952012183)
            ·
              refine ⟨2512211278173068928018275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1674807518782045952012183 2512211278173068928018275)
              ·
                refine ⟨3768316917259603392027413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512211278173068928018275 3768316917259603392027413)
                ·
                  refine ⟨176639855496543909001285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3768316917259603392027413 176639855496543909001285)
                  ·
                    rfl

theorem cell22_1548022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1548022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548022 prefixEnd_1548022 := by exact prefixLift 1548022
  have htrace : WordTrace (prefixWord ++ tailWord_1548022) baseStart_1548022 baseEnd_1548022 := by
    simpa [prefixWord, tailWord_1548022, baseEnd_1548022] using wordTrace_append hprefix tailTrace_1548022
  have hstable : (prefixWord ++ tailWord_1548022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548022).length < 2 ^ (prefixWord ++ tailWord_1548022).sum := by decide
  have hdescent : baseEnd_1548022 < baseStart_1548022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548033 : List Nat := [1, 2, 4, 1, 1, 1, 3, 9]
def baseStart_1548033 : Nat := 118140960795 + 1548033 * 2 ^ 59
def prefixEnd_1548033 : Nat := 4983230072969 + 3 ^ 40 * 1548033 * 2
def baseEnd_1548033 : Nat := 58880370223825707219869

theorem tailTrace_1548033 : CollatzResearch.WordTrace tailWord_1548033 prefixEnd_1548033 58880370223825707219869 := by
  unfold tailWord_1548033
  simp only [CollatzResearch.WordTrace]
  refine ⟨56461402000748298832904753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37640934667165532555269835 56461402000748298832904753)
  ·
    refine ⟨42346051500561224124678565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56461402000748298832904753 42346051500561224124678565)
    ·
      refine ⟨7939884656355229523377231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42346051500561224124678565 7939884656355229523377231)
      ·
        refine ⟨11909826984532844285065847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7939884656355229523377231 11909826984532844285065847)
        ·
          refine ⟨17864740476799266427598771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11909826984532844285065847 17864740476799266427598771)
          ·
            refine ⟨26797110715198899641398157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17864740476799266427598771 26797110715198899641398157)
            ·
              refine ⟨10048916518199587365524309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26797110715198899641398157 10048916518199587365524309)
              ·
                refine ⟨58880370223825707219869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10048916518199587365524309 58880370223825707219869)
                ·
                  rfl

theorem cell22_1548033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 9].length) (baseStart_1548033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548033 prefixEnd_1548033 := by exact prefixLift 1548033
  have htrace : WordTrace (prefixWord ++ tailWord_1548033) baseStart_1548033 baseEnd_1548033 := by
    simpa [prefixWord, tailWord_1548033, baseEnd_1548033] using wordTrace_append hprefix tailTrace_1548033
  have hstable : (prefixWord ++ tailWord_1548033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548033).length < 2 ^ (prefixWord ++ tailWord_1548033).sum := by decide
  have hdescent : baseEnd_1548033 < baseStart_1548033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548116 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1548116 : Nat := 118140960795 + 1548116 * 2 ^ 59
def prefixEnd_1548116 : Nat := 4983230072969 + 3 ^ 40 * 1548116 * 2
def baseEnd_1548116 : Nat := 529951744610646815153567

theorem tailTrace_1548116 : CollatzResearch.WordTrace tailWord_1548116 prefixEnd_1548116 529951744610646815153567 := by
  unfold tailWord_1548116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232214629723802004088101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37642952839631736005450801 28232214629723802004088101)
  ·
    refine ⟨5293540243073212875766519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28232214629723802004088101 5293540243073212875766519)
    ·
      refine ⟨7940310364609819313649779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5293540243073212875766519 7940310364609819313649779)
      ·
        refine ⟨11910465546914728970474669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7940310364609819313649779 11910465546914728970474669)
        ·
          refine ⟨4466424580093023363928001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11910465546914728970474669 4466424580093023363928001)
          ·
            refine ⟨3349818435069767522946001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4466424580093023363928001 3349818435069767522946001)
            ·
              refine ⟨2512363826302325642209501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3349818435069767522946001 2512363826302325642209501)
              ·
                refine ⟨942136434863372115828563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2512363826302325642209501 942136434863372115828563)
                ·
                  refine ⟨1413204652295058173742845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942136434863372115828563 1413204652295058173742845)
                  ·
                    refine ⟨529951744610646815153567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413204652295058173742845 529951744610646815153567)
                    ·
                      rfl

theorem cell22_1548116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1548116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548116 prefixEnd_1548116 := by exact prefixLift 1548116
  have htrace : WordTrace (prefixWord ++ tailWord_1548116) baseStart_1548116 baseEnd_1548116 := by
    simpa [prefixWord, tailWord_1548116, baseEnd_1548116] using wordTrace_append hprefix tailTrace_1548116
  have hstable : (prefixWord ++ tailWord_1548116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548116).length < 2 ^ (prefixWord ++ tailWord_1548116).sum := by decide
  have hdescent : baseEnd_1548116 < baseStart_1548116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548140 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_1548140 : Nat := 118140960795 + 1548140 * 2 ^ 59
def prefixEnd_1548140 : Nat := 4983230072969 + 3 ^ 40 * 1548140 * 2
def baseEnd_1548140 : Nat := 176653320100372917517831

theorem tailTrace_1548140 : CollatzResearch.WordTrace tailWord_1548140 prefixEnd_1548140 176653320100372917517831 := by
  unfold tailWord_1548140
  simp only [CollatzResearch.WordTrace]
  refine ⟨28232652305680328053524937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37643536407573770738033249 28232652305680328053524937)
  ·
    refine ⟨21174489229260246040143703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28232652305680328053524937 21174489229260246040143703)
    ·
      refine ⟨31761733843890369060215555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21174489229260246040143703 31761733843890369060215555)
      ·
        refine ⟨47642600765835553590323333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31761733843890369060215555 47642600765835553590323333)
        ·
          refine ⟨8932987643594166298185625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47642600765835553590323333 8932987643594166298185625)
          ·
            refine ⟨6699740732695624723639219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8932987643594166298185625 6699740732695624723639219)
            ·
              refine ⟨10049611099043437085458829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6699740732695624723639219 10049611099043437085458829)
              ·
                refine ⟨3768604162141288907047061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10049611099043437085458829 3768604162141288907047061)
                ·
                  refine ⟨176653320100372917517831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3768604162141288907047061 176653320100372917517831)
                  ·
                    rfl

theorem cell22_1548140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_1548140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548140 prefixEnd_1548140 := by exact prefixLift 1548140
  have htrace : WordTrace (prefixWord ++ tailWord_1548140) baseStart_1548140 baseEnd_1548140 := by
    simpa [prefixWord, tailWord_1548140, baseEnd_1548140] using wordTrace_append hprefix tailTrace_1548140
  have hstable : (prefixWord ++ tailWord_1548140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548140).length < 2 ^ (prefixWord ++ tailWord_1548140).sum := by decide
  have hdescent : baseEnd_1548140 < baseStart_1548140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548191 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 4]
def baseStart_1548191 : Nat := 118140960795 + 1548191 * 2 ^ 59
def prefixEnd_1548191 : Nat := 4983230072969 + 3 ^ 40 * 1548191 * 2
def baseEnd_1548191 : Nat := 176659139547790539842779

theorem tailTrace_1548191 : CollatzResearch.WordTrace tailWord_1548191 prefixEnd_1548191 176659139547790539842779 := by
  unfold tailWord_1548191
  simp only [CollatzResearch.WordTrace]
  refine ⟨56467164734175891817156427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37644776489450594544770951 56467164734175891817156427)
  ·
    refine ⟨84700747101263837725734641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56467164734175891817156427 84700747101263837725734641)
    ·
      refine ⟨63525560325947878294300981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84700747101263837725734641 63525560325947878294300981)
      ·
        refine ⟨5955521280557613590090717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63525560325947878294300981 5955521280557613590090717)
        ·
          refine ⟨2233320480209105096284019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5955521280557613590090717 2233320480209105096284019)
          ·
            refine ⟨3349980720313657644426029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233320480209105096284019 3349980720313657644426029)
            ·
              refine ⟨1256242770117621616659761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3349980720313657644426029 1256242770117621616659761)
              ·
                refine ⟨942182077588216212494821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256242770117621616659761 942182077588216212494821)
                ·
                  refine ⟨176659139547790539842779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942182077588216212494821 176659139547790539842779)
                  ·
                    rfl

theorem cell22_1548191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 4].length) (baseStart_1548191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548191 prefixEnd_1548191 := by exact prefixLift 1548191
  have htrace : WordTrace (prefixWord ++ tailWord_1548191) baseStart_1548191 baseEnd_1548191 := by
    simpa [prefixWord, tailWord_1548191, baseEnd_1548191] using wordTrace_append hprefix tailTrace_1548191
  have hstable : (prefixWord ++ tailWord_1548191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548191).length < 2 ^ (prefixWord ++ tailWord_1548191).sum := by decide
  have hdescent : baseEnd_1548191 < baseStart_1548191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548217 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_1548217 : Nat := 118140960795 + 1548217 * 2 ^ 59
def prefixEnd_1548217 : Nat := 4983230072969 + 3 ^ 40 * 1548217 * 2
def baseEnd_1548217 : Nat := 529986318974716218378257

theorem tailTrace_1548217 : CollatzResearch.WordTrace tailWord_1548217 prefixEnd_1548217 529986318974716218378257 := by
  unfold tailWord_1548217
  simp only [CollatzResearch.WordTrace]
  refine ⟨56468113032081698257602905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37645408688054465505068603 56468113032081698257602905)
  ·
    refine ⟨42351084774061273693202179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56468113032081698257602905 42351084774061273693202179)
    ·
      refine ⟨63526627161091910539803269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42351084774061273693202179 63526627161091910539803269)
      ·
        refine ⟨11911242592704733226213113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63526627161091910539803269 11911242592704733226213113)
        ·
          refine ⟨8933431944528549919659835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11911242592704733226213113 8933431944528549919659835)
          ·
            refine ⟨13400147916792824879489753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8933431944528549919659835 13400147916792824879489753)
            ·
              refine ⟨10050110937594618659617315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13400147916792824879489753 10050110937594618659617315)
              ·
                refine ⟨15075166406391927989425973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10050110937594618659617315 15075166406391927989425973)
                ·
                  refine ⟨1413296850599243249008685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15075166406391927989425973 1413296850599243249008685)
                  ·
                    refine ⟨529986318974716218378257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413296850599243249008685 529986318974716218378257)
                    ·
                      rfl

theorem cell22_1548217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_1548217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548217 prefixEnd_1548217 := by exact prefixLift 1548217
  have htrace : WordTrace (prefixWord ++ tailWord_1548217) baseStart_1548217 baseEnd_1548217 := by
    simpa [prefixWord, tailWord_1548217, baseEnd_1548217] using wordTrace_append hprefix tailTrace_1548217
  have hstable : (prefixWord ++ tailWord_1548217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548217).length < 2 ^ (prefixWord ++ tailWord_1548217).sum := by decide
  have hdescent : baseEnd_1548217 < baseStart_1548217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548247 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 5]
def baseStart_1548247 : Nat := 118140960795 + 1548247 * 2 ^ 59
def prefixEnd_1548247 : Nat := 4983230072969 + 3 ^ 40 * 1548247 * 2
def baseEnd_1548247 : Nat := 176665529529268713376055

theorem tailTrace_1548247 : CollatzResearch.WordTrace tailWord_1548247 prefixEnd_1548247 176665529529268713376055 := by
  unfold tailWord_1548247
  simp only [CollatzResearch.WordTrace]
  refine ⟨56469207221973013381194995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37646138147982008920796663 56469207221973013381194995)
  ·
    refine ⟨84703810832959520071792493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56469207221973013381194995 84703810832959520071792493)
    ·
      refine ⟨31763929062359820026922185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84703810832959520071792493 31763929062359820026922185)
      ·
        refine ⟨23822946796769865020191639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31763929062359820026922185 23822946796769865020191639)
        ·
          refine ⟨35734420195154797530287459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23822946796769865020191639 35734420195154797530287459)
          ·
            refine ⟨53601630292732196295431189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35734420195154797530287459 53601630292732196295431189)
            ·
              refine ⟨2512576419971821701348337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53601630292732196295431189 2512576419971821701348337)
              ·
                refine ⟨1884432314978866276011253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512576419971821701348337 1884432314978866276011253)
                ·
                  refine ⟨176665529529268713376055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1884432314978866276011253 176665529529268713376055)
                  ·
                    rfl

theorem cell22_1548247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 5].length) (baseStart_1548247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548247 prefixEnd_1548247 := by exact prefixLift 1548247
  have htrace : WordTrace (prefixWord ++ tailWord_1548247) baseStart_1548247 baseEnd_1548247 := by
    simpa [prefixWord, tailWord_1548247, baseEnd_1548247] using wordTrace_append hprefix tailTrace_1548247
  have hstable : (prefixWord ++ tailWord_1548247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548247).length < 2 ^ (prefixWord ++ tailWord_1548247).sum := by decide
  have hdescent : baseEnd_1548247 < baseStart_1548247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548309 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 6]
def baseStart_1548309 : Nat := 118140960795 + 1548309 * 2 ^ 59
def prefixEnd_1548309 : Nat := 4983230072969 + 3 ^ 40 * 1548309 * 2
def baseEnd_1548309 : Nat := 176672604151619548359325

theorem tailTrace_1548309 : CollatzResearch.WordTrace tailWord_1548309 prefixEnd_1548309 176672604151619548359325 := by
  unfold tailWord_1548309
  simp only [CollatzResearch.WordTrace]
  refine ⟨56471468547748397969951981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37647645698498931979967987 56471468547748397969951981)
  ·
    refine ⟨21176800705405649238731993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56471468547748397969951981 21176800705405649238731993)
    ·
      refine ⟨15882600529054236929048995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21176800705405649238731993 15882600529054236929048995)
      ·
        refine ⟨23823900793581355393573493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15882600529054236929048995 23823900793581355393573493)
        ·
          refine ⟨2233490699398252068147515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23823900793581355393573493 2233490699398252068147515)
          ·
            refine ⟨3350236049097378102221273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233490699398252068147515 3350236049097378102221273)
            ·
              refine ⟨2512677036823033576665955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3350236049097378102221273 2512677036823033576665955)
              ·
                refine ⟨3769015555234550364998933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2512677036823033576665955 3769015555234550364998933)
                ·
                  refine ⟨176672604151619548359325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3769015555234550364998933 176672604151619548359325)
                  ·
                    rfl

theorem cell22_1548309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_1548309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548309 prefixEnd_1548309 := by exact prefixLift 1548309
  have htrace : WordTrace (prefixWord ++ tailWord_1548309) baseStart_1548309 baseEnd_1548309 := by
    simpa [prefixWord, tailWord_1548309, baseEnd_1548309] using wordTrace_append hprefix tailTrace_1548309
  have hstable : (prefixWord ++ tailWord_1548309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548309).length < 2 ^ (prefixWord ++ tailWord_1548309).sum := by decide
  have hdescent : baseEnd_1548309 < baseStart_1548309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548322 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_1548322 : Nat := 118140960795 + 1548322 * 2 ^ 59
def prefixEnd_1548322 : Nat := 4983230072969 + 3 ^ 40 * 1548322 * 2
def baseEnd_1548322 : Nat := 530022262620530944502935

theorem tailTrace_1548322 : CollatzResearch.WordTrace tailWord_1548322 prefixEnd_1548322 530022262620530944502935 := by
  unfold tailWord_1548322
  simp only [CollatzResearch.WordTrace]
  refine ⟨14117985674175325297543805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37647961797800867460116813 14117985674175325297543805)
  ·
    refine ⟨5294244627815746986578927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14117985674175325297543805 5294244627815746986578927)
    ·
      refine ⟨7941366941723620479868391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5294244627815746986578927 7941366941723620479868391)
      ·
        refine ⟨11912050412585430719802587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941366941723620479868391 11912050412585430719802587)
        ·
          refine ⟨17868075618878146079703881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11912050412585430719802587 17868075618878146079703881)
          ·
            refine ⟨13401056714158609559777911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17868075618878146079703881 13401056714158609559777911)
            ·
              refine ⟨20101585071237914339666867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13401056714158609559777911 20101585071237914339666867)
              ·
                refine ⟨30152377606856871509500301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20101585071237914339666867 30152377606856871509500301)
                ·
                  refine ⟨11307141602571326816062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30152377606856871509500301 11307141602571326816062613)
                  ·
                    refine ⟨530022262620530944502935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11307141602571326816062613 530022262620530944502935)
                    ·
                      rfl

theorem cell22_1548322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_1548322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548322 prefixEnd_1548322 := by exact prefixLift 1548322
  have htrace : WordTrace (prefixWord ++ tailWord_1548322) baseStart_1548322 baseEnd_1548322 := by
    simpa [prefixWord, tailWord_1548322, baseEnd_1548322] using wordTrace_append hprefix tailTrace_1548322
  have hstable : (prefixWord ++ tailWord_1548322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548322).length < 2 ^ (prefixWord ++ tailWord_1548322).sum := by decide
  have hdescent : baseEnd_1548322 < baseStart_1548322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548328 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_1548328 : Nat := 118140960795 + 1548328 * 2 ^ 59
def prefixEnd_1548328 : Nat := 4983230072969 + 3 ^ 40 * 1548328 * 2
def baseEnd_1548328 : Nat := 530024316543148928852917

theorem tailTrace_1548328 : CollatzResearch.WordTrace tailWord_1548328 prefixEnd_1548328 530024316543148928852917 := by
  unfold tailWord_1548328
  simp only [CollatzResearch.WordTrace]
  refine ⟨28236080767339782107446819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37648107689786376143262425 28236080767339782107446819)
  ·
    refine ⟨42354121151009673161170229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28236080767339782107446819 42354121151009673161170229)
    ·
      refine ⟨3970698857907156858859709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42354121151009673161170229 3970698857907156858859709)
      ·
        refine ⟨1489012071715183822072391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3970698857907156858859709 1489012071715183822072391)
        ·
          refine ⟨2233518107572775733108587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489012071715183822072391 2233518107572775733108587)
          ·
            refine ⟨3350277161359163599662881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233518107572775733108587 3350277161359163599662881)
            ·
              refine ⟨2512707871019372699747161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3350277161359163599662881 2512707871019372699747161)
              ·
                refine ⟨1884530903264529524810371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2512707871019372699747161 1884530903264529524810371)
                ·
                  refine ⟨2826796354896794287215557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1884530903264529524810371 2826796354896794287215557)
                  ·
                    refine ⟨530024316543148928852917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2826796354896794287215557 530024316543148928852917)
                    ·
                      rfl

theorem cell22_1548328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_1548328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548328 prefixEnd_1548328 := by exact prefixLift 1548328
  have htrace : WordTrace (prefixWord ++ tailWord_1548328) baseStart_1548328 baseEnd_1548328 := by
    simpa [prefixWord, tailWord_1548328, baseEnd_1548328] using wordTrace_append hprefix tailTrace_1548328
  have hstable : (prefixWord ++ tailWord_1548328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548328).length < 2 ^ (prefixWord ++ tailWord_1548328).sum := by decide
  have hdescent : baseEnd_1548328 < baseStart_1548328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548337 : List Nat := [1, 2, 2, 3, 1, 4, 1, 8]
def baseStart_1548337 : Nat := 118140960795 + 1548337 * 2 ^ 59
def prefixEnd_1548337 : Nat := 4983230072969 + 3 ^ 40 * 1548337 * 2
def baseEnd_1548337 : Nat := 58891933047452878375321

theorem tailTrace_1548337 : CollatzResearch.WordTrace tailWord_1548337 prefixEnd_1548337 58891933047452878375321 := by
  unfold tailWord_1548337
  simp only [CollatzResearch.WordTrace]
  refine ⟨56472489791646958751971265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37648326527764639167980843 56472489791646958751971265)
  ·
    refine ⟨42354367343735219063978449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56472489791646958751971265 42354367343735219063978449)
    ·
      refine ⟨31765775507801414297983837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42354367343735219063978449 31765775507801414297983837)
      ·
        refine ⟨11912165815425530361743939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31765775507801414297983837 11912165815425530361743939)
        ·
          refine ⟨17868248723138295542615909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11912165815425530361743939 17868248723138295542615909)
          ·
            refine ⟨3350296635588430414240483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17868248723138295542615909 3350296635588430414240483)
            ·
              refine ⟨5025444953382645621360725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3350296635588430414240483 5025444953382645621360725)
              ·
                refine ⟨58891933047452878375321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5025444953382645621360725 58891933047452878375321)
                ·
                  rfl

theorem cell22_1548337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 8].length) (baseStart_1548337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548337 prefixEnd_1548337 := by exact prefixLift 1548337
  have htrace : WordTrace (prefixWord ++ tailWord_1548337) baseStart_1548337 baseEnd_1548337 := by
    simpa [prefixWord, tailWord_1548337, baseEnd_1548337] using wordTrace_append hprefix tailTrace_1548337
  have hstable : (prefixWord ++ tailWord_1548337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548337).length < 2 ^ (prefixWord ++ tailWord_1548337).sum := by decide
  have hdescent : baseEnd_1548337 < baseStart_1548337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548358 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_1548358 : Nat := 118140960795 + 1548358 * 2 ^ 59
def prefixEnd_1548358 : Nat := 4983230072969 + 3 ^ 40 * 1548358 * 2
def baseEnd_1548358 : Nat := 530034586156238850602825

theorem tailTrace_1548358 : CollatzResearch.WordTrace tailWord_1548358 prefixEnd_1548358 530034586156238850602825 := by
  unfold tailWord_1548358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764789241392839979327679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37648837149713919558990485 1764789241392839979327679)
  ·
    refine ⟨2647183862089259968991519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764789241392839979327679 2647183862089259968991519)
    ·
      refine ⟨3970775793133889953487279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647183862089259968991519 3970775793133889953487279)
      ·
        refine ⟨5956163689700834930230919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3970775793133889953487279 5956163689700834930230919)
        ·
          refine ⟨8934245534551252395346379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956163689700834930230919 8934245534551252395346379)
          ·
            refine ⟨13401368301826878593019569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934245534551252395346379 13401368301826878593019569)
            ·
              refine ⟨10051026226370158944764677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13401368301826878593019569 10051026226370158944764677)
              ·
                refine ⟨1884567417444404802143377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10051026226370158944764677 1884567417444404802143377)
                ·
                  refine ⟨1413425563083303601607533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884567417444404802143377 1413425563083303601607533)
                  ·
                    refine ⟨530034586156238850602825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413425563083303601607533 530034586156238850602825)
                    ·
                      rfl

theorem cell22_1548358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_1548358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548358 prefixEnd_1548358 := by exact prefixLift 1548358
  have htrace : WordTrace (prefixWord ++ tailWord_1548358) baseStart_1548358 baseEnd_1548358 := by
    simpa [prefixWord, tailWord_1548358, baseEnd_1548358] using wordTrace_append hprefix tailTrace_1548358
  have hstable : (prefixWord ++ tailWord_1548358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548358).length < 2 ^ (prefixWord ++ tailWord_1548358).sum := by decide
  have hdescent : baseEnd_1548358 < baseStart_1548358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548444 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_1548444 : Nat := 118140960795 + 1548444 * 2 ^ 59
def prefixEnd_1548444 : Nat := 4983230072969 + 3 ^ 40 * 1548444 * 2
def baseEnd_1548444 : Nat := 176688008571254430984187

theorem tailTrace_1548444 : CollatzResearch.WordTrace tailWord_1548444 prefixEnd_1548444 176688008571254430984187 := by
  unfold tailWord_1548444
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238196201129658013058193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37650928268172877350744257 28238196201129658013058193)
  ·
    refine ⟨21178647150847243509793645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28238196201129658013058193 21178647150847243509793645)
    ·
      refine ⟨7941992681567716316172617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21178647150847243509793645 7941992681567716316172617)
      ·
        refine ⟨5956494511175787237129463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7941992681567716316172617 5956494511175787237129463)
        ·
          refine ⟨8934741766763680855694195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5956494511175787237129463 8934741766763680855694195)
          ·
            refine ⟨13402112650145521283541293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8934741766763680855694195 13402112650145521283541293)
            ·
              refine ⟨5025792243804570481327985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13402112650145521283541293 5025792243804570481327985)
              ·
                refine ⟨3769344182853427860995989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5025792243804570481327985 3769344182853427860995989)
                ·
                  refine ⟨176688008571254430984187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3769344182853427860995989 176688008571254430984187)
                  ·
                    rfl

theorem cell22_1548444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_1548444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548444 prefixEnd_1548444 := by exact prefixLift 1548444
  have htrace : WordTrace (prefixWord ++ tailWord_1548444) baseStart_1548444 baseEnd_1548444 := by
    simpa [prefixWord, tailWord_1548444, baseEnd_1548444] using wordTrace_append hprefix tailTrace_1548444
  have hstable : (prefixWord ++ tailWord_1548444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548444).length < 2 ^ (prefixWord ++ tailWord_1548444).sum := by decide
  have hdescent : baseEnd_1548444 < baseStart_1548444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548472 : List Nat := [2, 1, 2, 1, 2, 1, 13]
def baseStart_1548472 : Nat := 118140960795 + 1548472 * 2 ^ 59
def prefixEnd_1548472 : Nat := 4983230072969 + 3 ^ 40 * 1548472 * 2
def baseEnd_1548472 : Nat := 19632355951332613083425

theorem tailTrace_1548472 : CollatzResearch.WordTrace tailWord_1548472 prefixEnd_1548472 19632355951332613083425 := by
  unfold tailWord_1548472
  simp only [CollatzResearch.WordTrace]
  refine ⟨28238706823078938404067835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37651609097438584538757113 28238706823078938404067835)
  ·
    refine ⟨42358060234618407606101753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28238706823078938404067835 42358060234618407606101753)
    ·
      refine ⟨31768545175963805704576315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42358060234618407606101753 31768545175963805704576315)
      ·
        refine ⟨47652817763945708556864473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31768545175963805704576315 47652817763945708556864473)
        ·
          refine ⟨35739613322959281417648355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47652817763945708556864473 35739613322959281417648355)
          ·
            refine ⟨53609419984438922126472533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35739613322959281417648355 53609419984438922126472533)
            ·
              refine ⟨19632355951332613083425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 53609419984438922126472533 19632355951332613083425)
              ·
                rfl

theorem cell22_1548472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 13].length) (baseStart_1548472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548472 prefixEnd_1548472 := by exact prefixLift 1548472
  have htrace : WordTrace (prefixWord ++ tailWord_1548472) baseStart_1548472 baseEnd_1548472 := by
    simpa [prefixWord, tailWord_1548472, baseEnd_1548472] using wordTrace_append hprefix tailTrace_1548472
  have hstable : (prefixWord ++ tailWord_1548472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548472).length < 2 ^ (prefixWord ++ tailWord_1548472).sum := by decide
  have hdescent : baseEnd_1548472 < baseStart_1548472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548474 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_1548474 : Nat := 118140960795 + 1548474 * 2 ^ 59
def prefixEnd_1548474 : Nat := 4983230072969 + 3 ^ 40 * 1548474 * 2
def baseEnd_1548474 : Nat := 530074295326853214702469

theorem tailTrace_1548474 : CollatzResearch.WordTrace tailWord_1548474 prefixEnd_1548474 530074295326853214702469 := by
  unfold tailWord_1548474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14119371648037657787427119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37651657728100420766472317 14119371648037657787427119)
  ·
    refine ⟨21179057472056486681140679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14119371648037657787427119 21179057472056486681140679)
    ·
      refine ⟨31768586208084730021711019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21179057472056486681140679 31768586208084730021711019)
      ·
        refine ⟨47652879312127095032566529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31768586208084730021711019 47652879312127095032566529)
        ·
          refine ⟨35739659484095321274424897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47652879312127095032566529 35739659484095321274424897)
          ·
            refine ⟨26804744613071490955818673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35739659484095321274424897 26804744613071490955818673)
            ·
              refine ⟨20103558459803618216864005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26804744613071490955818673 20103558459803618216864005)
              ·
                refine ⟨3769417211213178415662001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20103558459803618216864005 3769417211213178415662001)
                ·
                  refine ⟨2827062908409883811746501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769417211213178415662001 2827062908409883811746501)
                  ·
                    refine ⟨530074295326853214702469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827062908409883811746501 530074295326853214702469)
                    ·
                      rfl

theorem cell22_1548474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_1548474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548474 prefixEnd_1548474 := by exact prefixLift 1548474
  have htrace : WordTrace (prefixWord ++ tailWord_1548474) baseStart_1548474 baseEnd_1548474 := by
    simpa [prefixWord, tailWord_1548474, baseEnd_1548474] using wordTrace_append hprefix tailTrace_1548474
  have hstable : (prefixWord ++ tailWord_1548474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548474).length < 2 ^ (prefixWord ++ tailWord_1548474).sum := by decide
  have hdescent : baseEnd_1548474 < baseStart_1548474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548538 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_1548538 : Nat := 118140960795 + 1548538 * 2 ^ 59
def prefixEnd_1548538 : Nat := 4983230072969 + 3 ^ 40 * 1548538 * 2
def baseEnd_1548538 : Nat := 530096203834778381102273

theorem tailTrace_1548538 : CollatzResearch.WordTrace tailWord_1548538 prefixEnd_1548538 530096203834778381102273 := by
  unfold tailWord_1548538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14119955215979692520009567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37653213909279180053358845 14119955215979692520009567)
  ·
    refine ⟨21179932823969538780014351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14119955215979692520009567 21179932823969538780014351)
    ·
      refine ⟨31769899235954308170021527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21179932823969538780014351 31769899235954308170021527)
      ·
        refine ⟨47654848853931462255032291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31769899235954308170021527 47654848853931462255032291)
        ·
          refine ⟨71482273280897193382548437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47654848853931462255032291 71482273280897193382548437)
          ·
            refine ⟨1675365780021027969903479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 71482273280897193382548437 1675365780021027969903479)
            ·
              refine ⟨2513048670031541954855219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675365780021027969903479 2513048670031541954855219)
              ·
                refine ⟨3769573005047312932282829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513048670031541954855219 3769573005047312932282829)
                ·
                  refine ⟨1413589876892742349606061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3769573005047312932282829 1413589876892742349606061)
                  ·
                    refine ⟨530096203834778381102273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413589876892742349606061 530096203834778381102273)
                    ·
                      rfl

theorem cell22_1548538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_1548538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548538 prefixEnd_1548538 := by exact prefixLift 1548538
  have htrace : WordTrace (prefixWord ++ tailWord_1548538) baseStart_1548538 baseEnd_1548538 := by
    simpa [prefixWord, tailWord_1548538, baseEnd_1548538] using wordTrace_append hprefix tailTrace_1548538
  have hstable : (prefixWord ++ tailWord_1548538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548538).length < 2 ^ (prefixWord ++ tailWord_1548538).sum := by decide
  have hdescent : baseEnd_1548538 < baseStart_1548538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548645 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_1548645 : Nat := 118140960795 + 1548645 * 2 ^ 59
def prefixEnd_1548645 : Nat := 4983230072969 + 3 ^ 40 * 1548645 * 2
def baseEnd_1548645 : Nat := 530132832121465768676945

theorem tailTrace_1548645 : CollatzResearch.WordTrace tailWord_1548645 prefixEnd_1548645 530132832121465768676945 := by
  unfold tailWord_1548645
  simp only [CollatzResearch.WordTrace]
  refine ⟨56483723474531127354183389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37655815649687418236122259 56483723474531127354183389)
  ·
    refine ⟨21181396302949172757818771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56483723474531127354183389 21181396302949172757818771)
    ·
      refine ⟨31772094454423759136728157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21181396302949172757818771 31772094454423759136728157)
      ·
        refine ⟨11914535420408909676273059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31772094454423759136728157 11914535420408909676273059)
        ·
          refine ⟨17871803130613364514409589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11914535420408909676273059 17871803130613364514409589)
          ·
            refine ⟨1675481543495002923225899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17871803130613364514409589 1675481543495002923225899)
            ·
              refine ⟨2513222315242504384838849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675481543495002923225899 2513222315242504384838849)
              ·
                refine ⟨1884916736431878288629137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2513222315242504384838849 1884916736431878288629137)
                ·
                  refine ⟨1413687552323908716471853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1884916736431878288629137 1413687552323908716471853)
                  ·
                    refine ⟨530132832121465768676945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413687552323908716471853 530132832121465768676945)
                    ·
                      rfl

theorem cell22_1548645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_1548645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548645 prefixEnd_1548645 := by exact prefixLift 1548645
  have htrace : WordTrace (prefixWord ++ tailWord_1548645) baseStart_1548645 baseEnd_1548645 := by
    simpa [prefixWord, tailWord_1548645, baseEnd_1548645] using wordTrace_append hprefix tailTrace_1548645
  have hstable : (prefixWord ++ tailWord_1548645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548645).length < 2 ^ (prefixWord ++ tailWord_1548645).sum := by decide
  have hdescent : baseEnd_1548645 < baseStart_1548645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548662 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1548662 : Nat := 118140960795 + 1548662 * 2 ^ 59
def prefixEnd_1548662 : Nat := 4983230072969 + 3 ^ 40 * 1548662 * 2
def baseEnd_1548662 : Nat := 530138651568883391001893

theorem tailTrace_1548662 : CollatzResearch.WordTrace tailWord_1548662 prefixEnd_1548662 530138651568883391001893 := by
  unfold tailWord_1548662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530271469716846203597015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37656229010313026171701493 3530271469716846203597015)
  ·
    refine ⟨5295407204575269305395523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3530271469716846203597015 5295407204575269305395523)
    ·
      refine ⟨7943110806862903958093285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5295407204575269305395523 7943110806862903958093285)
      ·
        refine ⟨1489333276286794492142491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7943110806862903958093285 1489333276286794492142491)
        ·
          refine ⟨2233999914430191738213737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489333276286794492142491 2233999914430191738213737)
          ·
            refine ⟨1675499935822643803660303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233999914430191738213737 1675499935822643803660303)
            ·
              refine ⟨2513249903733965705490455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675499935822643803660303 2513249903733965705490455)
              ·
                refine ⟨3769874855600948558235683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513249903733965705490455 3769874855600948558235683)
                ·
                  refine ⟨5654812283401422837353525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3769874855600948558235683 5654812283401422837353525)
                  ·
                    refine ⟨530138651568883391001893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5654812283401422837353525 530138651568883391001893)
                    ·
                      rfl

theorem cell22_1548662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1548662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548662 prefixEnd_1548662 := by exact prefixLift 1548662
  have htrace : WordTrace (prefixWord ++ tailWord_1548662) baseStart_1548662 baseEnd_1548662 := by
    simpa [prefixWord, tailWord_1548662, baseEnd_1548662] using wordTrace_append hprefix tailTrace_1548662
  have hstable : (prefixWord ++ tailWord_1548662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548662).length < 2 ^ (prefixWord ++ tailWord_1548662).sum := by decide
  have hdescent : baseEnd_1548662 < baseStart_1548662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548675 : List Nat := [1, 1, 1, 3, 7, 1, 2, 6]
def baseStart_1548675 : Nat := 118140960795 + 1548675 * 2 ^ 59
def prefixEnd_1548675 : Nat := 4983230072969 + 3 ^ 40 * 1548675 * 2
def baseEnd_1548675 : Nat := 58904789081617298936317

theorem tailTrace_1548675 : CollatzResearch.WordTrace tailWord_1548675 prefixEnd_1548675 58904789081617298936317 := by
  unfold tailWord_1548675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56484817664422442477775479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37656545109614961651850319 56484817664422442477775479)
  ·
    refine ⟨84727226496633663716663219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56484817664422442477775479 84727226496633663716663219)
    ·
      refine ⟨127090839744950495574994829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84727226496633663716663219 127090839744950495574994829)
      ·
        refine ⟨47659064904356435840623061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127090839744950495574994829 47659064904356435840623061)
        ·
          refine ⟨1117009333695853965014603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47659064904356435840623061 1117009333695853965014603)
          ·
            refine ⟨1675514000543780947521905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117009333695853965014603 1675514000543780947521905)
            ·
              refine ⟨1256635500407835710641429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1675514000543780947521905 1256635500407835710641429)
              ·
                refine ⟨58904789081617298936317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1256635500407835710641429 58904789081617298936317)
                ·
                  rfl

theorem cell22_1548675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 6].length) (baseStart_1548675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548675 prefixEnd_1548675 := by exact prefixLift 1548675
  have htrace : WordTrace (prefixWord ++ tailWord_1548675) baseStart_1548675 baseEnd_1548675 := by
    simpa [prefixWord, tailWord_1548675, baseEnd_1548675] using wordTrace_append hprefix tailTrace_1548675
  have hstable : (prefixWord ++ tailWord_1548675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548675).length < 2 ^ (prefixWord ++ tailWord_1548675).sum := by decide
  have hdescent : baseEnd_1548675 < baseStart_1548675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548694 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1548694 : Nat := 118140960795 + 1548694 * 2 ^ 59
def prefixEnd_1548694 : Nat := 4983230072969 + 3 ^ 40 * 1548694 * 2
def baseEnd_1548694 : Nat := 530149605822845974201795

theorem tailTrace_1548694 : CollatzResearch.WordTrace tailWord_1548694 prefixEnd_1548694 530149605822845974201795 := by
  unfold tailWord_1548694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3530344415709600545169821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37657007100902405815144757 3530344415709600545169821)
  ·
    refine ⟨1323879155891100204438683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3530344415709600545169821 1323879155891100204438683)
    ·
      refine ⟨1985818733836650306658025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323879155891100204438683 1985818733836650306658025)
      ·
        refine ⟨1489364050377487729993519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1985818733836650306658025 1489364050377487729993519)
        ·
          refine ⟨2234046075566231594990279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489364050377487729993519 2234046075566231594990279)
          ·
            refine ⟨3351069113349347392485419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234046075566231594990279 3351069113349347392485419)
            ·
              refine ⟨5026603670024021088728129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351069113349347392485419 5026603670024021088728129)
              ·
                refine ⟨3769952752518015816546097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5026603670024021088728129 3769952752518015816546097)
                ·
                  refine ⟨2827464564388511862409573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3769952752518015816546097 2827464564388511862409573)
                  ·
                    refine ⟨530149605822845974201795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827464564388511862409573 530149605822845974201795)
                    ·
                      rfl

theorem cell22_1548694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1548694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548694 prefixEnd_1548694 := by exact prefixLift 1548694
  have htrace : WordTrace (prefixWord ++ tailWord_1548694) baseStart_1548694 baseEnd_1548694 := by
    simpa [prefixWord, tailWord_1548694, baseEnd_1548694] using wordTrace_append hprefix tailTrace_1548694
  have hstable : (prefixWord ++ tailWord_1548694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548694).length < 2 ^ (prefixWord ++ tailWord_1548694).sum := by decide
  have hdescent : baseEnd_1548694 < baseStart_1548694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548707 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 1, 3]
def baseStart_1548707 : Nat := 118140960795 + 1548707 * 2 ^ 59
def prefixEnd_1548707 : Nat := 4983230072969 + 3 ^ 40 * 1548707 * 2
def baseEnd_1548707 : Nat := 530154055988518273626755

theorem tailTrace_1548707 : CollatzResearch.WordTrace tailWord_1548707 prefixEnd_1548707 530154055988518273626755 := by
  unfold tailWord_1548707
  simp only [CollatzResearch.WordTrace]
  refine ⟨56485984800306511942940375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37657323200204341295293583 56485984800306511942940375)
  ·
    refine ⟨84728977200459767914410563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56485984800306511942940375 84728977200459767914410563)
    ·
      refine ⟨127093465800689651871615845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84728977200459767914410563 127093465800689651871615845)
      ·
        refine ⟨23830024837629309725927971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127093465800689651871615845 23830024837629309725927971)
        ·
          refine ⟨35745037256443964588891957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23830024837629309725927971 35745037256443964588891957)
          ·
            refine ⟨3351097242791621680208621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35745037256443964588891957 3351097242791621680208621)
            ·
              refine ⟨1256661466046858130078233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3351097242791621680208621 1256661466046858130078233)
              ·
                refine ⟨942496099535143597558675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1256661466046858130078233 942496099535143597558675)
                ·
                  refine ⟨1413744149302715396338013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942496099535143597558675 1413744149302715396338013)
                  ·
                    refine ⟨530154055988518273626755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413744149302715396338013 530154055988518273626755)
                    ·
                      rfl

theorem cell22_1548707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 3].length) (baseStart_1548707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548707 prefixEnd_1548707 := by exact prefixLift 1548707
  have htrace : WordTrace (prefixWord ++ tailWord_1548707) baseStart_1548707 baseEnd_1548707 := by
    simpa [prefixWord, tailWord_1548707, baseEnd_1548707] using wordTrace_append hprefix tailTrace_1548707
  have hstable : (prefixWord ++ tailWord_1548707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548707).length < 2 ^ (prefixWord ++ tailWord_1548707).sum := by decide
  have hdescent : baseEnd_1548707 < baseStart_1548707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548716 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_1548716 : Nat := 118140960795 + 1548716 * 2 ^ 59
def prefixEnd_1548716 : Nat := 4983230072969 + 3 ^ 40 * 1548716 * 2
def baseEnd_1548716 : Nat := 530157136872445250151727

theorem tailTrace_1548716 : CollatzResearch.WordTrace tailWord_1548716 prefixEnd_1548716 530157136872445250151727 := by
  unfold tailWord_1548716
  simp only [CollatzResearch.WordTrace]
  refine ⟨28243156528636953240009001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37657542038182604320012001 28243156528636953240009001)
  ·
    refine ⟨21182367396477714930006751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28243156528636953240009001 21182367396477714930006751)
    ·
      refine ⟨31773551094716572395010127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21182367396477714930006751 31773551094716572395010127)
      ·
        refine ⟨47660326642074858592515191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31773551094716572395010127 47660326642074858592515191)
        ·
          refine ⟨71490489963112287888772787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47660326642074858592515191 71490489963112287888772787)
          ·
            refine ⟨107235734944668431833159181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71490489963112287888772787 107235734944668431833159181)
            ·
              refine ⟨40213400604250661937434693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107235734944668431833159181 40213400604250661937434693)
              ·
                refine ⟨7540012613296999113269005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40213400604250661937434693 7540012613296999113269005)
                ·
                  refine ⟨2827504729986374667475877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7540012613296999113269005 2827504729986374667475877)
                  ·
                    refine ⟨530157136872445250151727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827504729986374667475877 530157136872445250151727)
                    ·
                      rfl

theorem cell22_1548716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_1548716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548716 prefixEnd_1548716 := by exact prefixLift 1548716
  have htrace : WordTrace (prefixWord ++ tailWord_1548716) baseStart_1548716 baseEnd_1548716 := by
    simpa [prefixWord, tailWord_1548716, baseEnd_1548716] using wordTrace_append hprefix tailTrace_1548716
  have hstable : (prefixWord ++ tailWord_1548716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548716).length < 2 ^ (prefixWord ++ tailWord_1548716).sum := by decide
  have hdescent : baseEnd_1548716 < baseStart_1548716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548733 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 3, 4]
def baseStart_1548733 : Nat := 118140960795 + 1548733 * 2 ^ 59
def prefixEnd_1548733 : Nat := 4983230072969 + 3 ^ 40 * 1548733 * 2
def baseEnd_1548733 : Nat := 530162956319862872476675

theorem tailTrace_1548733 : CollatzResearch.WordTrace tailWord_1548733 prefixEnd_1548733 530162956319862872476675 := by
  unfold tailWord_1548733
  simp only [CollatzResearch.WordTrace]
  refine ⟨56486933098212318383386853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37657955398808212255591235 56486933098212318383386853)
  ·
    refine ⟨10591299955914809696885035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56486933098212318383386853 10591299955914809696885035)
    ·
      refine ⟨15886949933872214545327553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10591299955914809696885035 15886949933872214545327553)
      ·
        refine ⟨11915212450404160908995665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15886949933872214545327553 11915212450404160908995665)
        ·
          refine ⟨8936409337803120681746749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11915212450404160908995665 8936409337803120681746749)
          ·
            refine ⟨3351153501676170255655031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8936409337803120681746749 3351153501676170255655031)
            ·
              refine ⟨5026730252514255383482547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351153501676170255655031 5026730252514255383482547)
              ·
                refine ⟨7540095378771383075223821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5026730252514255383482547 7540095378771383075223821)
                ·
                  refine ⟨2827535767039268653208933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7540095378771383075223821 2827535767039268653208933)
                  ·
                    refine ⟨530162956319862872476675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2827535767039268653208933 530162956319862872476675)
                    ·
                      rfl

theorem cell22_1548733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_1548733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548733 prefixEnd_1548733 := by exact prefixLift 1548733
  have htrace : WordTrace (prefixWord ++ tailWord_1548733) baseStart_1548733 baseEnd_1548733 := by
    simpa [prefixWord, tailWord_1548733, baseEnd_1548733] using wordTrace_append hprefix tailTrace_1548733
  have hstable : (prefixWord ++ tailWord_1548733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548733).length < 2 ^ (prefixWord ++ tailWord_1548733).sum := by decide
  have hdescent : baseEnd_1548733 < baseStart_1548733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548765 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 4]
def baseStart_1548765 : Nat := 118140960795 + 1548765 * 2 ^ 59
def prefixEnd_1548765 : Nat := 4983230072969 + 3 ^ 40 * 1548765 * 2
def baseEnd_1548765 : Nat := 176724636857941818558859

theorem tailTrace_1548765 : CollatzResearch.WordTrace tailWord_1548765 prefixEnd_1548765 176724636857941818558859 := by
  unfold tailWord_1548765
  simp only [CollatzResearch.WordTrace]
  refine ⟨56488100234096387848551749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37658733489397591899034499 56488100234096387848551749)
  ·
    refine ⟨10591518793893072721603453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56488100234096387848551749 10591518793893072721603453)
    ·
      refine ⟨3971819547709902270601295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10591518793893072721603453 3971819547709902270601295)
      ·
        refine ⟨5957729321564853405901943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971819547709902270601295 5957729321564853405901943)
        ·
          refine ⟨8936593982347280108852915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5957729321564853405901943 8936593982347280108852915)
          ·
            refine ⟨13404890973520920163279373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8936593982347280108852915 13404890973520920163279373)
            ·
              refine ⟨5026834115070345061229765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13404890973520920163279373 5026834115070345061229765)
              ·
                refine ⟨942531396575689698980581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5026834115070345061229765 942531396575689698980581)
                ·
                  refine ⟨176724636857941818558859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942531396575689698980581 176724636857941818558859)
                  ·
                    rfl

theorem cell22_1548765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_1548765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548765 prefixEnd_1548765 := by exact prefixLift 1548765
  have htrace : WordTrace (prefixWord ++ tailWord_1548765) baseStart_1548765 baseEnd_1548765 := by
    simpa [prefixWord, tailWord_1548765, baseEnd_1548765] using wordTrace_append hprefix tailTrace_1548765
  have hstable : (prefixWord ++ tailWord_1548765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548765).length < 2 ^ (prefixWord ++ tailWord_1548765).sum := by decide
  have hdescent : baseEnd_1548765 < baseStart_1548765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548808 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 7, 3]
def baseStart_1548808 : Nat := 118140960795 + 1548808 * 2 ^ 59
def prefixEnd_1548808 : Nat := 4983230072969 + 3 ^ 40 * 1548808 * 2
def baseEnd_1548808 : Nat := 530188630352587676851445

theorem tailTrace_1548808 : CollatzResearch.WordTrace tailWord_1548808 prefixEnd_1548808 530188630352587676851445 := by
  unfold tailWord_1548808
  simp only [CollatzResearch.WordTrace]
  refine ⟨28244834286470303096183539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37659779048627070794911385 28244834286470303096183539)
  ·
    refine ⟨42367251429705454644275309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28244834286470303096183539 42367251429705454644275309)
    ·
      refine ⟨15887719286139545491603241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42367251429705454644275309 15887719286139545491603241)
      ·
        refine ⟨11915789464604659118702431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15887719286139545491603241 11915789464604659118702431)
        ·
          refine ⟨17873684196906988678053647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11915789464604659118702431 17873684196906988678053647)
          ·
            refine ⟨26810526295360483017080471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17873684196906988678053647 26810526295360483017080471)
            ·
              refine ⟨40215789443040724525620707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26810526295360483017080471 40215789443040724525620707)
              ·
                refine ⟨60323684164561086788431061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40215789443040724525620707 60323684164561086788431061)
                ·
                  refine ⟨1413836347606900471603853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60323684164561086788431061 1413836347606900471603853)
                  ·
                    refine ⟨530188630352587676851445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413836347606900471603853 530188630352587676851445)
                    ·
                      rfl

theorem cell22_1548808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_1548808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548808 prefixEnd_1548808 := by exact prefixLift 1548808
  have htrace : WordTrace (prefixWord ++ tailWord_1548808) baseStart_1548808 baseEnd_1548808 := by
    simpa [prefixWord, tailWord_1548808, baseEnd_1548808] using wordTrace_append hprefix tailTrace_1548808
  have hstable : (prefixWord ++ tailWord_1548808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548808).length < 2 ^ (prefixWord ++ tailWord_1548808).sum := by decide
  have hdescent : baseEnd_1548808 < baseStart_1548808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548932 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1548932 : Nat := 118140960795 + 1548932 * 2 ^ 59
def prefixEnd_1548932 : Nat := 4983230072969 + 3 ^ 40 * 1548932 * 2
def baseEnd_1548932 : Nat := 530231078086692686751065

theorem tailTrace_1548932 : CollatzResearch.WordTrace tailWord_1548932 prefixEnd_1548932 530231078086692686751065 := by
  unfold tailWord_1548932
  simp only [CollatzResearch.WordTrace]
  refine ⟨28247095612245687684940525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37662794149660916913254033 28247095612245687684940525)
  ·
    refine ⟨10592660854592132881852697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28247095612245687684940525 10592660854592132881852697)
    ·
      refine ⟨7944495640944099661389523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10592660854592132881852697 7944495640944099661389523)
      ·
        refine ⟨11916743461416149492084285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7944495640944099661389523 11916743461416149492084285)
        ·
          refine ⟨4468778798031056059531607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11916743461416149492084285 4468778798031056059531607)
          ·
            refine ⟨6703168197046584089297411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4468778798031056059531607 6703168197046584089297411)
            ·
              refine ⟨10054752295569876133946117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6703168197046584089297411 10054752295569876133946117)
              ·
                refine ⟨1885266055419351775114897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10054752295569876133946117 1885266055419351775114897)
                ·
                  refine ⟨1413949541564513831336173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885266055419351775114897 1413949541564513831336173)
                  ·
                    refine ⟨530231078086692686751065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1413949541564513831336173 530231078086692686751065)
                    ·
                      rfl

theorem cell22_1548932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1548932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548932 prefixEnd_1548932 := by exact prefixLift 1548932
  have htrace : WordTrace (prefixWord ++ tailWord_1548932) baseStart_1548932 baseEnd_1548932 := by
    simpa [prefixWord, tailWord_1548932, baseEnd_1548932] using wordTrace_append hprefix tailTrace_1548932
  have hstable : (prefixWord ++ tailWord_1548932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548932).length < 2 ^ (prefixWord ++ tailWord_1548932).sum := by decide
  have hdescent : baseEnd_1548932 < baseStart_1548932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1548990 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1548990 : Nat := 118140960795 + 1548990 * 2 ^ 59
def prefixEnd_1548990 : Nat := 4983230072969 + 3 ^ 40 * 1548990 * 2
def baseEnd_1548990 : Nat := 176750310890666622933629

theorem tailTrace_1548990 : CollatzResearch.WordTrace tailWord_1548990 prefixEnd_1548990 176750310890666622933629 := by
  unfold tailWord_1548990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062038332285156409436553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37664204438854167516994949 7062038332285156409436553)
  ·
    refine ⟨5296528749213867307077415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7062038332285156409436553 5296528749213867307077415)
    ·
      refine ⟨7944793123820800960616123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296528749213867307077415 7944793123820800960616123)
      ·
        refine ⟨11917189685731201440924185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7944793123820800960616123 11917189685731201440924185)
        ·
          refine ⟨8937892264298401080693139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11917189685731201440924185 8937892264298401080693139)
          ·
            refine ⟨13406838396447601621039709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8937892264298401080693139 13406838396447601621039709)
            ·
              refine ⟨5027564398667850607889891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13406838396447601621039709 5027564398667850607889891)
              ·
                refine ⟨7541346598001775911834837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5027564398667850607889891 7541346598001775911834837)
                ·
                  refine ⟨176750310890666622933629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7541346598001775911834837 176750310890666622933629)
                  ·
                    rfl

theorem cell22_1548990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1548990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1548990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1548990 prefixEnd_1548990 := by exact prefixLift 1548990
  have htrace : WordTrace (prefixWord ++ tailWord_1548990) baseStart_1548990 baseEnd_1548990 := by
    simpa [prefixWord, tailWord_1548990, baseEnd_1548990] using wordTrace_append hprefix tailTrace_1548990
  have hstable : (prefixWord ++ tailWord_1548990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1548990).length < 2 ^ (prefixWord ++ tailWord_1548990).sum := by decide
  have hdescent : baseEnd_1548990 < baseStart_1548990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1548990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549037 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1549037 : Nat := 118140960795 + 1549037 * 2 ^ 59
def prefixEnd_1549037 : Nat := 4983230072969 + 3 ^ 40 * 1549037 * 2
def baseEnd_1549037 : Nat := 530267021732507412875743

theorem tailTrace_1549037 : CollatzResearch.WordTrace tailWord_1549037 prefixEnd_1549037 530267021732507412875743 := by
  unfold tailWord_1549037
  simp only [CollatzResearch.WordTrace]
  refine ⟨56498020889110978302453365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37665347259407318868302243 56498020889110978302453365)
  ·
    refine ⟨5296689458354154215855003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56498020889110978302453365 5296689458354154215855003)
    ·
      refine ⟨7945034187531231323782505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5296689458354154215855003 7945034187531231323782505)
      ·
        refine ⟨5958775640648423492836879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7945034187531231323782505 5958775640648423492836879)
        ·
          refine ⟨8938163460972635239255319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5958775640648423492836879 8938163460972635239255319)
          ·
            refine ⟨13407245191458952858882979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8938163460972635239255319 13407245191458952858882979)
            ·
              refine ⟨20110867787188429288324469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13407245191458952858882979 20110867787188429288324469)
              ·
                refine ⟨1885393855048915245780419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20110867787188429288324469 1885393855048915245780419)
                ·
                  refine ⟨2828090782573372868670629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885393855048915245780419 2828090782573372868670629)
                  ·
                    refine ⟨530267021732507412875743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828090782573372868670629 530267021732507412875743)
                    ·
                      rfl

theorem cell22_1549037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1549037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549037 prefixEnd_1549037 := by exact prefixLift 1549037
  have htrace : WordTrace (prefixWord ++ tailWord_1549037) baseStart_1549037 baseEnd_1549037 := by
    simpa [prefixWord, tailWord_1549037, baseEnd_1549037] using wordTrace_append hprefix tailTrace_1549037
  have hstable : (prefixWord ++ tailWord_1549037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549037).length < 2 ^ (prefixWord ++ tailWord_1549037).sum := by decide
  have hdescent : baseEnd_1549037 < baseStart_1549037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549045 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 3, 3]
def baseStart_1549045 : Nat := 118140960795 + 1549045 * 2 ^ 59
def prefixEnd_1549045 : Nat := 4983230072969 + 3 ^ 40 * 1549045 * 2
def baseEnd_1549045 : Nat := 530269760295998058675719

theorem tailTrace_1549045 : CollatzResearch.WordTrace tailWord_1549045 prefixEnd_1549045 530269760295998058675719 := by
  unfold tailWord_1549045
  simp only [CollatzResearch.WordTrace]
  refine ⟨56498312673081995668744589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37665541782054663779163059 56498312673081995668744589)
  ·
    refine ⟨21186867252405748375779221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56498312673081995668744589 21186867252405748375779221)
    ·
      refine ⟨993134402456519455114651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21186867252405748375779221 993134402456519455114651)
      ·
        refine ⟨1489701603684779182671977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993134402456519455114651 1489701603684779182671977)
        ·
          refine ⟨1117276202763584387003983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1489701603684779182671977 1117276202763584387003983)
          ·
            refine ⟨1675914304145376580505975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117276202763584387003983 1675914304145376580505975)
            ·
              refine ⟨2513871456218064870758963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675914304145376580505975 2513871456218064870758963)
              ·
                refine ⟨3770807184327097306138445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513871456218064870758963 3770807184327097306138445)
                ·
                  refine ⟨1414052694122661489801917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3770807184327097306138445 1414052694122661489801917)
                  ·
                    refine ⟨530269760295998058675719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414052694122661489801917 530269760295998058675719)
                    ·
                      rfl

theorem cell22_1549045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_1549045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549045 prefixEnd_1549045 := by exact prefixLift 1549045
  have htrace : WordTrace (prefixWord ++ tailWord_1549045) baseStart_1549045 baseEnd_1549045 := by
    simpa [prefixWord, tailWord_1549045, baseEnd_1549045] using wordTrace_append hprefix tailTrace_1549045
  have hstable : (prefixWord ++ tailWord_1549045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549045).length < 2 ^ (prefixWord ++ tailWord_1549045).sum := by decide
  have hdescent : baseEnd_1549045 < baseStart_1549045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549052 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_1549052 : Nat := 118140960795 + 1549052 * 2 ^ 59
def prefixEnd_1549052 : Nat := 4983230072969 + 3 ^ 40 * 1549052 * 2
def baseEnd_1549052 : Nat := 176757385513017457916899

theorem tailTrace_1549052 : CollatzResearch.WordTrace tailWord_1549052 prefixEnd_1549052 176757385513017457916899 := by
  unfold tailWord_1549052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28249283992028317932124705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37665711989371090576166273 28249283992028317932124705)
  ·
    refine ⟨21186962994021238449093529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28249283992028317932124705 21186962994021238449093529)
    ·
      refine ⟨15890222245515928836820147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21186962994021238449093529 15890222245515928836820147)
      ·
        refine ⟨23835333368273893255230221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15890222245515928836820147 23835333368273893255230221)
        ·
          refine ⟨8938250013102709970711333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23835333368273893255230221 8938250013102709970711333)
          ·
            refine ⟨1675921877456758119508375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8938250013102709970711333 1675921877456758119508375)
            ·
              refine ⟨2513882816185137179262563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675921877456758119508375 2513882816185137179262563)
              ·
                refine ⟨3770824224277705768893845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513882816185137179262563 3770824224277705768893845)
                ·
                  refine ⟨176757385513017457916899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3770824224277705768893845 176757385513017457916899)
                  ·
                    rfl

theorem cell22_1549052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_1549052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549052 prefixEnd_1549052 := by exact prefixLift 1549052
  have htrace : WordTrace (prefixWord ++ tailWord_1549052) baseStart_1549052 baseEnd_1549052 := by
    simpa [prefixWord, tailWord_1549052, baseEnd_1549052] using wordTrace_append hprefix tailTrace_1549052
  have hstable : (prefixWord ++ tailWord_1549052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549052).length < 2 ^ (prefixWord ++ tailWord_1549052).sum := by decide
  have hdescent : baseEnd_1549052 < baseStart_1549052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549082 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_1549082 : Nat := 118140960795 + 1549082 * 2 ^ 59
def prefixEnd_1549082 : Nat := 4983230072969 + 3 ^ 40 * 1549082 * 2
def baseEnd_1549082 : Nat := 530282426152142295500605

theorem tailTrace_1549082 : CollatzResearch.WordTrace tailWord_1549082 prefixEnd_1549082 530282426152142295500605 := by
  unfold tailWord_1549082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14124915543486987746960375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37666441449298633991894333 14124915543486987746960375)
  ·
    refine ⟨21187373315230481620440563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14124915543486987746960375 21187373315230481620440563)
    ·
      refine ⟨31781059972845722430660845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21187373315230481620440563 31781059972845722430660845)
      ·
        refine ⟨11917897489817145911497817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31781059972845722430660845 11917897489817145911497817)
        ·
          refine ⟨8938423117362859433623363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11917897489817145911497817 8938423117362859433623363)
          ·
            refine ⟨13407634676044289150435045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8938423117362859433623363 13407634676044289150435045)
            ·
              refine ⟨2513931501758304215706571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13407634676044289150435045 2513931501758304215706571)
              ·
                refine ⟨3770897252637456323559857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2513931501758304215706571 3770897252637456323559857)
                ·
                  refine ⟨2828172939478092242669893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3770897252637456323559857 2828172939478092242669893)
                  ·
                    refine ⟨530282426152142295500605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828172939478092242669893 530282426152142295500605)
                    ·
                      rfl

theorem cell22_1549082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_1549082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549082 prefixEnd_1549082 := by exact prefixLift 1549082
  have htrace : WordTrace (prefixWord ++ tailWord_1549082) baseStart_1549082 baseEnd_1549082 := by
    simpa [prefixWord, tailWord_1549082, baseEnd_1549082] using wordTrace_append hprefix tailTrace_1549082
  have hstable : (prefixWord ++ tailWord_1549082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549082).length < 2 ^ (prefixWord ++ tailWord_1549082).sum := by decide
  have hdescent : baseEnd_1549082 < baseStart_1549082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549112 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1549112 : Nat := 118140960795 + 1549112 * 2 ^ 59
def prefixEnd_1549112 : Nat := 4983230072969 + 3 ^ 40 * 1549112 * 2
def baseEnd_1549112 : Nat := 530292695765232217250513

theorem tailTrace_1549112 : CollatzResearch.WordTrace tailWord_1549112 prefixEnd_1549112 530292695765232217250513 := by
  unfold tailWord_1549112
  simp only [CollatzResearch.WordTrace]
  refine ⟨28250378181919633055716795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37667170909226177407622393 28250378181919633055716795)
  ·
    refine ⟨42375567272879449583575193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28250378181919633055716795 42375567272879449583575193)
    ·
      refine ⟨31781675454659587187681395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42375567272879449583575193 31781675454659587187681395)
      ·
        refine ⟨47672513181989380781522093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31781675454659587187681395 47672513181989380781522093)
        ·
          refine ⟨17877192443246017793070785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47672513181989380781522093 17877192443246017793070785)
          ·
            refine ⟨13407894332434513344803089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17877192443246017793070785 13407894332434513344803089)
            ·
              refine ⟨10055920749325885008602317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13407894332434513344803089 10055920749325885008602317)
              ·
                refine ⟨3770970280997206878225869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10055920749325885008602317 3770970280997206878225869)
                ·
                  refine ⟨1414113855373952579334701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3770970280997206878225869 1414113855373952579334701)
                  ·
                    refine ⟨530292695765232217250513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414113855373952579334701 530292695765232217250513)
                    ·
                      rfl

theorem cell22_1549112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1549112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549112 prefixEnd_1549112 := by exact prefixLift 1549112
  have htrace : WordTrace (prefixWord ++ tailWord_1549112) baseStart_1549112 baseEnd_1549112 := by
    simpa [prefixWord, tailWord_1549112, baseEnd_1549112] using wordTrace_append hprefix tailTrace_1549112
  have hstable : (prefixWord ++ tailWord_1549112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549112).length < 2 ^ (prefixWord ++ tailWord_1549112).sum := by decide
  have hdescent : baseEnd_1549112 < baseStart_1549112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549114 : List Nat := [3, 1, 1, 1, 7, 1, 1, 7]
def baseStart_1549114 : Nat := 118140960795 + 1549114 * 2 ^ 59
def prefixEnd_1549114 : Nat := 4983230072969 + 3 ^ 40 * 1549114 * 2
def baseEnd_1549114 : Nat := 58921486711789430966723

theorem tailTrace_1549114 : CollatzResearch.WordTrace tailWord_1549114 prefixEnd_1549114 58921486711789430966723 := by
  unfold tailWord_1549114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125207327458005113251599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37667219539888013635337597 14125207327458005113251599)
  ·
    refine ⟨21187810991187007669877399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14125207327458005113251599 21187810991187007669877399)
    ·
      refine ⟨31781716486780511504816099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21187810991187007669877399 31781716486780511504816099)
      ·
        refine ⟨47672574730170767257224149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31781716486780511504816099 47672574730170767257224149)
        ·
          refine ⟨1117325970238377357591191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47672574730170767257224149 1117325970238377357591191)
          ·
            refine ⟨1675988955357566036386787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117325970238377357591191 1675988955357566036386787)
            ·
              refine ⟨2513983433036349054580181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1675988955357566036386787 2513983433036349054580181)
              ·
                refine ⟨58921486711789430966723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2513983433036349054580181 58921486711789430966723)
                ·
                  rfl

theorem cell22_1549114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_1549114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549114 prefixEnd_1549114 := by exact prefixLift 1549114
  have htrace : WordTrace (prefixWord ++ tailWord_1549114) baseStart_1549114 baseEnd_1549114 := by
    simpa [prefixWord, tailWord_1549114, baseEnd_1549114] using wordTrace_append hprefix tailTrace_1549114
  have hstable : (prefixWord ++ tailWord_1549114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549114).length < 2 ^ (prefixWord ++ tailWord_1549114).sum := by decide
  have hdescent : baseEnd_1549114 < baseStart_1549114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549133 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1549133 : Nat := 118140960795 + 1549133 * 2 ^ 59
def prefixEnd_1549133 : Nat := 4983230072969 + 3 ^ 40 * 1549133 * 2
def baseEnd_1549133 : Nat := 530299884494395162475449

theorem tailTrace_1549133 : CollatzResearch.WordTrace tailWord_1549133 prefixEnd_1549133 530299884494395162475449 := by
  unfold tailWord_1549133
  simp only [CollatzResearch.WordTrace]
  refine ⟨56501522296763186697948053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37667681531175457798632035 56501522296763186697948053)
  ·
    refine ⟨2648508857660774376466315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56501522296763186697948053 2648508857660774376466315)
    ·
      refine ⟨3972763286491161564699473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2648508857660774376466315 3972763286491161564699473)
      ·
        refine ⟨2979572464868371173524605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3972763286491161564699473 2979572464868371173524605)
        ·
          refine ⟨1117339674325639190071727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2979572464868371173524605 1117339674325639190071727)
          ·
            refine ⟨1676009511488458785107591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117339674325639190071727 1676009511488458785107591)
            ·
              refine ⟨2514014267232688177661387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676009511488458785107591 2514014267232688177661387)
              ·
                refine ⟨3771021400849032266492081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514014267232688177661387 3771021400849032266492081)
                ·
                  refine ⟨2828266050636774199869061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3771021400849032266492081 2828266050636774199869061)
                  ·
                    refine ⟨530299884494395162475449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828266050636774199869061 530299884494395162475449)
                    ·
                      rfl

theorem cell22_1549133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1549133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549133 prefixEnd_1549133 := by exact prefixLift 1549133
  have htrace : WordTrace (prefixWord ++ tailWord_1549133) baseStart_1549133 baseEnd_1549133 := by
    simpa [prefixWord, tailWord_1549133, baseEnd_1549133] using wordTrace_append hprefix tailTrace_1549133
  have hstable : (prefixWord ++ tailWord_1549133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549133).length < 2 ^ (prefixWord ++ tailWord_1549133).sum := by decide
  have hdescent : baseEnd_1549133 < baseStart_1549133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549146 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_1549146 : Nat := 118140960795 + 1549146 * 2 ^ 59
def prefixEnd_1549146 : Nat := 4983230072969 + 3 ^ 40 * 1549146 * 2
def baseEnd_1549146 : Nat := 530304334660067461900409

theorem tailTrace_1549146 : CollatzResearch.WordTrace tailWord_1549146 prefixEnd_1549146 530304334660067461900409 := by
  unfold tailWord_1549146
  simp only [CollatzResearch.WordTrace]
  refine ⟨14125499111429022479542823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37667997630477393278780861 14125499111429022479542823)
  ·
    refine ⟨21188248667143533719314235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14125499111429022479542823 21188248667143533719314235)
    ·
      refine ⟨31782373000715300578971353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21188248667143533719314235 31782373000715300578971353)
      ·
        refine ⟨23836779750536475434228515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31782373000715300578971353 23836779750536475434228515)
        ·
          refine ⟨35755169625804713151342773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23836779750536475434228515 35755169625804713151342773)
          ·
            refine ⟨3352047152419191857938385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35755169625804713151342773 3352047152419191857938385)
            ·
              refine ⟨2514035364314393893453789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352047152419191857938385 2514035364314393893453789)
              ·
                refine ⟨942763261617897710045171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2514035364314393893453789 942763261617897710045171)
                ·
                  refine ⟨1414144892426846565067757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 942763261617897710045171 1414144892426846565067757)
                  ·
                    refine ⟨530304334660067461900409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414144892426846565067757 530304334660067461900409)
                    ·
                      rfl

theorem cell22_1549146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_1549146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549146 prefixEnd_1549146 := by exact prefixLift 1549146
  have htrace : WordTrace (prefixWord ++ tailWord_1549146) baseStart_1549146 baseEnd_1549146 := by
    simpa [prefixWord, tailWord_1549146, baseEnd_1549146] using wordTrace_append hprefix tailTrace_1549146
  have hstable : (prefixWord ++ tailWord_1549146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549146).length < 2 ^ (prefixWord ++ tailWord_1549146).sum := by decide
  have hdescent : baseEnd_1549146 < baseStart_1549146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549159 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 5]
def baseStart_1549159 : Nat := 118140960795 + 1549159 * 2 ^ 59
def prefixEnd_1549159 : Nat := 4983230072969 + 3 ^ 40 * 1549159 * 2
def baseEnd_1549159 : Nat := 176769594941913253775123

theorem tailTrace_1549159 : CollatzResearch.WordTrace tailWord_1549159 prefixEnd_1549159 176769594941913253775123 := by
  unfold tailWord_1549159
  simp only [CollatzResearch.WordTrace]
  refine ⟨56502470594668993138394531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37668313729779328758929687 56502470594668993138394531)
  ·
    refine ⟨84753705892003489707591797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56502470594668993138394531 84753705892003489707591797)
    ·
      refine ⟨7945659927375327160086731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84753705892003489707591797 7945659927375327160086731)
      ·
        refine ⟨11918489891062990740130097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7945659927375327160086731 11918489891062990740130097)
        ·
          refine ⟨8938867418297243055097573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11918489891062990740130097 8938867418297243055097573)
          ·
            refine ⟨1676037640930733072830795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8938867418297243055097573 1676037640930733072830795)
            ·
              refine ⟨2514056461396099609246193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676037640930733072830795 2514056461396099609246193)
              ·
                refine ⟨1885542346047074706934645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514056461396099609246193 1885542346047074706934645)
                ·
                  refine ⟨176769594941913253775123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1885542346047074706934645 176769594941913253775123)
                  ·
                    rfl

theorem cell22_1549159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 5].length) (baseStart_1549159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549159 prefixEnd_1549159 := by exact prefixLift 1549159
  have htrace : WordTrace (prefixWord ++ tailWord_1549159) baseStart_1549159 baseEnd_1549159 := by
    simpa [prefixWord, tailWord_1549159, baseEnd_1549159] using wordTrace_append hprefix tailTrace_1549159
  have hstable : (prefixWord ++ tailWord_1549159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549159).length < 2 ^ (prefixWord ++ tailWord_1549159).sum := by decide
  have hdescent : baseEnd_1549159 < baseStart_1549159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549174 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1549174 : Nat := 118140960795 + 1549174 * 2 ^ 59
def prefixEnd_1549174 : Nat := 4983230072969 + 3 ^ 40 * 1549174 * 2
def baseEnd_1549174 : Nat := 530313919632284722200323

theorem tailTrace_1549174 : CollatzResearch.WordTrace tailWord_1549174 prefixEnd_1549174 530313919632284722200323 := by
  unfold tailWord_1549174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531438605600915668761911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37668678459743100466793717 3531438605600915668761911)
  ·
    refine ⟨5297157908401373503142867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531438605600915668761911 5297157908401373503142867)
    ·
      refine ⟨7945736862602060254714301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297157908401373503142867 7945736862602060254714301)
      ·
        refine ⟨2979651323475772595517863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7945736862602060254714301 2979651323475772595517863)
        ·
          refine ⟨4469476985213658893276795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2979651323475772595517863 4469476985213658893276795)
          ·
            refine ⟨6704215477820488339915193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469476985213658893276795 6704215477820488339915193)
            ·
              refine ⟨5028161608365366254936395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6704215477820488339915193 5028161608365366254936395)
              ·
                refine ⟨7542242412548049382404593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028161608365366254936395 7542242412548049382404593)
                ·
                  refine ⟨5656681809411037036803445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7542242412548049382404593 5656681809411037036803445)
                  ·
                    refine ⟨530313919632284722200323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5656681809411037036803445 530313919632284722200323)
                    ·
                      rfl

theorem cell22_1549174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1549174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549174 prefixEnd_1549174 := by exact prefixLift 1549174
  have htrace : WordTrace (prefixWord ++ tailWord_1549174) baseStart_1549174 baseEnd_1549174 := by
    simpa [prefixWord, tailWord_1549174, baseEnd_1549174] using wordTrace_append hprefix tailTrace_1549174
  have hstable : (prefixWord ++ tailWord_1549174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549174).length < 2 ^ (prefixWord ++ tailWord_1549174).sum := by decide
  have hdescent : baseEnd_1549174 < baseStart_1549174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549189 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 1, 4]
def baseStart_1549189 : Nat := 118140960795 + 1549189 * 2 ^ 59
def prefixEnd_1549189 : Nat := 4983230072969 + 3 ^ 40 * 1549189 * 2
def baseEnd_1549189 : Nat := 530319054438829683075277

theorem tailTrace_1549189 : CollatzResearch.WordTrace tailWord_1549189 prefixEnd_1549189 530319054438829683075277 := by
  unfold tailWord_1549189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56503564784560308261986621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37669043189706872174657747 56503564784560308261986621)
  ·
    refine ⟨21188836794210115598244983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56503564784560308261986621 21188836794210115598244983)
    ·
      refine ⟨31783255191315173397367475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21188836794210115598244983 31783255191315173397367475)
      ·
        refine ⟨47674882786972760096051213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31783255191315173397367475 47674882786972760096051213)
        ·
          refine ⟨17878081045114785036019205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47674882786972760096051213 17878081045114785036019205)
          ·
            refine ⟨3352140195959022194253601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17878081045114785036019205 3352140195959022194253601)
            ·
              refine ⟨2514105146969266645690201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352140195959022194253601 2514105146969266645690201)
              ·
                refine ⟨1885578860226949984267651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514105146969266645690201 1885578860226949984267651)
                ·
                  refine ⟨2828368290340424976401477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1885578860226949984267651 2828368290340424976401477)
                  ·
                    refine ⟨530319054438829683075277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828368290340424976401477 530319054438829683075277)
                    ·
                      rfl

theorem cell22_1549189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_1549189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549189 prefixEnd_1549189 := by exact prefixLift 1549189
  have htrace : WordTrace (prefixWord ++ tailWord_1549189) baseStart_1549189 baseEnd_1549189 := by
    simpa [prefixWord, tailWord_1549189, baseEnd_1549189] using wordTrace_append hprefix tailTrace_1549189
  have hstable : (prefixWord ++ tailWord_1549189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549189).length < 2 ^ (prefixWord ++ tailWord_1549189).sum := by decide
  have hdescent : baseEnd_1549189 < baseStart_1549189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549200 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_1549200 : Nat := 118140960795 + 1549200 * 2 ^ 59
def prefixEnd_1549200 : Nat := 4983230072969 + 3 ^ 40 * 1549200 * 2
def baseEnd_1549200 : Nat := 530322819963629321050243

theorem tailTrace_1549200 : CollatzResearch.WordTrace tailWord_1549200 prefixEnd_1549200 530322819963629321050243 := by
  unfold tailWord_1549200
  simp only [CollatzResearch.WordTrace]
  refine ⟨28251982993760228570318527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37669310658346971427091369 28251982993760228570318527)
  ·
    refine ⟨42377974490640342855477791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28251982993760228570318527 42377974490640342855477791)
    ·
      refine ⟨63566961735960514283216687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42377974490640342855477791 63566961735960514283216687)
      ·
        refine ⟨95350442603940771424825031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63566961735960514283216687 95350442603940771424825031)
        ·
          refine ⟨143025663905911157137237547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95350442603940771424825031 143025663905911157137237547)
          ·
            refine ⟨214538495858866735705856321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143025663905911157137237547 214538495858866735705856321)
            ·
              refine ⟨160903871894150051779392241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214538495858866735705856321 160903871894150051779392241)
              ·
                refine ⟨120677903920612538834544181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160903871894150051779392241 120677903920612538834544181)
                ·
                  refine ⟨11313553492557425515738517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120677903920612538834544181 11313553492557425515738517)
                  ·
                    refine ⟨530322819963629321050243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11313553492557425515738517 530322819963629321050243)
                    ·
                      rfl

theorem cell22_1549200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_1549200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549200 prefixEnd_1549200 := by exact prefixLift 1549200
  have htrace : WordTrace (prefixWord ++ tailWord_1549200) baseStart_1549200 baseEnd_1549200 := by
    simpa [prefixWord, tailWord_1549200, baseEnd_1549200] using wordTrace_append hprefix tailTrace_1549200
  have hstable : (prefixWord ++ tailWord_1549200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549200).length < 2 ^ (prefixWord ++ tailWord_1549200).sum := by decide
  have hdescent : baseEnd_1549200 < baseStart_1549200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549298 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_1549298 : Nat := 118140960795 + 1549298 * 2 ^ 59
def prefixEnd_1549298 : Nat := 4983230072969 + 3 ^ 40 * 1549298 * 2
def baseEnd_1549298 : Nat := 530356367366389732099943

theorem tailTrace_1549298 : CollatzResearch.WordTrace tailWord_1549298 prefixEnd_1549298 530356367366389732099943 := by
  unfold tailWord_1549298
  simp only [CollatzResearch.WordTrace]
  refine ⟨14126885085291354969426137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37671693560776946585136365 14126885085291354969426137)
  ·
    refine ⟨10595163813968516227069603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14126885085291354969426137 10595163813968516227069603)
    ·
      refine ⟨15892745720952774340604405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10595163813968516227069603 15892745720952774340604405)
      ·
        refine ⟨1489944911339322594431663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15892745720952774340604405 1489944911339322594431663)
        ·
          refine ⟨2234917367008983891647495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1489944911339322594431663 2234917367008983891647495)
          ·
            refine ⟨3352376050513475837471243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2234917367008983891647495 3352376050513475837471243)
            ·
              refine ⟨5028564075770213756206865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352376050513475837471243 5028564075770213756206865)
              ·
                refine ⟨3771423056827660317155149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5028564075770213756206865 3771423056827660317155149)
                ·
                  refine ⟨1414283646310372618933181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3771423056827660317155149 1414283646310372618933181)
                  ·
                    refine ⟨530356367366389732099943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414283646310372618933181 530356367366389732099943)
                    ·
                      rfl

theorem cell22_1549298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_1549298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549298 prefixEnd_1549298 := by exact prefixLift 1549298
  have htrace : WordTrace (prefixWord ++ tailWord_1549298) baseStart_1549298 baseEnd_1549298 := by
    simpa [prefixWord, tailWord_1549298, baseEnd_1549298] using wordTrace_append hprefix tailTrace_1549298
  have hstable : (prefixWord ++ tailWord_1549298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549298).length < 2 ^ (prefixWord ++ tailWord_1549298).sum := by decide
  have hdescent : baseEnd_1549298 < baseStart_1549298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549337 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_1549337 : Nat := 118140960795 + 1549337 * 2 ^ 59
def prefixEnd_1549337 : Nat := 4983230072969 + 3 ^ 40 * 1549337 * 2
def baseEnd_1549337 : Nat := 530369717863406630374823

theorem tailTrace_1549337 : CollatzResearch.WordTrace tailWord_1549337 prefixEnd_1549337 530369717863406630374823 := by
  unfold tailWord_1549337
  simp only [CollatzResearch.WordTrace]
  refine ⟨56508962788024129538374265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37672641858682753025582843 56508962788024129538374265)
  ·
    refine ⟨42381722091018097153780699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56508962788024129538374265 42381722091018097153780699)
    ·
      refine ⟨63572583136527145730671049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42381722091018097153780699 63572583136527145730671049)
      ·
        refine ⟨47679437352395359298003287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63572583136527145730671049 47679437352395359298003287)
        ·
          refine ⟨71519156028593038947004931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47679437352395359298003287 71519156028593038947004931)
          ·
            refine ⟨107278734042889558420507397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71519156028593038947004931 107278734042889558420507397)
            ·
              refine ⟨20114762633041792203845137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107278734042889558420507397 20114762633041792203845137)
              ·
                refine ⟨15086071974781344152883853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20114762633041792203845137 15086071974781344152883853)
                ·
                  refine ⟨5657276990543004057331445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15086071974781344152883853 5657276990543004057331445)
                  ·
                    refine ⟨530369717863406630374823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5657276990543004057331445 530369717863406630374823)
                    ·
                      rfl

theorem cell22_1549337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_1549337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549337 prefixEnd_1549337 := by exact prefixLift 1549337
  have htrace : WordTrace (prefixWord ++ tailWord_1549337) baseStart_1549337 baseEnd_1549337 := by
    simpa [prefixWord, tailWord_1549337, baseEnd_1549337] using wordTrace_append hprefix tailTrace_1549337
  have hstable : (prefixWord ++ tailWord_1549337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549337).length < 2 ^ (prefixWord ++ tailWord_1549337).sum := by decide
  have hdescent : baseEnd_1549337 < baseStart_1549337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549369 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 6]
def baseStart_1549369 : Nat := 118140960795 + 1549369 * 2 ^ 59
def prefixEnd_1549369 : Nat := 4983230072969 + 3 ^ 40 * 1549369 * 2
def baseEnd_1549369 : Nat := 530380672117369213574725

theorem tailTrace_1549369 : CollatzResearch.WordTrace tailWord_1549369 prefixEnd_1549369 530380672117369213574725 := by
  unfold tailWord_1549369
  simp only [CollatzResearch.WordTrace]
  refine ⟨56510129923908199003539161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37673419949272132669026107 56510129923908199003539161)
  ·
    refine ⟨42382597442931149252654371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56510129923908199003539161 42382597442931149252654371)
    ·
      refine ⟨63573896164396723878981557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42382597442931149252654371 63573896164396723878981557)
      ·
        refine ⟨5960052765412192863654521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63573896164396723878981557 5960052765412192863654521)
        ·
          refine ⟨4470039574059144647740891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960052765412192863654521 4470039574059144647740891)
          ·
            refine ⟨6705059361088716971611337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470039574059144647740891 6705059361088716971611337)
            ·
              refine ⟨5028794520816537728708503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705059361088716971611337 5028794520816537728708503)
              ·
                refine ⟨7543191781224806593062755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5028794520816537728708503 7543191781224806593062755)
                ·
                  refine ⟨11314787671837209889594133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7543191781224806593062755 11314787671837209889594133)
                  ·
                    refine ⟨530380672117369213574725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11314787671837209889594133 530380672117369213574725)
                    ·
                      rfl

theorem cell22_1549369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_1549369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549369 prefixEnd_1549369 := by exact prefixLift 1549369
  have htrace : WordTrace (prefixWord ++ tailWord_1549369) baseStart_1549369 baseEnd_1549369 := by
    simpa [prefixWord, tailWord_1549369, baseEnd_1549369] using wordTrace_append hprefix tailTrace_1549369
  have hstable : (prefixWord ++ tailWord_1549369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549369).length < 2 ^ (prefixWord ++ tailWord_1549369).sum := by decide
  have hdescent : baseEnd_1549369 < baseStart_1549369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549373 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 4]
def baseStart_1549373 : Nat := 118140960795 + 1549373 * 2 ^ 59
def prefixEnd_1549373 : Nat := 4983230072969 + 3 ^ 40 * 1549373 * 2
def baseEnd_1549373 : Nat := 176794013799704845491571

theorem tailTrace_1549373 : CollatzResearch.WordTrace tailWord_1549373 prefixEnd_1549373 176794013799704845491571 := by
  unfold tailWord_1549373
  simp only [CollatzResearch.WordTrace]
  refine ⟨56510275815893707686684773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37673517210595805124456515 56510275815893707686684773)
  ·
    refine ⟨10595676715480070191253395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56510275815893707686684773 10595676715480070191253395)
    ·
      refine ⟨15893515073220105286880093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10595676715480070191253395 15893515073220105286880093)
      ·
        refine ⟨5960068152457539482580035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15893515073220105286880093 5960068152457539482580035)
        ·
          refine ⟨8940102228686309223870053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5960068152457539482580035 8940102228686309223870053)
          ·
            refine ⟨1676269167878682979475635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8940102228686309223870053 1676269167878682979475635)
            ·
              refine ⟨2514403751818024469213453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676269167878682979475635 2514403751818024469213453)
              ·
                refine ⟨942901406931759175955045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2514403751818024469213453 942901406931759175955045)
                ·
                  refine ⟨176794013799704845491571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942901406931759175955045 176794013799704845491571)
                  ·
                    rfl

theorem cell22_1549373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_1549373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549373 prefixEnd_1549373 := by exact prefixLift 1549373
  have htrace : WordTrace (prefixWord ++ tailWord_1549373) baseStart_1549373 baseEnd_1549373 := by
    simpa [prefixWord, tailWord_1549373, baseEnd_1549373] using wordTrace_append hprefix tailTrace_1549373
  have hstable : (prefixWord ++ tailWord_1549373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549373).length < 2 ^ (prefixWord ++ tailWord_1549373).sum := by decide
  have hdescent : baseEnd_1549373 < baseStart_1549373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549405 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1549405 : Nat := 118140960795 + 1549405 * 2 ^ 59
def prefixEnd_1549405 : Nat := 4983230072969 + 3 ^ 40 * 1549405 * 2
def baseEnd_1549405 : Nat := 530392995653077119674615

theorem tailTrace_1549405 : CollatzResearch.WordTrace tailWord_1549405 prefixEnd_1549405 530392995653077119674615 := by
  unfold tailWord_1549405
  simp only [CollatzResearch.WordTrace]
  refine ⟨56511442951777777151849669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37674295301185184767899779 56511442951777777151849669)
  ·
    refine ⟨10595895553458333215971813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56511442951777777151849669 10595895553458333215971813)
    ·
      refine ⟨1986730416273437477994715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10595895553458333215971813 1986730416273437477994715)
      ·
        refine ⟨2980095624410156216992073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986730416273437477994715 2980095624410156216992073)
        ·
          refine ⟨2235071718307617162744055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980095624410156216992073 2235071718307617162744055)
          ·
            refine ⟨3352607577461425744116083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235071718307617162744055 3352607577461425744116083)
            ·
              refine ⟨5028911366192138616174125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352607577461425744116083 5028911366192138616174125)
              ·
                refine ⟨1885841762322051981065297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5028911366192138616174125 1885841762322051981065297)
                ·
                  refine ⟨1414381321741538985798973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885841762322051981065297 1414381321741538985798973)
                  ·
                    refine ⟨530392995653077119674615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414381321741538985798973 530392995653077119674615)
                    ·
                      rfl

theorem cell22_1549405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1549405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549405 prefixEnd_1549405 := by exact prefixLift 1549405
  have htrace : WordTrace (prefixWord ++ tailWord_1549405) baseStart_1549405 baseEnd_1549405 := by
    simpa [prefixWord, tailWord_1549405, baseEnd_1549405] using wordTrace_append hprefix tailTrace_1549405
  have hstable : (prefixWord ++ tailWord_1549405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549405).length < 2 ^ (prefixWord ++ tailWord_1549405).sum := by decide
  have hdescent : baseEnd_1549405 < baseStart_1549405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549459 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 3, 4]
def baseStart_1549459 : Nat := 118140960795 + 1549459 * 2 ^ 59
def prefixEnd_1549459 : Nat := 4983230072969 + 3 ^ 40 * 1549459 * 2
def baseEnd_1549459 : Nat := 530411480956638978824449

theorem tailTrace_1549459 : CollatzResearch.WordTrace tailWord_1549459 prefixEnd_1549459 530411480956638978824449 := by
  unfold tailWord_1549459
  simp only [CollatzResearch.WordTrace]
  refine ⟨56513412493582144374315431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37675608329054762916210287 56513412493582144374315431)
  ·
    refine ⟨84770118740373216561473147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56513412493582144374315431 84770118740373216561473147)
    ·
      refine ⟨127155178110559824842209721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84770118740373216561473147 127155178110559824842209721)
      ·
        refine ⟨95366383582919868631657291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127155178110559824842209721 95366383582919868631657291)
        ·
          refine ⟨143049575374379802947485937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95366383582919868631657291 143049575374379802947485937)
          ·
            refine ⟨107287181530784852210614453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143049575374379802947485937 107287181530784852210614453)
            ·
              refine ⟨10058173268511079894745105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107287181530784852210614453 10058173268511079894745105)
              ·
                refine ⟨7543629951383309921058829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10058173268511079894745105 7543629951383309921058829)
                ·
                  refine ⟨2828861231768741220397061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7543629951383309921058829 2828861231768741220397061)
                  ·
                    refine ⟨530411480956638978824449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828861231768741220397061 530411480956638978824449)
                    ·
                      rfl

theorem cell22_1549459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_1549459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549459 prefixEnd_1549459 := by exact prefixLift 1549459
  have htrace : WordTrace (prefixWord ++ tailWord_1549459) baseStart_1549459 baseEnd_1549459 := by
    simpa [prefixWord, tailWord_1549459, baseEnd_1549459] using wordTrace_append hprefix tailTrace_1549459
  have hstable : (prefixWord ++ tailWord_1549459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549459).length < 2 ^ (prefixWord ++ tailWord_1549459).sum := by decide
  have hdescent : baseEnd_1549459 < baseStart_1549459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549476 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_1549476 : Nat := 118140960795 + 1549476 * 2 ^ 59
def prefixEnd_1549476 : Nat := 4983230072969 + 3 ^ 40 * 1549476 * 2
def baseEnd_1549476 : Nat := 530417300404056601149397

theorem tailTrace_1549476 : CollatzResearch.WordTrace tailWord_1549476 prefixEnd_1549476 530417300404056601149397 := by
  unfold tailWord_1549476
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257016267260278138842141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37676021689680370851789521 28257016267260278138842141)
  ·
    refine ⟨10596381100222604302065803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28257016267260278138842141 10596381100222604302065803)
    ·
      refine ⟨15894571650333906453098705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10596381100222604302065803 15894571650333906453098705)
      ·
        refine ⟨11920928737750429839824029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15894571650333906453098705 11920928737750429839824029)
        ·
          refine ⟨4470348276656411189934011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11920928737750429839824029 4470348276656411189934011)
          ·
            refine ⟨6705522414984616784901017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470348276656411189934011 6705522414984616784901017)
            ·
              refine ⟨5029141811238462588675763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6705522414984616784901017 5029141811238462588675763)
              ·
                refine ⟨7543712716857693883013645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029141811238462588675763 7543712716857693883013645)
                ·
                  refine ⟨2828892268821635206130117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7543712716857693883013645 2828892268821635206130117)
                  ·
                    refine ⟨530417300404056601149397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2828892268821635206130117 530417300404056601149397)
                    ·
                      rfl

theorem cell22_1549476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_1549476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549476 prefixEnd_1549476 := by exact prefixLift 1549476
  have htrace : WordTrace (prefixWord ++ tailWord_1549476) baseStart_1549476 baseEnd_1549476 := by
    simpa [prefixWord, tailWord_1549476, baseEnd_1549476] using wordTrace_append hprefix tailTrace_1549476
  have hstable : (prefixWord ++ tailWord_1549476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549476).length < 2 ^ (prefixWord ++ tailWord_1549476).sum := by decide
  have hdescent : baseEnd_1549476 < baseStart_1549476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549491 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 4]
def baseStart_1549491 : Nat := 118140960795 + 1549491 * 2 ^ 59
def prefixEnd_1549491 : Nat := 4983230072969 + 3 ^ 40 * 1549491 * 2
def baseEnd_1549491 : Nat := 176807478403533854008117

theorem tailTrace_1549491 : CollatzResearch.WordTrace tailWord_1549491 prefixEnd_1549491 176807478403533854008117 := by
  unfold tailWord_1549491
  simp only [CollatzResearch.WordTrace]
  refine ⟨56514579629466213839480327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37676386419644142559653551 56514579629466213839480327)
  ·
    refine ⟨84771869444199320759220491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56514579629466213839480327 84771869444199320759220491)
    ·
      refine ⟨127157804166298981138830737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84771869444199320759220491 127157804166298981138830737)
      ·
        refine ⟨95368353124724235854123053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127157804166298981138830737 95368353124724235854123053)
        ·
          refine ⟨35763132421771588445296145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95368353124724235854123053 35763132421771588445296145)
          ·
            refine ⟨26822349316328691333972109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35763132421771588445296145 26822349316328691333972109)
            ·
              refine ⟨10058380993623259250239541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26822349316328691333972109 10058380993623259250239541)
              ·
                refine ⟨942973218152180554709957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10058380993623259250239541 942973218152180554709957)
                ·
                  refine ⟨176807478403533854008117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 942973218152180554709957 176807478403533854008117)
                  ·
                    rfl

theorem cell22_1549491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 4].length) (baseStart_1549491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549491 prefixEnd_1549491 := by exact prefixLift 1549491
  have htrace : WordTrace (prefixWord ++ tailWord_1549491) baseStart_1549491 baseEnd_1549491 := by
    simpa [prefixWord, tailWord_1549491, baseEnd_1549491] using wordTrace_append hprefix tailTrace_1549491
  have hstable : (prefixWord ++ tailWord_1549491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549491).length < 2 ^ (prefixWord ++ tailWord_1549491).sum := by decide
  have hdescent : baseEnd_1549491 < baseStart_1549491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549508 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1549508 : Nat := 118140960795 + 1549508 * 2 ^ 59
def prefixEnd_1549508 : Nat := 4983230072969 + 3 ^ 40 * 1549508 * 2
def baseEnd_1549508 : Nat := 176809418219339728116433

theorem tailTrace_1549508 : CollatzResearch.WordTrace tailWord_1549508 prefixEnd_1549508 176809418219339728116433 := by
  unfold tailWord_1549508
  simp only [CollatzResearch.WordTrace]
  refine ⟨28257599835202312871424589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37676799780269750495232785 28257599835202312871424589)
  ·
    refine ⟨10596599938200867326784221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28257599835202312871424589 10596599938200867326784221)
    ·
      refine ⟨3973724976825325247544083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10596599938200867326784221 3973724976825325247544083)
      ·
        refine ⟨5960587465237987871316125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973724976825325247544083 5960587465237987871316125)
        ·
          refine ⟨2235220299464245451743547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5960587465237987871316125 2235220299464245451743547)
          ·
            refine ⟨3352830449196368177615321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235220299464245451743547 3352830449196368177615321)
            ·
              refine ⟨2514622836897276133211491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3352830449196368177615321 2514622836897276133211491)
              ·
                refine ⟨3771934255345914199817237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2514622836897276133211491 3771934255345914199817237)
                ·
                  refine ⟨176809418219339728116433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3771934255345914199817237 176809418219339728116433)
                  ·
                    rfl

theorem cell22_1549508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1549508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549508 prefixEnd_1549508 := by exact prefixLift 1549508
  have htrace : WordTrace (prefixWord ++ tailWord_1549508) baseStart_1549508 baseEnd_1549508 := by
    simpa [prefixWord, tailWord_1549508, baseEnd_1549508] using wordTrace_append hprefix tailTrace_1549508
  have hstable : (prefixWord ++ tailWord_1549508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549508).length < 2 ^ (prefixWord ++ tailWord_1549508).sum := by decide
  have hdescent : baseEnd_1549508 < baseStart_1549508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549536 : List Nat := [2, 1, 1, 3, 1, 4, 4, 6]
def baseStart_1549536 : Nat := 118140960795 + 1549536 * 2 ^ 59
def prefixEnd_1549536 : Nat := 4983230072969 + 3 ^ 40 * 1549536 * 2
def baseEnd_1549536 : Nat := 58937537736692938294357

theorem tailTrace_1549536 : CollatzResearch.WordTrace tailWord_1549536 prefixEnd_1549536 58937537736692938294357 := by
  unfold tailWord_1549536
  simp only [CollatzResearch.WordTrace]
  refine ⟨28258110457151593262434231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37677480609535457683245641 28258110457151593262434231)
  ·
    refine ⟨42387165685727389893651347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28258110457151593262434231 42387165685727389893651347)
    ·
      refine ⟨63580748528591084840477021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42387165685727389893651347 63580748528591084840477021)
      ·
        refine ⟨23842780698221656815178883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63580748528591084840477021 23842780698221656815178883)
        ·
          refine ⟨35764171047332485222768325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23842780698221656815178883 35764171047332485222768325)
          ·
            refine ⟨6705782071374840979269061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35764171047332485222768325 6705782071374840979269061)
            ·
              refine ⟨1257334138382782683612949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6705782071374840979269061 1257334138382782683612949)
              ·
                refine ⟨58937537736692938294357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1257334138382782683612949 58937537736692938294357)
                ·
                  rfl

theorem cell22_1549536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_1549536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549536 prefixEnd_1549536 := by exact prefixLift 1549536
  have htrace : WordTrace (prefixWord ++ tailWord_1549536) baseStart_1549536 baseEnd_1549536 := by
    simpa [prefixWord, tailWord_1549536, baseEnd_1549536] using wordTrace_append hprefix tailTrace_1549536
  have hstable : (prefixWord ++ tailWord_1549536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549536).length < 2 ^ (prefixWord ++ tailWord_1549536).sum := by decide
  have hdescent : baseEnd_1549536 < baseStart_1549536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549626 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_1549626 : Nat := 118140960795 + 1549626 * 2 ^ 59
def prefixEnd_1549626 : Nat := 4983230072969 + 3 ^ 40 * 1549626 * 2
def baseEnd_1549626 : Nat := 176822882823168736632979

theorem tailTrace_1549626 : CollatzResearch.WordTrace tailWord_1549626 prefixEnd_1549626 176822882823168736632979 := by
  unfold tailWord_1549626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129875870994282973911183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37679668989318087930429821 14129875870994282973911183)
  ·
    refine ⟨21194813806491424460866775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14129875870994282973911183 21194813806491424460866775)
    ·
      refine ⟨31792220709737136691300163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21194813806491424460866775 31792220709737136691300163)
      ·
        refine ⟨47688331064605705036950245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31792220709737136691300163 47688331064605705036950245)
        ·
          refine ⟨8941562074613569694428171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47688331064605705036950245 8941562074613569694428171)
          ·
            refine ⟨13412343111920354541642257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8941562074613569694428171 13412343111920354541642257)
            ·
              refine ⟨10059257333940265906231693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13412343111920354541642257 10059257333940265906231693)
              ·
                refine ⟨3772221500227599714836885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10059257333940265906231693 3772221500227599714836885)
                ·
                  refine ⟨176822882823168736632979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3772221500227599714836885 176822882823168736632979)
                  ·
                    rfl

theorem cell22_1549626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_1549626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549626 prefixEnd_1549626 := by exact prefixLift 1549626
  have htrace : WordTrace (prefixWord ++ tailWord_1549626) baseStart_1549626 baseEnd_1549626 := by
    simpa [prefixWord, tailWord_1549626, baseEnd_1549626] using wordTrace_append hprefix tailTrace_1549626
  have hstable : (prefixWord ++ tailWord_1549626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549626).length < 2 ^ (prefixWord ++ tailWord_1549626).sum := by decide
  have hdescent : baseEnd_1549626 < baseStart_1549626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549641 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_1549641 : Nat := 118140960795 + 1549641 * 2 ^ 59
def prefixEnd_1549641 : Nat := 4983230072969 + 3 ^ 40 * 1549641 * 2
def baseEnd_1549641 : Nat := 530473783276051170773891

theorem tailTrace_1549641 : CollatzResearch.WordTrace tailWord_1549641 prefixEnd_1549641 530473783276051170773891 := by
  unfold tailWord_1549641
  simp only [CollatzResearch.WordTrace]
  refine ⟨56520050578922789457440777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37680033719281859638293851 56520050578922789457440777)
  ·
    refine ⟨42390037934192092093080583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56520050578922789457440777 42390037934192092093080583)
    ·
      refine ⟨63585056901288138139620875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42390037934192092093080583 63585056901288138139620875)
      ·
        refine ⟨95377585351932207209431313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63585056901288138139620875 95377585351932207209431313)
        ·
          refine ⟨71533189013949155407073485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95377585351932207209431313 71533189013949155407073485)
          ·
            refine ⟨26824945880230933277652557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71533189013949155407073485 26824945880230933277652557)
            ·
              refine ⟨10059354705086599979119709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26824945880230933277652557 10059354705086599979119709)
              ·
                refine ⟨3772258014407474992169891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10059354705086599979119709 3772258014407474992169891)
                ·
                  refine ⟨5658387021611212488254837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772258014407474992169891 5658387021611212488254837)
                  ·
                    refine ⟨530473783276051170773891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5658387021611212488254837 530473783276051170773891)
                    ·
                      rfl

theorem cell22_1549641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_1549641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549641 prefixEnd_1549641 := by exact prefixLift 1549641
  have htrace : WordTrace (prefixWord ++ tailWord_1549641) baseStart_1549641 baseEnd_1549641 := by
    simpa [prefixWord, tailWord_1549641, baseEnd_1549641] using wordTrace_append hprefix tailTrace_1549641
  have hstable : (prefixWord ++ tailWord_1549641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549641).length < 2 ^ (prefixWord ++ tailWord_1549641).sum := by decide
  have hdescent : baseEnd_1549641 < baseStart_1549641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549656 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_1549656 : Nat := 118140960795 + 1549656 * 2 ^ 59
def prefixEnd_1549656 : Nat := 4983230072969 + 3 ^ 40 * 1549656 * 2
def baseEnd_1549656 : Nat := 530478918082596131648845

theorem tailTrace_1549656 : CollatzResearch.WordTrace tailWord_1549656 prefixEnd_1549656 530478918082596131648845 := by
  unfold tailWord_1549656
  simp only [CollatzResearch.WordTrace]
  refine ⟨28260298836934223509618411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37680398449245631346157881 28260298836934223509618411)
  ·
    refine ⟨42390448255401335264427617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28260298836934223509618411 42390448255401335264427617)
    ·
      refine ⟨31792836191551001448320713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42390448255401335264427617 31792836191551001448320713)
      ·
        refine ⟨23844627143663251086240535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31792836191551001448320713 23844627143663251086240535)
        ·
          refine ⟨35766940715494876629360803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23844627143663251086240535 35766940715494876629360803)
          ·
            refine ⟨53650411073242314944041205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35766940715494876629360803 53650411073242314944041205)
            ·
              refine ⟨5029726038116467026003863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53650411073242314944041205 5029726038116467026003863)
              ·
                refine ⟨7544589057174700539005795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5029726038116467026003863 7544589057174700539005795)
                ·
                  refine ⟨11316883585762050808508693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7544589057174700539005795 11316883585762050808508693)
                  ·
                    refine ⟨530478918082596131648845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11316883585762050808508693 530478918082596131648845)
                    ·
                      rfl

theorem cell22_1549656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_1549656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549656 prefixEnd_1549656 := by exact prefixLift 1549656
  have htrace : WordTrace (prefixWord ++ tailWord_1549656) baseStart_1549656 baseEnd_1549656 := by
    simpa [prefixWord, tailWord_1549656, baseEnd_1549656] using wordTrace_append hprefix tailTrace_1549656
  have hstable : (prefixWord ++ tailWord_1549656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549656).length < 2 ^ (prefixWord ++ tailWord_1549656).sum := by decide
  have hdescent : baseEnd_1549656 < baseStart_1549656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549701 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_1549701 : Nat := 118140960795 + 1549701 * 2 ^ 59
def prefixEnd_1549701 : Nat := 4983230072969 + 3 ^ 40 * 1549701 * 2
def baseEnd_1549701 : Nat := 530494322502231014273707

theorem tailTrace_1549701 : CollatzResearch.WordTrace tailWord_1549701 prefixEnd_1549701 530494322502231014273707 := by
  unfold tailWord_1549701
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522238958705419704624957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37681492639136946469749971 56522238958705419704624957)
  ·
    refine ⟨21195839609514532389234359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56522238958705419704624957 21195839609514532389234359)
    ·
      refine ⟨31793759414271798583851539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21195839609514532389234359 31793759414271798583851539)
      ·
        refine ⟨47690639121407697875777309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31793759414271798583851539 47690639121407697875777309)
        ·
          refine ⟨17883989670527886703416491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47690639121407697875777309 17883989670527886703416491)
          ·
            refine ⟨26825984505791830055124737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17883989670527886703416491 26825984505791830055124737)
            ·
              refine ⟨20119488379343872541343553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26825984505791830055124737 20119488379343872541343553)
              ·
                refine ⟨15089616284507904406007665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20119488379343872541343553 15089616284507904406007665)
                ·
                  refine ⟨11317212213380928304505749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15089616284507904406007665 11317212213380928304505749)
                  ·
                    refine ⟨530494322502231014273707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11317212213380928304505749 530494322502231014273707)
                    ·
                      rfl

theorem cell22_1549701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_1549701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549701 prefixEnd_1549701 := by exact prefixLift 1549701
  have htrace : WordTrace (prefixWord ++ tailWord_1549701) baseStart_1549701 baseEnd_1549701 := by
    simpa [prefixWord, tailWord_1549701, baseEnd_1549701] using wordTrace_append hprefix tailTrace_1549701
  have hstable : (prefixWord ++ tailWord_1549701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549701).length < 2 ^ (prefixWord ++ tailWord_1549701).sum := by decide
  have hdescent : baseEnd_1549701 < baseStart_1549701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549705 : List Nat := [1, 2, 1, 1, 7, 2, 2, 6]
def baseStart_1549705 : Nat := 118140960795 + 1549705 * 2 ^ 59
def prefixEnd_1549705 : Nat := 4983230072969 + 3 ^ 40 * 1549705 * 2
def baseEnd_1549705 : Nat := 58943965753775148574855

theorem tailTrace_1549705 : CollatzResearch.WordTrace tailWord_1549705 prefixEnd_1549705 58943965753775148574855 := by
  unfold tailWord_1549705
  simp only [CollatzResearch.WordTrace]
  refine ⟨56522384850690928387770569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37681589900460618925180379 56522384850690928387770569)
  ·
    refine ⟨42391788638018196290827927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56522384850690928387770569 42391788638018196290827927)
    ·
      refine ⟨63587682957027294436241891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42391788638018196290827927 63587682957027294436241891)
      ·
        refine ⟨95381524435540941654362837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63587682957027294436241891 95381524435540941654362837)
        ·
          refine ⟨2235504478957990820024129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 95381524435540941654362837 2235504478957990820024129)
          ·
            refine ⟨1676628359218493115018097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235504478957990820024129 1676628359218493115018097)
            ·
              refine ⟨1257471269413869836263573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1676628359218493115018097 1257471269413869836263573)
              ·
                refine ⟨58943965753775148574855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1257471269413869836263573 58943965753775148574855)
                ·
                  rfl

theorem cell22_1549705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 6].length) (baseStart_1549705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549705 prefixEnd_1549705 := by exact prefixLift 1549705
  have htrace : WordTrace (prefixWord ++ tailWord_1549705) baseStart_1549705 baseEnd_1549705 := by
    simpa [prefixWord, tailWord_1549705, baseEnd_1549705] using wordTrace_append hprefix tailTrace_1549705
  have hstable : (prefixWord ++ tailWord_1549705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549705).length < 2 ^ (prefixWord ++ tailWord_1549705).sum := by decide
  have hdescent : baseEnd_1549705 < baseStart_1549705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549810 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_1549810 : Nat := 118140960795 + 1549810 * 2 ^ 59
def prefixEnd_1549810 : Nat := 4983230072969 + 3 ^ 40 * 1549810 * 2
def baseEnd_1549810 : Nat := 530531635429791063298373

theorem tailTrace_1549810 : CollatzResearch.WordTrace tailWord_1549810 prefixEnd_1549810 530531635429791063298373 := by
  unfold tailWord_1549810
  simp only [CollatzResearch.WordTrace]
  refine ⟨14131553628827632830085721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37684143010207020880228589 14131553628827632830085721)
  ·
    refine ⟨10598665221620724622564291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14131553628827632830085721 10598665221620724622564291)
    ·
      refine ⟨15897997832431086933846437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598665221620724622564291 15897997832431086933846437)
      ·
        refine ⟨2980874593580828800096207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15897997832431086933846437 2980874593580828800096207)
        ·
          refine ⟨4471311890371243200144311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2980874593580828800096207 4471311890371243200144311)
          ·
            refine ⟨6706967835556864800216467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4471311890371243200144311 6706967835556864800216467)
            ·
              refine ⟨10060451753335297200324701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6706967835556864800216467 10060451753335297200324701)
              ·
                refine ⟨3772669407500736450121763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10060451753335297200324701 3772669407500736450121763)
                ·
                  refine ⟨5659004111251104675182645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772669407500736450121763 5659004111251104675182645)
                  ·
                    refine ⟨530531635429791063298373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5659004111251104675182645 530531635429791063298373)
                    ·
                      rfl

theorem cell22_1549810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_1549810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549810 prefixEnd_1549810 := by exact prefixLift 1549810
  have htrace : WordTrace (prefixWord ++ tailWord_1549810) baseStart_1549810 baseEnd_1549810 := by
    simpa [prefixWord, tailWord_1549810, baseEnd_1549810] using wordTrace_append hprefix tailTrace_1549810
  have hstable : (prefixWord ++ tailWord_1549810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549810).length < 2 ^ (prefixWord ++ tailWord_1549810).sum := by decide
  have hdescent : baseEnd_1549810 < baseStart_1549810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549825 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 6]
def baseStart_1549825 : Nat := 118140960795 + 1549825 * 2 ^ 59
def prefixEnd_1549825 : Nat := 4983230072969 + 3 ^ 40 * 1549825 * 2
def baseEnd_1549825 : Nat := 530536770236336024173327

theorem tailTrace_1549825 : CollatzResearch.WordTrace tailWord_1549825 prefixEnd_1549825 530536770236336024173327 := by
  unfold tailWord_1549825
  simp only [CollatzResearch.WordTrace]
  refine ⟨56526761610256188882138929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37684507740170792588092619 56526761610256188882138929)
  ·
    refine ⟨42395071207692141661604197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56526761610256188882138929 42395071207692141661604197)
    ·
      refine ⟨7949075851442276561550787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42395071207692141661604197 7949075851442276561550787)
      ·
        refine ⟨11923613777163414842326181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7949075851442276561550787 11923613777163414842326181)
        ·
          refine ⟨2235677583218140282936159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11923613777163414842326181 2235677583218140282936159)
          ·
            refine ⟨3353516374827210424404239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235677583218140282936159 3353516374827210424404239)
            ·
              refine ⟨5030274562240815636606359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353516374827210424404239 5030274562240815636606359)
              ·
                refine ⟨7545411843361223454909539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030274562240815636606359 7545411843361223454909539)
                ·
                  refine ⟨11318117765041835182364309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7545411843361223454909539 11318117765041835182364309)
                  ·
                    refine ⟨530536770236336024173327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11318117765041835182364309 530536770236336024173327)
                    ·
                      rfl

theorem cell22_1549825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_1549825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549825 prefixEnd_1549825 := by exact prefixLift 1549825
  have htrace : WordTrace (prefixWord ++ tailWord_1549825) baseStart_1549825 baseEnd_1549825 := by
    simpa [prefixWord, tailWord_1549825, baseEnd_1549825] using wordTrace_append hprefix tailTrace_1549825
  have hstable : (prefixWord ++ tailWord_1549825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549825).length < 2 ^ (prefixWord ++ tailWord_1549825).sum := by decide
  have hdescent : baseEnd_1549825 < baseStart_1549825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549844 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1549844 : Nat := 118140960795 + 1549844 * 2 ^ 59
def prefixEnd_1549844 : Nat := 4983230072969 + 3 ^ 40 * 1549844 * 2
def baseEnd_1549844 : Nat := 530543274324626307948269

theorem tailTrace_1549844 : CollatzResearch.WordTrace tailWord_1549844 prefixEnd_1549844 530543274324626307948269 := by
  unfold tailWord_1549844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28263727298593677563540293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37684969731458236751387057 28263727298593677563540293)
  ·
    refine ⟨5299448868486314543163805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28263727298593677563540293 5299448868486314543163805)
    ·
      refine ⟨1987293325682367953686427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5299448868486314543163805 1987293325682367953686427)
      ·
        refine ⟨2980939988523551930529641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987293325682367953686427 2980939988523551930529641)
        ·
          refine ⟨2235704991392663947897231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980939988523551930529641 2235704991392663947897231)
          ·
            refine ⟨3353557487088995921845847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235704991392663947897231 3353557487088995921845847)
            ·
              refine ⟨5030336230633493882768771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3353557487088995921845847 5030336230633493882768771)
              ·
                refine ⟨7545504345950240824153157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5030336230633493882768771 7545504345950240824153157)
                ·
                  refine ⟨1414782064865670154528717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7545504345950240824153157 1414782064865670154528717)
                  ·
                    refine ⟨530543274324626307948269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414782064865670154528717 530543274324626307948269)
                    ·
                      rfl

theorem cell22_1549844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1549844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549844 prefixEnd_1549844 := by exact prefixLift 1549844
  have htrace : WordTrace (prefixWord ++ tailWord_1549844) baseStart_1549844 baseEnd_1549844 := by
    simpa [prefixWord, tailWord_1549844, baseEnd_1549844] using wordTrace_append hprefix tailTrace_1549844
  have hstable : (prefixWord ++ tailWord_1549844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549844).length < 2 ^ (prefixWord ++ tailWord_1549844).sum := by decide
  have hdescent : baseEnd_1549844 < baseStart_1549844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549855 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 3, 3]
def baseStart_1549855 : Nat := 118140960795 + 1549855 * 2 ^ 59
def prefixEnd_1549855 : Nat := 4983230072969 + 3 ^ 40 * 1549855 * 2
def baseEnd_1549855 : Nat := 530547039849425945923235

theorem tailTrace_1549855 : CollatzResearch.WordTrace tailWord_1549855 prefixEnd_1549855 530547039849425945923235 := by
  unfold tailWord_1549855
  simp only [CollatzResearch.WordTrace]
  refine ⟨56527855800147504005731019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37685237200098336003820679 56527855800147504005731019)
  ·
    refine ⟨84791783700221256008596529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56527855800147504005731019 84791783700221256008596529)
    ·
      refine ⟨63593837775165942006447397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84791783700221256008596529 63593837775165942006447397)
      ·
        refine ⟨11923844582843614126208887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63593837775165942006447397 11923844582843614126208887)
        ·
          refine ⟨17885766874265421189313331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11923844582843614126208887 17885766874265421189313331)
          ·
            refine ⟨26828650311398131783969997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17885766874265421189313331 26828650311398131783969997)
            ·
              refine ⟨10060743866774299418988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26828650311398131783969997 10060743866774299418988749)
              ·
                refine ⟨3772778950040362282120781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10060743866774299418988749 3772778950040362282120781)
                ·
                  refine ⟨1414792106265135855795293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3772778950040362282120781 1414792106265135855795293)
                  ·
                    refine ⟨530547039849425945923235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414792106265135855795293 530547039849425945923235)
                    ·
                      rfl

theorem cell22_1549855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 3].length) (baseStart_1549855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549855 prefixEnd_1549855 := by exact prefixLift 1549855
  have htrace : WordTrace (prefixWord ++ tailWord_1549855) baseStart_1549855 baseEnd_1549855 := by
    simpa [prefixWord, tailWord_1549855, baseEnd_1549855] using wordTrace_append hprefix tailTrace_1549855
  have hstable : (prefixWord ++ tailWord_1549855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549855).length < 2 ^ (prefixWord ++ tailWord_1549855).sum := by decide
  have hdescent : baseEnd_1549855 < baseStart_1549855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549906 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_1549906 : Nat := 118140960795 + 1549906 * 2 ^ 59
def prefixEnd_1549906 : Nat := 4983230072969 + 3 ^ 40 * 1549906 * 2
def baseEnd_1549906 : Nat := 530564498191678812898079

theorem tailTrace_1549906 : CollatzResearch.WordTrace tailWord_1549906 prefixEnd_1549906 530564498191678812898079 := by
  unfold tailWord_1549906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14132428980740684928959393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37686477281975159810558381 14132428980740684928959393)
  ·
    refine ⟨10599321735555513696719545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14132428980740684928959393 10599321735555513696719545)
    ·
      refine ⟨7949491301666635272539659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10599321735555513696719545 7949491301666635272539659)
      ·
        refine ⟨11924236952499952908809489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7949491301666635272539659 11924236952499952908809489)
        ·
          refine ⟨8943177714374964681607117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924236952499952908809489 8943177714374964681607117)
          ·
            refine ⟨3353691642890611755602669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8943177714374964681607117 3353691642890611755602669)
            ·
              refine ⟨1257634366083979408351001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353691642890611755602669 1257634366083979408351001)
              ·
                refine ⟨943225774562984556263251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257634366083979408351001 943225774562984556263251)
                ·
                  refine ⟨1414838661844476834394877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943225774562984556263251 1414838661844476834394877)
                  ·
                    refine ⟨530564498191678812898079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414838661844476834394877 530564498191678812898079)
                    ·
                      rfl

theorem cell22_1549906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_1549906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549906 prefixEnd_1549906 := by exact prefixLift 1549906
  have htrace : WordTrace (prefixWord ++ tailWord_1549906) baseStart_1549906 baseEnd_1549906 := by
    simpa [prefixWord, tailWord_1549906, baseEnd_1549906] using wordTrace_append hprefix tailTrace_1549906
  have hstable : (prefixWord ++ tailWord_1549906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549906).length < 2 ^ (prefixWord ++ tailWord_1549906).sum := by decide
  have hdescent : baseEnd_1549906 < baseStart_1549906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549945 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 1, 5]
def baseStart_1549945 : Nat := 118140960795 + 1549945 * 2 ^ 59
def prefixEnd_1549945 : Nat := 4983230072969 + 3 ^ 40 * 1549945 * 2
def baseEnd_1549945 : Nat := 530577848688695711172959

theorem tailTrace_1549945 : CollatzResearch.WordTrace tailWord_1549945 prefixEnd_1549945 530577848688695711172959 := by
  unfold tailWord_1549945
  simp only [CollatzResearch.WordTrace]
  refine ⟨56531138369821449376507289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37687425579880966251004859 56531138369821449376507289)
  ·
    refine ⟨42398353777366087032380467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56531138369821449376507289 42398353777366087032380467)
    ·
      refine ⟨63597530666049130548570701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42398353777366087032380467 63597530666049130548570701)
      ·
        refine ⟨23849073999768423955714013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63597530666049130548570701 23849073999768423955714013)
        ·
          refine ⟨8943402749913158983392755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23849073999768423955714013 8943402749913158983392755)
          ·
            refine ⟨13415104124869738475089133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8943402749913158983392755 13415104124869738475089133)
            ·
              refine ⟨5030664046826151928158425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13415104124869738475089133 5030664046826151928158425)
              ·
                refine ⟨3772998035119613946118819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5030664046826151928158425 3772998035119613946118819)
                ·
                  refine ⟨5659497052679420919178229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3772998035119613946118819 5659497052679420919178229)
                  ·
                    refine ⟨530577848688695711172959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5659497052679420919178229 530577848688695711172959)
                    ·
                      rfl

theorem cell22_1549945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_1549945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549945 prefixEnd_1549945 := by exact prefixLift 1549945
  have htrace : WordTrace (prefixWord ++ tailWord_1549945) baseStart_1549945 baseEnd_1549945 := by
    simpa [prefixWord, tailWord_1549945, baseEnd_1549945] using wordTrace_append hprefix tailTrace_1549945
  have hstable : (prefixWord ++ tailWord_1549945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549945).length < 2 ^ (prefixWord ++ tailWord_1549945).sum := by decide
  have hdescent : baseEnd_1549945 < baseStart_1549945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549949 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_1549949 : Nat := 118140960795 + 1549949 * 2 ^ 59
def prefixEnd_1549949 : Nat := 4983230072969 + 3 ^ 40 * 1549949 * 2
def baseEnd_1549949 : Nat := 530579217970441034072947

theorem tailTrace_1549949 : CollatzResearch.WordTrace tailWord_1549949 prefixEnd_1549949 530579217970441034072947 := by
  unfold tailWord_1549949
  simp only [CollatzResearch.WordTrace]
  refine ⟨56531284261806958059652901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37687522841204638706435267 56531284261806958059652901)
  ·
    refine ⟨10599615799088804636184919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56531284261806958059652901 10599615799088804636184919)
    ·
      refine ⟨15899423698633206954277379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10599615799088804636184919 15899423698633206954277379)
      ·
        refine ⟨23849135547949810431416069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15899423698633206954277379 23849135547949810431416069)
        ·
          refine ⟨4471712915240589455890513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23849135547949810431416069 4471712915240589455890513)
          ·
            refine ⟨3353784686430442091917885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471712915240589455890513 3353784686430442091917885)
            ·
              refine ⟨1257669257411415784469207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353784686430442091917885 1257669257411415784469207)
              ·
                refine ⟨1886503886117123676703811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1257669257411415784469207 1886503886117123676703811)
                ·
                  refine ⟨2829755829175685515055717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886503886117123676703811 2829755829175685515055717)
                  ·
                    refine ⟨530579217970441034072947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2829755829175685515055717 530579217970441034072947)
                    ·
                      rfl

theorem cell22_1549949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_1549949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549949 prefixEnd_1549949 := by exact prefixLift 1549949
  have htrace : WordTrace (prefixWord ++ tailWord_1549949) baseStart_1549949 baseEnd_1549949 := by
    simpa [prefixWord, tailWord_1549949, baseEnd_1549949] using wordTrace_append hprefix tailTrace_1549949
  have hstable : (prefixWord ++ tailWord_1549949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549949).length < 2 ^ (prefixWord ++ tailWord_1549949).sum := by decide
  have hdescent : baseEnd_1549949 < baseStart_1549949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1549975 : List Nat := [1, 1, 3, 3, 2, 2, 3, 7]
def baseStart_1549975 : Nat := 118140960795 + 1549975 * 2 ^ 59
def prefixEnd_1549975 : Nat := 4983230072969 + 3 ^ 40 * 1549975 * 2
def baseEnd_1549975 : Nat := 58954235366865070324763

theorem tailTrace_1549975 : CollatzResearch.WordTrace tailWord_1549975 prefixEnd_1549975 58954235366865070324763 := by
  unfold tailWord_1549975
  simp only [CollatzResearch.WordTrace]
  refine ⟨56532232559712764500099379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37688155039808509666732919 56532232559712764500099379)
  ·
    refine ⟨84798348839569146750149069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56532232559712764500099379 84798348839569146750149069)
    ·
      refine ⟨31799380814838430031305901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84798348839569146750149069 31799380814838430031305901)
      ·
        refine ⟨11924767805564411261739713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31799380814838430031305901 11924767805564411261739713)
        ·
          refine ⟨8943575854173308446304785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11924767805564411261739713 8943575854173308446304785)
          ·
            refine ⟨6707681890629981334728589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8943575854173308446304785 6707681890629981334728589)
            ·
              refine ⟨2515380708986243000523221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6707681890629981334728589 2515380708986243000523221)
              ·
                refine ⟨58954235366865070324763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2515380708986243000523221 58954235366865070324763)
                ·
                  rfl

theorem cell22_1549975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 7].length) (baseStart_1549975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1549975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1549975 prefixEnd_1549975 := by exact prefixLift 1549975
  have htrace : WordTrace (prefixWord ++ tailWord_1549975) baseStart_1549975 baseEnd_1549975 := by
    simpa [prefixWord, tailWord_1549975, baseEnd_1549975] using wordTrace_append hprefix tailTrace_1549975
  have hstable : (prefixWord ++ tailWord_1549975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1549975).length < 2 ^ (prefixWord ++ tailWord_1549975).sum := by decide
  have hdescent : baseEnd_1549975 < baseStart_1549975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1549975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550024 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1550024 : Nat := 118140960795 + 1550024 * 2 ^ 59
def prefixEnd_1550024 : Nat := 4983230072969 + 3 ^ 40 * 1550024 * 2
def baseEnd_1550024 : Nat := 530604892003165838447717

theorem tailTrace_1550024 : CollatzResearch.WordTrace tailWord_1550024 prefixEnd_1550024 530604892003165838447717 := by
  unfold tailWord_1550024
  simp only [CollatzResearch.WordTrace]
  refine ⟨28267009868267622934316563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37689346491023497245755417 28267009868267622934316563)
  ·
    refine ⟨42400514802401434401474845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28267009868267622934316563 42400514802401434401474845)
    ·
      refine ⟨15900193050900537900553067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42400514802401434401474845 15900193050900537900553067)
      ·
        refine ⟨23850289576350806850829601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15900193050900537900553067 23850289576350806850829601)
        ·
          refine ⟨17887717182263105138122201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23850289576350806850829601 17887717182263105138122201)
          ·
            refine ⟨13415787886697328853591651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17887717182263105138122201 13415787886697328853591651)
            ·
              refine ⟨20123681830045993280387477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13415787886697328853591651 20123681830045993280387477)
              ·
                refine ⟨943297585783405935018163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20123681830045993280387477 943297585783405935018163)
                ·
                  refine ⟨1414946378675108902527245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943297585783405935018163 1414946378675108902527245)
                  ·
                    refine ⟨530604892003165838447717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1414946378675108902527245 530604892003165838447717)
                    ·
                      rfl

theorem cell22_1550024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1550024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550024 prefixEnd_1550024 := by exact prefixLift 1550024
  have htrace : WordTrace (prefixWord ++ tailWord_1550024) baseStart_1550024 baseEnd_1550024 := by
    simpa [prefixWord, tailWord_1550024, baseEnd_1550024] using wordTrace_append hprefix tailTrace_1550024
  have hstable : (prefixWord ++ tailWord_1550024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550024).length < 2 ^ (prefixWord ++ tailWord_1550024).sum := by decide
  have hdescent : baseEnd_1550024 < baseStart_1550024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550067 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 1, 4]
def baseStart_1550067 : Nat := 118140960795 + 1550067 * 2 ^ 59
def prefixEnd_1550067 : Nat := 4983230072969 + 3 ^ 40 * 1550067 * 2
def baseEnd_1550067 : Nat := 530619611781928059622585

theorem tailTrace_1550067 : CollatzResearch.WordTrace tailWord_1550067 prefixEnd_1550067 530619611781928059622585 := by
  unfold tailWord_1550067
  simp only [CollatzResearch.WordTrace]
  refine ⟨56535588075379464212448455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37690392050252976141632303 56535588075379464212448455)
  ·
    refine ⟨84803382113069196318672683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56535588075379464212448455 84803382113069196318672683)
    ·
      refine ⟨127205073169603794478009025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84803382113069196318672683 127205073169603794478009025)
      ·
        refine ⟨95403804877202845858506769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127205073169603794478009025 95403804877202845858506769)
        ·
          refine ⟨71552853657902134393880077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95403804877202845858506769 71552853657902134393880077)
          ·
            refine ⟨26832320121713300397705029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71552853657902134393880077 26832320121713300397705029)
            ·
              refine ⟨5031060022821243824569693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26832320121713300397705029 5031060022821243824569693)
              ·
                refine ⟨1886647508557966434213635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5031060022821243824569693 1886647508557966434213635)
                ·
                  refine ⟨2829971262836949651320453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886647508557966434213635 2829971262836949651320453)
                  ·
                    refine ⟨530619611781928059622585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2829971262836949651320453 530619611781928059622585)
                    ·
                      rfl

theorem cell22_1550067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 4].length) (baseStart_1550067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550067 prefixEnd_1550067 := by exact prefixLift 1550067
  have htrace : WordTrace (prefixWord ++ tailWord_1550067) baseStart_1550067 baseEnd_1550067 := by
    simpa [prefixWord, tailWord_1550067, baseEnd_1550067] using wordTrace_append hprefix tailTrace_1550067
  have hstable : (prefixWord ++ tailWord_1550067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550067).length < 2 ^ (prefixWord ++ tailWord_1550067).sum := by decide
  have hdescent : baseEnd_1550067 < baseStart_1550067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550080 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_1550080 : Nat := 118140960795 + 1550080 * 2 ^ 59
def prefixEnd_1550080 : Nat := 4983230072969 + 3 ^ 40 * 1550080 * 2
def baseEnd_1550080 : Nat := 530624061947600359047545

theorem tailTrace_1550080 : CollatzResearch.WordTrace tailWord_1550080 prefixEnd_1550080 530624061947600359047545 := by
  unfold tailWord_1550080
  simp only [CollatzResearch.WordTrace]
  refine ⟨28268031112166183716335847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37690708149554911621781129 28268031112166183716335847)
  ·
    refine ⟨42402046668249275574503771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28268031112166183716335847 42402046668249275574503771)
    ·
      refine ⟨63603070002373913361755657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42402046668249275574503771 63603070002373913361755657)
      ·
        refine ⟨47702302501780435021316743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63603070002373913361755657 47702302501780435021316743)
        ·
          refine ⟨71553453752670652531975115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47702302501780435021316743 71553453752670652531975115)
          ·
            refine ⟨107330180629005978797962673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71553453752670652531975115 107330180629005978797962673)
            ·
              refine ⟨80497635471754484098472005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107330180629005978797962673 80497635471754484098472005)
              ·
                refine ⟨15093306650953965768463501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80497635471754484098472005 15093306650953965768463501)
                ·
                  refine ⟨5659989994107737163173813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15093306650953965768463501 5659989994107737163173813)
                  ·
                    refine ⟨530624061947600359047545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5659989994107737163173813 530624061947600359047545)
                    ·
                      rfl

theorem cell22_1550080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_1550080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550080 prefixEnd_1550080 := by exact prefixLift 1550080
  have htrace : WordTrace (prefixWord ++ tailWord_1550080) baseStart_1550080 baseEnd_1550080 := by
    simpa [prefixWord, tailWord_1550080, baseEnd_1550080] using wordTrace_append hprefix tailTrace_1550080
  have hstable : (prefixWord ++ tailWord_1550080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550080).length < 2 ^ (prefixWord ++ tailWord_1550080).sum := by decide
  have hdescent : baseEnd_1550080 < baseStart_1550080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550095 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 6]
def baseStart_1550095 : Nat := 118140960795 + 1550095 * 2 ^ 59
def prefixEnd_1550095 : Nat := 4983230072969 + 3 ^ 40 * 1550095 * 2
def baseEnd_1550095 : Nat := 530629196754145319922499

theorem tailTrace_1550095 : CollatzResearch.WordTrace tailWord_1550095 prefixEnd_1550095 530629196754145319922499 := by
  unfold tailWord_1550095
  simp only [CollatzResearch.WordTrace]
  refine ⟨56536609319278024994467739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37691072879518683329645159 56536609319278024994467739)
  ·
    refine ⟨84804913978917037491701609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56536609319278024994467739 84804913978917037491701609)
    ·
      refine ⟨63603685484187778118776207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84804913978917037491701609 63603685484187778118776207)
      ·
        refine ⟨95405528226281667178164311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63603685484187778118776207 95405528226281667178164311)
        ·
          refine ⟨143108292339422500767246467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95405528226281667178164311 143108292339422500767246467)
          ·
            refine ⟨214662438509133751150869701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143108292339422500767246467 214662438509133751150869701)
            ·
              refine ⟨40249207220462578340788069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214662438509133751150869701 40249207220462578340788069)
              ·
                refine ⟨7546726353836733438897763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40249207220462578340788069 7546726353836733438897763)
                ·
                  refine ⟨11320089530755100158346645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7546726353836733438897763 11320089530755100158346645)
                  ·
                    refine ⟨530629196754145319922499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11320089530755100158346645 530629196754145319922499)
                    ·
                      rfl

theorem cell22_1550095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_1550095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550095 prefixEnd_1550095 := by exact prefixLift 1550095
  have htrace : WordTrace (prefixWord ++ tailWord_1550095) baseStart_1550095 baseEnd_1550095 := by
    simpa [prefixWord, tailWord_1550095, baseEnd_1550095] using wordTrace_append hprefix tailTrace_1550095
  have hstable : (prefixWord ++ tailWord_1550095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550095).length < 2 ^ (prefixWord ++ tailWord_1550095).sum := by decide
  have hdescent : baseEnd_1550095 < baseStart_1550095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550131 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 2, 3]
def baseStart_1550131 : Nat := 118140960795 + 1550131 * 2 ^ 59
def prefixEnd_1550131 : Nat := 4983230072969 + 3 ^ 40 * 1550131 * 2
def baseEnd_1550131 : Nat := 530641520289853226022389

theorem tailTrace_1550131 : CollatzResearch.WordTrace tailWord_1550131 prefixEnd_1550131 530641520289853226022389 := by
  unfold tailWord_1550131
  simp only [CollatzResearch.WordTrace]
  refine ⟨56537922347147603142778247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37691948231431735428518831 56537922347147603142778247)
  ·
    refine ⟨84806883520721404714167371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56537922347147603142778247 84806883520721404714167371)
    ·
      refine ⟨127210325281082107071251057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84806883520721404714167371 127210325281082107071251057)
      ·
        refine ⟨95407743960811580303438293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127210325281082107071251057 95407743960811580303438293)
        ·
          refine ⟨2236118999081521413361835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 95407743960811580303438293 2236118999081521413361835)
          ·
            refine ⟨3354178498622282120042753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236118999081521413361835 3354178498622282120042753)
            ·
              refine ⟨2515633873966711590032065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3354178498622282120042753 2515633873966711590032065)
              ·
                refine ⟨1886725405475033692524049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515633873966711590032065 1886725405475033692524049)
                ·
                  refine ⟨1415044054106275269393037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1886725405475033692524049 1415044054106275269393037)
                  ·
                    refine ⟨530641520289853226022389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415044054106275269393037 530641520289853226022389)
                    ·
                      rfl

theorem cell22_1550131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 3].length) (baseStart_1550131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550131 prefixEnd_1550131 := by exact prefixLift 1550131
  have htrace : WordTrace (prefixWord ++ tailWord_1550131) baseStart_1550131 baseEnd_1550131 := by
    simpa [prefixWord, tailWord_1550131, baseEnd_1550131] using wordTrace_append hprefix tailTrace_1550131
  have hstable : (prefixWord ++ tailWord_1550131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550131).length < 2 ^ (prefixWord ++ tailWord_1550131).sum := by decide
  have hdescent : baseEnd_1550131 < baseStart_1550131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550133 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 4]
def baseStart_1550133 : Nat := 118140960795 + 1550133 * 2 ^ 59
def prefixEnd_1550133 : Nat := 4983230072969 + 3 ^ 40 * 1550133 * 2
def baseEnd_1550133 : Nat := 176880734976908629157461

theorem tailTrace_1550133 : CollatzResearch.WordTrace tailWord_1550133 prefixEnd_1550133 176880734976908629157461 := by
  unfold tailWord_1550133
  simp only [CollatzResearch.WordTrace]
  refine ⟨56537995293140357484351053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37691996862093571656234035 56537995293140357484351053)
  ·
    refine ⟨21201748234927634056631645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56537995293140357484351053 21201748234927634056631645)
    ·
      refine ⟨7950655588097862771236867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21201748234927634056631645 7950655588097862771236867)
      ·
        refine ⟨11925983382146794156855301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7950655588097862771236867 11925983382146794156855301)
        ·
          refine ⟨2236121884152523904410369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11925983382146794156855301 2236121884152523904410369)
          ·
            refine ⟨1677091413114392928307777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2236121884152523904410369 1677091413114392928307777)
            ·
              refine ⟨1257818559835794696230833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677091413114392928307777 1257818559835794696230833)
              ·
                refine ⟨943363919876846022173125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1257818559835794696230833 943363919876846022173125)
                ·
                  refine ⟨176880734976908629157461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943363919876846022173125 176880734976908629157461)
                  ·
                    rfl

theorem cell22_1550133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_1550133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550133 prefixEnd_1550133 := by exact prefixLift 1550133
  have htrace : WordTrace (prefixWord ++ tailWord_1550133) baseStart_1550133 baseEnd_1550133 := by
    simpa [prefixWord, tailWord_1550133, baseEnd_1550133] using wordTrace_append hprefix tailTrace_1550133
  have hstable : (prefixWord ++ tailWord_1550133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550133).length < 2 ^ (prefixWord ++ tailWord_1550133).sum := by decide
  have hdescent : baseEnd_1550133 < baseStart_1550133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550176 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 1, 3]
def baseStart_1550176 : Nat := 118140960795 + 1550176 * 2 ^ 59
def prefixEnd_1550176 : Nat := 4983230072969 + 3 ^ 40 * 1550176 * 2
def baseEnd_1550176 : Nat := 530656924709488108647251

theorem tailTrace_1550176 : CollatzResearch.WordTrace tailWord_1550176 prefixEnd_1550176 530656924709488108647251 := by
  unfold tailWord_1550176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28269781815992287914083191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37693042421323050552110921 28269781815992287914083191)
  ·
    refine ⟨42404672723988431871124787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28269781815992287914083191 42404672723988431871124787)
    ·
      refine ⟨63607009085982647806687181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42404672723988431871124787 63607009085982647806687181)
      ·
        refine ⟨23852628407243492927507693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63607009085982647806687181 23852628407243492927507693)
        ·
          refine ⟨8944735652716309847815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23852628407243492927507693 8944735652716309847815385)
          ·
            refine ⟨6708551739537232385861539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8944735652716309847815385 6708551739537232385861539)
            ·
              refine ⟨10062827609305848578792309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6708551739537232385861539 10062827609305848578792309)
              ·
                refine ⟨943390088372423304261779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10062827609305848578792309 943390088372423304261779)
                ·
                  refine ⟨1415085132558634956392669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943390088372423304261779 1415085132558634956392669)
                  ·
                    refine ⟨530656924709488108647251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415085132558634956392669 530656924709488108647251)
                    ·
                      rfl

theorem cell22_1550176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_1550176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550176 prefixEnd_1550176 := by exact prefixLift 1550176
  have htrace : WordTrace (prefixWord ++ tailWord_1550176) baseStart_1550176 baseEnd_1550176 := by
    simpa [prefixWord, tailWord_1550176, baseEnd_1550176] using wordTrace_append hprefix tailTrace_1550176
  have hstable : (prefixWord ++ tailWord_1550176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550176).length < 2 ^ (prefixWord ++ tailWord_1550176).sum := by decide
  have hdescent : baseEnd_1550176 < baseStart_1550176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550189 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 5]
def baseStart_1550189 : Nat := 118140960795 + 1550189 * 2 ^ 59
def prefixEnd_1550189 : Nat := 4983230072969 + 3 ^ 40 * 1550189 * 2
def baseEnd_1550189 : Nat := 176887124958386802690737

theorem tailTrace_1550189 : CollatzResearch.WordTrace tailWord_1550189 prefixEnd_1550189 176887124958386802690737 := by
  unfold tailWord_1550189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56540037780937479048389621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37693358520624986032259747 56540037780937479048389621)
  ·
    refine ⟨5300628541962888660786527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56540037780937479048389621 5300628541962888660786527)
    ·
      refine ⟨7950942812944332991179791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5300628541962888660786527 7950942812944332991179791)
      ·
        refine ⟨11926414219416499486769687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7950942812944332991179791 11926414219416499486769687)
        ·
          refine ⟨17889621329124749230154531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11926414219416499486769687 17889621329124749230154531)
          ·
            refine ⟨26834431993687123845231797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17889621329124749230154531 26834431993687123845231797)
            ·
              refine ⟨2515727999408167860490481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26834431993687123845231797 2515727999408167860490481)
              ·
                refine ⟨1886795999556125895367861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515727999408167860490481 1886795999556125895367861)
                ·
                  refine ⟨176887124958386802690737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1886795999556125895367861 176887124958386802690737)
                  ·
                    rfl

theorem cell22_1550189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_1550189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550189 prefixEnd_1550189 := by exact prefixLift 1550189
  have htrace : WordTrace (prefixWord ++ tailWord_1550189) baseStart_1550189 baseEnd_1550189 := by
    simpa [prefixWord, tailWord_1550189, baseEnd_1550189] using wordTrace_append hprefix tailTrace_1550189
  have hstable : (prefixWord ++ tailWord_1550189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550189).length < 2 ^ (prefixWord ++ tailWord_1550189).sum := by decide
  have hdescent : baseEnd_1550189 < baseStart_1550189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550202 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_1550202 : Nat := 118140960795 + 1550202 * 2 ^ 59
def prefixEnd_1550202 : Nat := 4983230072969 + 3 ^ 40 * 1550202 * 2
def baseEnd_1550202 : Nat := 530665825040832707497171

theorem tailTrace_1550202 : CollatzResearch.WordTrace tailWord_1550202 prefixEnd_1550202 530665825040832707497171 := by
  unfold tailWord_1550202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14135127982472595567153215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37693674619926921512408573 14135127982472595567153215)
  ·
    refine ⟨21202691973708893350729823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14135127982472595567153215 21202691973708893350729823)
    ·
      refine ⟨31804037960563340026094735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21202691973708893350729823 31804037960563340026094735)
      ·
        refine ⟨47706056940845010039142103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31804037960563340026094735 47706056940845010039142103)
        ·
          refine ⟨71559085411267515058713155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47706056940845010039142103 71559085411267515058713155)
          ·
            refine ⟨107338628116901272588069733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71559085411267515058713155 107338628116901272588069733)
            ·
              refine ⟨20125992771918988610263075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107338628116901272588069733 20125992771918988610263075)
              ·
                refine ⟨30188989157878482915394613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20125992771918988610263075 30188989157878482915394613)
                ·
                  refine ⟨2830217733551107773318245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30188989157878482915394613 2830217733551107773318245)
                  ·
                    refine ⟨530665825040832707497171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830217733551107773318245 530665825040832707497171)
                    ·
                      rfl

theorem cell22_1550202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_1550202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550202 prefixEnd_1550202 := by exact prefixLift 1550202
  have htrace : WordTrace (prefixWord ++ tailWord_1550202) baseStart_1550202 baseEnd_1550202 := by
    simpa [prefixWord, tailWord_1550202, baseEnd_1550202] using wordTrace_append hprefix tailTrace_1550202
  have hstable : (prefixWord ++ tailWord_1550202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550202).length < 2 ^ (prefixWord ++ tailWord_1550202).sum := by decide
  have hdescent : baseEnd_1550202 < baseStart_1550202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550217 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 6]
def baseStart_1550217 : Nat := 118140960795 + 1550217 * 2 ^ 59
def prefixEnd_1550217 : Nat := 4983230072969 + 3 ^ 40 * 1550217 * 2
def baseEnd_1550217 : Nat := 176890319949125889457375

theorem tailTrace_1550217 : CollatzResearch.WordTrace tailWord_1550217 prefixEnd_1550217 176890319949125889457375 := by
  unfold tailWord_1550217
  simp only [CollatzResearch.WordTrace]
  refine ⟨56541059024836039830408905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37694039349890693220272603 56541059024836039830408905)
  ·
    refine ⟨42405794268627029872806679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56541059024836039830408905 42405794268627029872806679)
    ·
      refine ⟨63608691402940544809210019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42405794268627029872806679 63608691402940544809210019)
      ·
        refine ⟨95413037104410817213815029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63608691402940544809210019 95413037104410817213815029)
        ·
          refine ⟨8944972228538514113795159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95413037104410817213815029 8944972228538514113795159)
          ·
            refine ⟨13417458342807771170692739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8944972228538514113795159 13417458342807771170692739)
            ·
              refine ⟨20126187514211656756039109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13417458342807771170692739 20126187514211656756039109)
              ·
                refine ⟨3773660158914685641757333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20126187514211656756039109 3773660158914685641757333)
                ·
                  refine ⟨176890319949125889457375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3773660158914685641757333 176890319949125889457375)
                  ·
                    rfl

theorem cell22_1550217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_1550217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550217 prefixEnd_1550217 := by exact prefixLift 1550217
  have htrace : WordTrace (prefixWord ++ tailWord_1550217) baseStart_1550217 baseEnd_1550217 := by
    simpa [prefixWord, tailWord_1550217, baseEnd_1550217] using wordTrace_append hprefix tailTrace_1550217
  have hstable : (prefixWord ++ tailWord_1550217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550217).length < 2 ^ (prefixWord ++ tailWord_1550217).sum := by decide
  have hdescent : baseEnd_1550217 < baseStart_1550217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550236 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 1, 4]
def baseStart_1550236 : Nat := 118140960795 + 1550236 * 2 ^ 59
def prefixEnd_1550236 : Nat := 4983230072969 + 3 ^ 40 * 1550236 * 2
def baseEnd_1550236 : Nat := 530677463935667952147067

theorem tailTrace_1550236 : CollatzResearch.WordTrace tailWord_1550236 prefixEnd_1550236 530677463935667952147067 := by
  unfold tailWord_1550236
  simp only [CollatzResearch.WordTrace]
  refine ⟨28270876005883603037675281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37694501341178137383567041 28270876005883603037675281)
  ·
    refine ⟨21203157004412702278256461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28270876005883603037675281 21203157004412702278256461)
    ·
      refine ⟨7951183876654763354346173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21203157004412702278256461 7951183876654763354346173)
      ·
        refine ⟨2981693953745536257879815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7951183876654763354346173 2981693953745536257879815)
        ·
          refine ⟨4472540930618304386819723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2981693953745536257879815 4472540930618304386819723)
          ·
            refine ⟨6708811395927456580229585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4472540930618304386819723 6708811395927456580229585)
            ·
              refine ⟨5031608546945592435172189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6708811395927456580229585 5031608546945592435172189)
              ·
                refine ⟨1886853205104597163189571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5031608546945592435172189 1886853205104597163189571)
                ·
                  refine ⟨2830279807656895744784357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1886853205104597163189571 2830279807656895744784357)
                  ·
                    refine ⟨530677463935667952147067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2830279807656895744784357 530677463935667952147067)
                    ·
                      rfl

theorem cell22_1550236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_1550236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550236 prefixEnd_1550236 := by exact prefixLift 1550236
  have htrace : WordTrace (prefixWord ++ tailWord_1550236) baseStart_1550236 baseEnd_1550236 := by
    simpa [prefixWord, tailWord_1550236, baseEnd_1550236] using wordTrace_append hprefix tailTrace_1550236
  have hstable : (prefixWord ++ tailWord_1550236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550236).length < 2 ^ (prefixWord ++ tailWord_1550236).sum := by decide
  have hdescent : baseEnd_1550236 < baseStart_1550236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550375 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 5]
def baseStart_1550375 : Nat := 118140960795 + 1550375 * 2 ^ 59
def prefixEnd_1550375 : Nat := 4983230072969 + 3 ^ 40 * 1550375 * 2
def baseEnd_1550375 : Nat := 176908348825439307640547

theorem tailTrace_1550375 : CollatzResearch.WordTrace tailWord_1550375 prefixEnd_1550375 176908348825439307640547 := by
  unfold tailWord_1550375
  simp only [CollatzResearch.WordTrace]
  refine ⟨56546821758263632814660579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37697881172175755209773719 56546821758263632814660579)
  ·
    refine ⟨84820232637395449221990869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56546821758263632814660579 84820232637395449221990869)
    ·
      refine ⟨1987974202438955841140411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 84820232637395449221990869 1987974202438955841140411)
      ·
        refine ⟨2981961303658433761710617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1987974202438955841140411 2981961303658433761710617)
        ·
          refine ⟨2236470977743825321282963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2981961303658433761710617 2236470977743825321282963)
          ·
            refine ⟨3354706466615737981924445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2236470977743825321282963 3354706466615737981924445)
            ·
              refine ⟨1258014924980901743221667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3354706466615737981924445 1258014924980901743221667)
              ·
                refine ⟨1887022387471352614832501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258014924980901743221667 1887022387471352614832501)
                ·
                  refine ⟨176908348825439307640547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1887022387471352614832501 176908348825439307640547)
                  ·
                    rfl

theorem cell22_1550375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 5].length) (baseStart_1550375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550375 prefixEnd_1550375 := by exact prefixLift 1550375
  have htrace : WordTrace (prefixWord ++ tailWord_1550375) baseStart_1550375 baseEnd_1550375 := by
    simpa [prefixWord, tailWord_1550375, baseEnd_1550375] using wordTrace_append hprefix tailTrace_1550375
  have hstable : (prefixWord ++ tailWord_1550375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550375).length < 2 ^ (prefixWord ++ tailWord_1550375).sum := by decide
  have hdescent : baseEnd_1550375 < baseStart_1550375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550399 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_1550399 : Nat := 118140960795 + 1550399 * 2 ^ 59
def prefixEnd_1550399 : Nat := 4983230072969 + 3 ^ 40 * 1550399 * 2
def baseEnd_1550399 : Nat := 530733262166789860321567

theorem tailTrace_1550399 : CollatzResearch.WordTrace tailWord_1550399 prefixEnd_1550399 530733262166789860321567 := by
  unfold tailWord_1550399
  simp only [CollatzResearch.WordTrace]
  refine ⟨56547697110176684913534251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37698464740117789942356167 56547697110176684913534251)
  ·
    refine ⟨84821545665265027370301377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56547697110176684913534251 84821545665265027370301377)
    ·
      refine ⟨63616159248948770527726033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84821545665265027370301377 63616159248948770527726033)
      ·
        refine ⟨47712119436711577895794525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63616159248948770527726033 47712119436711577895794525)
        ·
          refine ⟨17892044788766841710922947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47712119436711577895794525 17892044788766841710922947)
          ·
            refine ⟨26838067183150262566384421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17892044788766841710922947 26838067183150262566384421)
            ·
              refine ⟨5032137596840674231197079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26838067183150262566384421 5032137596840674231197079)
              ·
                refine ⟨7548206395261011346795619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5032137596840674231197079 7548206395261011346795619)
                ·
                  refine ⟨11322309592891517020193429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7548206395261011346795619 11322309592891517020193429)
                  ·
                    refine ⟨530733262166789860321567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11322309592891517020193429 530733262166789860321567)
                    ·
                      rfl

theorem cell22_1550399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_1550399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550399 prefixEnd_1550399 := by exact prefixLift 1550399
  have htrace : WordTrace (prefixWord ++ tailWord_1550399) baseStart_1550399 baseEnd_1550399 := by
    simpa [prefixWord, tailWord_1550399, baseEnd_1550399] using wordTrace_append hprefix tailTrace_1550399
  have hstable : (prefixWord ++ tailWord_1550399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550399).length < 2 ^ (prefixWord ++ tailWord_1550399).sum := by decide
  have hdescent : baseEnd_1550399 < baseStart_1550399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550414 : List Nat := [4, 1, 1, 1, 1, 4, 10]
def baseStart_1550414 : Nat := 118140960795 + 1550414 * 2 ^ 59
def prefixEnd_1550414 : Nat := 4983230072969 + 3 ^ 40 * 1550414 * 2
def baseEnd_1550414 : Nat := 19656977665679067451723

theorem tailTrace_1550414 : CollatzResearch.WordTrace tailWord_1550414 prefixEnd_1550414 19656977665679067451723 := by
  unfold tailWord_1550414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068530525640292809416287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37698829470081561650220197 7068530525640292809416287)
  ·
    refine ⟨10602795788460439214124431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7068530525640292809416287 10602795788460439214124431)
    ·
      refine ⟨15904193682690658821186647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10602795788460439214124431 15904193682690658821186647)
      ·
        refine ⟨23856290524035988231779971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15904193682690658821186647 23856290524035988231779971)
        ·
          refine ⟨35784435786053982347669957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23856290524035988231779971 35784435786053982347669957)
          ·
            refine ⟨6709581709885121690188117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35784435786053982347669957 6709581709885121690188117)
            ·
              refine ⟨19656977665679067451723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6709581709885121690188117 19656977665679067451723)
              ·
                rfl

theorem cell22_1550414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 10].length) (baseStart_1550414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550414 prefixEnd_1550414 := by exact prefixLift 1550414
  have htrace : WordTrace (prefixWord ++ tailWord_1550414) baseStart_1550414 baseEnd_1550414 := by
    simpa [prefixWord, tailWord_1550414, baseEnd_1550414] using wordTrace_append hprefix tailTrace_1550414
  have hstable : (prefixWord ++ tailWord_1550414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550414).length < 2 ^ (prefixWord ++ tailWord_1550414).sum := by decide
  have hdescent : baseEnd_1550414 < baseStart_1550414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550538 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_1550538 : Nat := 118140960795 + 1550538 * 2 ^ 59
def prefixEnd_1550538 : Nat := 4983230072969 + 3 ^ 40 * 1550538 * 2
def baseEnd_1550538 : Nat := 176926948235813277032047

theorem tailTrace_1550538 : CollatzResearch.WordTrace tailWord_1550538 prefixEnd_1550538 176926948235813277032047 := by
  unfold tailWord_1550538
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138191714168277913211067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37701844571115407768562845 14138191714168277913211067)
  ·
    refine ⟨21207287571252416869816601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14138191714168277913211067 21207287571252416869816601)
    ·
      refine ⟨15905465678439312652362451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21207287571252416869816601 15905465678439312652362451)
      ·
        refine ⟨23858198517658968978543677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15905465678439312652362451 23858198517658968978543677)
        ·
          refine ⟨8946824444122113366953879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23858198517658968978543677 8946824444122113366953879)
          ·
            refine ⟨13420236666183170050430819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8946824444122113366953879 13420236666183170050430819)
            ·
              refine ⟨20130354999274755075646229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13420236666183170050430819 20130354999274755075646229)
              ·
                refine ⟨943610390591004144170917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20130354999274755075646229 943610390591004144170917)
                ·
                  refine ⟨176926948235813277032047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 943610390591004144170917 176926948235813277032047)
                  ·
                    rfl

theorem cell22_1550538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_1550538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550538 prefixEnd_1550538 := by exact prefixLift 1550538
  have htrace : WordTrace (prefixWord ++ tailWord_1550538) baseStart_1550538 baseEnd_1550538 := by
    simpa [prefixWord, tailWord_1550538, baseEnd_1550538] using wordTrace_append hprefix tailTrace_1550538
  have hstable : (prefixWord ++ tailWord_1550538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550538).length < 2 ^ (prefixWord ++ tailWord_1550538).sum := by decide
  have hdescent : baseEnd_1550538 < baseStart_1550538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550553 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_1550553 : Nat := 118140960795 + 1550553 * 2 ^ 59
def prefixEnd_1550553 : Nat := 4983230072969 + 3 ^ 40 * 1550553 * 2
def baseEnd_1550553 : Nat := 530785979513984791971095

theorem tailTrace_1550553 : CollatzResearch.WordTrace tailWord_1550553 prefixEnd_1550553 530785979513984791971095 := by
  unfold tailWord_1550553
  simp only [CollatzResearch.WordTrace]
  refine ⟨56553313951618769214640313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37702209301079179476426875 56553313951618769214640313)
  ·
    refine ⟨42414985463714076910980235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56553313951618769214640313 42414985463714076910980235)
    ·
      refine ⟨63622478195571115366470353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42414985463714076910980235 63622478195571115366470353)
      ·
        refine ⟨47716858646678336524852765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63622478195571115366470353 47716858646678336524852765)
        ·
          refine ⟨17893821992504376196819787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47716858646678336524852765 17893821992504376196819787)
          ·
            refine ⟨26840732988756564295229681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17893821992504376196819787 26840732988756564295229681)
            ·
              refine ⟨20130549741567423221422261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26840732988756564295229681 20130549741567423221422261)
              ·
                refine ⟨1887239038271945927008337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20130549741567423221422261 1887239038271945927008337)
                ·
                  refine ⟨1415429278703959445256253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887239038271945927008337 1415429278703959445256253)
                  ·
                    refine ⟨530785979513984791971095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415429278703959445256253 530785979513984791971095)
                    ·
                      rfl

theorem cell22_1550553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_1550553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550553 prefixEnd_1550553 := by exact prefixLift 1550553
  have htrace : WordTrace (prefixWord ++ tailWord_1550553) baseStart_1550553 baseEnd_1550553 := by
    simpa [prefixWord, tailWord_1550553, baseEnd_1550553] using wordTrace_append hprefix tailTrace_1550553
  have hstable : (prefixWord ++ tailWord_1550553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550553).length < 2 ^ (prefixWord ++ tailWord_1550553).sum := by decide
  have hdescent : baseEnd_1550553 < baseStart_1550553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550649 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 1, 3]
def baseStart_1550649 : Nat := 118140960795 + 1550649 * 2 ^ 59
def prefixEnd_1550649 : Nat := 4983230072969 + 3 ^ 40 * 1550649 * 2
def baseEnd_1550649 : Nat := 530818842275872541570801

theorem tailTrace_1550649 : CollatzResearch.WordTrace tailWord_1550649 prefixEnd_1550649 530818842275872541570801 := by
  unfold tailWord_1550649
  simp only [CollatzResearch.WordTrace]
  refine ⟨56556815359270977610135001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37704543572847318406756667 56556815359270977610135001)
  ·
    refine ⟨42417611519453233207601251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56556815359270977610135001 42417611519453233207601251)
    ·
      refine ⟨63626417279179849811401877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42417611519453233207601251 63626417279179849811401877)
      ·
        refine ⟨2982488309961555459909463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63626417279179849811401877 2982488309961555459909463)
        ·
          refine ⟨4473732464942333189864195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982488309961555459909463 4473732464942333189864195)
          ·
            refine ⟨6710598697413499784796293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4473732464942333189864195 6710598697413499784796293)
            ·
              refine ⟨1258237255765031209649305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6710598697413499784796293 1258237255765031209649305)
              ·
                refine ⟨943677941823773407236979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258237255765031209649305 943677941823773407236979)
                ·
                  refine ⟨1415516912735660110855469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943677941823773407236979 1415516912735660110855469)
                  ·
                    refine ⟨530818842275872541570801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415516912735660110855469 530818842275872541570801)
                    ·
                      rfl

theorem cell22_1550649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_1550649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550649 prefixEnd_1550649 := by exact prefixLift 1550649
  have htrace : WordTrace (prefixWord ++ tailWord_1550649) baseStart_1550649 baseEnd_1550649 := by
    simpa [prefixWord, tailWord_1550649, baseEnd_1550649] using wordTrace_append hprefix tailTrace_1550649
  have hstable : (prefixWord ++ tailWord_1550649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550649).length < 2 ^ (prefixWord ++ tailWord_1550649).sum := by decide
  have hdescent : baseEnd_1550649 < baseStart_1550649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550673 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 6]
def baseStart_1550673 : Nat := 118140960795 + 1550673 * 2 ^ 59
def prefixEnd_1550673 : Nat := 4983230072969 + 3 ^ 40 * 1550673 * 2
def baseEnd_1550673 : Nat := 176942352655448159656909

theorem tailTrace_1550673 : CollatzResearch.WordTrace tailWord_1550673 prefixEnd_1550673 176942352655448159656909 := by
  unfold tailWord_1550673
  simp only [CollatzResearch.WordTrace]
  refine ⟨56557690711184029709008673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37705127140789353139339115 56557690711184029709008673)
  ·
    refine ⟨42418268033388022281756505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56557690711184029709008673 42418268033388022281756505)
    ·
      refine ⟨31813701025041016711317379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42418268033388022281756505 31813701025041016711317379)
      ·
        refine ⟨47720551537561525066976069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31813701025041016711317379 47720551537561525066976069)
        ·
          refine ⟨8947603413292785950058013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47720551537561525066976069 8947603413292785950058013)
          ·
            refine ⟨3355351279984794731271755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8947603413292785950058013 3355351279984794731271755)
            ·
              refine ⟨5033026919977192096907633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355351279984794731271755 5033026919977192096907633)
              ·
                refine ⟨3774770189982894072680725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5033026919977192096907633 3774770189982894072680725)
                ·
                  refine ⟨176942352655448159656909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3774770189982894072680725 176942352655448159656909)
                  ·
                    rfl

theorem cell22_1550673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_1550673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550673 prefixEnd_1550673 := by exact prefixLift 1550673
  have htrace : WordTrace (prefixWord ++ tailWord_1550673) baseStart_1550673 baseEnd_1550673 := by
    simpa [prefixWord, tailWord_1550673, baseEnd_1550673] using wordTrace_append hprefix tailTrace_1550673
  have hstable : (prefixWord ++ tailWord_1550673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550673).length < 2 ^ (prefixWord ++ tailWord_1550673).sum := by decide
  have hdescent : baseEnd_1550673 < baseStart_1550673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_1550778 : Nat := 118140960795 + 1550778 * 2 ^ 59
def prefixEnd_1550778 : Nat := 4983230072969 + 3 ^ 40 * 1550778 * 2
def baseEnd_1550778 : Nat := 530863001612159205095405

theorem tailTrace_1550778 : CollatzResearch.WordTrace tailWord_1550778 prefixEnd_1550778 530863001612159205095405 := by
  unfold tailWord_1550778
  simp only [CollatzResearch.WordTrace]
  refine ⟨14140380093950908160395247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37707680250535755094387325 14140380093950908160395247)
  ·
    refine ⟨21210570140926362240592871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14140380093950908160395247 21210570140926362240592871)
    ·
      refine ⟨31815855211389543360889307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21210570140926362240592871 31815855211389543360889307)
      ·
        refine ⟨47723782817084315041333961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31815855211389543360889307 47723782817084315041333961)
        ·
          refine ⟨35792837112813236281000471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47723782817084315041333961 35792837112813236281000471)
          ·
            refine ⟨53689255669219854421500707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35792837112813236281000471 53689255669219854421500707)
            ·
              refine ⟨80533883503829781632251061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53689255669219854421500707 80533883503829781632251061)
              ·
                refine ⟨7550051578484042028023537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80533883503829781632251061 7550051578484042028023537)
                ·
                  refine ⟨5662538683863031521017653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7550051578484042028023537 5662538683863031521017653)
                  ·
                    refine ⟨530863001612159205095405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5662538683863031521017653 530863001612159205095405)
                    ·
                      rfl

theorem cell22_1550778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_1550778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550778 prefixEnd_1550778 := by exact prefixLift 1550778
  have htrace : WordTrace (prefixWord ++ tailWord_1550778) baseStart_1550778 baseEnd_1550778 := by
    simpa [prefixWord, tailWord_1550778, baseEnd_1550778] using wordTrace_append hprefix tailTrace_1550778
  have hstable : (prefixWord ++ tailWord_1550778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550778).length < 2 ^ (prefixWord ++ tailWord_1550778).sum := by decide
  have hdescent : baseEnd_1550778 < baseStart_1550778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550818 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1550818 : Nat := 118140960795 + 1550818 * 2 ^ 59
def prefixEnd_1550818 : Nat := 4983230072969 + 3 ^ 40 * 1550818 * 2
def baseEnd_1550818 : Nat := 530876694429612434095283

theorem tailTrace_1550818 : CollatzResearch.WordTrace tailWord_1550818 prefixEnd_1550818 530876694429612434095283 := by
  unfold tailWord_1550818
  simp only [CollatzResearch.WordTrace]
  refine ⟨14140744823914679868259277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37708652863772479648691405 14140744823914679868259277)
  ·
    refine ⟨5302779308968004950597229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14140744823914679868259277 5302779308968004950597229)
    ·
      refine ⟨1988542240863001856473961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5302779308968004950597229 1988542240863001856473961)
      ·
        refine ⟨1491406680647251392355471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1988542240863001856473961 1491406680647251392355471)
        ·
          refine ⟨2237110020970877088533207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491406680647251392355471 2237110020970877088533207)
          ·
            refine ⟨3355665031456315632799811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237110020970877088533207 3355665031456315632799811)
            ·
              refine ⟨5033497547184473449199717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355665031456315632799811 5033497547184473449199717)
              ·
                refine ⟨943780790097088771724947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5033497547184473449199717 943780790097088771724947)
                ·
                  refine ⟨1415671185145633157587421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 943780790097088771724947 1415671185145633157587421)
                  ·
                    refine ⟨530876694429612434095283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415671185145633157587421 530876694429612434095283)
                    ·
                      rfl

theorem cell22_1550818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1550818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550818 prefixEnd_1550818 := by exact prefixLift 1550818
  have htrace : WordTrace (prefixWord ++ tailWord_1550818) baseStart_1550818 baseEnd_1550818 := by
    simpa [prefixWord, tailWord_1550818, baseEnd_1550818] using wordTrace_append hprefix tailTrace_1550818
  have hstable : (prefixWord ++ tailWord_1550818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550818).length < 2 ^ (prefixWord ++ tailWord_1550818).sum := by decide
  have hdescent : baseEnd_1550818 < baseStart_1550818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550840 : List Nat := [2, 1, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_1550840 : Nat := 118140960795 + 1550840 * 2 ^ 59
def prefixEnd_1550840 : Nat := 4983230072969 + 3 ^ 40 * 1550840 * 2
def baseEnd_1550840 : Nat := 530884225479211710045215

theorem tailTrace_1550840 : CollatzResearch.WordTrace tailWord_1550840 prefixEnd_1550840 530884225479211710045215 := by
  unfold tailWord_1550840
  simp only [CollatzResearch.WordTrace]
  refine ⟨28281890850789508615168987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37709187801052678153558649 28281890850789508615168987)
  ·
    refine ⟨42422836276184262922753481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28281890850789508615168987 42422836276184262922753481)
    ·
      refine ⟨31817127207138197192065111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42422836276184262922753481 31817127207138197192065111)
      ·
        refine ⟨47725690810707295788097667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31817127207138197192065111 47725690810707295788097667)
        ·
          refine ⟨71588536216060943682146501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47725690810707295788097667 71588536216060943682146501)
          ·
            refine ⟨13422850540511426940402469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71588536216060943682146501 13422850540511426940402469)
            ·
              refine ⟨2516784476345892551325463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13422850540511426940402469 2516784476345892551325463)
              ·
                refine ⟨3775176714518838826988195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2516784476345892551325463 3775176714518838826988195)
                ·
                  refine ⟨5662765071778258240482293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775176714518838826988195 5662765071778258240482293)
                  ·
                    refine ⟨530884225479211710045215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5662765071778258240482293 530884225479211710045215)
                    ·
                      rfl

theorem cell22_1550840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_1550840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550840 prefixEnd_1550840 := by exact prefixLift 1550840
  have htrace : WordTrace (prefixWord ++ tailWord_1550840) baseStart_1550840 baseEnd_1550840 := by
    simpa [prefixWord, tailWord_1550840, baseEnd_1550840] using wordTrace_append hprefix tailTrace_1550840
  have hstable : (prefixWord ++ tailWord_1550840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550840).length < 2 ^ (prefixWord ++ tailWord_1550840).sum := by decide
  have hdescent : baseEnd_1550840 < baseStart_1550840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550853 : List Nat := [1, 3, 1, 1, 2, 2, 2, 10]
def baseStart_1550853 : Nat := 118140960795 + 1550853 * 2 ^ 59
def prefixEnd_1550853 : Nat := 4983230072969 + 3 ^ 40 * 1550853 * 2
def baseEnd_1550853 : Nat := 58987630627209334385575

theorem tailTrace_1550853 : CollatzResearch.WordTrace tailWord_1550853 prefixEnd_1550853 58987630627209334385575 := by
  unfold tailWord_1550853
  simp only [CollatzResearch.WordTrace]
  refine ⟨56564255850531920450561213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37709503900354613633707475 56564255850531920450561213)
  ·
    refine ⟨21211595943949470168960455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56564255850531920450561213 21211595943949470168960455)
    ·
      refine ⟨31817393915924205253440683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21211595943949470168960455 31817393915924205253440683)
      ·
        refine ⟨47726090873886307880161025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31817393915924205253440683 47726090873886307880161025)
        ·
          refine ⟨35794568155414730910120769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47726090873886307880161025 35794568155414730910120769)
          ·
            refine ⟨26845926116561048182590577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35794568155414730910120769 26845926116561048182590577)
            ·
              refine ⟨20134444587420786136942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26845926116561048182590577 20134444587420786136942933)
              ·
                refine ⟨58987630627209334385575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20134444587420786136942933 58987630627209334385575)
                ·
                  rfl

theorem cell22_1550853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 10].length) (baseStart_1550853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550853 prefixEnd_1550853 := by exact prefixLift 1550853
  have htrace : WordTrace (prefixWord ++ tailWord_1550853) baseStart_1550853 baseEnd_1550853 := by
    simpa [prefixWord, tailWord_1550853, baseEnd_1550853] using wordTrace_append hprefix tailTrace_1550853
  have hstable : (prefixWord ++ tailWord_1550853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550853).length < 2 ^ (prefixWord ++ tailWord_1550853).sum := by decide
  have hdescent : baseEnd_1550853 < baseStart_1550853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550861 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1550861 : Nat := 118140960795 + 1550861 * 2 ^ 59
def prefixEnd_1550861 : Nat := 4983230072969 + 3 ^ 40 * 1550861 * 2
def baseEnd_1550861 : Nat := 530891414208374655270151

theorem tailTrace_1550861 : CollatzResearch.WordTrace tailWord_1550861 prefixEnd_1550861 530891414208374655270151 := by
  unfold tailWord_1550861
  simp only [CollatzResearch.WordTrace]
  refine ⟨56564547634502937816852437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37709698423001958544568291 56564547634502937816852437)
  ·
    refine ⟨1325731585183662605082479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56564547634502937816852437 1325731585183662605082479)
    ·
      refine ⟨1988597377775493907623719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325731585183662605082479 1988597377775493907623719)
      ·
        refine ⟨2982896066663240861435579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988597377775493907623719 2982896066663240861435579)
        ·
          refine ⟨4474344099994861292153369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2982896066663240861435579 4474344099994861292153369)
          ·
            refine ⟨3355758074996145969115027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4474344099994861292153369 3355758074996145969115027)
            ·
              refine ⟨5033637112494218953672541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3355758074996145969115027 5033637112494218953672541)
              ·
                refine ⟨1887613917185332107627203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5033637112494218953672541 1887613917185332107627203)
                ·
                  refine ⟨2831420875777998161440805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887613917185332107627203 2831420875777998161440805)
                  ·
                    refine ⟨530891414208374655270151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831420875777998161440805 530891414208374655270151)
                    ·
                      rfl

theorem cell22_1550861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1550861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550861 prefixEnd_1550861 := by exact prefixLift 1550861
  have htrace : WordTrace (prefixWord ++ tailWord_1550861) baseStart_1550861 baseEnd_1550861 := by
    simpa [prefixWord, tailWord_1550861, baseEnd_1550861] using wordTrace_append hprefix tailTrace_1550861
  have hstable : (prefixWord ++ tailWord_1550861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550861).length < 2 ^ (prefixWord ++ tailWord_1550861).sum := by decide
  have hdescent : baseEnd_1550861 < baseStart_1550861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1550942 : List Nat := [4, 4, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1550942 : Nat := 118140960795 + 1550942 * 2 ^ 59
def prefixEnd_1550942 : Nat := 4983230072969 + 3 ^ 40 * 1550942 * 2
def baseEnd_1550942 : Nat := 530919142163717443994903

theorem tailTrace_1550942 : CollatzResearch.WordTrace tailWord_1550942 prefixEnd_1550942 530919142163717443994903 := by
  unfold tailWord_1550942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070937743401186081318885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37711667964806325767034053 7070937743401186081318885)
  ·
    refine ⟨1325800826887722390247291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7070937743401186081318885 1325800826887722390247291)
    ·
      refine ⟨1988701240331583585370937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325800826887722390247291 1988701240331583585370937)
      ·
        refine ⟨1491525930248687689028203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1988701240331583585370937 1491525930248687689028203)
        ·
          refine ⟨2237288895373031533542305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491525930248687689028203 2237288895373031533542305)
          ·
            refine ⟨1677966671529773650156729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237288895373031533542305 1677966671529773650156729)
            ·
              refine ⟨1258475003647330237617547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677966671529773650156729 1258475003647330237617547)
              ·
                refine ⟨1887712505470995356426321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258475003647330237617547 1887712505470995356426321)
                ·
                  refine ⟨1415784379103246517319741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1887712505470995356426321 1415784379103246517319741)
                  ·
                    refine ⟨530919142163717443994903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415784379103246517319741 530919142163717443994903)
                    ·
                      rfl

theorem cell22_1550942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1550942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1550942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1550942 prefixEnd_1550942 := by exact prefixLift 1550942
  have htrace : WordTrace (prefixWord ++ tailWord_1550942) baseStart_1550942 baseEnd_1550942 := by
    simpa [prefixWord, tailWord_1550942, baseEnd_1550942] using wordTrace_append hprefix tailTrace_1550942
  have hstable : (prefixWord ++ tailWord_1550942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1550942).length < 2 ^ (prefixWord ++ tailWord_1550942).sum := by decide
  have hdescent : baseEnd_1550942 < baseStart_1550942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1550942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551009 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_1551009 : Nat := 118140960795 + 1551009 * 2 ^ 59
def prefixEnd_1551009 : Nat := 4983230072969 + 3 ^ 40 * 1551009 * 2
def baseEnd_1551009 : Nat := 530942077632951602569697

theorem tailTrace_1551009 : CollatzResearch.WordTrace tailWord_1551009 prefixEnd_1551009 530942077632951602569697 := by
  unfold tailWord_1551009
  simp only [CollatzResearch.WordTrace]
  refine ⟨56569945637966759093240081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37713297091977839395493387 56569945637966759093240081)
  ·
    refine ⟨42427459228475069319930061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56569945637966759093240081 42427459228475069319930061)
    ·
      refine ⟨15910297210678150994973773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42427459228475069319930061 15910297210678150994973773)
      ·
        refine ⟨5966361454004306623115165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15910297210678150994973773 5966361454004306623115165)
        ·
          refine ⟨2237385545251614983668187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5966361454004306623115165 2237385545251614983668187)
          ·
            refine ⟨3356078317877422475502281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2237385545251614983668187 3356078317877422475502281)
            ·
              refine ⟨2517058738408066856626711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3356078317877422475502281 2517058738408066856626711)
              ·
                refine ⟨3775588107612100284940067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517058738408066856626711 3775588107612100284940067)
                ·
                  refine ⟨5663382161418150427410101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775588107612100284940067 5663382161418150427410101)
                  ·
                    refine ⟨530942077632951602569697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5663382161418150427410101 530942077632951602569697)
                    ·
                      rfl

theorem cell22_1551009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_1551009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551009 prefixEnd_1551009 := by exact prefixLift 1551009
  have htrace : WordTrace (prefixWord ++ tailWord_1551009) baseStart_1551009 baseEnd_1551009 := by
    simpa [prefixWord, tailWord_1551009, baseEnd_1551009] using wordTrace_append hprefix tailTrace_1551009
  have hstable : (prefixWord ++ tailWord_1551009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551009).length < 2 ^ (prefixWord ++ tailWord_1551009).sum := by decide
  have hdescent : baseEnd_1551009 < baseStart_1551009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551030 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1551030 : Nat := 118140960795 + 1551030 * 2 ^ 59
def prefixEnd_1551030 : Nat := 4983230072969 + 3 ^ 40 * 1551030 * 2
def baseEnd_1551030 : Nat := 530949266362114547794633

theorem tailTrace_1551030 : CollatzResearch.WordTrace tailWord_1551030 prefixEnd_1551030 530949266362114547794633 := by
  unfold tailWord_1551030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535669473180667479984659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37713807713927119786503029 3535669473180667479984659)
  ·
    refine ⟨5303504209771001219976989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535669473180667479984659 5303504209771001219976989)
    ·
      refine ⟨1988814078664125457491371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5303504209771001219976989 1988814078664125457491371)
      ·
        refine ⟨2983221117996188186237057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988814078664125457491371 2983221117996188186237057)
        ·
          refine ⟨2237415838497141139677793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2983221117996188186237057 2237415838497141139677793)
          ·
            refine ⟨1678061878872855854758345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237415838497141139677793 1678061878872855854758345)
            ·
              refine ⟨1258546409154641891068759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1678061878872855854758345 1258546409154641891068759)
              ·
                refine ⟨1887819613731962836603139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258546409154641891068759 1887819613731962836603139)
                ·
                  refine ⟨2831729420597944254904709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1887819613731962836603139 2831729420597944254904709)
                  ·
                    refine ⟨530949266362114547794633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2831729420597944254904709 530949266362114547794633)
                    ·
                      rfl

theorem cell22_1551030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1551030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551030 prefixEnd_1551030 := by exact prefixLift 1551030
  have htrace : WordTrace (prefixWord ++ tailWord_1551030) baseStart_1551030 baseEnd_1551030 := by
    simpa [prefixWord, tailWord_1551030, baseEnd_1551030] using wordTrace_append hprefix tailTrace_1551030
  have hstable : (prefixWord ++ tailWord_1551030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551030).length < 2 ^ (prefixWord ++ tailWord_1551030).sum := by decide
  have hdescent : baseEnd_1551030 < baseStart_1551030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551054 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1551054 : Nat := 118140960795 + 1551054 * 2 ^ 59
def prefixEnd_1551054 : Nat := 4983230072969 + 3 ^ 40 * 1551054 * 2
def baseEnd_1551054 : Nat := 530957482052586485194559

theorem tailTrace_1551054 : CollatzResearch.WordTrace tailWord_1551054 prefixEnd_1551054 530957482052586485194559 := by
  unfold tailWord_1551054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7071448365350466472328527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37714391281869154519085477 7071448365350466472328527)
  ·
    refine ⟨10607172548025699708492791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7071448365350466472328527 10607172548025699708492791)
    ·
      refine ⟨15910758822038549562739187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10607172548025699708492791 15910758822038549562739187)
      ·
        refine ⟨23866138233057824344108781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15910758822038549562739187 23866138233057824344108781)
        ·
          refine ⟨8949801837396684129040793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23866138233057824344108781 8949801837396684129040793)
          ·
            refine ⟨6712351378047513096780595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8949801837396684129040793 6712351378047513096780595)
            ·
              refine ⟨10068527067071269645170893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6712351378047513096780595 10068527067071269645170893)
              ·
                refine ⟨3775697650151726116939085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10068527067071269645170893 3775697650151726116939085)
                ·
                  refine ⟨1415886618806897293852157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3775697650151726116939085 1415886618806897293852157)
                  ·
                    refine ⟨530957482052586485194559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1415886618806897293852157 530957482052586485194559)
                    ·
                      rfl

theorem cell22_1551054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1551054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551054 prefixEnd_1551054 := by exact prefixLift 1551054
  have htrace : WordTrace (prefixWord ++ tailWord_1551054) baseStart_1551054 baseEnd_1551054 := by
    simpa [prefixWord, tailWord_1551054, baseEnd_1551054] using wordTrace_append hprefix tailTrace_1551054
  have hstable : (prefixWord ++ tailWord_1551054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551054).length < 2 ^ (prefixWord ++ tailWord_1551054).sum := by decide
  have hdescent : baseEnd_1551054 < baseStart_1551054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551144 : List Nat := [2, 1, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1551144 : Nat := 118140960795 + 1551144 * 2 ^ 59
def prefixEnd_1551144 : Nat := 4983230072969 + 3 ^ 40 * 1551144 * 2
def baseEnd_1551144 : Nat := 530988290891856250444283

theorem tailTrace_1551144 : CollatzResearch.WordTrace tailWord_1551144 prefixEnd_1551144 530988290891856250444283 := by
  unfold tailWord_1551144
  simp only [CollatzResearch.WordTrace]
  refine ⟨28287434746238838574702243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37716579661651784766269657 28287434746238838574702243)
  ·
    refine ⟨42431152119358257862053365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28287434746238838574702243 42431152119358257862053365)
    ·
      refine ⟨3977920511189836674567503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42431152119358257862053365 3977920511189836674567503)
      ·
        refine ⟨5966880766784755011851255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3977920511189836674567503 5966880766784755011851255)
        ·
          refine ⟨8950321150177132517776883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5966880766784755011851255 8950321150177132517776883)
          ·
            refine ⟨13425481725265698776665325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8950321150177132517776883 13425481725265698776665325)
            ·
              refine ⟨5034555646974637041249497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13425481725265698776665325 5034555646974637041249497)
              ·
                refine ⟨3775916735230977780937123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5034555646974637041249497 3775916735230977780937123)
                ·
                  refine ⟨5663875102846466671405685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3775916735230977780937123 5663875102846466671405685)
                  ·
                    refine ⟨530988290891856250444283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5663875102846466671405685 530988290891856250444283)
                    ·
                      rfl

theorem cell22_1551144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1551144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551144 prefixEnd_1551144 := by exact prefixLift 1551144
  have htrace : WordTrace (prefixWord ++ tailWord_1551144) baseStart_1551144 baseEnd_1551144 := by
    simpa [prefixWord, tailWord_1551144, baseEnd_1551144] using wordTrace_append hprefix tailTrace_1551144
  have hstable : (prefixWord ++ tailWord_1551144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551144).length < 2 ^ (prefixWord ++ tailWord_1551144).sum := by decide
  have hdescent : baseEnd_1551144 < baseStart_1551144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551157 : List Nat := [1, 3, 3, 1, 3, 11]
def baseStart_1551157 : Nat := 118140960795 + 1551157 * 2 ^ 59
def prefixEnd_1551157 : Nat := 4983230072969 + 3 ^ 40 * 1551157 * 2
def baseEnd_1551157 : Nat := 6555465938981833949003

theorem tailTrace_1551157 : CollatzResearch.WordTrace tailWord_1551157 prefixEnd_1551157 6555465938981833949003 := by
  unfold tailWord_1551157
  simp only [CollatzResearch.WordTrace]
  refine ⟨56575343641430580369627725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37716895760953720246418483 56575343641430580369627725)
  ·
    refine ⟨21215753865536467638610397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56575343641430580369627725 21215753865536467638610397)
    ·
      refine ⟨7955907699576175364478899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21215753865536467638610397 7955907699576175364478899)
      ·
        refine ⟨11933861549364263046718349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7955907699576175364478899 11933861549364263046718349)
        ·
          refine ⟨4475198081011598642519381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11933861549364263046718349 4475198081011598642519381)
          ·
            refine ⟨6555465938981833949003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4475198081011598642519381 6555465938981833949003)
            ·
              rfl

theorem cell22_1551157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 11].length) (baseStart_1551157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551157 prefixEnd_1551157 := by exact prefixLift 1551157
  have htrace : WordTrace (prefixWord ++ tailWord_1551157) baseStart_1551157 baseEnd_1551157 := by
    simpa [prefixWord, tailWord_1551157, baseEnd_1551157] using wordTrace_append hprefix tailTrace_1551157
  have hstable : (prefixWord ++ tailWord_1551157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551157).length < 2 ^ (prefixWord ++ tailWord_1551157).sum := by decide
  have hdescent : baseEnd_1551157 < baseStart_1551157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551219 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 5]
def baseStart_1551219 : Nat := 118140960795 + 1551219 * 2 ^ 59
def prefixEnd_1551219 : Nat := 4983230072969 + 3 ^ 40 * 1551219 * 2
def baseEnd_1551219 : Nat := 177004654974860351606351

theorem tailTrace_1551219 : CollatzResearch.WordTrace tailWord_1551219 prefixEnd_1551219 177004654974860351606351 := by
  unfold tailWord_1551219
  simp only [CollatzResearch.WordTrace]
  refine ⟨56577604967205964958384711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37718403311470643305589807 56577604967205964958384711)
  ·
    refine ⟨84866407450808947437577067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56577604967205964958384711 84866407450808947437577067)
    ·
      refine ⟨127299611176213421156365601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84866407450808947437577067 127299611176213421156365601)
      ·
        refine ⟨95474708382160065867274201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127299611176213421156365601 95474708382160065867274201)
        ·
          refine ⟨71606031286620049400455651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95474708382160065867274201 71606031286620049400455651)
          ·
            refine ⟨107409046929930074100683477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71606031286620049400455651 107409046929930074100683477)
            ·
              refine ⟨2517399537420236111734769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 107409046929930074100683477 2517399537420236111734769)
              ·
                refine ⟨1888049653065177083801077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2517399537420236111734769 1888049653065177083801077)
                ·
                  refine ⟨177004654974860351606351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888049653065177083801077 177004654974860351606351)
                  ·
                    rfl

theorem cell22_1551219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 5].length) (baseStart_1551219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551219 prefixEnd_1551219 := by exact prefixLift 1551219
  have htrace : WordTrace (prefixWord ++ tailWord_1551219) baseStart_1551219 baseEnd_1551219 := by
    simpa [prefixWord, tailWord_1551219, baseEnd_1551219] using wordTrace_append hprefix tailTrace_1551219
  have hstable : (prefixWord ++ tailWord_1551219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551219).length < 2 ^ (prefixWord ++ tailWord_1551219).sum := by decide
  have hdescent : baseEnd_1551219 < baseStart_1551219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551232 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_1551232 : Nat := 118140960795 + 1551232 * 2 ^ 59
def prefixEnd_1551232 : Nat := 4983230072969 + 3 ^ 40 * 1551232 * 2
def baseEnd_1551232 : Nat := 531018415090253354244013

theorem tailTrace_1551232 : CollatzResearch.WordTrace tailWord_1551232 prefixEnd_1551232 531018415090253354244013 := by
  unfold tailWord_1551232
  simp only [CollatzResearch.WordTrace]
  refine ⟨28289039558079434089303975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37718719410772578785738633 28289039558079434089303975)
  ·
    refine ⟨42433559337119151133955963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28289039558079434089303975 42433559337119151133955963)
    ·
      refine ⟨63650339005678726700933945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42433559337119151133955963 63650339005678726700933945)
      ·
        refine ⟨47737754254259045025700459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63650339005678726700933945 47737754254259045025700459)
        ·
          refine ⟨71606631381388567538550689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47737754254259045025700459 71606631381388567538550689)
          ·
            refine ⟨53704973536041425653913017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71606631381388567538550689 53704973536041425653913017)
            ·
              refine ⟨40278730152031069240434763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53704973536041425653913017 40278730152031069240434763)
              ·
                refine ⟨60418095228046603860652145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40278730152031069240434763 60418095228046603860652145)
                ·
                  refine ⟨45313571421034952895489109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60418095228046603860652145 45313571421034952895489109)
                  ·
                    refine ⟨531018415090253354244013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45313571421034952895489109 531018415090253354244013)
                    ·
                      rfl

theorem cell22_1551232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_1551232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551232 prefixEnd_1551232 := by exact prefixLift 1551232
  have htrace : WordTrace (prefixWord ++ tailWord_1551232) baseStart_1551232 baseEnd_1551232 := by
    simpa [prefixWord, tailWord_1551232, baseEnd_1551232] using wordTrace_append hprefix tailTrace_1551232
  have hstable : (prefixWord ++ tailWord_1551232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551232).length < 2 ^ (prefixWord ++ tailWord_1551232).sum := by decide
  have hdescent : baseEnd_1551232 < baseStart_1551232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551311 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 2, 4]
def baseStart_1551311 : Nat := 118140960795 + 1551311 * 2 ^ 59
def prefixEnd_1551311 : Nat := 4983230072969 + 3 ^ 40 * 1551311 * 2
def baseEnd_1551311 : Nat := 531045458404723481518771

theorem tailTrace_1551311 : CollatzResearch.WordTrace tailWord_1551311 prefixEnd_1551311 531045458404723481518771 := by
  unfold tailWord_1551311
  simp only [CollatzResearch.WordTrace]
  refine ⟨56580960482872664670733787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37720640321915109780489191 56580960482872664670733787)
  ·
    refine ⟨84871440724308997006100681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56580960482872664670733787 84871440724308997006100681)
    ·
      refine ⟨63653580543231747754575511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84871440724308997006100681 63653580543231747754575511)
      ·
        refine ⟨95480370814847621631863267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63653580543231747754575511 95480370814847621631863267)
        ·
          refine ⟨143220556222271432447794901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95480370814847621631863267 143220556222271432447794901)
          ·
            refine ⟨3356731786459486697995193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143220556222271432447794901 3356731786459486697995193)
            ·
              refine ⟨2517548839844615023496395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3356731786459486697995193 2517548839844615023496395)
              ·
                refine ⟨3776323259766922535244593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517548839844615023496395 3776323259766922535244593)
                ·
                  refine ⟨2832242444825191901433445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776323259766922535244593 2832242444825191901433445)
                  ·
                    refine ⟨531045458404723481518771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832242444825191901433445 531045458404723481518771)
                    ·
                      rfl

theorem cell22_1551311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_1551311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551311 prefixEnd_1551311 := by exact prefixLift 1551311
  have htrace : WordTrace (prefixWord ++ tailWord_1551311) baseStart_1551311 baseEnd_1551311 := by
    simpa [prefixWord, tailWord_1551311, baseEnd_1551311] using wordTrace_append hprefix tailTrace_1551311
  have hstable : (prefixWord ++ tailWord_1551311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551311).length < 2 ^ (prefixWord ++ tailWord_1551311).sum := by decide
  have hdescent : baseEnd_1551311 < baseStart_1551311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551330 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1551330 : Nat := 118140960795 + 1551330 * 2 ^ 59
def prefixEnd_1551330 : Nat := 4983230072969 + 3 ^ 40 * 1551330 * 2
def baseEnd_1551330 : Nat := 531051962493013765293713

theorem tailTrace_1551330 : CollatzResearch.WordTrace tailWord_1551330 prefixEnd_1551330 531051962493013765293713 := by
  unfold tailWord_1551330
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145413367450957728918861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37721102313202553943783629 14145413367450957728918861)
  ·
    refine ⟨5304530012794109148344573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14145413367450957728918861 5304530012794109148344573)
    ·
      refine ⟨1989198754797790930629215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5304530012794109148344573 1989198754797790930629215)
      ·
        refine ⟨2983798132196686395943823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989198754797790930629215 2983798132196686395943823)
        ·
          refine ⟨4475697198295029593915735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983798132196686395943823 4475697198295029593915735)
          ·
            refine ⟨6713545797442544390873603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475697198295029593915735 6713545797442544390873603)
            ·
              refine ⟨10070318696163816586310405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713545797442544390873603 10070318696163816586310405)
              ·
                refine ⟨1888184755530715609933201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10070318696163816586310405 1888184755530715609933201)
                ·
                  refine ⟨1416138566648036707449901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1888184755530715609933201 1416138566648036707449901)
                  ·
                    refine ⟨531051962493013765293713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416138566648036707449901 531051962493013765293713)
                    ·
                      rfl

theorem cell22_1551330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1551330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551330 prefixEnd_1551330 := by exact prefixLift 1551330
  have htrace : WordTrace (prefixWord ++ tailWord_1551330) baseStart_1551330 baseEnd_1551330 := by
    simpa [prefixWord, tailWord_1551330, baseEnd_1551330] using wordTrace_append hprefix tailTrace_1551330
  have hstable : (prefixWord ++ tailWord_1551330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551330).length < 2 ^ (prefixWord ++ tailWord_1551330).sum := by decide
  have hdescent : baseEnd_1551330 < baseStart_1551330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551362 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1551362 : Nat := 118140960795 + 1551362 * 2 ^ 59
def prefixEnd_1551362 : Nat := 4983230072969 + 3 ^ 40 * 1551362 * 2
def baseEnd_1551362 : Nat := 531062916746976348493615

theorem tailTrace_1551362 : CollatzResearch.WordTrace tailWord_1551362 prefixEnd_1551362 531062916746976348493615 := by
  unfold tailWord_1551362
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145705151421975095210085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37721880403791933587226893 14145705151421975095210085)
  ·
    refine ⟨2652319715891620330351891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14145705151421975095210085 2652319715891620330351891)
    ·
      refine ⟨3978479573837430495527837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652319715891620330351891 3978479573837430495527837)
      ·
        refine ⟨1491929840189036435822939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3978479573837430495527837 1491929840189036435822939)
        ·
          refine ⟨2237894760283554653734409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1491929840189036435822939 2237894760283554653734409)
          ·
            refine ⟨1678421070212665990300807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2237894760283554653734409 1678421070212665990300807)
            ·
              refine ⟨2517631605318998985451211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678421070212665990300807 2517631605318998985451211)
              ·
                refine ⟨3776447407978498478176817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517631605318998985451211 3776447407978498478176817)
                ·
                  refine ⟨2832335555983873858632613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3776447407978498478176817 2832335555983873858632613)
                  ·
                    refine ⟨531062916746976348493615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832335555983873858632613 531062916746976348493615)
                    ·
                      rfl

theorem cell22_1551362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1551362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551362 prefixEnd_1551362 := by exact prefixLift 1551362
  have htrace : WordTrace (prefixWord ++ tailWord_1551362) baseStart_1551362 baseEnd_1551362 := by
    simpa [prefixWord, tailWord_1551362, baseEnd_1551362] using wordTrace_append hprefix tailTrace_1551362
  have hstable : (prefixWord ++ tailWord_1551362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551362).length < 2 ^ (prefixWord ++ tailWord_1551362).sum := by decide
  have hdescent : baseEnd_1551362 < baseStart_1551362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551416 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_1551416 : Nat := 118140960795 + 1551416 * 2 ^ 59
def prefixEnd_1551416 : Nat := 4983230072969 + 3 ^ 40 * 1551416 * 2
def baseEnd_1551416 : Nat := 177027134016846069214483

theorem tailTrace_1551416 : CollatzResearch.WordTrace tailWord_1551416 prefixEnd_1551416 177027134016846069214483 := by
  unfold tailWord_1551416
  simp only [CollatzResearch.WordTrace]
  refine ⟨28292395073746133801653051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37723193431661511735537401 28292395073746133801653051)
  ·
    refine ⟨42438592610619200702479577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28292395073746133801653051 42438592610619200702479577)
    ·
      refine ⟨31828944457964400526859683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42438592610619200702479577 31828944457964400526859683)
      ·
        refine ⟨47743416686946600790289525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31828944457964400526859683 47743416686946600790289525)
        ·
          refine ⟨4475945314401243824089643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47743416686946600790289525 4475945314401243824089643)
          ·
            refine ⟨6713917971601865736134465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4475945314401243824089643 6713917971601865736134465)
            ·
              refine ⟨5035438478701399302100849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713917971601865736134465 5035438478701399302100849)
              ·
                refine ⟨3776578859026049476575637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035438478701399302100849 3776578859026049476575637)
                ·
                  refine ⟨177027134016846069214483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3776578859026049476575637 177027134016846069214483)
                  ·
                    rfl

theorem cell22_1551416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_1551416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551416 prefixEnd_1551416 := by exact prefixLift 1551416
  have htrace : WordTrace (prefixWord ++ tailWord_1551416) baseStart_1551416 baseEnd_1551416 := by
    simpa [prefixWord, tailWord_1551416, baseEnd_1551416] using wordTrace_append hprefix tailTrace_1551416
  have hstable : (prefixWord ++ tailWord_1551416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551416).length < 2 ^ (prefixWord ++ tailWord_1551416).sum := by decide
  have hdescent : baseEnd_1551416 < baseStart_1551416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551448 : List Nat := [2, 1, 2, 2, 1, 3, 2, 4, 2, 3]
def baseStart_1551448 : Nat := 118140960795 + 1551448 * 2 ^ 59
def prefixEnd_1551448 : Nat := 4983230072969 + 3 ^ 40 * 1551448 * 2
def baseEnd_1551448 : Nat := 531092356304500790843351

theorem tailTrace_1551448 : CollatzResearch.WordTrace tailWord_1551448 prefixEnd_1551448 531092356304500790843351 := by
  unfold tailWord_1551448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28292978641688168534235499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37723971522250891378980665 28292978641688168534235499)
  ·
    refine ⟨42439467962532252801353249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28292978641688168534235499 42439467962532252801353249)
    ·
      refine ⟨31829600971899189601014937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42439467962532252801353249 31829600971899189601014937)
      ·
        refine ⟨23872200728924392200761203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31829600971899189601014937 23872200728924392200761203)
        ·
          refine ⟨35808301093386588301141805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23872200728924392200761203 35808301093386588301141805)
          ·
            refine ⟨13428112910019970612928177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35808301093386588301141805 13428112910019970612928177)
            ·
              refine ⟨10071084682514977959696133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13428112910019970612928177 10071084682514977959696133)
              ·
                refine ⟨1888328377971558367443025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10071084682514977959696133 1888328377971558367443025)
                ·
                  refine ⟨1416246283478668775582269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1888328377971558367443025 1416246283478668775582269)
                  ·
                    refine ⟨531092356304500790843351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416246283478668775582269 531092356304500790843351)
                    ·
                      rfl

theorem cell22_1551448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_1551448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551448 prefixEnd_1551448 := by exact prefixLift 1551448
  have htrace : WordTrace (prefixWord ++ tailWord_1551448) baseStart_1551448 baseEnd_1551448 := by
    simpa [prefixWord, tailWord_1551448, baseEnd_1551448] using wordTrace_append hprefix tailTrace_1551448
  have hstable : (prefixWord ++ tailWord_1551448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551448).length < 2 ^ (prefixWord ++ tailWord_1551448).sum := by decide
  have hdescent : baseEnd_1551448 < baseStart_1551448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551461 : List Nat := [1, 3, 1, 3, 2, 1, 4, 7]
def baseStart_1551461 : Nat := 118140960795 + 1551461 * 2 ^ 59
def prefixEnd_1551461 : Nat := 4983230072969 + 3 ^ 40 * 1551461 * 2
def baseEnd_1551461 : Nat := 59010756274463676696479

theorem tailTrace_1551461 : CollatzResearch.WordTrace tailWord_1551461 prefixEnd_1551461 59010756274463676696479 := by
  unfold tailWord_1551461
  simp only [CollatzResearch.WordTrace]
  refine ⟨56586431432329240288694237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37724287621552826859129491 56586431432329240288694237)
  ·
    refine ⟨21219911787123465108260339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56586431432329240288694237 21219911787123465108260339)
    ·
      refine ⟨31829867680685197662390509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21219911787123465108260339 31829867680685197662390509)
      ·
        refine ⟨11936200380256949123396441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31829867680685197662390509 11936200380256949123396441)
        ·
          refine ⟨8952150285192711842547331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11936200380256949123396441 8952150285192711842547331)
          ·
            refine ⟨13428225427789067763820997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952150285192711842547331 13428225427789067763820997)
            ·
              refine ⟨2517792267710450205716437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13428225427789067763820997 2517792267710450205716437)
              ·
                refine ⟨59010756274463676696479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2517792267710450205716437 59010756274463676696479)
                ·
                  rfl

theorem cell22_1551461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 7].length) (baseStart_1551461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551461 prefixEnd_1551461 := by exact prefixLift 1551461
  have htrace : WordTrace (prefixWord ++ tailWord_1551461) baseStart_1551461 baseEnd_1551461 := by
    simpa [prefixWord, tailWord_1551461, baseEnd_1551461] using wordTrace_append hprefix tailTrace_1551461
  have hstable : (prefixWord ++ tailWord_1551461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551461).length < 2 ^ (prefixWord ++ tailWord_1551461).sum := by decide
  have hdescent : baseEnd_1551461 < baseStart_1551461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551465 : List Nat := [1, 2, 1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_1551465 : Nat := 118140960795 + 1551465 * 2 ^ 59
def prefixEnd_1551465 : Nat := 4983230072969 + 3 ^ 40 * 1551465 * 2
def baseEnd_1551465 : Nat := 531098175751918413168299

theorem tailTrace_1551465 : CollatzResearch.WordTrace tailWord_1551465 prefixEnd_1551465 531098175751918413168299 := by
  unfold tailWord_1551465
  simp only [CollatzResearch.WordTrace]
  refine ⟨56586577324314748971839849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37724384882876499314559899 56586577324314748971839849)
  ·
    refine ⟨42439932993236061728879887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56586577324314748971839849 42439932993236061728879887)
    ·
      refine ⟨63659899489854092593319831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42439932993236061728879887 63659899489854092593319831)
      ·
        refine ⟨95489849234781138889979747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63659899489854092593319831 95489849234781138889979747)
        ·
          refine ⟨143234773852171708334969621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95489849234781138889979747 143234773852171708334969621)
          ·
            refine ⟨6714130024320548828201701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143234773852171708334969621 6714130024320548828201701)
            ·
              refine ⟨1258899379560102905287819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6714130024320548828201701 1258899379560102905287819)
              ·
                refine ⟨1888349069340154357931729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258899379560102905287819 1888349069340154357931729)
                ·
                  refine ⟨1416261802005115768448797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1888349069340154357931729 1416261802005115768448797)
                  ·
                    refine ⟨531098175751918413168299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416261802005115768448797 531098175751918413168299)
                    ·
                      rfl

theorem cell22_1551465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_1551465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551465 prefixEnd_1551465 := by exact prefixLift 1551465
  have htrace : WordTrace (prefixWord ++ tailWord_1551465) baseStart_1551465 baseEnd_1551465 := by
    simpa [prefixWord, tailWord_1551465, baseEnd_1551465] using wordTrace_append hprefix tailTrace_1551465
  have hstable : (prefixWord ++ tailWord_1551465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551465).length < 2 ^ (prefixWord ++ tailWord_1551465).sum := by decide
  have hdescent : baseEnd_1551465 < baseStart_1551465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551486 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1551486 : Nat := 118140960795 + 1551486 * 2 ^ 59
def prefixEnd_1551486 : Nat := 4983230072969 + 3 ^ 40 * 1551486 * 2
def baseEnd_1551486 : Nat := 531105364481081358393235

theorem tailTrace_1551486 : CollatzResearch.WordTrace tailWord_1551486 prefixEnd_1551486 531105364481081358393235 := by
  unfold tailWord_1551486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073417907154833694794289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37724895504825779705569541 7073417907154833694794289)
  ·
    refine ⟨5305063430366125271095717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7073417907154833694794289 5305063430366125271095717)
    ·
      refine ⟨994699393193648488330447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5305063430366125271095717 994699393193648488330447)
      ·
        refine ⟨1492049089790472732495671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994699393193648488330447 1492049089790472732495671)
        ·
          refine ⟨2238073634685709098743507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492049089790472732495671 2238073634685709098743507)
          ·
            refine ⟨3357110452028563648115261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238073634685709098743507 3357110452028563648115261)
            ·
              refine ⟨1258916419510711368043223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3357110452028563648115261 1258916419510711368043223)
              ·
                refine ⟨1888374629266067052064835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258916419510711368043223 1888374629266067052064835)
                ·
                  refine ⟨2832561943899100578097253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1888374629266067052064835 2832561943899100578097253)
                  ·
                    refine ⟨531105364481081358393235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2832561943899100578097253 531105364481081358393235)
                    ·
                      rfl

theorem cell22_1551486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1551486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551486 prefixEnd_1551486 := by exact prefixLift 1551486
  have htrace : WordTrace (prefixWord ++ tailWord_1551486) baseStart_1551486 baseEnd_1551486 := by
    simpa [prefixWord, tailWord_1551486, baseEnd_1551486] using wordTrace_append hprefix tailTrace_1551486
  have hstable : (prefixWord ++ tailWord_1551486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551486).length < 2 ^ (prefixWord ++ tailWord_1551486).sum := by decide
  have hdescent : baseEnd_1551486 < baseStart_1551486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551574 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 5]
def baseStart_1551574 : Nat := 118140960795 + 1551574 * 2 ^ 59
def prefixEnd_1551574 : Nat := 4983230072969 + 3 ^ 40 * 1551574 * 2
def baseEnd_1551574 : Nat := 177045162893159487397655

theorem tailTrace_1551574 : CollatzResearch.WordTrace tailWord_1551574 prefixEnd_1551574 177045162893159487397655 := by
  unfold tailWord_1551574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536909555057491286722361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37727035253946573725038517 3536909555057491286722361)
  ·
    refine ⟨2652682166293118465041771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3536909555057491286722361 2652682166293118465041771)
    ·
      refine ⟨3979023249439677697562657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2652682166293118465041771 3979023249439677697562657)
      ·
        refine ⟨2984267437079758273171993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979023249439677697562657 2984267437079758273171993)
        ·
          refine ⟨2238200577809818704878995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984267437079758273171993 2238200577809818704878995)
          ·
            refine ⟨3357300866714728057318493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238200577809818704878995 3357300866714728057318493)
            ·
              refine ⟨1258987825018023021494435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3357300866714728057318493 1258987825018023021494435)
              ·
                refine ⟨1888481737527034532241653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258987825018023021494435 1888481737527034532241653)
                ·
                  refine ⟨177045162893159487397655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888481737527034532241653 177045162893159487397655)
                  ·
                    rfl

theorem cell22_1551574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_1551574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551574 prefixEnd_1551574 := by exact prefixLift 1551574
  have htrace : WordTrace (prefixWord ++ tailWord_1551574) baseStart_1551574 baseEnd_1551574 := by
    simpa [prefixWord, tailWord_1551574, baseEnd_1551574] using wordTrace_append hprefix tailTrace_1551574
  have hstable : (prefixWord ++ tailWord_1551574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551574).length < 2 ^ (prefixWord ++ tailWord_1551574).sum := by decide
  have hdescent : baseEnd_1551574 < baseStart_1551574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551583 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 1, 5]
def baseStart_1551583 : Nat := 118140960795 + 1551583 * 2 ^ 59
def prefixEnd_1551583 : Nat := 4983230072969 + 3 ^ 40 * 1551583 * 2
def baseEnd_1551583 : Nat := 531138569563405438717937

theorem tailTrace_1551583 : CollatzResearch.WordTrace tailWord_1551583 prefixEnd_1551583 531138569563405438717937 := by
  unfold tailWord_1551583
  simp only [CollatzResearch.WordTrace]
  refine ⟨56590881137887255124635403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37727254091924836749756935 56590881137887255124635403)
  ·
    refine ⟨84886321706830882686953105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56590881137887255124635403 84886321706830882686953105)
    ·
      refine ⟨63664741280123162015214829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84886321706830882686953105 63664741280123162015214829)
      ·
        refine ⟨23874277980046185755705561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63664741280123162015214829 23874277980046185755705561)
        ·
          refine ⟨17905708485034639316779171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23874277980046185755705561 17905708485034639316779171)
          ·
            refine ⟨26858562727551958975168757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17905708485034639316779171 26858562727551958975168757)
            ·
              refine ⟨2517990255707996153922071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26858562727551958975168757 2517990255707996153922071)
              ·
                refine ⟨3776985383561994230883107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2517990255707996153922071 3776985383561994230883107)
                ·
                  refine ⟨5665478075342991346324661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776985383561994230883107 5665478075342991346324661)
                  ·
                    refine ⟨531138569563405438717937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5665478075342991346324661 531138569563405438717937)
                    ·
                      rfl

theorem cell22_1551583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 5].length) (baseStart_1551583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551583 prefixEnd_1551583 := by exact prefixLift 1551583
  have htrace : WordTrace (prefixWord ++ tailWord_1551583) baseStart_1551583 baseEnd_1551583 := by
    simpa [prefixWord, tailWord_1551583, baseEnd_1551583] using wordTrace_append hprefix tailTrace_1551583
  have hstable : (prefixWord ++ tailWord_1551583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551583).length < 2 ^ (prefixWord ++ tailWord_1551583).sum := by decide
  have hdescent : baseEnd_1551583 < baseStart_1551583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551598 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1551598 : Nat := 118140960795 + 1551598 * 2 ^ 59
def prefixEnd_1551598 : Nat := 4983230072969 + 3 ^ 40 * 1551598 * 2
def baseEnd_1551598 : Nat := 531143704369950399592891

theorem tailTrace_1551598 : CollatzResearch.WordTrace tailWord_1551598 prefixEnd_1551598 531143704369950399592891 := by
  unfold tailWord_1551598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073928529104114085803931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37727618821888608457620965 7073928529104114085803931)
  ·
    refine ⟨10610892793656171128705897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7073928529104114085803931 10610892793656171128705897)
    ·
      refine ⟨7958169595242128346529423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10610892793656171128705897 7958169595242128346529423)
      ·
        refine ⟨11937254392863192519794135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7958169595242128346529423 11937254392863192519794135)
        ·
          refine ⟨17905881589294788779691203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11937254392863192519794135 17905881589294788779691203)
          ·
            refine ⟨26858822383942183169536805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17905881589294788779691203 26858822383942183169536805)
            ·
              refine ⟨5036029196989159344288151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26858822383942183169536805 5036029196989159344288151)
              ·
                refine ⟨7554043795483739016432227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036029196989159344288151 7554043795483739016432227)
                ·
                  refine ⟨11331065693225608524648341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554043795483739016432227 11331065693225608524648341)
                  ·
                    refine ⟨531143704369950399592891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11331065693225608524648341 531143704369950399592891)
                    ·
                      rfl

theorem cell22_1551598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1551598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551598 prefixEnd_1551598 := by exact prefixLift 1551598
  have htrace : WordTrace (prefixWord ++ tailWord_1551598) baseStart_1551598 baseEnd_1551598 := by
    simpa [prefixWord, tailWord_1551598, baseEnd_1551598] using wordTrace_append hprefix tailTrace_1551598
  have hstable : (prefixWord ++ tailWord_1551598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551598).length < 2 ^ (prefixWord ++ tailWord_1551598).sum := by decide
  have hdescent : baseEnd_1551598 < baseStart_1551598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551679 : List Nat := [1, 1, 2, 2, 4, 2, 4, 2, 1, 3]
def baseStart_1551679 : Nat := 118140960795 + 1551679 * 2 ^ 59
def prefixEnd_1551679 : Nat := 4983230072969 + 3 ^ 40 * 1551679 * 2
def baseEnd_1551679 : Nat := 531171432325293188317643

theorem tailTrace_1551679 : CollatzResearch.WordTrace tailWord_1551679 prefixEnd_1551679 531171432325293188317643 := by
  unfold tailWord_1551679
  simp only [CollatzResearch.WordTrace]
  refine ⟨56594382545539463520130091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37729588363692975680086727 56594382545539463520130091)
  ·
    refine ⟨84891573818309195280195137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56594382545539463520130091 84891573818309195280195137)
    ·
      refine ⟨63668680363731896460146353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84891573818309195280195137 63668680363731896460146353)
      ·
        refine ⟨47751510272798922345109765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63668680363731896460146353 47751510272798922345109765)
        ·
          refine ⟨8953408176149797939708081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47751510272798922345109765 8953408176149797939708081)
          ·
            refine ⟨6715056132112348454781061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953408176149797939708081 6715056132112348454781061)
            ·
              refine ⟨1259073024771065335271449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6715056132112348454781061 1259073024771065335271449)
              ·
                refine ⟨944304768578299001453587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1259073024771065335271449 944304768578299001453587)
                ·
                  refine ⟨1416457152867448502180381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944304768578299001453587 1416457152867448502180381)
                  ·
                    refine ⟨531171432325293188317643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416457152867448502180381 531171432325293188317643)
                    ·
                      rfl

theorem cell22_1551679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2, 1, 3].length) (baseStart_1551679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551679 prefixEnd_1551679 := by exact prefixLift 1551679
  have htrace : WordTrace (prefixWord ++ tailWord_1551679) baseStart_1551679 baseEnd_1551679 := by
    simpa [prefixWord, tailWord_1551679, baseEnd_1551679] using wordTrace_append hprefix tailTrace_1551679
  have hstable : (prefixWord ++ tailWord_1551679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551679).length < 2 ^ (prefixWord ++ tailWord_1551679).sum := by decide
  have hdescent : baseEnd_1551679 < baseStart_1551679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551703 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 8]
def baseStart_1551703 : Nat := 118140960795 + 1551703 * 2 ^ 59
def prefixEnd_1551703 : Nat := 4983230072969 + 3 ^ 40 * 1551703 * 2
def baseEnd_1551703 : Nat := 177059882671921708572523

theorem tailTrace_1551703 : CollatzResearch.WordTrace tailWord_1551703 prefixEnd_1551703 177059882671921708572523 := by
  unfold tailWord_1551703
  simp only [CollatzResearch.WordTrace]
  refine ⟨56595257897452515619003763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37730171931635010412669175 56595257897452515619003763)
  ·
    refine ⟨84892886846178773428505645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56595257897452515619003763 84892886846178773428505645)
    ·
      refine ⟨31834832567317040035689617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84892886846178773428505645 31834832567317040035689617)
      ·
        refine ⟨23876124425487780026767213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31834832567317040035689617 23876124425487780026767213)
        ·
          refine ⟨8953546659557917510037705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23876124425487780026767213 8953546659557917510037705)
          ·
            refine ⟨6715159994668438132528279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953546659557917510037705 6715159994668438132528279)
            ·
              refine ⟨10072739992002657198792419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715159994668438132528279 10072739992002657198792419)
              ·
                refine ⟨15109109988003985798188629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10072739992002657198792419 15109109988003985798188629)
                ·
                  refine ⟨177059882671921708572523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15109109988003985798188629 177059882671921708572523)
                  ·
                    rfl

theorem cell22_1551703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 8].length) (baseStart_1551703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551703 prefixEnd_1551703 := by exact prefixLift 1551703
  have htrace : WordTrace (prefixWord ++ tailWord_1551703) baseStart_1551703 baseEnd_1551703 := by
    simpa [prefixWord, tailWord_1551703, baseEnd_1551703] using wordTrace_append hprefix tailTrace_1551703
  have hstable : (prefixWord ++ tailWord_1551703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551703).length < 2 ^ (prefixWord ++ tailWord_1551703).sum := by decide
  have hdescent : baseEnd_1551703 < baseStart_1551703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551726 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_1551726 : Nat := 118140960795 + 1551726 * 2 ^ 59
def prefixEnd_1551726 : Nat := 4983230072969 + 3 ^ 40 * 1551726 * 2
def baseEnd_1551726 : Nat := 177062507128600244130833

theorem tailTrace_1551726 : CollatzResearch.WordTrace tailWord_1551726 prefixEnd_1551726 177062507128600244130833 := by
  unfold tailWord_1551726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7074512097046148818386379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37730731184246127031394021 7074512097046148818386379)
  ·
    refine ⟨10611768145569223227579569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7074512097046148818386379 10611768145569223227579569)
    ·
      refine ⟨7958826109176917420684677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10611768145569223227579569 7958826109176917420684677)
      ·
        refine ⟨1492279895470672016378377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7958826109176917420684677 1492279895470672016378377)
        ·
          refine ⟨1119209921603004012283783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492279895470672016378377 1119209921603004012283783)
          ·
            refine ⟨1678814882404506018425675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119209921603004012283783 1678814882404506018425675)
            ·
              refine ⟨2518222323606759027638513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678814882404506018425675 2518222323606759027638513)
              ·
                refine ⟨1888666742705069270728885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518222323606759027638513 1888666742705069270728885)
                ·
                  refine ⟨177062507128600244130833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1888666742705069270728885 177062507128600244130833)
                  ·
                    rfl

theorem cell22_1551726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_1551726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551726 prefixEnd_1551726 := by exact prefixLift 1551726
  have htrace : WordTrace (prefixWord ++ tailWord_1551726) baseStart_1551726 baseEnd_1551726 := by
    simpa [prefixWord, tailWord_1551726, baseEnd_1551726] using wordTrace_append hprefix tailTrace_1551726
  have hstable : (prefixWord ++ tailWord_1551726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551726).length < 2 ^ (prefixWord ++ tailWord_1551726).sum := by decide
  have hdescent : baseEnd_1551726 < baseStart_1551726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551735 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 4, 3]
def baseStart_1551735 : Nat := 118140960795 + 1551735 * 2 ^ 59
def prefixEnd_1551735 : Nat := 4983230072969 + 3 ^ 40 * 1551735 * 2
def baseEnd_1551735 : Nat := 531190602269727708917471

theorem tailTrace_1551735 : CollatzResearch.WordTrace tailWord_1551735 prefixEnd_1551735 531190602269727708917471 := by
  unfold tailWord_1551735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56596425033336585084168659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37730950022224390056112439 56596425033336585084168659)
  ·
    refine ⟨84894637550004877626252989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56596425033336585084168659 84894637550004877626252989)
    ·
      refine ⟨31835489081251829109844871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84894637550004877626252989 31835489081251829109844871)
      ·
        refine ⟨47753233621877743664767307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31835489081251829109844871 47753233621877743664767307)
        ·
          refine ⟨71629850432816615497150961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47753233621877743664767307 71629850432816615497150961)
          ·
            refine ⟨53722387824612461622863221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71629850432816615497150961 53722387824612461622863221)
            ·
              refine ⟨5036473858557418277143427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53722387824612461622863221 5036473858557418277143427)
              ·
                refine ⟨7554710787836127415715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036473858557418277143427 7554710787836127415715141)
                ·
                  refine ⟨1416508272719273890446589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7554710787836127415715141 1416508272719273890446589)
                  ·
                    refine ⟨531190602269727708917471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416508272719273890446589 531190602269727708917471)
                    ·
                      rfl

theorem cell22_1551735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_1551735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551735 prefixEnd_1551735 := by exact prefixLift 1551735
  have htrace : WordTrace (prefixWord ++ tailWord_1551735) baseStart_1551735 baseEnd_1551735 := by
    simpa [prefixWord, tailWord_1551735, baseEnd_1551735] using wordTrace_append hprefix tailTrace_1551735
  have hstable : (prefixWord ++ tailWord_1551735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551735).length < 2 ^ (prefixWord ++ tailWord_1551735).sum := by decide
  have hdescent : baseEnd_1551735 < baseStart_1551735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551752 : List Nat := [2, 1, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1551752 : Nat := 118140960795 + 1551752 * 2 ^ 59
def prefixEnd_1551752 : Nat := 4983230072969 + 3 ^ 40 * 1551752 * 2
def baseEnd_1551752 : Nat := 531196421717145331242419

theorem tailTrace_1551752 : CollatzResearch.WordTrace tailWord_1551752 prefixEnd_1551752 531196421717145331242419 := by
  unfold tailWord_1551752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28298522537137498493768755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37731363382849997991691673 28298522537137498493768755)
  ·
    refine ⟨42447783805706247740653133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28298522537137498493768755 42447783805706247740653133)
    ·
      refine ⟨15917918927139842902744925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42447783805706247740653133 15917918927139842902744925)
      ·
        refine ⟨5969219597677441088529347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15917918927139842902744925 5969219597677441088529347)
        ·
          refine ⟨8953829396516161632794021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969219597677441088529347 8953829396516161632794021)
          ·
            refine ⟨1678843011846780306148879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8953829396516161632794021 1678843011846780306148879)
            ·
              refine ⟨2518264517770170459223319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678843011846780306148879 2518264517770170459223319)
              ·
                refine ⟨3777396776655255688834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518264517770170459223319 3777396776655255688834979)
                ·
                  refine ⟨5666095164982883533252469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777396776655255688834979 5666095164982883533252469)
                  ·
                    refine ⟨531196421717145331242419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5666095164982883533252469 531196421717145331242419)
                    ·
                      rfl

theorem cell22_1551752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1551752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551752 prefixEnd_1551752 := by exact prefixLift 1551752
  have htrace : WordTrace (prefixWord ++ tailWord_1551752) baseStart_1551752 baseEnd_1551752 := by
    simpa [prefixWord, tailWord_1551752, baseEnd_1551752] using wordTrace_append hprefix tailTrace_1551752
  have hstable : (prefixWord ++ tailWord_1551752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551752).length < 2 ^ (prefixWord ++ tailWord_1551752).sum := by decide
  have hdescent : baseEnd_1551752 < baseStart_1551752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551765 : List Nat := [1, 3, 2, 1, 1, 2, 6, 6]
def baseStart_1551765 : Nat := 118140960795 + 1551765 * 2 ^ 59
def prefixEnd_1551765 : Nat := 4983230072969 + 3 ^ 40 * 1551765 * 2
def baseEnd_1551765 : Nat := 59022319098090847851931

theorem tailTrace_1551765 : CollatzResearch.WordTrace tailWord_1551765 prefixEnd_1551765 59022319098090847851931 := by
  unfold tailWord_1551765
  simp only [CollatzResearch.WordTrace]
  refine ⟨56597519223227900207760749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37731679482151933471840499 56597519223227900207760749)
  ·
    refine ⟨21224069708710462577910281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56597519223227900207760749 21224069708710462577910281)
    ·
      refine ⟨15918052281532846933432711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21224069708710462577910281 15918052281532846933432711)
      ·
        refine ⟨23877078422299270400149067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15918052281532846933432711 23877078422299270400149067)
        ·
          refine ⟨35815617633448905600223601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23877078422299270400149067 35815617633448905600223601)
          ·
            refine ⟨26861713225086679200167701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35815617633448905600223601 26861713225086679200167701)
            ·
              refine ⟨1259142807425938087507861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 26861713225086679200167701 1259142807425938087507861)
              ·
                refine ⟨59022319098090847851931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1259142807425938087507861 59022319098090847851931)
                ·
                  rfl

theorem cell22_1551765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 6].length) (baseStart_1551765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551765 prefixEnd_1551765 := by exact prefixLift 1551765
  have htrace : WordTrace (prefixWord ++ tailWord_1551765) baseStart_1551765 baseEnd_1551765 := by
    simpa [prefixWord, tailWord_1551765, baseEnd_1551765] using wordTrace_append hprefix tailTrace_1551765
  have hstable : (prefixWord ++ tailWord_1551765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551765).length < 2 ^ (prefixWord ++ tailWord_1551765).sum := by decide
  have hdescent : baseEnd_1551765 < baseStart_1551765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551784 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1551784 : Nat := 118140960795 + 1551784 * 2 ^ 59
def prefixEnd_1551784 : Nat := 4983230072969 + 3 ^ 40 * 1551784 * 2
def baseEnd_1551784 : Nat := 531207375971107914442321

theorem tailTrace_1551784 : CollatzResearch.WordTrace tailWord_1551784 prefixEnd_1551784 531207375971107914442321 := by
  unfold tailWord_1551784
  simp only [CollatzResearch.WordTrace]
  refine ⟨28299106105079533226351203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37732141473439377635134937 28299106105079533226351203)
  ·
    refine ⟨42448659157619299839526805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28299106105079533226351203 42448659157619299839526805)
    ·
      refine ⟨1989780898013404679977819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42448659157619299839526805 1989780898013404679977819)
      ·
        refine ⟨2984671347020107019966729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1989780898013404679977819 2984671347020107019966729)
        ·
          refine ⟨2238503510265080264975047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2984671347020107019966729 2238503510265080264975047)
          ·
            refine ⟨3357755265397620397462571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2238503510265080264975047 3357755265397620397462571)
            ·
              refine ⟨5036632898096430596193857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3357755265397620397462571 5036632898096430596193857)
              ·
                refine ⟨3777474673572322947145393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036632898096430596193857 3777474673572322947145393)
                ·
                  refine ⟨2833106005179242210359045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3777474673572322947145393 2833106005179242210359045)
                  ·
                    refine ⟨531207375971107914442321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833106005179242210359045 531207375971107914442321)
                    ·
                      rfl

theorem cell22_1551784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1551784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551784 prefixEnd_1551784 := by exact prefixLift 1551784
  have htrace : WordTrace (prefixWord ++ tailWord_1551784) baseStart_1551784 baseEnd_1551784 := by
    simpa [prefixWord, tailWord_1551784, baseEnd_1551784] using wordTrace_append hprefix tailTrace_1551784
  have hstable : (prefixWord ++ tailWord_1551784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551784).length < 2 ^ (prefixWord ++ tailWord_1551784).sum := by decide
  have hdescent : baseEnd_1551784 < baseStart_1551784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551874 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_1551874 : Nat := 118140960795 + 1551874 * 2 ^ 59
def prefixEnd_1551874 : Nat := 4983230072969 + 3 ^ 40 * 1551874 * 2
def baseEnd_1551874 : Nat := 531238184810377679692045

theorem tailTrace_1551874 : CollatzResearch.WordTrace tailWord_1551874 prefixEnd_1551874 531238184810377679692045 := by
  unfold tailWord_1551874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14150373694958252955869669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37734329853222007882319117 14150373694958252955869669)
  ·
    refine ⟨2653195067804672429225563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14150373694958252955869669 2653195067804672429225563)
    ·
      refine ⟨3979792601707008643838345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653195067804672429225563 3979792601707008643838345)
      ·
        refine ⟨2984844451280256482878759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3979792601707008643838345 2984844451280256482878759)
        ·
          refine ⟨4477266676920384724318139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984844451280256482878759 4477266676920384724318139)
          ·
            refine ⟨6715900015380577086477209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477266676920384724318139 6715900015380577086477209)
            ·
              refine ⟨5036925011535432814857907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715900015380577086477209 5036925011535432814857907)
              ·
                refine ⟨7555387517303149222286861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036925011535432814857907 7555387517303149222286861)
                ·
                  refine ⟨2833270318988680958357573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7555387517303149222286861 2833270318988680958357573)
                  ·
                    refine ⟨531238184810377679692045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833270318988680958357573 531238184810377679692045)
                    ·
                      rfl

theorem cell22_1551874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_1551874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551874 prefixEnd_1551874 := by exact prefixLift 1551874
  have htrace : WordTrace (prefixWord ++ tailWord_1551874) baseStart_1551874 baseEnd_1551874 := by
    simpa [prefixWord, tailWord_1551874, baseEnd_1551874] using wordTrace_append hprefix tailTrace_1551874
  have hstable : (prefixWord ++ tailWord_1551874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551874).length < 2 ^ (prefixWord ++ tailWord_1551874).sum := by decide
  have hdescent : baseEnd_1551874 < baseStart_1551874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551900 : List Nat := [2, 2, 3, 1, 2, 1, 11]
def baseStart_1551900 : Nat := 118140960795 + 1551900 * 2 ^ 59
def prefixEnd_1551900 : Nat := 4983230072969 + 3 ^ 40 * 1551900 * 2
def baseEnd_1551900 : Nat := 19675817968211936242295

theorem tailTrace_1551900 : CollatzResearch.WordTrace tailWord_1551900 prefixEnd_1551900 19675817968211936242295 := by
  unfold tailWord_1551900
  simp only [CollatzResearch.WordTrace]
  refine ⟨28301221538869409131962577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37734962051825878842616769 28301221538869409131962577)
  ·
    refine ⟨21225916154152056848971933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28301221538869409131962577 21225916154152056848971933)
    ·
      refine ⟨7959718557807021318364475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21225916154152056848971933 7959718557807021318364475)
      ·
        refine ⟨11939577836710531977546713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959718557807021318364475 11939577836710531977546713)
        ·
          refine ⟨8954683377532898983160035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11939577836710531977546713 8954683377532898983160035)
          ·
            refine ⟨13432025066299348474740053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954683377532898983160035 13432025066299348474740053)
            ·
              refine ⟨19675817968211936242295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13432025066299348474740053 19675817968211936242295)
              ·
                rfl

theorem cell22_1551900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 11].length) (baseStart_1551900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551900 prefixEnd_1551900 := by exact prefixLift 1551900
  have htrace : WordTrace (prefixWord ++ tailWord_1551900) baseStart_1551900 baseEnd_1551900 := by
    simpa [prefixWord, tailWord_1551900, baseEnd_1551900] using wordTrace_append hprefix tailTrace_1551900
  have hstable : (prefixWord ++ tailWord_1551900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551900).length < 2 ^ (prefixWord ++ tailWord_1551900).sum := by decide
  have hdescent : baseEnd_1551900 < baseStart_1551900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1551904 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 4, 3]
def baseStart_1551904 : Nat := 118140960795 + 1551904 * 2 ^ 59
def prefixEnd_1551904 : Nat := 4983230072969 + 3 ^ 40 * 1551904 * 2
def baseEnd_1551904 : Nat := 531248454423467601441953

theorem tailTrace_1551904 : CollatzResearch.WordTrace tailWord_1551904 prefixEnd_1551904 531248454423467601441953 := by
  unfold tailWord_1551904
  simp only [CollatzResearch.WordTrace]
  refine ⟨28301294484862163473535383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37735059313149551298047177 28301294484862163473535383)
  ·
    refine ⟨42451941727293245210303075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28301294484862163473535383 42451941727293245210303075)
    ·
      refine ⟨63677912590939867815454613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42451941727293245210303075 63677912590939867815454613)
      ·
        refine ⟨2984902152700306303849435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63677912590939867815454613 2984902152700306303849435)
        ·
          refine ⟨4477353229050459455774153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2984902152700306303849435 4477353229050459455774153)
          ·
            refine ⟨3358014921787844591830615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477353229050459455774153 3358014921787844591830615)
            ·
              refine ⟨5037022382681766887745923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3358014921787844591830615 5037022382681766887745923)
              ·
                refine ⟨7555533574022650331618885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037022382681766887745923 7555533574022650331618885)
                ·
                  refine ⟨1416662545129246937178541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7555533574022650331618885 1416662545129246937178541)
                  ·
                    refine ⟨531248454423467601441953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416662545129246937178541 531248454423467601441953)
                    ·
                      rfl

theorem cell22_1551904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 3].length) (baseStart_1551904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1551904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1551904 prefixEnd_1551904 := by exact prefixLift 1551904
  have htrace : WordTrace (prefixWord ++ tailWord_1551904) baseStart_1551904 baseEnd_1551904 := by
    simpa [prefixWord, tailWord_1551904, baseEnd_1551904] using wordTrace_append hprefix tailTrace_1551904
  have hstable : (prefixWord ++ tailWord_1551904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1551904).length < 2 ^ (prefixWord ++ tailWord_1551904).sum := by decide
  have hdescent : baseEnd_1551904 < baseStart_1551904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1551904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552037 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_1552037 : Nat := 118140960795 + 1552037 * 2 ^ 59
def prefixEnd_1552037 : Nat := 4983230072969 + 3 ^ 40 * 1552037 * 2
def baseEnd_1552037 : Nat := 531293983041499587866545

theorem tailTrace_1552037 : CollatzResearch.WordTrace tailWord_1552037 prefixEnd_1552037 531293983041499587866545 := by
  unfold tailWord_1552037
  simp only [CollatzResearch.WordTrace]
  refine ⟨56607439878242490661662365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37738293252161660441108243 56607439878242490661662365)
  ·
    refine ⟨21227789954340933998123387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56607439878242490661662365 21227789954340933998123387)
    ·
      refine ⟨31841684931511400997185081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21227789954340933998123387 31841684931511400997185081)
      ·
        refine ⟨23881263698633550747888811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31841684931511400997185081 23881263698633550747888811)
        ·
          refine ⟨35821895547950326121833217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23881263698633550747888811 35821895547950326121833217)
          ·
            refine ⟨26866421660962744591374913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35821895547950326121833217 26866421660962744591374913)
            ·
              refine ⟨20149816245722058443531185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26866421660962744591374913 20149816245722058443531185)
              ·
                refine ⟨15112362184291543832648389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20149816245722058443531185 15112362184291543832648389)
                ·
                  refine ⟨2833567909554664468621573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15112362184291543832648389 2833567909554664468621573)
                  ·
                    refine ⟨531293983041499587866545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833567909554664468621573 531293983041499587866545)
                    ·
                      rfl

theorem cell22_1552037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_1552037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552037 prefixEnd_1552037 := by exact prefixLift 1552037
  have htrace : WordTrace (prefixWord ++ tailWord_1552037) baseStart_1552037 baseEnd_1552037 := by
    simpa [prefixWord, tailWord_1552037, baseEnd_1552037] using wordTrace_append hprefix tailTrace_1552037
  have hstable : (prefixWord ++ tailWord_1552037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552037).length < 2 ^ (prefixWord ++ tailWord_1552037).sum := by decide
  have hdescent : baseEnd_1552037 < baseStart_1552037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552103 : List Nat := [1, 1, 5, 4, 1, 2, 2, 6]
def baseStart_1552103 : Nat := 118140960795 + 1552103 * 2 ^ 59
def prefixEnd_1552103 : Nat := 4983230072969 + 3 ^ 40 * 1552103 * 2
def baseEnd_1552103 : Nat := 59035175132255268412927

theorem tailTrace_1552103 : CollatzResearch.WordTrace tailWord_1552103 prefixEnd_1552103 59035175132255268412927 := by
  unfold tailWord_1552103
  simp only [CollatzResearch.WordTrace]
  refine ⟨56609847096003383933564963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37739898064002255955709975 56609847096003383933564963)
  ·
    refine ⟨84914770644005075900347445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56609847096003383933564963 84914770644005075900347445)
    ·
      refine ⟨7960759747875475865657573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84914770644005075900347445 7960759747875475865657573)
      ·
        refine ⟨1492642452726651724810795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7960759747875475865657573 1492642452726651724810795)
        ·
          refine ⟨2238963679089977587216193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492642452726651724810795 2238963679089977587216193)
          ·
            refine ⟨1679222759317483190412145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2238963679089977587216193 1679222759317483190412145)
            ·
              refine ⟨1259417069488112392809109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679222759317483190412145 1259417069488112392809109)
              ·
                refine ⟨59035175132255268412927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1259417069488112392809109 59035175132255268412927)
                ·
                  rfl

theorem cell22_1552103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 6].length) (baseStart_1552103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552103 prefixEnd_1552103 := by exact prefixLift 1552103
  have htrace : WordTrace (prefixWord ++ tailWord_1552103) baseStart_1552103 baseEnd_1552103 := by
    simpa [prefixWord, tailWord_1552103, baseEnd_1552103] using wordTrace_append hprefix tailTrace_1552103
  have hstable : (prefixWord ++ tailWord_1552103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552103).length < 2 ^ (prefixWord ++ tailWord_1552103).sum := by decide
  have hdescent : baseEnd_1552103 < baseStart_1552103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552112 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_1552112 : Nat := 118140960795 + 1552112 * 2 ^ 59
def prefixEnd_1552112 : Nat := 4983230072969 + 3 ^ 40 * 1552112 * 2
def baseEnd_1552112 : Nat := 531319657074224392241315

theorem tailTrace_1552112 : CollatzResearch.WordTrace tailWord_1552112 prefixEnd_1552112 531319657074224392241315 := by
  unfold tailWord_1552112
  simp only [CollatzResearch.WordTrace]
  refine ⟨28305087676485389235321295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37740116901980518980428393 28305087676485389235321295)
  ·
    refine ⟨42457631514728083852981943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28305087676485389235321295 42457631514728083852981943)
    ·
      refine ⟨63686447272092125779472915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42457631514728083852981943 63686447272092125779472915)
      ·
        refine ⟨95529670908138188669209373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63686447272092125779472915 95529670908138188669209373)
        ·
          refine ⟨35823626590551820750953515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95529670908138188669209373 35823626590551820750953515)
          ·
            refine ⟨53735439885827731126430273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35823626590551820750953515 53735439885827731126430273)
            ·
              refine ⟨40301579914370798344822705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53735439885827731126430273 40301579914370798344822705)
              ·
                refine ⟨30226184935778098758617029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40301579914370798344822705 30226184935778098758617029)
                ·
                  refine ⟨5667409675458393517240693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30226184935778098758617029 5667409675458393517240693)
                  ·
                    refine ⟨531319657074224392241315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5667409675458393517240693 531319657074224392241315)
                    ·
                      rfl

theorem cell22_1552112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_1552112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552112 prefixEnd_1552112 := by exact prefixLift 1552112
  have htrace : WordTrace (prefixWord ++ tailWord_1552112) baseStart_1552112 baseEnd_1552112 := by
    simpa [prefixWord, tailWord_1552112, baseEnd_1552112] using wordTrace_append hprefix tailTrace_1552112
  have hstable : (prefixWord ++ tailWord_1552112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552112).length < 2 ^ (prefixWord ++ tailWord_1552112).sum := by decide
  have hdescent : baseEnd_1552112 < baseStart_1552112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552135 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1552135 : Nat := 118140960795 + 1552135 * 2 ^ 59
def prefixEnd_1552135 : Nat := 4983230072969 + 3 ^ 40 * 1552135 * 2
def baseEnd_1552135 : Nat := 531327530444259998916245

theorem tailTrace_1552135 : CollatzResearch.WordTrace tailWord_1552135 prefixEnd_1552135 531327530444259998916245 := by
  unfold tailWord_1552135
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611014231887453398729859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37740676154591635599153239 56611014231887453398729859)
  ·
    refine ⟨84916521347831180098094789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56611014231887453398729859 84916521347831180098094789)
    ·
      refine ⟨15921847752718346268392773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84916521347831180098094789 15921847752718346268392773)
      ·
        refine ⟨2985346453634689925323645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15921847752718346268392773 2985346453634689925323645)
        ·
          refine ⟨1119504920113008721996367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2985346453634689925323645 1119504920113008721996367)
          ·
            refine ⟨1679257380169513082994551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119504920113008721996367 1679257380169513082994551)
            ·
              refine ⟨2518886070254269624491827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679257380169513082994551 2518886070254269624491827)
              ·
                refine ⟨3778329105381404436737741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2518886070254269624491827 3778329105381404436737741)
                ·
                  refine ⟨1416873414518026663776653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3778329105381404436737741 1416873414518026663776653)
                  ·
                    refine ⟨531327530444259998916245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416873414518026663776653 531327530444259998916245)
                    ·
                      rfl

theorem cell22_1552135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1552135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552135 prefixEnd_1552135 := by exact prefixLift 1552135
  have htrace : WordTrace (prefixWord ++ tailWord_1552135) baseStart_1552135 baseEnd_1552135 := by
    simpa [prefixWord, tailWord_1552135, baseEnd_1552135] using wordTrace_append hprefix tailTrace_1552135
  have hstable : (prefixWord ++ tailWord_1552135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552135).length < 2 ^ (prefixWord ++ tailWord_1552135).sum := by decide
  have hdescent : baseEnd_1552135 < baseStart_1552135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552141 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_1552141 : Nat := 118140960795 + 1552141 * 2 ^ 59
def prefixEnd_1552141 : Nat := 4983230072969 + 3 ^ 40 * 1552141 * 2
def baseEnd_1552141 : Nat := 531329584366877983266227

theorem tailTrace_1552141 : CollatzResearch.WordTrace tailWord_1552141 prefixEnd_1552141 531329584366877983266227 := by
  unfold tailWord_1552141
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611233069865716423448277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37740822046577144282298851 56611233069865716423448277)
  ·
    refine ⟨1326825775074977728674569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56611233069865716423448277 1326825775074977728674569)
    ·
      refine ⟨995119331306233296505927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326825775074977728674569 995119331306233296505927)
      ·
        refine ⟨1492678996959349944758891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995119331306233296505927 1492678996959349944758891)
        ·
          refine ⟨2239018495439024917138337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1492678996959349944758891 2239018495439024917138337)
          ·
            refine ⟨1679263871579268687853753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239018495439024917138337 1679263871579268687853753)
            ·
              refine ⟨1259447903684451515890315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679263871579268687853753 1259447903684451515890315)
              ·
                refine ⟨1889171855526677273835473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259447903684451515890315 1889171855526677273835473)
                ·
                  refine ⟨1416878891645007955376605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889171855526677273835473 1416878891645007955376605)
                  ·
                    refine ⟨531329584366877983266227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1416878891645007955376605 531329584366877983266227)
                    ·
                      rfl

theorem cell22_1552141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_1552141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552141 prefixEnd_1552141 := by exact prefixLift 1552141
  have htrace : WordTrace (prefixWord ++ tailWord_1552141) baseStart_1552141 baseEnd_1552141 := by
    simpa [prefixWord, tailWord_1552141, baseEnd_1552141] using wordTrace_append hprefix tailTrace_1552141
  have hstable : (prefixWord ++ tailWord_1552141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552141).length < 2 ^ (prefixWord ++ tailWord_1552141).sum := by decide
  have hdescent : baseEnd_1552141 < baseStart_1552141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552161 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_1552161 : Nat := 118140960795 + 1552161 * 2 ^ 59
def prefixEnd_1552161 : Nat := 4983230072969 + 3 ^ 40 * 1552161 * 2
def baseEnd_1552161 : Nat := 531336430775604597766165

theorem tailTrace_1552161 : CollatzResearch.WordTrace tailWord_1552161 prefixEnd_1552161 531336430775604597766165 := by
  unfold tailWord_1552161
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611962529793259839176337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37741308353195506559450891 56611962529793259839176337)
  ·
    refine ⟨42458971897344944879382253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56611962529793259839176337 42458971897344944879382253)
    ·
      refine ⟨15922114461504354329768345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42458971897344944879382253 15922114461504354329768345)
      ·
        refine ⟨11941585846128265747326259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15922114461504354329768345 11941585846128265747326259)
        ·
          refine ⟨17912378769192398620989389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11941585846128265747326259 17912378769192398620989389)
          ·
            refine ⟨6717142038447149482871021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17912378769192398620989389 6717142038447149482871021)
            ·
              refine ⟨2518928264417681056076633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6717142038447149482871021 2518928264417681056076633)
              ·
                refine ⟨1889196198313260792057475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518928264417681056076633 1889196198313260792057475)
                ·
                  refine ⟨2833794297469891188086213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889196198313260792057475 2833794297469891188086213)
                  ·
                    refine ⟨531336430775604597766165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833794297469891188086213 531336430775604597766165)
                    ·
                      rfl

theorem cell22_1552161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_1552161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552161 prefixEnd_1552161 := by exact prefixLift 1552161
  have htrace : WordTrace (prefixWord ++ tailWord_1552161) baseStart_1552161 baseEnd_1552161 := by
    simpa [prefixWord, tailWord_1552161, baseEnd_1552161] using wordTrace_append hprefix tailTrace_1552161
  have hstable : (prefixWord ++ tailWord_1552161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552161).length < 2 ^ (prefixWord ++ tailWord_1552161).sum := by decide
  have hdescent : baseEnd_1552161 < baseStart_1552161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552178 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_1552178 : Nat := 118140960795 + 1552178 * 2 ^ 59
def prefixEnd_1552178 : Nat := 4983230072969 + 3 ^ 40 * 1552178 * 2
def baseEnd_1552178 : Nat := 531342250223022220091113

theorem tailTrace_1552178 : CollatzResearch.WordTrace tailWord_1552178 prefixEnd_1552178 531342250223022220091113 := by
  unfold tailWord_1552178
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153145642682917935636297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37741721713821114495030125 14153145642682917935636297)
  ·
    refine ⟨10614859232012188451727223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14153145642682917935636297 10614859232012188451727223)
    ·
      refine ⟨15922288848018282677590835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10614859232012188451727223 15922288848018282677590835)
      ·
        refine ⟨23883433272027424016386253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15922288848018282677590835 23883433272027424016386253)
        ·
          refine ⟨8956287477010284006144845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23883433272027424016386253 8956287477010284006144845)
          ·
            refine ⟨3358607803878856502304317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8956287477010284006144845 3358607803878856502304317)
            ·
              refine ⟨1259477926454571188364119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3358607803878856502304317 1259477926454571188364119)
              ·
                refine ⟨1889216889681856782546179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259477926454571188364119 1889216889681856782546179)
                ·
                  refine ⟨2833825334522785173819269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889216889681856782546179 2833825334522785173819269)
                  ·
                    refine ⟨531342250223022220091113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833825334522785173819269 531342250223022220091113)
                    ·
                      rfl

theorem cell22_1552178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_1552178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552178 prefixEnd_1552178 := by exact prefixLift 1552178
  have htrace : WordTrace (prefixWord ++ tailWord_1552178) baseStart_1552178 baseEnd_1552178 := by
    simpa [prefixWord, tailWord_1552178, baseEnd_1552178] using wordTrace_append hprefix tailTrace_1552178
  have hstable : (prefixWord ++ tailWord_1552178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552178).length < 2 ^ (prefixWord ++ tailWord_1552178).sum := by decide
  have hdescent : baseEnd_1552178 < baseStart_1552178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552249 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 7]
def baseStart_1552249 : Nat := 118140960795 + 1552249 * 2 ^ 59
def prefixEnd_1552249 : Nat := 4983230072969 + 3 ^ 40 * 1552249 * 2
def baseEnd_1552249 : Nat := 177122184991333900521965

theorem tailTrace_1552249 : CollatzResearch.WordTrace tailWord_1552249 prefixEnd_1552249 177122184991333900521965 := by
  unfold tailWord_1552249
  simp only [CollatzResearch.WordTrace]
  refine ⟨56615172153474450868379801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37743448102316300578919867 56615172153474450868379801)
  ·
    refine ⟨42461379115105838151284851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56615172153474450868379801 42461379115105838151284851)
    ·
      refine ⟨63692068672658757226927277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42461379115105838151284851 63692068672658757226927277)
      ·
        refine ⟨23884525752247033960097729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63692068672658757226927277 23884525752247033960097729)
        ·
          refine ⟨17913394314185275470073297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23884525752247033960097729 17913394314185275470073297)
          ·
            refine ⟨13435045735638956602554973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17913394314185275470073297 13435045735638956602554973)
            ·
              refine ⟨5038142150864608725958115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13435045735638956602554973 5038142150864608725958115)
              ·
                refine ⟨7557213226296913088937173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038142150864608725958115 7557213226296913088937173)
                ·
                  refine ⟨177122184991333900521965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7557213226296913088937173 177122184991333900521965)
                  ·
                    rfl

theorem cell22_1552249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 7].length) (baseStart_1552249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552249 prefixEnd_1552249 := by exact prefixLift 1552249
  have htrace : WordTrace (prefixWord ++ tailWord_1552249) baseStart_1552249 baseEnd_1552249 := by
    simpa [prefixWord, tailWord_1552249, baseEnd_1552249] using wordTrace_append hprefix tailTrace_1552249
  have hstable : (prefixWord ++ tailWord_1552249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552249).length < 2 ^ (prefixWord ++ tailWord_1552249).sum := by decide
  have hdescent : baseEnd_1552249 < baseStart_1552249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552287 : List Nat := [1, 1, 2, 5, 3, 2, 1, 3, 1, 3]
def baseStart_1552287 : Nat := 118140960795 + 1552287 * 2 ^ 59
def prefixEnd_1552287 : Nat := 4983230072969 + 3 ^ 40 * 1552287 * 2
def baseEnd_1552287 : Nat := 531379563150582269115779

theorem tailTrace_1552287 : CollatzResearch.WordTrace tailWord_1552287 prefixEnd_1552287 531379563150582269115779 := by
  unfold tailWord_1552287
  simp only [CollatzResearch.WordTrace]
  refine ⟨56616558127336783358263115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37744372084891188905508743 56616558127336783358263115)
  ·
    refine ⟨84924837191005175037394673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56616558127336783358263115 84924837191005175037394673)
    ·
      refine ⟨63693627893253881278046005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84924837191005175037394673 63693627893253881278046005)
      ·
        refine ⟨5971277614992551369816813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63693627893253881278046005 5971277614992551369816813)
        ·
          refine ⟨2239229105622206763681305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5971277614992551369816813 2239229105622206763681305)
          ·
            refine ⟨1679421829216655072760979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239229105622206763681305 1679421829216655072760979)
            ·
              refine ⟨2519132743824982609141469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679421829216655072760979 2519132743824982609141469)
              ·
                refine ⟨944674778934368478428051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2519132743824982609141469 944674778934368478428051)
                ·
                  refine ⟨1417012168401552717642077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 944674778934368478428051 1417012168401552717642077)
                  ·
                    refine ⟨531379563150582269115779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417012168401552717642077 531379563150582269115779)
                    ·
                      rfl

theorem cell22_1552287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_1552287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552287 prefixEnd_1552287 := by exact prefixLift 1552287
  have htrace : WordTrace (prefixWord ++ tailWord_1552287) baseStart_1552287 baseEnd_1552287 := by
    simpa [prefixWord, tailWord_1552287, baseEnd_1552287] using wordTrace_append hprefix tailTrace_1552287
  have hstable : (prefixWord ++ tailWord_1552287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552287).length < 2 ^ (prefixWord ++ tailWord_1552287).sum := by decide
  have hdescent : baseEnd_1552287 < baseStart_1552287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552371 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 7, 3]
def baseStart_1552371 : Nat := 118140960795 + 1552371 * 2 ^ 59
def prefixEnd_1552371 : Nat := 4983230072969 + 3 ^ 40 * 1552371 * 2
def baseEnd_1552371 : Nat := 531408318067234050015521

theorem tailTrace_1552371 : CollatzResearch.WordTrace tailWord_1552371 prefixEnd_1552371 531408318067234050015521 := by
  unfold tailWord_1552371
  simp only [CollatzResearch.WordTrace]
  refine ⟨56619621859032465704320967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37746414572688310469547311 56619621859032465704320967)
  ·
    refine ⟨84929432788548698556481451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56619621859032465704320967 84929432788548698556481451)
    ·
      refine ⟨127394149182823047834722177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84929432788548698556481451 127394149182823047834722177)
      ·
        refine ⟨95545611887117285876041633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127394149182823047834722177 95545611887117285876041633)
        ·
          refine ⟨71659208915337964407031225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95545611887117285876041633 71659208915337964407031225)
          ·
            refine ⟨53744406686503473305273419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71659208915337964407031225 53744406686503473305273419)
            ·
              refine ⟨80616610029755209957910129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53744406686503473305273419 80616610029755209957910129)
              ·
                refine ⟨60462457522316407468432597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80616610029755209957910129 60462457522316407468432597)
                ·
                  refine ⟨1417088848179290800041389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 60462457522316407468432597 1417088848179290800041389)
                  ·
                    refine ⟨531408318067234050015521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417088848179290800041389 531408318067234050015521)
                    ·
                      rfl

theorem cell22_1552371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 3].length) (baseStart_1552371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552371 prefixEnd_1552371 := by exact prefixLift 1552371
  have htrace : WordTrace (prefixWord ++ tailWord_1552371) baseStart_1552371 baseEnd_1552371 := by
    simpa [prefixWord, tailWord_1552371, baseEnd_1552371] using wordTrace_append hprefix tailTrace_1552371
  have hstable : (prefixWord ++ tailWord_1552371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552371).length < 2 ^ (prefixWord ++ tailWord_1552371).sum := by decide
  have hdescent : baseEnd_1552371 < baseStart_1552371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552431 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 3, 4]
def baseStart_1552431 : Nat := 118140960795 + 1552431 * 2 ^ 59
def prefixEnd_1552431 : Nat := 4983230072969 + 3 ^ 40 * 1552431 * 2
def baseEnd_1552431 : Nat := 531428857293413893515337

theorem tailTrace_1552431 : CollatzResearch.WordTrace tailWord_1552431 prefixEnd_1552431 531428857293413893515337 := by
  unfold tailWord_1552431
  simp only [CollatzResearch.WordTrace]
  refine ⟨56621810238815095951505147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37747873492543397301003431 56621810238815095951505147)
  ·
    refine ⟨84932715358222643927257721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56621810238815095951505147 84932715358222643927257721)
    ·
      refine ⟨63699536518666982945443291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84932715358222643927257721 63699536518666982945443291)
      ·
        refine ⟨95549304778000474418164937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63699536518666982945443291 95549304778000474418164937)
        ·
          refine ⟨71661978583500355813623703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95549304778000474418164937 71661978583500355813623703)
          ·
            refine ⟨107492967875250533720435555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71661978583500355813623703 107492967875250533720435555)
            ·
              refine ⟨161239451812875800580653333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107492967875250533720435555 161239451812875800580653333)
              ·
                refine ⟨7558099303728553152218125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 161239451812875800580653333 7558099303728553152218125)
                ·
                  refine ⟨2834287238898207432081797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7558099303728553152218125 2834287238898207432081797)
                  ·
                    refine ⟨531428857293413893515337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834287238898207432081797 531428857293413893515337)
                    ·
                      rfl

theorem cell22_1552431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_1552431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552431 prefixEnd_1552431 := by exact prefixLift 1552431
  have htrace : WordTrace (prefixWord ++ tailWord_1552431) baseStart_1552431 baseEnd_1552431 := by
    simpa [prefixWord, tailWord_1552431, baseEnd_1552431] using wordTrace_append hprefix tailTrace_1552431
  have hstable : (prefixWord ++ tailWord_1552431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552431).length < 2 ^ (prefixWord ++ tailWord_1552431).sum := by decide
  have hdescent : baseEnd_1552431 < baseStart_1552431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552448 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_1552448 : Nat := 118140960795 + 1552448 * 2 ^ 59
def prefixEnd_1552448 : Nat := 4983230072969 + 3 ^ 40 * 1552448 * 2
def baseEnd_1552448 : Nat := 531434676740831515840285

theorem tailTrace_1552448 : CollatzResearch.WordTrace tailWord_1552448 prefixEnd_1552448 531434676740831515840285 := by
  unfold tailWord_1552448
  simp only [CollatzResearch.WordTrace]
  refine ⟨28311215139876753927436999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37748286853169005236582665 28311215139876753927436999)
  ·
    refine ⟨42466822709815130891155499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28311215139876753927436999 42466822709815130891155499)
    ·
      refine ⟨63700234064722696336733249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42466822709815130891155499 63700234064722696336733249)
      ·
        refine ⟨47775175548542022252549937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63700234064722696336733249 47775175548542022252549937)
        ·
          refine ⟨35831381661406516689412453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47775175548542022252549937 35831381661406516689412453)
          ·
            refine ⟨6718384061513721879264835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35831381661406516689412453 6718384061513721879264835)
            ·
              refine ⟨10077576092270582818897253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718384061513721879264835 10077576092270582818897253)
              ·
                refine ⟨1889545517300734278543235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10077576092270582818897253 1889545517300734278543235)
                ·
                  refine ⟨2834318275951101417814853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889545517300734278543235 2834318275951101417814853)
                  ·
                    refine ⟨531434676740831515840285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834318275951101417814853 531434676740831515840285)
                    ·
                      rfl

theorem cell22_1552448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_1552448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552448 prefixEnd_1552448 := by exact prefixLift 1552448
  have htrace : WordTrace (prefixWord ++ tailWord_1552448) baseStart_1552448 baseEnd_1552448 := by
    simpa [prefixWord, tailWord_1552448, baseEnd_1552448] using wordTrace_append hprefix tailTrace_1552448
  have hstable : (prefixWord ++ tailWord_1552448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552448).length < 2 ^ (prefixWord ++ tailWord_1552448).sum := by decide
  have hdescent : baseEnd_1552448 < baseStart_1552448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552493 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1552493 : Nat := 118140960795 + 1552493 * 2 ^ 59
def prefixEnd_1552493 : Nat := 4983230072969 + 3 ^ 40 * 1552493 * 2
def baseEnd_1552493 : Nat := 531450081160466398465147

theorem tailTrace_1552493 : CollatzResearch.WordTrace tailWord_1552493 prefixEnd_1552493 531450081160466398465147 := by
  unfold tailWord_1552493
  simp only [CollatzResearch.WordTrace]
  refine ⟨56624071564590480540262133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37749381043060320360174755 56624071564590480540262133)
  ·
    refine ⟨5308506709180357550649575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56624071564590480540262133 5308506709180357550649575)
    ·
      refine ⟨7962760063770536325974363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308506709180357550649575 7962760063770536325974363)
      ·
        refine ⟨11944140095655804488961545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7962760063770536325974363 11944140095655804488961545)
        ·
          refine ⟨8958105071741853366721159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11944140095655804488961545 8958105071741853366721159)
          ·
            refine ⟨13437157607612780050081739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958105071741853366721159 13437157607612780050081739)
            ·
              refine ⟨20155736411419170075122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13437157607612780050081739 20155736411419170075122609)
              ·
                refine ⟨15116802308564377556341957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20155736411419170075122609 15116802308564377556341957)
                ·
                  refine ⟨2834400432855820791814117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15116802308564377556341957 2834400432855820791814117)
                  ·
                    refine ⟨531450081160466398465147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834400432855820791814117 531450081160466398465147)
                    ·
                      rfl

theorem cell22_1552493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1552493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552493 prefixEnd_1552493 := by exact prefixLift 1552493
  have htrace : WordTrace (prefixWord ++ tailWord_1552493) baseStart_1552493 baseEnd_1552493 := by
    simpa [prefixWord, tailWord_1552493, baseEnd_1552493] using wordTrace_append hprefix tailTrace_1552493
  have hstable : (prefixWord ++ tailWord_1552493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552493).length < 2 ^ (prefixWord ++ tailWord_1552493).sum := by decide
  have hdescent : baseEnd_1552493 < baseStart_1552493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552495 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 2, 3]
def baseStart_1552495 : Nat := 118140960795 + 1552495 * 2 ^ 59
def prefixEnd_1552495 : Nat := 4983230072969 + 3 ^ 40 * 1552495 * 2
def baseEnd_1552495 : Nat := 531450765801339059915141

theorem tailTrace_1552495 : CollatzResearch.WordTrace tailWord_1552495 prefixEnd_1552495 531450765801339059915141 := by
  unfold tailWord_1552495
  simp only [CollatzResearch.WordTrace]
  refine ⟨56624144510583234881834939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37749429673722156587889959 56624144510583234881834939)
  ·
    refine ⟨84936216765874852322752409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56624144510583234881834939 84936216765874852322752409)
    ·
      refine ⟨63702162574406139242064307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84936216765874852322752409 63702162574406139242064307)
      ·
        refine ⟨95553243861609208863096461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63702162574406139242064307 95553243861609208863096461)
        ·
          refine ⟨35832466448103453323661173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95553243861609208863096461 35832466448103453323661173)
          ·
            refine ⟨3359293729509698749093235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35832466448103453323661173 3359293729509698749093235)
            ·
              refine ⟨5038940594264548123639853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359293729509698749093235 5038940594264548123639853)
              ·
                refine ⟨1889602722849205546364945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5038940594264548123639853 1889602722849205546364945)
                ·
                  refine ⟨1417202042136904159773709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1889602722849205546364945 1417202042136904159773709)
                  ·
                    refine ⟨531450765801339059915141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417202042136904159773709 531450765801339059915141)
                    ·
                      rfl

theorem cell22_1552495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 3].length) (baseStart_1552495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552495 prefixEnd_1552495 := by exact prefixLift 1552495
  have htrace : WordTrace (prefixWord ++ tailWord_1552495) baseStart_1552495 baseEnd_1552495 := by
    simpa [prefixWord, tailWord_1552495, baseEnd_1552495] using wordTrace_append hprefix tailTrace_1552495
  have hstable : (prefixWord ++ tailWord_1552495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552495).length < 2 ^ (prefixWord ++ tailWord_1552495).sum := by decide
  have hdescent : baseEnd_1552495 < baseStart_1552495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552540 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 3, 3]
def baseStart_1552540 : Nat := 118140960795 + 1552540 * 2 ^ 59
def prefixEnd_1552540 : Nat := 4983230072969 + 3 ^ 40 * 1552540 * 2
def baseEnd_1552540 : Nat := 531466170220973942540003

theorem tailTrace_1552540 : CollatzResearch.WordTrace tailWord_1552540 prefixEnd_1552540 531466170220973942540003 := by
  unfold tailWord_1552540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28312892897710103783611537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37750523863613471711482049 28312892897710103783611537)
  ·
    refine ⟨21234669673282577837708653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28312892897710103783611537 21234669673282577837708653)
    ·
      refine ⟨7963001127480966689140745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21234669673282577837708653 7963001127480966689140745)
      ·
        refine ⟨5972250845610725016855559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7963001127480966689140745 5972250845610725016855559)
        ·
          refine ⟨8958376268416087525283339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5972250845610725016855559 8958376268416087525283339)
          ·
            refine ⟨13437564402624131287925009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958376268416087525283339 13437564402624131287925009)
            ·
              refine ⟨10078173301968098465943757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13437564402624131287925009 10078173301968098465943757)
              ·
                refine ⟨3779314988238036924728909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10078173301968098465943757 3779314988238036924728909)
                ·
                  refine ⟨1417243120589263846773341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3779314988238036924728909 1417243120589263846773341)
                  ·
                    refine ⟨531466170220973942540003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417243120589263846773341 531466170220973942540003)
                    ·
                      rfl

theorem cell22_1552540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_1552540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552540 prefixEnd_1552540 := by exact prefixLift 1552540
  have htrace : WordTrace (prefixWord ++ tailWord_1552540) baseStart_1552540 baseEnd_1552540 := by
    simpa [prefixWord, tailWord_1552540, baseEnd_1552540] using wordTrace_append hprefix tailTrace_1552540
  have hstable : (prefixWord ++ tailWord_1552540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552540).length < 2 ^ (prefixWord ++ tailWord_1552540).sum := by decide
  have hdescent : baseEnd_1552540 < baseStart_1552540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552542 : List Nat := [4, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1552542 : Nat := 118140960795 + 1552542 * 2 ^ 59
def prefixEnd_1552542 : Nat := 4983230072969 + 3 ^ 40 * 1552542 * 2
def baseEnd_1552542 : Nat := 59051872762427400443333

theorem tailTrace_1552542 : CollatzResearch.WordTrace tailWord_1552542 prefixEnd_1552542 59051872762427400443333 := by
  unfold tailWord_1552542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7078232342676620238599485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37750572494275307939197253 7078232342676620238599485)
  ·
    refine ⟨2654337128503732589474807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7078232342676620238599485 2654337128503732589474807)
    ·
      refine ⟨3981505692755598884212211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2654337128503732589474807 3981505692755598884212211)
      ·
        refine ⟨5972258539133398326318317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981505692755598884212211 5972258539133398326318317)
        ·
          refine ⟨2239596952175024372369369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5972258539133398326318317 2239596952175024372369369)
          ·
            refine ⟨1679697714131268279277027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2239596952175024372369369 1679697714131268279277027)
            ·
              refine ⟨2519546571196902418915541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679697714131268279277027 2519546571196902418915541)
              ·
                refine ⟨59051872762427400443333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2519546571196902418915541 59051872762427400443333)
                ·
                  rfl

theorem cell22_1552542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1552542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552542 prefixEnd_1552542 := by exact prefixLift 1552542
  have htrace : WordTrace (prefixWord ++ tailWord_1552542) baseStart_1552542 baseEnd_1552542 := by
    simpa [prefixWord, tailWord_1552542, baseEnd_1552542] using wordTrace_append hprefix tailTrace_1552542
  have hstable : (prefixWord ++ tailWord_1552542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552542).length < 2 ^ (prefixWord ++ tailWord_1552542).sum := by decide
  have hdescent : baseEnd_1552542 < baseStart_1552542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552557 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1552557 : Nat := 118140960795 + 1552557 * 2 ^ 59
def prefixEnd_1552557 : Nat := 4983230072969 + 3 ^ 40 * 1552557 * 2
def baseEnd_1552557 : Nat := 531471989668391564864951

theorem tailTrace_1552557 : CollatzResearch.WordTrace tailWord_1552557 prefixEnd_1552557 531471989668391564864951 := by
  unfold tailWord_1552557
  simp only [CollatzResearch.WordTrace]
  refine ⟨56626405836358619470591925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37750937224239079647061283 56626405836358619470591925)
  ·
    refine ⟨5308725547158620575367993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56626405836358619470591925 5308725547158620575367993)
    ·
      refine ⟨3981544160368965431525995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5308725547158620575367993 3981544160368965431525995)
      ·
        refine ⟨5972316240553448147288993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981544160368965431525995 5972316240553448147288993)
        ·
          refine ⟨4479237180415086110466745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5972316240553448147288993 4479237180415086110466745)
          ·
            refine ⟨3359427885311314582850059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479237180415086110466745 3359427885311314582850059)
            ·
              refine ⟨5039141827966971874275089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359427885311314582850059 5039141827966971874275089)
              ·
                refine ⟨3779356370975228905706317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039141827966971874275089 3779356370975228905706317)
                ·
                  refine ⟨1417258639115710839639869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3779356370975228905706317 1417258639115710839639869)
                  ·
                    refine ⟨531471989668391564864951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417258639115710839639869 531471989668391564864951)
                    ·
                      rfl

theorem cell22_1552557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1552557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552557 prefixEnd_1552557 := by exact prefixLift 1552557
  have htrace : WordTrace (prefixWord ++ tailWord_1552557) baseStart_1552557 baseEnd_1552557 := by
    simpa [prefixWord, tailWord_1552557, baseEnd_1552557] using wordTrace_append hprefix tailTrace_1552557
  have hstable : (prefixWord ++ tailWord_1552557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552557).length < 2 ^ (prefixWord ++ tailWord_1552557).sum := by decide
  have hdescent : baseEnd_1552557 < baseStart_1552557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552615 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 6]
def baseStart_1552615 : Nat := 118140960795 + 1552615 * 2 ^ 59
def prefixEnd_1552615 : Nat := 4983230072969 + 3 ^ 40 * 1552615 * 2
def baseEnd_1552615 : Nat := 177163948084566248971591

theorem tailTrace_1552615 : CollatzResearch.WordTrace tailWord_1552615 prefixEnd_1552615 177163948084566248971591 := by
  unfold tailWord_1552615
  simp only [CollatzResearch.WordTrace]
  refine ⟨56628521270148495376203299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37752347513432330250802199 56628521270148495376203299)
  ·
    refine ⟨84942781905222743064304949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56628521270148495376203299 84942781905222743064304949)
    ·
      refine ⟨7963385803614632162278589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84942781905222743064304949 7963385803614632162278589)
      ·
        refine ⟨2986269676355487060854471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7963385803614632162278589 2986269676355487060854471)
        ·
          refine ⟨4479404514533230591281707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986269676355487060854471 4479404514533230591281707)
          ·
            refine ⟨6719106771799845886922561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4479404514533230591281707 6719106771799845886922561)
            ·
              refine ⟨5039330078849884415191921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719106771799845886922561 5039330078849884415191921)
              ·
                refine ⟨3779497559137413311393941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039330078849884415191921 3779497559137413311393941)
                ·
                  refine ⟨177163948084566248971591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3779497559137413311393941 177163948084566248971591)
                  ·
                    rfl

theorem cell22_1552615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 6].length) (baseStart_1552615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552615 prefixEnd_1552615 := by exact prefixLift 1552615
  have htrace : WordTrace (prefixWord ++ tailWord_1552615) baseStart_1552615 baseEnd_1552615 := by
    simpa [prefixWord, tailWord_1552615, baseEnd_1552615] using wordTrace_append hprefix tailTrace_1552615
  have hstable : (prefixWord ++ tailWord_1552615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552615).length < 2 ^ (prefixWord ++ tailWord_1552615).sum := by decide
  have hdescent : baseEnd_1552615 < baseStart_1552615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552630 : List Nat := [5, 1, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1552630 : Nat := 118140960795 + 1552630 * 2 ^ 59
def prefixEnd_1552630 : Nat := 4983230072969 + 3 ^ 40 * 1552630 * 2
def baseEnd_1552630 : Nat := 531496979060243707789727

theorem tailTrace_1552630 : CollatzResearch.WordTrace tailWord_1552630 prefixEnd_1552630 531496979060243707789727 := by
  unfold tailWord_1552630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539316772818384558624959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37752712243396101958666229 3539316772818384558624959)
  ·
    refine ⟨5308975159227576837937439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3539316772818384558624959 5308975159227576837937439)
    ·
      refine ⟨7963462738841365256906159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308975159227576837937439 7963462738841365256906159)
      ·
        refine ⟨11945194108262047885359239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7963462738841365256906159 11945194108262047885359239)
        ·
          refine ⟨17917791162393071828038859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11945194108262047885359239 17917791162393071828038859)
          ·
            refine ⟨26876686743589607742058289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17917791162393071828038859 26876686743589607742058289)
            ·
              refine ⟨20157515057692205806543717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26876686743589607742058289 20157515057692205806543717)
              ·
                refine ⟨3779534073317288588726947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20157515057692205806543717 3779534073317288588726947)
                ·
                  refine ⟨5669301109975932883090421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779534073317288588726947 5669301109975932883090421)
                  ·
                    refine ⟨531496979060243707789727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5669301109975932883090421 531496979060243707789727)
                    ·
                      rfl

theorem cell22_1552630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1552630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552630 prefixEnd_1552630 := by exact prefixLift 1552630
  have htrace : WordTrace (prefixWord ++ tailWord_1552630) baseStart_1552630 baseEnd_1552630 := by
    simpa [prefixWord, tailWord_1552630, baseEnd_1552630] using wordTrace_append hprefix tailTrace_1552630
  have hstable : (prefixWord ++ tailWord_1552630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552630).length < 2 ^ (prefixWord ++ tailWord_1552630).sum := by decide
  have hdescent : baseEnd_1552630 < baseStart_1552630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552675 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 5, 3]
def baseStart_1552675 : Nat := 118140960795 + 1552675 * 2 ^ 59
def prefixEnd_1552675 : Nat := 4983230072969 + 3 ^ 40 * 1552675 * 2
def baseEnd_1552675 : Nat := 531512383479878590414589

theorem tailTrace_1552675 : CollatzResearch.WordTrace tailWord_1552675 prefixEnd_1552675 531512383479878590414589 := by
  unfold tailWord_1552675
  simp only [CollatzResearch.WordTrace]
  refine ⟨56630709649931125623387479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37753806433287417082258319 56630709649931125623387479)
  ·
    refine ⟨84946064474896688435081219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56630709649931125623387479 84946064474896688435081219)
    ·
      refine ⟨127419096712345032652621829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84946064474896688435081219 127419096712345032652621829)
      ·
        refine ⟨23891080633564693622366593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127419096712345032652621829 23891080633564693622366593)
        ·
          refine ⟨17918310475173520216774945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23891080633564693622366593 17918310475173520216774945)
          ·
            refine ⟨13438732856380140162581209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17918310475173520216774945 13438732856380140162581209)
            ·
              refine ⟨10079049642285105121935907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13438732856380140162581209 10079049642285105121935907)
              ·
                refine ⟨15118574463427657682903861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10079049642285105121935907 15118574463427657682903861)
                ·
                  refine ⟨1417366355946342907772237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15118574463427657682903861 1417366355946342907772237)
                  ·
                    refine ⟨531512383479878590414589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417366355946342907772237 531512383479878590414589)
                    ·
                      rfl

theorem cell22_1552675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 3].length) (baseStart_1552675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552675 prefixEnd_1552675 := by exact prefixLift 1552675
  have htrace : WordTrace (prefixWord ++ tailWord_1552675) baseStart_1552675 baseEnd_1552675 := by
    simpa [prefixWord, tailWord_1552675, baseEnd_1552675] using wordTrace_append hprefix tailTrace_1552675
  have hstable : (prefixWord ++ tailWord_1552675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552675).length < 2 ^ (prefixWord ++ tailWord_1552675).sum := by decide
  have hdescent : baseEnd_1552675 < baseStart_1552675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552688 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_1552688 : Nat := 118140960795 + 1552688 * 2 ^ 59
def prefixEnd_1552688 : Nat := 4983230072969 + 3 ^ 40 * 1552688 * 2
def baseEnd_1552688 : Nat := 177172277881850296613183

theorem tailTrace_1552688 : CollatzResearch.WordTrace tailWord_1552688 prefixEnd_1552688 177172277881850296613183 := by
  unfold tailWord_1552688
  simp only [CollatzResearch.WordTrace]
  refine ⟨28315591899442014421805359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37754122532589352562407145 28315591899442014421805359)
  ·
    refine ⟨42473387849163021632708039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28315591899442014421805359 42473387849163021632708039)
    ·
      refine ⟨63710081773744532449062059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42473387849163021632708039 63710081773744532449062059)
      ·
        refine ⟨95565122660616798673593089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63710081773744532449062059 95565122660616798673593089)
        ·
          refine ⟨71673841995462599005194817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95565122660616798673593089 71673841995462599005194817)
          ·
            refine ⟨53755381496596949253896113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71673841995462599005194817 53755381496596949253896113)
            ·
              refine ⟨40316536122447711940422085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53755381496596949253896113 40316536122447711940422085)
              ·
                refine ⟨7559350522958945988829141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40316536122447711940422085 7559350522958945988829141)
                ·
                  refine ⟨177172277881850296613183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7559350522958945988829141 177172277881850296613183)
                  ·
                    rfl

theorem cell22_1552688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_1552688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552688 prefixEnd_1552688 := by exact prefixLift 1552688
  have htrace : WordTrace (prefixWord ++ tailWord_1552688) baseStart_1552688 baseEnd_1552688 := by
    simpa [prefixWord, tailWord_1552688, baseEnd_1552688] using wordTrace_append hprefix tailTrace_1552688
  have hstable : (prefixWord ++ tailWord_1552688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552688).length < 2 ^ (prefixWord ++ tailWord_1552688).sum := by decide
  have hdescent : baseEnd_1552688 < baseStart_1552688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552720 : List Nat := [2, 1, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_1552720 : Nat := 118140960795 + 1552720 * 2 ^ 59
def prefixEnd_1552720 : Nat := 4983230072969 + 3 ^ 40 * 1552720 * 2
def baseEnd_1552720 : Nat := 531527787899513473039451

theorem tailTrace_1552720 : CollatzResearch.WordTrace tailWord_1552720 prefixEnd_1552720 531527787899513473039451 := by
  unfold tailWord_1552720
  simp only [CollatzResearch.WordTrace]
  refine ⟨28316175467384049154387807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37754900623178732205850409 28316175467384049154387807)
  ·
    refine ⟨42474263201076073731581711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28316175467384049154387807 42474263201076073731581711)
    ·
      refine ⟨63711394801614110597372567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42474263201076073731581711 63711394801614110597372567)
      ·
        refine ⟨95567092202421165896058851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63711394801614110597372567 95567092202421165896058851)
        ·
          refine ⟨143350638303631748844088277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95567092202421165896058851 143350638303631748844088277)
          ·
            refine ⟨3359780585241369113533319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 143350638303631748844088277 3359780585241369113533319)
            ·
              refine ⟨5039670877862053670299979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359780585241369113533319 5039670877862053670299979)
              ·
                refine ⟨7559506316793080505449969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039670877862053670299979 7559506316793080505449969)
                ·
                  refine ⟨5669629737594810379087477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7559506316793080505449969 5669629737594810379087477)
                  ·
                    refine ⟨531527787899513473039451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5669629737594810379087477 531527787899513473039451)
                    ·
                      rfl

theorem cell22_1552720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_1552720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552720 prefixEnd_1552720 := by exact prefixLift 1552720
  have htrace : WordTrace (prefixWord ++ tailWord_1552720) baseStart_1552720 baseEnd_1552720 := by
    simpa [prefixWord, tailWord_1552720, baseEnd_1552720] using wordTrace_append hprefix tailTrace_1552720
  have hstable : (prefixWord ++ tailWord_1552720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552720).length < 2 ^ (prefixWord ++ tailWord_1552720).sum := by decide
  have hdescent : baseEnd_1552720 < baseStart_1552720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552735 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 3, 4]
def baseStart_1552735 : Nat := 118140960795 + 1552735 * 2 ^ 59
def prefixEnd_1552735 : Nat := 4983230072969 + 3 ^ 40 * 1552735 * 2
def baseEnd_1552735 : Nat := 531532922706058433914405

theorem tailTrace_1552735 : CollatzResearch.WordTrace tailWord_1552735 prefixEnd_1552735 531532922706058433914405 := by
  unfold tailWord_1552735
  simp only [CollatzResearch.WordTrace]
  refine ⟨56632898029713755870571659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37755265353142503913714439 56632898029713755870571659)
  ·
    refine ⟨84949347044570633805857489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56632898029713755870571659 84949347044570633805857489)
    ·
      refine ⟨63712010283427975354393117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84949347044570633805857489 63712010283427975354393117)
      ·
        refine ⟨23892003856285490757897419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63712010283427975354393117 23892003856285490757897419)
        ·
          refine ⟨35838005784428236136846129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23892003856285490757897419 35838005784428236136846129)
          ·
            refine ⟨26878504338321177102634597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35838005784428236136846129 26878504338321177102634597)
            ·
              refine ⟨5039719563435220706743987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26878504338321177102634597 5039719563435220706743987)
              ·
                refine ⟨7559579345152831060115981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039719563435220706743987 7559579345152831060115981)
                ·
                  refine ⟨2834842254432311647543493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7559579345152831060115981 2834842254432311647543493)
                  ·
                    refine ⟨531532922706058433914405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834842254432311647543493 531532922706058433914405)
                    ·
                      rfl

theorem cell22_1552735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 4].length) (baseStart_1552735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552735 prefixEnd_1552735 := by exact prefixLift 1552735
  have htrace : WordTrace (prefixWord ++ tailWord_1552735) baseStart_1552735 baseEnd_1552735 := by
    simpa [prefixWord, tailWord_1552735, baseEnd_1552735] using wordTrace_append hprefix tailTrace_1552735
  have hstable : (prefixWord ++ tailWord_1552735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552735).length < 2 ^ (prefixWord ++ tailWord_1552735).sum := by decide
  have hdescent : baseEnd_1552735 < baseStart_1552735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552752 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_1552752 : Nat := 118140960795 + 1552752 * 2 ^ 59
def prefixEnd_1552752 : Nat := 4983230072969 + 3 ^ 40 * 1552752 * 2
def baseEnd_1552752 : Nat := 531538742153476056239353

theorem tailTrace_1552752 : CollatzResearch.WordTrace tailWord_1552752 prefixEnd_1552752 531538742153476056239353 := by
  unfold tailWord_1552752
  simp only [CollatzResearch.WordTrace]
  refine ⟨28316759035326083886970255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37755678713768111849293673 28316759035326083886970255)
  ·
    refine ⟨42475138552989125830455383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28316759035326083886970255 42475138552989125830455383)
    ·
      refine ⟨63712707829483688745683075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42475138552989125830455383 63712707829483688745683075)
      ·
        refine ⟨95569061744225533118524613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63712707829483688745683075 95569061744225533118524613)
        ·
          refine ⟨17919199077042287459723365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95569061744225533118524613 17919199077042287459723365)
          ·
            refine ⟨3359849826945428898698131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17919199077042287459723365 3359849826945428898698131)
            ·
              refine ⟨5039774740418143348047197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3359849826945428898698131 5039774740418143348047197)
              ·
                refine ⟨1889915527656803755517699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5039774740418143348047197 1889915527656803755517699)
                ·
                  refine ⟨2834873291485205633276549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889915527656803755517699 2834873291485205633276549)
                  ·
                    refine ⟨531538742153476056239353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2834873291485205633276549 531538742153476056239353)
                    ·
                      rfl

theorem cell22_1552752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_1552752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552752 prefixEnd_1552752 := by exact prefixLift 1552752
  have htrace : WordTrace (prefixWord ++ tailWord_1552752) baseStart_1552752 baseEnd_1552752 := by
    simpa [prefixWord, tailWord_1552752, baseEnd_1552752] using wordTrace_append hprefix tailTrace_1552752
  have hstable : (prefixWord ++ tailWord_1552752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552752).length < 2 ^ (prefixWord ++ tailWord_1552752).sum := by decide
  have hdescent : baseEnd_1552752 < baseStart_1552752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552780 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_1552780 : Nat := 118140960795 + 1552780 * 2 ^ 59
def prefixEnd_1552780 : Nat := 4983230072969 + 3 ^ 40 * 1552780 * 2
def baseEnd_1552780 : Nat := 531548327125693316539267

theorem tailTrace_1552780 : CollatzResearch.WordTrace tailWord_1552780 prefixEnd_1552780 531548327125693316539267 := by
  unfold tailWord_1552780
  simp only [CollatzResearch.WordTrace]
  refine ⟨28317269657275364277979897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37756359543033819037306529 28317269657275364277979897)
  ·
    refine ⟨21237952242956523208484923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28317269657275364277979897 21237952242956523208484923)
    ·
      refine ⟨31856928364434784812727385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21237952242956523208484923 31856928364434784812727385)
      ·
        refine ⟨23892696273326088609545539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31856928364434784812727385 23892696273326088609545539)
        ·
          refine ⟨35839044409989132914318309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23892696273326088609545539 35839044409989132914318309)
          ·
            refine ⟨6719820826872962421434683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35839044409989132914318309 6719820826872962421434683)
            ·
              refine ⟨10079731240309443632152025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719820826872962421434683 10079731240309443632152025)
              ·
                refine ⟨7559798430232082724114019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10079731240309443632152025 7559798430232082724114019)
                ·
                  refine ⟨11339697645348124086171029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7559798430232082724114019 11339697645348124086171029)
                  ·
                    refine ⟨531548327125693316539267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11339697645348124086171029 531548327125693316539267)
                    ·
                      rfl

theorem cell22_1552780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_1552780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552780 prefixEnd_1552780 := by exact prefixLift 1552780
  have htrace : WordTrace (prefixWord ++ tailWord_1552780) baseStart_1552780 baseEnd_1552780 := by
    simpa [prefixWord, tailWord_1552780, baseEnd_1552780] using wordTrace_append hprefix tailTrace_1552780
  have hstable : (prefixWord ++ tailWord_1552780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552780).length < 2 ^ (prefixWord ++ tailWord_1552780).sum := by decide
  have hdescent : baseEnd_1552780 < baseStart_1552780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552855 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 6, 5]
def baseStart_1552855 : Nat := 118140960795 + 1552855 * 2 ^ 59
def prefixEnd_1552855 : Nat := 4983230072969 + 3 ^ 40 * 1552855 * 2
def baseEnd_1552855 : Nat := 531574001158418120914037

theorem tailTrace_1552855 : CollatzResearch.WordTrace tailWord_1552855 prefixEnd_1552855 531574001158418120914037 := by
  unfold tailWord_1552855
  simp only [CollatzResearch.WordTrace]
  refine ⟨56637274789279016364940019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37758183192852677576626679 56637274789279016364940019)
  ·
    refine ⟨84955912183918524547410029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56637274789279016364940019 84955912183918524547410029)
    ·
      refine ⟨31858467068969446705278761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84955912183918524547410029 31858467068969446705278761)
      ·
        refine ⟨23893850301727085028959071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31858467068969446705278761 23893850301727085028959071)
        ·
          refine ⟨35840775452590627543438607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23893850301727085028959071 35840775452590627543438607)
          ·
            refine ⟨53761163178885941315157911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35840775452590627543438607 53761163178885941315157911)
            ·
              refine ⟨80641744768328911972736867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53761163178885941315157911 80641744768328911972736867)
              ·
                refine ⟨120962617152493367959105301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80641744768328911972736867 120962617152493367959105301)
                ·
                  refine ⟨5670122679023126623083061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120962617152493367959105301 5670122679023126623083061)
                  ·
                    refine ⟨531574001158418120914037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5670122679023126623083061 531574001158418120914037)
                    ·
                      rfl

theorem cell22_1552855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_1552855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552855 prefixEnd_1552855 := by exact prefixLift 1552855
  have htrace : WordTrace (prefixWord ++ tailWord_1552855) baseStart_1552855 baseEnd_1552855 := by
    simpa [prefixWord, tailWord_1552855, baseEnd_1552855] using wordTrace_append hprefix tailTrace_1552855
  have hstable : (prefixWord ++ tailWord_1552855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552855).length < 2 ^ (prefixWord ++ tailWord_1552855).sum := by decide
  have hdescent : baseEnd_1552855 < baseStart_1552855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552861 : List Nat := [1, 4, 3, 1, 1, 1, 2, 5, 1, 3]
def baseStart_1552861 : Nat := 118140960795 + 1552861 * 2 ^ 59
def prefixEnd_1552861 : Nat := 4983230072969 + 3 ^ 40 * 1552861 * 2
def baseEnd_1552861 : Nat := 531576055081036105264019

theorem tailTrace_1552861 : CollatzResearch.WordTrace tailWord_1552861 prefixEnd_1552861 531576055081036105264019 := by
  unfold tailWord_1552861
  simp only [CollatzResearch.WordTrace]
  refine ⟨56637493627257279389658437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37758329084838186259772291 56637493627257279389658437)
  ·
    refine ⟨10619530055110739885560957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56637493627257279389658437 10619530055110739885560957)
    ·
      refine ⟨3982323770666527457085359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10619530055110739885560957 3982323770666527457085359)
      ·
        refine ⟨5973485655999791185628039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982323770666527457085359 5973485655999791185628039)
        ·
          refine ⟨8960228483999686778442059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5973485655999791185628039 8960228483999686778442059)
          ·
            refine ⟨13440342725999530167663089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8960228483999686778442059 13440342725999530167663089)
            ·
              refine ⟨10080257044499647625747317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13440342725999530167663089 10080257044499647625747317)
              ·
                refine ⟨945024097921841964913811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10080257044499647625747317 945024097921841964913811)
                ·
                  refine ⟨1417536146882762947370717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945024097921841964913811 1417536146882762947370717)
                  ·
                    refine ⟨531576055081036105264019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417536146882762947370717 531576055081036105264019)
                    ·
                      rfl

theorem cell22_1552861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_1552861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552861 prefixEnd_1552861 := by exact prefixLift 1552861
  have htrace : WordTrace (prefixWord ++ tailWord_1552861) baseStart_1552861 baseEnd_1552861 := by
    simpa [prefixWord, tailWord_1552861, baseEnd_1552861] using wordTrace_append hprefix tailTrace_1552861
  have hstable : (prefixWord ++ tailWord_1552861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552861).length < 2 ^ (prefixWord ++ tailWord_1552861).sum := by decide
  have hdescent : baseEnd_1552861 < baseStart_1552861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552874 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_1552874 : Nat := 118140960795 + 1552874 * 2 ^ 59
def prefixEnd_1552874 : Nat := 4983230072969 + 3 ^ 40 * 1552874 * 2
def baseEnd_1552874 : Nat := 177193501748902801562993

theorem tailTrace_1552874 : CollatzResearch.WordTrace tailWord_1552874 prefixEnd_1552874 177193501748902801562993 := by
  unfold tailWord_1552874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159491944052545652470419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37758645184140121739921117 14159491944052545652470419)
  ·
    refine ⟨21239237916078818478705629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14159491944052545652470419 21239237916078818478705629)
    ·
      refine ⟨7964714218529556929514611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21239237916078818478705629 7964714218529556929514611)
      ·
        refine ⟨11947071327794335394271917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7964714218529556929514611 11947071327794335394271917)
        ·
          refine ⟨4480151747922875772851969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11947071327794335394271917 4480151747922875772851969)
          ·
            refine ⟨3360113810942156829638977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480151747922875772851969 3360113810942156829638977)
            ·
              refine ⟨2520085358206617622229233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3360113810942156829638977 2520085358206617622229233)
              ·
                refine ⟨1890064018654963216671925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2520085358206617622229233 1890064018654963216671925)
                ·
                  refine ⟨177193501748902801562993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1890064018654963216671925 177193501748902801562993)
                  ·
                    rfl

theorem cell22_1552874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_1552874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552874 prefixEnd_1552874 := by exact prefixLift 1552874
  have htrace : WordTrace (prefixWord ++ tailWord_1552874) baseStart_1552874 baseEnd_1552874 := by
    simpa [prefixWord, tailWord_1552874, baseEnd_1552874] using wordTrace_append hprefix tailTrace_1552874
  have hstable : (prefixWord ++ tailWord_1552874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552874).length < 2 ^ (prefixWord ++ tailWord_1552874).sum := by decide
  have hdescent : baseEnd_1552874 < baseStart_1552874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552878 : List Nat := [4, 1, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1552878 : Nat := 118140960795 + 1552878 * 2 ^ 59
def prefixEnd_1552878 : Nat := 4983230072969 + 3 ^ 40 * 1552878 * 2
def baseEnd_1552878 : Nat := 531581874528453727588967

theorem tailTrace_1552878 : CollatzResearch.WordTrace tailWord_1552878 prefixEnd_1552878 531581874528453727588967 := by
  unfold tailWord_1552878
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079764208524461411628411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37758742445463794195351525 7079764208524461411628411)
  ·
    refine ⟨10619646312786692117442617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079764208524461411628411 10619646312786692117442617)
    ·
      refine ⟨7964734734590019088081963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10619646312786692117442617 7964734734590019088081963)
      ·
        refine ⟨11947102101885028632122945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7964734734590019088081963 11947102101885028632122945)
        ·
          refine ⟨8960326576413771474092209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11947102101885028632122945 8960326576413771474092209)
          ·
            refine ⟨6720244932310328605569157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8960326576413771474092209 6720244932310328605569157)
            ·
              refine ⟨1260045924808186613544217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6720244932310328605569157 1260045924808186613544217)
              ·
                refine ⟨945034443606139960158163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260045924808186613544217 945034443606139960158163)
                ·
                  refine ⟨1417551665409209940237245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945034443606139960158163 1417551665409209940237245)
                  ·
                    refine ⟨531581874528453727588967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417551665409209940237245 531581874528453727588967)
                    ·
                      rfl

theorem cell22_1552878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1552878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552878 prefixEnd_1552878 := by exact prefixLift 1552878
  have htrace : WordTrace (prefixWord ++ tailWord_1552878) baseStart_1552878 baseEnd_1552878 := by
    simpa [prefixWord, tailWord_1552878, baseEnd_1552878] using wordTrace_append hprefix tailTrace_1552878
  have hstable : (prefixWord ++ tailWord_1552878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552878).length < 2 ^ (prefixWord ++ tailWord_1552878).sum := by decide
  have hdescent : baseEnd_1552878 < baseStart_1552878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552917 : List Nat := [1, 3, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1552917 : Nat := 118140960795 + 1552917 * 2 ^ 59
def prefixEnd_1552917 : Nat := 4983230072969 + 3 ^ 40 * 1552917 * 2
def baseEnd_1552917 : Nat := 531595225025470625863847

theorem tailTrace_1552917 : CollatzResearch.WordTrace tailWord_1552917 prefixEnd_1552917 531595225025470625863847 := by
  unfold tailWord_1552917
  simp only [CollatzResearch.WordTrace]
  refine ⟨56639536115054400953697005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37759690743369600635798003 56639536115054400953697005)
  ·
    refine ⟨21239826043145400357636377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56639536115054400953697005 21239826043145400357636377)
    ·
      refine ⟨15929869532359050268227283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21239826043145400357636377 15929869532359050268227283)
      ·
        refine ⟨23894804298538575402340925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15929869532359050268227283 23894804298538575402340925)
        ·
          refine ⟨8960551611951965775877847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23894804298538575402340925 8960551611951965775877847)
          ·
            refine ⟨13440827417927948663816771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8960551611951965775877847 13440827417927948663816771)
            ·
              refine ⟨20161241126891922995725157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13440827417927948663816771 20161241126891922995725157)
              ·
                refine ⟨3780232711292235561698467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20161241126891922995725157 3780232711292235561698467)
                ·
                  refine ⟨5670349066938353342547701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3780232711292235561698467 5670349066938353342547701)
                  ·
                    refine ⟨531595225025470625863847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5670349066938353342547701 531595225025470625863847)
                    ·
                      rfl

theorem cell22_1552917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1552917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552917 prefixEnd_1552917 := by exact prefixLift 1552917
  have htrace : WordTrace (prefixWord ++ tailWord_1552917) baseStart_1552917 baseEnd_1552917 := by
    simpa [prefixWord, tailWord_1552917, baseEnd_1552917] using wordTrace_append hprefix tailTrace_1552917
  have hstable : (prefixWord ++ tailWord_1552917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552917).length < 2 ^ (prefixWord ++ tailWord_1552917).sum := by decide
  have hdescent : baseEnd_1552917 < baseStart_1552917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552936 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 4]
def baseStart_1552936 : Nat := 118140960795 + 1552936 * 2 ^ 59
def prefixEnd_1552936 : Nat := 4983230072969 + 3 ^ 40 * 1552936 * 2
def baseEnd_1552936 : Nat := 177200576371253636546263

theorem tailTrace_1552936 : CollatzResearch.WordTrace tailWord_1552936 prefixEnd_1552936 177200576371253636546263 := by
  unfold tailWord_1552936
  simp only [CollatzResearch.WordTrace]
  refine ⟨28320114550992783599319331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37760152734657044799092441 28320114550992783599319331)
  ·
    refine ⟨42480171826489175398978997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28320114550992783599319331 42480171826489175398978997)
    ·
      refine ⟨3982516108733360193654281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42480171826489175398978997 3982516108733360193654281)
      ·
        refine ⟨2986887081550020145240711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3982516108733360193654281 2986887081550020145240711)
        ·
          refine ⟨4480330622325030217861067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986887081550020145240711 4480330622325030217861067)
          ·
            refine ⟨6720495933487545326791601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480330622325030217861067 6720495933487545326791601)
            ·
              refine ⟨5040371950115658995093701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720495933487545326791601 5040371950115658995093701)
              ·
                refine ⟨945069740646686061580069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5040371950115658995093701 945069740646686061580069)
                ·
                  refine ⟨177200576371253636546263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945069740646686061580069 177200576371253636546263)
                  ·
                    rfl

theorem cell22_1552936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 4].length) (baseStart_1552936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552936 prefixEnd_1552936 := by exact prefixLift 1552936
  have htrace : WordTrace (prefixWord ++ tailWord_1552936) baseStart_1552936 baseEnd_1552936 := by
    simpa [prefixWord, tailWord_1552936, baseEnd_1552936] using wordTrace_append hprefix tailTrace_1552936
  have hstable : (prefixWord ++ tailWord_1552936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552936).length < 2 ^ (prefixWord ++ tailWord_1552936).sum := by decide
  have hdescent : baseEnd_1552936 < baseStart_1552936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552951 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 2, 3]
def baseStart_1552951 : Nat := 118140960795 + 1552951 * 2 ^ 59
def prefixEnd_1552951 : Nat := 4983230072969 + 3 ^ 40 * 1552951 * 2
def baseEnd_1552951 : Nat := 531606863920305870513743

theorem tailTrace_1552951 : CollatzResearch.WordTrace tailWord_1552951 prefixEnd_1552951 531606863920305870513743 := by
  unfold tailWord_1552951
  simp only [CollatzResearch.WordTrace]
  refine ⟨56640776196931224760434707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37760517464620816506956471 56640776196931224760434707)
  ·
    refine ⟨84961164295396837140652061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56640776196931224760434707 84961164295396837140652061)
    ·
      refine ⟨31860436610773813927744523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84961164295396837140652061 31860436610773813927744523)
      ·
        refine ⟨47790654916160720891616785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31860436610773813927744523 47790654916160720891616785)
        ·
          refine ⟨35842991187120540668712589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47790654916160720891616785 35842991187120540668712589)
          ·
            refine ⟨13441121695170202750767221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35842991187120540668712589 13441121695170202750767221)
            ·
              refine ⟨1260105158922206507884427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13441121695170202750767221 1260105158922206507884427)
              ·
                refine ⟨1890157738383309761826641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260105158922206507884427 1890157738383309761826641)
                ·
                  refine ⟨1417618303787482321369981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1890157738383309761826641 1417618303787482321369981)
                  ·
                    refine ⟨531606863920305870513743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417618303787482321369981 531606863920305870513743)
                    ·
                      rfl

theorem cell22_1552951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_1552951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552951 prefixEnd_1552951 := by exact prefixLift 1552951
  have htrace : WordTrace (prefixWord ++ tailWord_1552951) baseStart_1552951 baseEnd_1552951 := by
    simpa [prefixWord, tailWord_1552951, baseEnd_1552951] using wordTrace_append hprefix tailTrace_1552951
  have hstable : (prefixWord ++ tailWord_1552951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552951).length < 2 ^ (prefixWord ++ tailWord_1552951).sum := by decide
  have hdescent : baseEnd_1552951 < baseStart_1552951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552966 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1552966 : Nat := 118140960795 + 1552966 * 2 ^ 59
def prefixEnd_1552966 : Nat := 4983230072969 + 3 ^ 40 * 1552966 * 2
def baseEnd_1552966 : Nat := 531611998726850831388697

theorem tailTrace_1552966 : CollatzResearch.WordTrace tailWord_1552966 prefixEnd_1552966 531611998726850831388697 := by
  unfold tailWord_1552966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770041352871152572569711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37760882194584588214820501 1770041352871152572569711)
  ·
    refine ⟨2655062029306728858854567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770041352871152572569711 2655062029306728858854567)
    ·
      refine ⟨3982593043960093288281851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2655062029306728858854567 3982593043960093288281851)
      ·
        refine ⟨5973889565940139932422777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982593043960093288281851 5973889565940139932422777)
        ·
          refine ⟨4480417174455104949317083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5973889565940139932422777 4480417174455104949317083)
          ·
            refine ⟨6720625761682657423975625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4480417174455104949317083 6720625761682657423975625)
            ·
              refine ⟨5040469321261993067981719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6720625761682657423975625 5040469321261993067981719)
              ·
                refine ⟨7560703981892989601972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040469321261993067981719 7560703981892989601972579)
                ·
                  refine ⟨11341055972839484402958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7560703981892989601972579 11341055972839484402958869)
                  ·
                    refine ⟨531611998726850831388697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11341055972839484402958869 531611998726850831388697)
                    ·
                      rfl

theorem cell22_1552966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1552966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552966 prefixEnd_1552966 := by exact prefixLift 1552966
  have htrace : WordTrace (prefixWord ++ tailWord_1552966) baseStart_1552966 baseEnd_1552966 := by
    simpa [prefixWord, tailWord_1552966, baseEnd_1552966] using wordTrace_append hprefix tailTrace_1552966
  have hstable : (prefixWord ++ tailWord_1552966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552966).length < 2 ^ (prefixWord ++ tailWord_1552966).sum := by decide
  have hdescent : baseEnd_1552966 < baseStart_1552966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1552992 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_1552992 : Nat := 118140960795 + 1552992 * 2 ^ 59
def prefixEnd_1552992 : Nat := 4983230072969 + 3 ^ 40 * 1552992 * 2
def baseEnd_1552992 : Nat := 177206966352731810079539

theorem tailTrace_1552992 : CollatzResearch.WordTrace tailWord_1552992 prefixEnd_1552992 177206966352731810079539 := by
  unfold tailWord_1552992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28321135794891344381338615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37761514393188459175118153 28321135794891344381338615)
  ·
    refine ⟨42481703692337016572007923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28321135794891344381338615 42481703692337016572007923)
    ·
      refine ⟨63722555538505524858011885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42481703692337016572007923 63722555538505524858011885)
      ·
        refine ⟨23895958326939571821754457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63722555538505524858011885 23895958326939571821754457)
        ·
          refine ⟨17921968745204678866315843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23895958326939571821754457 17921968745204678866315843)
          ·
            refine ⟨26882953117807018299473765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17921968745204678866315843 26882953117807018299473765)
            ·
              refine ⟨5040553709588815931151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26882953117807018299473765 5040553709588815931151331)
              ·
                refine ⟨7560830564383223896726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040553709588815931151331 7560830564383223896726997)
                ·
                  refine ⟨177206966352731810079539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7560830564383223896726997 177206966352731810079539)
                  ·
                    rfl

theorem cell22_1552992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_1552992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1552992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1552992 prefixEnd_1552992 := by exact prefixLift 1552992
  have htrace : WordTrace (prefixWord ++ tailWord_1552992) baseStart_1552992 baseEnd_1552992 := by
    simpa [prefixWord, tailWord_1552992, baseEnd_1552992] using wordTrace_append hprefix tailTrace_1552992
  have hstable : (prefixWord ++ tailWord_1552992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1552992).length < 2 ^ (prefixWord ++ tailWord_1552992).sum := by decide
  have hdescent : baseEnd_1552992 < baseStart_1552992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1552992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553007 : List Nat := [1, 1, 2, 1, 3, 2, 2, 3, 2, 5]
def baseStart_1553007 : Nat := 118140960795 + 1553007 * 2 ^ 59
def prefixEnd_1553007 : Nat := 4983230072969 + 3 ^ 40 * 1553007 * 2
def baseEnd_1553007 : Nat := 531626033864740391113571

theorem tailTrace_1553007 : CollatzResearch.WordTrace tailWord_1553007 prefixEnd_1553007 531626033864740391113571 := by
  unfold tailWord_1553007
  simp only [CollatzResearch.WordTrace]
  refine ⟨56642818684728346324473275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37761879123152230882982183 56642818684728346324473275)
  ·
    refine ⟨84964228027092519486709913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56642818684728346324473275 84964228027092519486709913)
    ·
      refine ⟨63723171020319389615032435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84964228027092519486709913 63723171020319389615032435)
      ·
        refine ⟨95584756530479084422548653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63723171020319389615032435 95584756530479084422548653)
        ·
          refine ⟨35844283698929656658455745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95584756530479084422548653 35844283698929656658455745)
          ·
            refine ⟨26883212774197242493841809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35844283698929656658455745 26883212774197242493841809)
            ·
              refine ⟨20162409580647931870381357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26883212774197242493841809 20162409580647931870381357)
              ·
                refine ⟨7560903592742974451393009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20162409580647931870381357 7560903592742974451393009)
                ·
                  refine ⟨5670677694557230838544757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7560903592742974451393009 5670677694557230838544757)
                  ·
                    refine ⟨531626033864740391113571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5670677694557230838544757 531626033864740391113571)
                    ·
                      rfl

theorem cell22_1553007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_1553007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553007 prefixEnd_1553007 := by exact prefixLift 1553007
  have htrace : WordTrace (prefixWord ++ tailWord_1553007) baseStart_1553007 baseEnd_1553007 := by
    simpa [prefixWord, tailWord_1553007, baseEnd_1553007] using wordTrace_append hprefix tailTrace_1553007
  have hstable : (prefixWord ++ tailWord_1553007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553007).length < 2 ^ (prefixWord ++ tailWord_1553007).sum := by decide
  have hdescent : baseEnd_1553007 < baseStart_1553007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553084 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_1553084 : Nat := 118140960795 + 1553084 * 2 ^ 59
def prefixEnd_1553084 : Nat := 4983230072969 + 3 ^ 40 * 1553084 * 2
def baseEnd_1553084 : Nat := 531652392538337856938335

theorem tailTrace_1553084 : CollatzResearch.WordTrace tailWord_1553084 prefixEnd_1553084 531652392538337856938335 := by
  unfold tailWord_1553084
  simp only [CollatzResearch.WordTrace]
  refine ⟨28322813552724694237513153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37763751403632925650017537 28322813552724694237513153)
  ·
    refine ⟨21242110164543520678134865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28322813552724694237513153 21242110164543520678134865)
    ·
      refine ⟨15931582623407640508601149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21242110164543520678134865 15931582623407640508601149)
      ·
        refine ⟨5974343483777865190725431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15931582623407640508601149 5974343483777865190725431)
        ·
          refine ⟨8961515225666797786088147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974343483777865190725431 8961515225666797786088147)
          ·
            refine ⟨13442272838500196679132221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961515225666797786088147 13442272838500196679132221)
            ·
              refine ⟨5040852314437573754674583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13442272838500196679132221 5040852314437573754674583)
              ·
                refine ⟨7561278471656360632011875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040852314437573754674583 7561278471656360632011875)
                ·
                  refine ⟨11341917707484540948017813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7561278471656360632011875 11341917707484540948017813)
                  ·
                    refine ⟨531652392538337856938335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11341917707484540948017813 531652392538337856938335)
                    ·
                      rfl

theorem cell22_1553084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_1553084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553084 prefixEnd_1553084 := by exact prefixLift 1553084
  have htrace : WordTrace (prefixWord ++ tailWord_1553084) baseStart_1553084 baseEnd_1553084 := by
    simpa [prefixWord, tailWord_1553084, baseEnd_1553084] using wordTrace_append hprefix tailTrace_1553084
  have hstable : (prefixWord ++ tailWord_1553084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553084).length < 2 ^ (prefixWord ++ tailWord_1553084).sum := by decide
  have hdescent : baseEnd_1553084 < baseStart_1553084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553086 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 4, 3]
def baseStart_1553086 : Nat := 118140960795 + 1553086 * 2 ^ 59
def prefixEnd_1553086 : Nat := 4983230072969 + 3 ^ 40 * 1553086 * 2
def baseEnd_1553086 : Nat := 531653077179210518388329

theorem tailTrace_1553086 : CollatzResearch.WordTrace tailWord_1553086 prefixEnd_1553086 531653077179210518388329 := by
  unfold tailWord_1553086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080712506430267852074889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37763800034294761877732741 7080712506430267852074889)
  ·
    refine ⟨5310534379822700889056167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7080712506430267852074889 5310534379822700889056167)
    ·
      refine ⟨7965801569734051333584251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310534379822700889056167 7965801569734051333584251)
      ·
        refine ⟨11948702354601077000376377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7965801569734051333584251 11948702354601077000376377)
        ·
          refine ⟨8961526765950807750282283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11948702354601077000376377 8961526765950807750282283)
          ·
            refine ⟨13442290148926211625423425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8961526765950807750282283 13442290148926211625423425)
            ·
              refine ⟨10081717611694658719067569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13442290148926211625423425 10081717611694658719067569)
              ·
                refine ⟨7561288208770994039300677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10081717611694658719067569 7561288208770994039300677)
                ·
                  refine ⟨1417741539144561382368877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7561288208770994039300677 1417741539144561382368877)
                  ·
                    refine ⟨531653077179210518388329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417741539144561382368877 531653077179210518388329)
                    ·
                      rfl

theorem cell22_1553086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_1553086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553086 prefixEnd_1553086 := by exact prefixLift 1553086
  have htrace : WordTrace (prefixWord ++ tailWord_1553086) baseStart_1553086 baseEnd_1553086 := by
    simpa [prefixWord, tailWord_1553086, baseEnd_1553086] using wordTrace_append hprefix tailTrace_1553086
  have hstable : (prefixWord ++ tailWord_1553086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553086).length < 2 ^ (prefixWord ++ tailWord_1553086).sum := by decide
  have hdescent : baseEnd_1553086 < baseStart_1553086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553097 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_1553097 : Nat := 118140960795 + 1553097 * 2 ^ 59
def prefixEnd_1553097 : Nat := 4983230072969 + 3 ^ 40 * 1553097 * 2
def baseEnd_1553097 : Nat := 531656842704010156363295

theorem tailTrace_1553097 : CollatzResearch.WordTrace tailWord_1553097 prefixEnd_1553097 531656842704010156363295 := by
  unfold tailWord_1553097
  simp only [CollatzResearch.WordTrace]
  refine ⟨56646101254402291695249545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37764067502934861130166363 56646101254402291695249545)
  ·
    refine ⟨42484575940801718771437159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56646101254402291695249545 42484575940801718771437159)
    ·
      refine ⟨63726863911202578157155739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42484575940801718771437159 63726863911202578157155739)
      ·
        refine ⟨95590295866803867235733609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63726863911202578157155739 95590295866803867235733609)
        ·
          refine ⟨71692721900102900426800207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95590295866803867235733609 71692721900102900426800207)
          ·
            refine ⟨107539082850154350640200311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71692721900102900426800207 107539082850154350640200311)
            ·
              refine ⟨161308624275231525960300467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107539082850154350640200311 161308624275231525960300467)
              ·
                refine ⟨241962936412847288940450701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161308624275231525960300467 241962936412847288940450701)
                ·
                  refine ⟨90736101154817733352669013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241962936412847288940450701 90736101154817733352669013)
                  ·
                    refine ⟨531656842704010156363295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 90736101154817733352669013 531656842704010156363295)
                    ·
                      rfl

theorem cell22_1553097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_1553097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553097 prefixEnd_1553097 := by exact prefixLift 1553097
  have htrace : WordTrace (prefixWord ++ tailWord_1553097) baseStart_1553097 baseEnd_1553097 := by
    simpa [prefixWord, tailWord_1553097, baseEnd_1553097] using wordTrace_append hprefix tailTrace_1553097
  have hstable : (prefixWord ++ tailWord_1553097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553097).length < 2 ^ (prefixWord ++ tailWord_1553097).sum := by decide
  have hdescent : baseEnd_1553097 < baseStart_1553097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553189 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 8]
def baseStart_1553189 : Nat := 118140960795 + 1553189 * 2 ^ 59
def prefixEnd_1553189 : Nat := 4983230072969 + 3 ^ 40 * 1553189 * 2
def baseEnd_1553189 : Nat := 177229445394717527687671

theorem tailTrace_1553189 : CollatzResearch.WordTrace tailWord_1553189 prefixEnd_1553189 177229445394717527687671 := by
  unfold tailWord_1553189
  simp only [CollatzResearch.WordTrace]
  refine ⟨56649456770068991407598621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37766304513379327605065747 56649456770068991407598621)
  ·
    refine ⟨21243546288775871777849483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56649456770068991407598621 21243546288775871777849483)
    ·
      refine ⟨31865319433163807666774225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21243546288775871777849483 31865319433163807666774225)
      ·
        refine ⟨23898989574872855750080669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31865319433163807666774225 23898989574872855750080669)
        ·
          refine ⟨8962121090577320906280251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23898989574872855750080669 8962121090577320906280251)
          ·
            refine ⟨13443181635865981359420377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962121090577320906280251 13443181635865981359420377)
            ·
              refine ⟨10082386226899486019565283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13443181635865981359420377 10082386226899486019565283)
              ·
                refine ⟨15123579340349229029347925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10082386226899486019565283 15123579340349229029347925)
                ·
                  refine ⟨177229445394717527687671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15123579340349229029347925 177229445394717527687671)
                  ·
                    rfl

theorem cell22_1553189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_1553189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553189 prefixEnd_1553189 := by exact prefixLift 1553189
  have htrace : WordTrace (prefixWord ++ tailWord_1553189) baseStart_1553189 baseEnd_1553189 := by
    simpa [prefixWord, tailWord_1553189, baseEnd_1553189] using wordTrace_append hprefix tailTrace_1553189
  have hstable : (prefixWord ++ tailWord_1553189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553189).length < 2 ^ (prefixWord ++ tailWord_1553189).sum := by decide
  have hdescent : baseEnd_1553189 < baseStart_1553189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553208 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 1, 4]
def baseStart_1553208 : Nat := 118140960795 + 1553208 * 2 ^ 59
def prefixEnd_1553208 : Nat := 4983230072969 + 3 ^ 40 * 1553208 * 2
def baseEnd_1553208 : Nat := 531694840272442866837955

theorem tailTrace_1553208 : CollatzResearch.WordTrace tailWord_1553208 prefixEnd_1553208 531694840272442866837955 := by
  unfold tailWord_1553208
  simp only [CollatzResearch.WordTrace]
  refine ⟨28325074878500078826270139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37766766504666771768360185 28325074878500078826270139)
  ·
    refine ⟨42487612317750118239405209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28325074878500078826270139 42487612317750118239405209)
    ·
      refine ⟨31865709238312588679553907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42487612317750118239405209 31865709238312588679553907)
      ·
        refine ⟨47798563857468883019330861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31865709238312588679553907 47798563857468883019330861)
        ·
          refine ⟨17924461446550831132249073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47798563857468883019330861 17924461446550831132249073)
          ·
            refine ⟨13443346084913123349186805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17924461446550831132249073 13443346084913123349186805)
            ·
              refine ⟨1260313695460605313986263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13443346084913123349186805 1260313695460605313986263)
              ·
                refine ⟨1890470543190907970979395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1260313695460605313986263 1890470543190907970979395)
                ·
                  refine ⟨2835705814786361956469093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890470543190907970979395 2835705814786361956469093)
                  ·
                    refine ⟨531694840272442866837955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2835705814786361956469093 531694840272442866837955)
                    ·
                      rfl

theorem cell22_1553208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_1553208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553208 prefixEnd_1553208 := by exact prefixLift 1553208
  have htrace : WordTrace (prefixWord ++ tailWord_1553208) baseStart_1553208 baseEnd_1553208 := by
    simpa [prefixWord, tailWord_1553208, baseEnd_1553208] using wordTrace_append hprefix tailTrace_1553208
  have hstable : (prefixWord ++ tailWord_1553208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553208).length < 2 ^ (prefixWord ++ tailWord_1553208).sum := by decide
  have hdescent : baseEnd_1553208 < baseStart_1553208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553249 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_1553249 : Nat := 118140960795 + 1553249 * 2 ^ 59
def prefixEnd_1553249 : Nat := 4983230072969 + 3 ^ 40 * 1553249 * 2
def baseEnd_1553249 : Nat := 531708875410332426562829

theorem tailTrace_1553249 : CollatzResearch.WordTrace tailWord_1553249 prefixEnd_1553249 531708875410332426562829 := by
  unfold tailWord_1553249
  simp only [CollatzResearch.WordTrace]
  refine ⟨56651645149851621654782801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37767763433234414436521867 56651645149851621654782801)
  ·
    refine ⟨42488733862388716241087101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56651645149851621654782801 42488733862388716241087101)
    ·
      refine ⟨15933275198395768590407663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42488733862388716241087101 15933275198395768590407663)
      ·
        refine ⟨23899912797593652885611495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15933275198395768590407663 23899912797593652885611495)
        ·
          refine ⟨35849869196390479328417243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23899912797593652885611495 35849869196390479328417243)
          ·
            refine ⟨53774803794585718992625865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35849869196390479328417243 53774803794585718992625865)
            ·
              refine ⟨40331102845939289244469399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53774803794585718992625865 40331102845939289244469399)
              ·
                refine ⟨60496654268908933866704099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40331102845939289244469399 60496654268908933866704099)
                ·
                  refine ⟨90744981403363400800056149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60496654268908933866704099 90744981403363400800056149)
                  ·
                    refine ⟨531708875410332426562829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 90744981403363400800056149 531708875410332426562829)
                    ·
                      rfl

theorem cell22_1553249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_1553249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553249 prefixEnd_1553249 := by exact prefixLift 1553249
  have htrace : WordTrace (prefixWord ++ tailWord_1553249) baseStart_1553249 baseEnd_1553249 := by
    simpa [prefixWord, tailWord_1553249, baseEnd_1553249] using wordTrace_append hprefix tailTrace_1553249
  have hstable : (prefixWord ++ tailWord_1553249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553249).length < 2 ^ (prefixWord ++ tailWord_1553249).sum := by decide
  have hdescent : baseEnd_1553249 < baseStart_1553249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553283 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 3, 3]
def baseStart_1553283 : Nat := 118140960795 + 1553283 * 2 ^ 59
def prefixEnd_1553283 : Nat := 4983230072969 + 3 ^ 40 * 1553283 * 2
def baseEnd_1553283 : Nat := 531720514305167671212725

theorem tailTrace_1553283 : CollatzResearch.WordTrace tailWord_1553283 prefixEnd_1553283 531720514305167671212725 := by
  unfold tailWord_1553283
  simp only [CollatzResearch.WordTrace]
  refine ⟨56652885231728445461520503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37768590154485630307680335 56652885231728445461520503)
  ·
    refine ⟨84979327847592668192280755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56652885231728445461520503 84979327847592668192280755)
    ·
      refine ⟨127468991771389002288421133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84979327847592668192280755 127468991771389002288421133)
      ·
        refine ⟨47800871914270875858157925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127468991771389002288421133 47800871914270875858157925)
        ·
          refine ⟨8962663483925789223404611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47800871914270875858157925 8962663483925789223404611)
          ·
            refine ⟨13443995225888683835106917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8962663483925789223404611 13443995225888683835106917)
            ·
              refine ⟨2520749104854128219082547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13443995225888683835106917 2520749104854128219082547)
              ·
                refine ⟨3781123657281192328623821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2520749104854128219082547 3781123657281192328623821)
                ·
                  refine ⟨1417921371480447123233933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3781123657281192328623821 1417921371480447123233933)
                  ·
                    refine ⟨531720514305167671212725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1417921371480447123233933 531720514305167671212725)
                    ·
                      rfl

theorem cell22_1553283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 3].length) (baseStart_1553283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553283 prefixEnd_1553283 := by exact prefixLift 1553283
  have htrace : WordTrace (prefixWord ++ tailWord_1553283) baseStart_1553283 baseEnd_1553283 := by
    simpa [prefixWord, tailWord_1553283, baseEnd_1553283] using wordTrace_append hprefix tailTrace_1553283
  have hstable : (prefixWord ++ tailWord_1553283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553283).length < 2 ^ (prefixWord ++ tailWord_1553283).sum := by decide
  have hdescent : baseEnd_1553283 < baseStart_1553283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553302 : List Nat := [5, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1553302 : Nat := 118140960795 + 1553302 * 2 ^ 59
def prefixEnd_1553302 : Nat := 4983230072969 + 3 ^ 40 * 1553302 * 2
def baseEnd_1553302 : Nat := 59080779821495328331963

theorem tailTrace_1553302 : CollatzResearch.WordTrace tailWord_1553302 prefixEnd_1553302 59080779821495328331963 := by
  unfold tailWord_1553302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540848638666225731653885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37769052145773074470974773 3540848638666225731653885)
  ·
    refine ⟨1327818239499834649370207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3540848638666225731653885 1327818239499834649370207)
    ·
      refine ⟨1991727359249751974055311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1327818239499834649370207 1991727359249751974055311)
      ·
        refine ⟨2987591038874627961082967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1991727359249751974055311 2987591038874627961082967)
        ·
          refine ⟨4481386558311941941624451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2987591038874627961082967 4481386558311941941624451)
          ·
            refine ⟨6722079837467912912436677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481386558311941941624451 6722079837467912912436677)
            ·
              refine ⟨1260389969525233671081877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6722079837467912912436677 1260389969525233671081877)
              ·
                refine ⟨59080779821495328331963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1260389969525233671081877 59080779821495328331963)
                ·
                  rfl

theorem cell22_1553302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1553302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553302 prefixEnd_1553302 := by exact prefixLift 1553302
  have htrace : WordTrace (prefixWord ++ tailWord_1553302) baseStart_1553302 baseEnd_1553302 := by
    simpa [prefixWord, tailWord_1553302, baseEnd_1553302] using wordTrace_append hprefix tailTrace_1553302
  have hstable : (prefixWord ++ tailWord_1553302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553302).length < 2 ^ (prefixWord ++ tailWord_1553302).sum := by decide
  have hdescent : baseEnd_1553302 < baseStart_1553302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553373 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1553373 : Nat := 118140960795 + 1553373 * 2 ^ 59
def prefixEnd_1553373 : Nat := 4983230072969 + 3 ^ 40 * 1553373 * 2
def baseEnd_1553373 : Nat := 531751323144437436462449

theorem tailTrace_1553373 : CollatzResearch.WordTrace tailWord_1553373 prefixEnd_1553373 531751323144437436462449 := by
  unfold tailWord_1553373
  simp only [CollatzResearch.WordTrace]
  refine ⟨56656167801402390832296773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37770778534268260554864515 56656167801402390832296773)
  ·
    refine ⟨10623031462762948281055645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56656167801402390832296773 10623031462762948281055645)
    ·
      refine ⟨3983636798536105605395867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10623031462762948281055645 3983636798536105605395867)
      ·
        refine ⟨5975455197804158408093801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3983636798536105605395867 5975455197804158408093801)
        ·
          refine ⟨4481591398353118806070351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5975455197804158408093801 4481591398353118806070351)
          ·
            refine ⟨6722387097529678209105527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481591398353118806070351 6722387097529678209105527)
            ·
              refine ⟨10083580646294517313658291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6722387097529678209105527 10083580646294517313658291)
              ·
                refine ⟨15125370969441775970487437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10083580646294517313658291 15125370969441775970487437)
                ·
                  refine ⟨5672014113540665988932789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15125370969441775970487437 5672014113540665988932789)
                  ·
                    refine ⟨531751323144437436462449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5672014113540665988932789 531751323144437436462449)
                    ·
                      rfl

theorem cell22_1553373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1553373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553373 prefixEnd_1553373 := by exact prefixLift 1553373
  have htrace : WordTrace (prefixWord ++ tailWord_1553373) baseStart_1553373 baseEnd_1553373 := by
    simpa [prefixWord, tailWord_1553373, baseEnd_1553373] using wordTrace_append hprefix tailTrace_1553373
  have hstable : (prefixWord ++ tailWord_1553373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553373).length < 2 ^ (prefixWord ++ tailWord_1553373).sum := by decide
  have hdescent : baseEnd_1553373 < baseStart_1553373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553386 : List Nat := [3, 1, 3, 1, 2, 12]
def baseStart_1553386 : Nat := 118140960795 + 1553386 * 2 ^ 59
def prefixEnd_1553386 : Nat := 4983230072969 + 3 ^ 40 * 1553386 * 2
def baseEnd_1553386 : Nat := 6564886090248268344289

theorem tailTrace_1553386 : CollatzResearch.WordTrace tailWord_1553386 prefixEnd_1553386 6564886090248268344289 := by
  unfold tailWord_1553386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164160487588823513130003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37771094633570196035013341 14164160487588823513130003)
  ·
    refine ⟨21246240731383235269695005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14164160487588823513130003 21246240731383235269695005)
    ·
      refine ⟨7967340274268713226135627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21246240731383235269695005 7967340274268713226135627)
      ·
        refine ⟨11951010411403069839203441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7967340274268713226135627 11951010411403069839203441)
        ·
          refine ⟨8963257808552302379402581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11951010411403069839203441 8963257808552302379402581)
          ·
            refine ⟨6564886090248268344289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 8963257808552302379402581 6564886090248268344289)
            ·
              rfl

theorem cell22_1553386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 12].length) (baseStart_1553386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553386 prefixEnd_1553386 := by exact prefixLift 1553386
  have htrace : WordTrace (prefixWord ++ tailWord_1553386) baseStart_1553386 baseEnd_1553386 := by
    simpa [prefixWord, tailWord_1553386, baseEnd_1553386] using wordTrace_append hprefix tailTrace_1553386
  have hstable : (prefixWord ++ tailWord_1553386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553386).length < 2 ^ (prefixWord ++ tailWord_1553386).sum := by decide
  have hdescent : baseEnd_1553386 < baseStart_1553386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553426 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_1553426 : Nat := 118140960795 + 1553426 * 2 ^ 59
def prefixEnd_1553426 : Nat := 4983230072969 + 3 ^ 40 * 1553426 * 2
def baseEnd_1553426 : Nat := 177256488709187654962429

theorem tailTrace_1553426 : CollatzResearch.WordTrace tailWord_1553426 prefixEnd_1553426 177256488709187654962429 := by
  unfold tailWord_1553426
  simp only [CollatzResearch.WordTrace]
  refine ⟨14164525217552595220994033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37772067246806920589317421 14164525217552595220994033)
  ·
    refine ⟨10623393913164446415745525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14164525217552595220994033 10623393913164446415745525)
    ·
      refine ⟨995943179359166851476143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10623393913164446415745525 995943179359166851476143)
      ·
        refine ⟨1493914769038750277214215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995943179359166851476143 1493914769038750277214215)
        ·
          refine ⟨2240872153558125415821323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493914769038750277214215 2240872153558125415821323)
          ·
            refine ⟨3361308230337188123731985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2240872153558125415821323 3361308230337188123731985)
            ·
              refine ⟨2520981172752891092798989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3361308230337188123731985 2520981172752891092798989)
              ·
                refine ⟨945367939782334159799621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2520981172752891092798989 945367939782334159799621)
                ·
                  refine ⟨177256488709187654962429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945367939782334159799621 177256488709187654962429)
                  ·
                    rfl

theorem cell22_1553426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_1553426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553426 prefixEnd_1553426 := by exact prefixLift 1553426
  have htrace : WordTrace (prefixWord ++ tailWord_1553426) baseStart_1553426 baseEnd_1553426 := by
    simpa [prefixWord, tailWord_1553426, baseEnd_1553426] using wordTrace_append hprefix tailTrace_1553426
  have hstable : (prefixWord ++ tailWord_1553426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553426).length < 2 ^ (prefixWord ++ tailWord_1553426).sum := by decide
  have hdescent : baseEnd_1553426 < baseStart_1553426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553529 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_1553529 : Nat := 118140960795 + 1553529 * 2 ^ 59
def prefixEnd_1553529 : Nat := 4983230072969 + 3 ^ 40 * 1553529 * 2
def baseEnd_1553529 : Nat := 531804725132505029561971

theorem tailTrace_1553529 : CollatzResearch.WordTrace tailWord_1553529 prefixEnd_1553529 531804725132505029561971 := by
  unfold tailWord_1553529
  simp only [CollatzResearch.WordTrace]
  refine ⟨56661857588837229474975641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37774571725891486316650427 56661857588837229474975641)
  ·
    refine ⟨42496393191627922106231731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56661857588837229474975641 42496393191627922106231731)
    ·
      refine ⟨63744589787441883159347597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42496393191627922106231731 63744589787441883159347597)
      ·
        refine ⟨23904221170290706184755349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63744589787441883159347597 23904221170290706184755349)
        ·
          refine ⟨1120510367357376852410407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23904221170290706184755349 1120510367357376852410407)
          ·
            refine ⟨1680765551036065278615611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120510367357376852410407 1680765551036065278615611)
            ·
              refine ⟨2521148326554097917923417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1680765551036065278615611 2521148326554097917923417)
              ·
                refine ⟨1890861244915573438442563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2521148326554097917923417 1890861244915573438442563)
                ·
                  refine ⟨2836291867373360157663845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1890861244915573438442563 2836291867373360157663845)
                  ·
                    refine ⟨531804725132505029561971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836291867373360157663845 531804725132505029561971)
                    ·
                      rfl

theorem cell22_1553529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_1553529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553529 prefixEnd_1553529 := by exact prefixLift 1553529
  have htrace : WordTrace (prefixWord ++ tailWord_1553529) baseStart_1553529 baseEnd_1553529 := by
    simpa [prefixWord, tailWord_1553529, baseEnd_1553529] using wordTrace_append hprefix tailTrace_1553529
  have hstable : (prefixWord ++ tailWord_1553529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553529).length < 2 ^ (prefixWord ++ tailWord_1553529).sum := by decide
  have hdescent : baseEnd_1553529 < baseStart_1553529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553540 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_1553540 : Nat := 118140960795 + 1553540 * 2 ^ 59
def prefixEnd_1553540 : Nat := 4983230072969 + 3 ^ 40 * 1553540 * 2
def baseEnd_1553540 : Nat := 531808490657304667536937

theorem tailTrace_1553540 : CollatzResearch.WordTrace tailWord_1553540 prefixEnd_1553540 531808490657304667536937 := by
  unfold tailWord_1553540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28331129395898689176813037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37774839194531585569084049 28331129395898689176813037)
  ·
    refine ⟨10624173523462008441304889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28331129395898689176813037 10624173523462008441304889)
    ·
      refine ⟨7968130142596506330978667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10624173523462008441304889 7968130142596506330978667)
      ·
        refine ⟨11952195213894759496468001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7968130142596506330978667 11952195213894759496468001)
        ·
          refine ⟨8964146410421069622351001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11952195213894759496468001 8964146410421069622351001)
          ·
            refine ⟨6723109807815802216763251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8964146410421069622351001 6723109807815802216763251)
            ·
              refine ⟨10084664711723703325144877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6723109807815802216763251 10084664711723703325144877)
              ·
                refine ⟨3781749266896388746929329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10084664711723703325144877 3781749266896388746929329)
                ·
                  refine ⟨2836311950172291560196997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3781749266896388746929329 2836311950172291560196997)
                  ·
                    refine ⟨531808490657304667536937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2836311950172291560196997 531808490657304667536937)
                    ·
                      rfl

theorem cell22_1553540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_1553540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553540 prefixEnd_1553540 := by exact prefixLift 1553540
  have htrace : WordTrace (prefixWord ++ tailWord_1553540) baseStart_1553540 baseEnd_1553540 := by
    simpa [prefixWord, tailWord_1553540, baseEnd_1553540] using wordTrace_append hprefix tailTrace_1553540
  have hstable : (prefixWord ++ tailWord_1553540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553540).length < 2 ^ (prefixWord ++ tailWord_1553540).sum := by decide
  have hdescent : baseEnd_1553540 < baseStart_1553540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1553568 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1553568 : Nat := 118140960795 + 1553568 * 2 ^ 59
def prefixEnd_1553568 : Nat := 4983230072969 + 3 ^ 40 * 1553568 * 2
def baseEnd_1553568 : Nat := 531818075629521927836851

theorem tailTrace_1553568 : CollatzResearch.WordTrace tailWord_1553568 prefixEnd_1553568 531818075629521927836851 := by
  unfold tailWord_1553568
  simp only [CollatzResearch.WordTrace]
  refine ⟨28331640017847969567822679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37775520023797292757096905 28331640017847969567822679)
  ·
    refine ⟨42497460026771954351734019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28331640017847969567822679 42497460026771954351734019)
    ·
      refine ⟨63746190040157931527601029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42497460026771954351734019 63746190040157931527601029)
      ·
        refine ⟨11952410632529612161425193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63746190040157931527601029 11952410632529612161425193)
        ·
          refine ⟨8964307974397209121068895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11952410632529612161425193 8964307974397209121068895)
          ·
            refine ⟨13446461961595813681603343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8964307974397209121068895 13446461961595813681603343)
            ·
              refine ⟨20169692942393720522405015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13446461961595813681603343 20169692942393720522405015)
              ·
                refine ⟨30254539413590580783607523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20169692942393720522405015 30254539413590580783607523)
                ·
                  refine ⟨45381809120385871175411285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30254539413590580783607523 45381809120385871175411285)
                  ·
                    refine ⟨531818075629521927836851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 45381809120385871175411285 531818075629521927836851)
                    ·
                      rfl

theorem cell22_1553568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1553568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1553568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1553568 prefixEnd_1553568 := by exact prefixLift 1553568
  have htrace : WordTrace (prefixWord ++ tailWord_1553568) baseStart_1553568 baseEnd_1553568 := by
    simpa [prefixWord, tailWord_1553568, baseEnd_1553568] using wordTrace_append hprefix tailTrace_1553568
  have hstable : (prefixWord ++ tailWord_1553568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1553568).length < 2 ^ (prefixWord ++ tailWord_1553568).sum := by decide
  have hdescent : baseEnd_1553568 < baseStart_1553568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1553568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
