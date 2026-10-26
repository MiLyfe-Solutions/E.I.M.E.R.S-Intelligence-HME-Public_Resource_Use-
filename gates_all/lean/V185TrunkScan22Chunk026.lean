import V185TrunkScan22Chunk025

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_231578 : List Nat := [3, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_231578 : Nat := 118140960795 + 231578 * 2 ^ 59
def prefixEnd_231578 : Nat := 4983230072969 + 3 ^ 40 * 231578 * 2
def baseEnd_231578 : Nat := 26424627334888929713333

theorem tailTrace_231578 : CollatzResearch.WordTrace tailWord_231578 prefixEnd_231578 26424627334888929713333 := by
  unfold tailWord_231578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111585888759982804685847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5630895703359954145828925 2111585888759982804685847)
  ·
    refine ⟨3167378833139974207028771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111585888759982804685847 3167378833139974207028771)
    ·
      refine ⟨4751068249709961310543157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167378833139974207028771 4751068249709961310543157)
      ·
        refine ⟨445412648410308872863421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4751068249709961310543157 445412648410308872863421)
        ·
          refine ⟨167029743153865827323783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445412648410308872863421 167029743153865827323783)
          ·
            refine ⟨250544614730798740985675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167029743153865827323783 250544614730798740985675)
            ·
              refine ⟨375816922096198111478513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250544614730798740985675 375816922096198111478513)
              ·
                refine ⟨281862691572148583608885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 375816922096198111478513 281862691572148583608885)
                ·
                  refine ⟨26424627334888929713333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281862691572148583608885 26424627334888929713333)
                  ·
                    rfl

theorem cell22_231578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_231578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231578 prefixEnd_231578 := by exact prefixLift 231578
  have htrace : WordTrace (prefixWord ++ tailWord_231578) baseStart_231578 baseEnd_231578 := by
    simpa [prefixWord, tailWord_231578, baseEnd_231578] using wordTrace_append hprefix tailTrace_231578
  have hstable : (prefixWord ++ tailWord_231578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231578).length < 2 ^ (prefixWord ++ tailWord_231578).sum := by decide
  have hdescent : baseEnd_231578 < baseStart_231578 := by decide
  rcases family_descends (prefixWord ++ tailWord_231578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231589 : List Nat := [1, 3, 1, 2, 1, 3, 1, 6, 4]
def baseStart_231589 : Nat := 118140960795 + 231589 * 2 ^ 59
def prefixEnd_231589 : Nat := 4983230072969 + 3 ^ 40 * 231589 * 2
def baseEnd_231589 : Nat := 26425882509822142371655

theorem tailTrace_231589 : CollatzResearch.WordTrace tailWord_231589 prefixEnd_231589 26425882509822142371655 := by
  unfold tailWord_231589
  simp only [CollatzResearch.WordTrace]
  refine ⟨8446744758000080097393821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5631163172000053398262547 8446744758000080097393821)
  ·
    refine ⟨3167529284250030036522683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8446744758000080097393821 3167529284250030036522683)
    ·
      refine ⟨4751293926375045054784025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3167529284250030036522683 4751293926375045054784025)
      ·
        refine ⟨3563470444781283791088019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4751293926375045054784025 3563470444781283791088019)
        ·
          refine ⟨5345205667171925686632029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563470444781283791088019 5345205667171925686632029)
          ·
            refine ⟨2004452125189472132487011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5345205667171925686632029 2004452125189472132487011)
            ·
              refine ⟨3006678187784208198730517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004452125189472132487011 3006678187784208198730517)
              ·
                refine ⟨140938040052384759315493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3006678187784208198730517 140938040052384759315493)
                ·
                  refine ⟨26425882509822142371655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140938040052384759315493 26425882509822142371655)
                  ·
                    rfl

theorem cell22_231589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_231589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231589 prefixEnd_231589 := by exact prefixLift 231589
  have htrace : WordTrace (prefixWord ++ tailWord_231589) baseStart_231589 baseEnd_231589 := by
    simpa [prefixWord, tailWord_231589, baseEnd_231589] using wordTrace_append hprefix tailTrace_231589
  have hstable : (prefixWord ++ tailWord_231589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231589).length < 2 ^ (prefixWord ++ tailWord_231589).sum := by decide
  have hdescent : baseEnd_231589 < baseStart_231589 := by decide
  rcases family_descends (prefixWord ++ tailWord_231589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231602 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_231602 : Nat := 118140960795 + 231602 * 2 ^ 59
def prefixEnd_231602 : Nat := 4983230072969 + 3 ^ 40 * 231602 * 2
def baseEnd_231602 : Nat := 79282097695138726539925

theorem tailTrace_231602 : CollatzResearch.WordTrace tailWord_231602 prefixEnd_231602 79282097695138726539925 := by
  unfold tailWord_231602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111804726738245829404265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5631479271301988878411373 2111804726738245829404265)
  ·
    refine ⟨1583853545053684372053199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2111804726738245829404265 1583853545053684372053199)
    ·
      refine ⟨2375780317580526558079799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583853545053684372053199 2375780317580526558079799)
      ·
        refine ⟨3563670476370789837119699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375780317580526558079799 3563670476370789837119699)
        ·
          refine ⟨5345505714556184755679549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563670476370789837119699 5345505714556184755679549)
          ·
            refine ⟨2004564642958569283379831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5345505714556184755679549 2004564642958569283379831)
            ·
              refine ⟨3006846964437853925069747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004564642958569283379831 3006846964437853925069747)
              ·
                refine ⟨4510270446656780887604621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3006846964437853925069747 4510270446656780887604621)
                ·
                  refine ⟨1691351417496292832851733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4510270446656780887604621 1691351417496292832851733)
                  ·
                    refine ⟨79282097695138726539925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1691351417496292832851733 79282097695138726539925)
                    ·
                      rfl

theorem cell22_231602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_231602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231602 prefixEnd_231602 := by exact prefixLift 231602
  have htrace : WordTrace (prefixWord ++ tailWord_231602) baseStart_231602 baseEnd_231602 := by
    simpa [prefixWord, tailWord_231602, baseEnd_231602] using wordTrace_append hprefix tailTrace_231602
  have hstable : (prefixWord ++ tailWord_231602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231602).length < 2 ^ (prefixWord ++ tailWord_231602).sum := by decide
  have hdescent : baseEnd_231602 < baseStart_231602 := by decide
  rcases family_descends (prefixWord ++ tailWord_231602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231634 : List Nat := [3, 2, 2, 2, 1, 4, 8]
def baseStart_231634 : Nat := 118140960795 + 231634 * 2 ^ 59
def prefixEnd_231634 : Nat := 4983230072969 + 3 ^ 40 * 231634 * 2
def baseEnd_231634 : Nat := 2936779701818567027401

theorem tailTrace_231634 : CollatzResearch.WordTrace tailWord_231634 prefixEnd_231634 2936779701818567027401 := by
  unfold tailWord_231634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112096510709263195695489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5632257361891368521854637 2112096510709263195695489)
  ·
    refine ⟨1584072383031947396771617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2112096510709263195695489 1584072383031947396771617)
    ·
      refine ⟨1188054287273960547578713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584072383031947396771617 1188054287273960547578713)
      ·
        refine ⟨891040715455470410684035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188054287273960547578713 891040715455470410684035)
        ·
          refine ⟨1336561073183205616026053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891040715455470410684035 1336561073183205616026053)
          ·
            refine ⟨250605201221851053004885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1336561073183205616026053 250605201221851053004885)
            ·
              refine ⟨2936779701818567027401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 250605201221851053004885 2936779701818567027401)
              ·
                rfl

theorem cell22_231634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 8].length) (baseStart_231634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231634 prefixEnd_231634 := by exact prefixLift 231634
  have htrace : WordTrace (prefixWord ++ tailWord_231634) baseStart_231634 baseEnd_231634 := by
    simpa [prefixWord, tailWord_231634, baseEnd_231634] using wordTrace_append hprefix tailTrace_231634
  have hstable : (prefixWord ++ tailWord_231634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231634).length < 2 ^ (prefixWord ++ tailWord_231634).sum := by decide
  have hdescent : baseEnd_231634 < baseStart_231634 := by decide
  rcases family_descends (prefixWord ++ tailWord_231634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231638 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_231638 : Nat := 118140960795 + 231638 * 2 ^ 59
def prefixEnd_231638 : Nat := 4983230072969 + 3 ^ 40 * 231638 * 2
def baseEnd_231638 : Nat := 79294421230846632639815

theorem tailTrace_231638 : CollatzResearch.WordTrace tailWord_231638 prefixEnd_231638 79294421230846632639815 := by
  unfold tailWord_231638
  simp only [CollatzResearch.WordTrace]
  refine ⟨528033245926410091620473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5632354623215040977285045 528033245926410091620473)
  ·
    refine ⟨396024934444807568715355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 528033245926410091620473 396024934444807568715355)
    ·
      refine ⟨594037401667211353073033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 396024934444807568715355 594037401667211353073033)
      ·
        refine ⟨445528051250408514804775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594037401667211353073033 445528051250408514804775)
        ·
          refine ⟨668292076875612772207163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445528051250408514804775 668292076875612772207163)
          ·
            refine ⟨1002438115313419158310745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668292076875612772207163 1002438115313419158310745)
            ·
              refine ⟨751828586485064368733059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002438115313419158310745 751828586485064368733059)
              ·
                refine ⟨1127742879727596553099589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751828586485064368733059 1127742879727596553099589)
                ·
                  refine ⟨211451789948924353706173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1127742879727596553099589 211451789948924353706173)
                  ·
                    refine ⟨79294421230846632639815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211451789948924353706173 79294421230846632639815)
                    ·
                      rfl

theorem cell22_231638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_231638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231638 prefixEnd_231638 := by exact prefixLift 231638
  have htrace : WordTrace (prefixWord ++ tailWord_231638) baseStart_231638 baseEnd_231638 := by
    simpa [prefixWord, tailWord_231638, baseEnd_231638] using wordTrace_append hprefix tailTrace_231638
  have hstable : (prefixWord ++ tailWord_231638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231638).length < 2 ^ (prefixWord ++ tailWord_231638).sum := by decide
  have hdescent : baseEnd_231638 < baseStart_231638 := by decide
  rcases family_descends (prefixWord ++ tailWord_231638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231647 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_231647 : Nat := 118140960795 + 231647 * 2 ^ 59
def prefixEnd_231647 : Nat := 4983230072969 + 3 ^ 40 * 231647 * 2
def baseEnd_231647 : Nat := 79297502114773609164787

theorem tailTrace_231647 : CollatzResearch.WordTrace tailWord_231647 prefixEnd_231647 79297502114773609164787 := by
  unfold tailWord_231647
  simp only [CollatzResearch.WordTrace]
  refine ⟨8448860191789956003005195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5632573461193304002003463 8448860191789956003005195)
  ·
    refine ⟨12673290287684934004507793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8448860191789956003005195 12673290287684934004507793)
    ·
      refine ⟨9504967715763700503380845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12673290287684934004507793 9504967715763700503380845)
      ·
        refine ⟨3564362893411387688767817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9504967715763700503380845 3564362893411387688767817)
        ·
          refine ⟨2673272170058540766575863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3564362893411387688767817 2673272170058540766575863)
          ·
            refine ⟨4009908255087811149863795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673272170058540766575863 4009908255087811149863795)
            ·
              refine ⟨6014862382631716724795693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4009908255087811149863795 6014862382631716724795693)
              ·
                refine ⟨2255573393486893771798385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6014862382631716724795693 2255573393486893771798385)
                ·
                  refine ⟨1691680045115170328848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2255573393486893771798385 1691680045115170328848789)
                  ·
                    refine ⟨79297502114773609164787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1691680045115170328848789 79297502114773609164787)
                    ·
                      rfl

theorem cell22_231647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_231647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231647 prefixEnd_231647 := by exact prefixLift 231647
  have htrace : WordTrace (prefixWord ++ tailWord_231647) baseStart_231647 baseEnd_231647 := by
    simpa [prefixWord, tailWord_231647, baseEnd_231647] using wordTrace_append hprefix tailTrace_231647
  have hstable : (prefixWord ++ tailWord_231647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231647).length < 2 ^ (prefixWord ++ tailWord_231647).sum := by decide
  have hdescent : baseEnd_231647 < baseStart_231647 := by decide
  rcases family_descends (prefixWord ++ tailWord_231647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231651 : List Nat := [1, 1, 1, 8, 1, 1, 2, 7]
def baseStart_231651 : Nat := 118140960795 + 231651 * 2 ^ 59
def prefixEnd_231651 : Nat := 4983230072969 + 3 ^ 40 * 231651 * 2
def baseEnd_231651 : Nat := 8810985710724325784975

theorem tailTrace_231651 : CollatzResearch.WordTrace tailWord_231651 prefixEnd_231651 8810985710724325784975 := by
  unfold tailWord_231651
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449006083775464686150807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5632670722516976457433871 8449006083775464686150807)
  ·
    refine ⟨12673509125663197029226211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8449006083775464686150807 12673509125663197029226211)
    ·
      refine ⟨19010263688494795543839317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12673509125663197029226211 19010263688494795543839317)
      ·
        refine ⟨222776527599548385279367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 19010263688494795543839317 222776527599548385279367)
        ·
          refine ⟨334164791399322577919051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222776527599548385279367 334164791399322577919051)
          ·
            refine ⟨501247187098983866878577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334164791399322577919051 501247187098983866878577)
            ·
              refine ⟨375935390324237900158933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501247187098983866878577 375935390324237900158933)
              ·
                refine ⟨8810985710724325784975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 375935390324237900158933 8810985710724325784975)
                ·
                  rfl

theorem cell22_231651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 7].length) (baseStart_231651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231651 prefixEnd_231651 := by exact prefixLift 231651
  have htrace : WordTrace (prefixWord ++ tailWord_231651) baseStart_231651 baseEnd_231651 := by
    simpa [prefixWord, tailWord_231651, baseEnd_231651] using wordTrace_append hprefix tailTrace_231651
  have hstable : (prefixWord ++ tailWord_231651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231651).length < 2 ^ (prefixWord ++ tailWord_231651).sum := by decide
  have hdescent : baseEnd_231651 < baseStart_231651 := by decide
  rcases family_descends (prefixWord ++ tailWord_231651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231655 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 2, 3]
def baseStart_231655 : Nat := 118140960795 + 231655 * 2 ^ 59
def prefixEnd_231655 : Nat := 4983230072969 + 3 ^ 40 * 231655 * 2
def baseEnd_231655 : Nat := 79300240678264254964763

theorem tailTrace_231655 : CollatzResearch.WordTrace tailWord_231655 prefixEnd_231655 79300240678264254964763 := by
  unfold tailWord_231655
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449151975760973369296419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5632767983840648912864279 8449151975760973369296419)
  ·
    refine ⟨12673727963641460053944629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8449151975760973369296419 12673727963641460053944629)
    ·
      refine ⟨1188161996591386880057309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12673727963641460053944629 1188161996591386880057309)
      ·
        refine ⟨445560748721770080021491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1188161996591386880057309 445560748721770080021491)
        ·
          refine ⟨668341123082655120032237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445560748721770080021491 668341123082655120032237)
          ·
            refine ⟨250627921155995670012089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668341123082655120032237 250627921155995670012089)
            ·
              refine ⟨187970940866996752509067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250627921155995670012089 187970940866996752509067)
              ·
                refine ⟨281956411300495128763601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187970940866996752509067 281956411300495128763601)
                ·
                  refine ⟨211467308475371346572701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 281956411300495128763601 211467308475371346572701)
                  ·
                    refine ⟨79300240678264254964763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211467308475371346572701 79300240678264254964763)
                    ·
                      rfl

theorem cell22_231655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_231655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231655 prefixEnd_231655 := by exact prefixLift 231655
  have htrace : WordTrace (prefixWord ++ tailWord_231655) baseStart_231655 baseEnd_231655 := by
    simpa [prefixWord, tailWord_231655, baseEnd_231655] using wordTrace_append hprefix tailTrace_231655
  have hstable : (prefixWord ++ tailWord_231655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231655).length < 2 ^ (prefixWord ++ tailWord_231655).sum := by decide
  have hdescent : baseEnd_231655 < baseStart_231655 := by decide
  rcases family_descends (prefixWord ++ tailWord_231655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231694 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_231694 : Nat := 118140960795 + 231694 * 2 ^ 59
def prefixEnd_231694 : Nat := 4983230072969 + 3 ^ 40 * 231694 * 2
def baseEnd_231694 : Nat := 79313591175281153239643

theorem tailTrace_231694 : CollatzResearch.WordTrace tailWord_231694 prefixEnd_231694 79313591175281153239643 := by
  unfold tailWord_231694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1056321802827460378745767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5633716281746455353310757 1056321802827460378745767)
  ·
    refine ⟨1584482704241190568118651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1056321802827460378745767 1584482704241190568118651)
    ·
      refine ⟨2376724056361785852177977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584482704241190568118651 2376724056361785852177977)
      ·
        refine ⟨1782543042271339389133483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2376724056361785852177977 1782543042271339389133483)
        ·
          refine ⟨2673814563407009083700225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782543042271339389133483 2673814563407009083700225)
          ·
            refine ⟨2005360922555256812775169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2673814563407009083700225 2005360922555256812775169)
            ·
              refine ⟨1504020691916442609581377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005360922555256812775169 1504020691916442609581377)
              ·
                refine ⟨1128015518937331957186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504020691916442609581377 1128015518937331957186033)
                ·
                  refine ⟨846011639202998967889525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1128015518937331957186033 846011639202998967889525)
                  ·
                    refine ⟨79313591175281153239643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 846011639202998967889525 79313591175281153239643)
                    ·
                      rfl

theorem cell22_231694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_231694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231694 prefixEnd_231694 := by exact prefixLift 231694
  have htrace : WordTrace (prefixWord ++ tailWord_231694) baseStart_231694 baseEnd_231694 := by
    simpa [prefixWord, tailWord_231694, baseEnd_231694] using wordTrace_append hprefix tailTrace_231694
  have hstable : (prefixWord ++ tailWord_231694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231694).length < 2 ^ (prefixWord ++ tailWord_231694).sum := by decide
  have hdescent : baseEnd_231694 < baseStart_231694 := by decide
  rcases family_descends (prefixWord ++ tailWord_231694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231756 : List Nat := [2, 2, 1, 3, 2, 1, 3, 1, 4, 3]
def baseStart_231756 : Nat := 118140960795 + 231756 * 2 ^ 59
def prefixEnd_231756 : Nat := 4983230072969 + 3 ^ 40 * 231756 * 2
def baseEnd_231756 : Nat := 79334815042333658189453

theorem tailTrace_231756 : CollatzResearch.WordTrace tailWord_231756 prefixEnd_231756 79334815042333658189453 := by
  unfold tailWord_231756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226417874197533809361561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5635223832263378412482081 4226417874197533809361561)
  ·
    refine ⟨3169813405648150357021171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4226417874197533809361561 3169813405648150357021171)
    ·
      refine ⟨4754720108472225535531757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3169813405648150357021171 4754720108472225535531757)
      ·
        refine ⟨1783020040677084575824409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4754720108472225535531757 1783020040677084575824409)
        ·
          refine ⟨1337265030507813431868307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783020040677084575824409 1337265030507813431868307)
          ·
            refine ⟨2005897545761720147802461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337265030507813431868307 2005897545761720147802461)
            ·
              refine ⟨752211579660645055425923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2005897545761720147802461 752211579660645055425923)
              ·
                refine ⟨1128317369490967583138885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752211579660645055425923 1128317369490967583138885)
                ·
                  refine ⟨211559506779556421838541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1128317369490967583138885 211559506779556421838541)
                  ·
                    refine ⟨79334815042333658189453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211559506779556421838541 79334815042333658189453)
                    ·
                      rfl

theorem cell22_231756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_231756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231756 prefixEnd_231756 := by exact prefixLift 231756
  have htrace : WordTrace (prefixWord ++ tailWord_231756) baseStart_231756 baseEnd_231756 := by
    simpa [prefixWord, tailWord_231756, baseEnd_231756] using wordTrace_append hprefix tailTrace_231756
  have hstable : (prefixWord ++ tailWord_231756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231756).length < 2 ^ (prefixWord ++ tailWord_231756).sum := by decide
  have hdescent : baseEnd_231756 < baseStart_231756 := by decide
  rcases family_descends (prefixWord ++ tailWord_231756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231786 : List Nat := [3, 1, 3, 3, 1, 2, 1, 8]
def baseStart_231786 : Nat := 118140960795 + 231786 * 2 ^ 59
def prefixEnd_231786 : Nat := 4983230072969 + 3 ^ 40 * 231786 * 2
def baseEnd_231786 : Nat := 8816120517269286659929

theorem tailTrace_231786 : CollatzResearch.WordTrace tailWord_231786 prefixEnd_231786 8816120517269286659929 := by
  unfold tailWord_231786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113482484571595685578803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5635953292190921828210141 2113482484571595685578803)
  ·
    refine ⟨3170223726857393528368205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2113482484571595685578803 3170223726857393528368205)
    ·
      refine ⟨1188833897571522573138077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3170223726857393528368205 1188833897571522573138077)
      ·
        refine ⟨445812711589320964926779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1188833897571522573138077 445812711589320964926779)
        ·
          refine ⟨668719067383981447390169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 445812711589320964926779 668719067383981447390169)
          ·
            refine ⟨501539300537986085542627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 668719067383981447390169 501539300537986085542627)
            ·
              refine ⟨752308950806979128313941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 501539300537986085542627 752308950806979128313941)
              ·
                refine ⟨8816120517269286659929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 752308950806979128313941 8816120517269286659929)
                ·
                  rfl

theorem cell22_231786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_231786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231786 prefixEnd_231786 := by exact prefixLift 231786
  have htrace : WordTrace (prefixWord ++ tailWord_231786) baseStart_231786 baseEnd_231786 := by
    simpa [prefixWord, tailWord_231786, baseEnd_231786] using wordTrace_append hprefix tailTrace_231786
  have hstable : (prefixWord ++ tailWord_231786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231786).length < 2 ^ (prefixWord ++ tailWord_231786).sum := by decide
  have hdescent : baseEnd_231786 < baseStart_231786 := by decide
  rcases family_descends (prefixWord ++ tailWord_231786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231829 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_231829 : Nat := 118140960795 + 231829 * 2 ^ 59
def prefixEnd_231829 : Nat := 4983230072969 + 3 ^ 40 * 231829 * 2
def baseEnd_231829 : Nat := 79359804434185801114229

theorem tailTrace_231829 : CollatzResearch.WordTrace tailWord_231829 prefixEnd_231829 79359804434185801114229 := by
  unfold tailWord_231829
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455498277130601086130541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5636998851420400724087027 8455498277130601086130541)
  ·
    refine ⟨3170811853923975407298953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8455498277130601086130541 3170811853923975407298953)
    ·
      refine ⟨2378108890442981555474215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3170811853923975407298953 2378108890442981555474215)
      ·
        refine ⟨3567163335664472333211323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378108890442981555474215 3567163335664472333211323)
        ·
          refine ⟨5350745003496708499816985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567163335664472333211323 5350745003496708499816985)
          ·
            refine ⟨4013058752622531374862739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5350745003496708499816985 4013058752622531374862739)
            ·
              refine ⟨6019588128933797062294109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013058752622531374862739 6019588128933797062294109)
              ·
                refine ⟨2257345548350173898360291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6019588128933797062294109 2257345548350173898360291)
                ·
                  refine ⟨3386018322525260847540437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2257345548350173898360291 3386018322525260847540437)
                  ·
                    refine ⟨79359804434185801114229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3386018322525260847540437 79359804434185801114229)
                    ·
                      rfl

theorem cell22_231829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_231829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231829 prefixEnd_231829 := by exact prefixLift 231829
  have htrace : WordTrace (prefixWord ++ tailWord_231829) baseStart_231829 baseEnd_231829 := by
    simpa [prefixWord, tailWord_231829, baseEnd_231829] using wordTrace_append hprefix tailTrace_231829
  have hstable : (prefixWord ++ tailWord_231829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231829).length < 2 ^ (prefixWord ++ tailWord_231829).sum := by decide
  have hdescent : baseEnd_231829 < baseStart_231829 := by decide
  rcases family_descends (prefixWord ++ tailWord_231829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_231987 : List Nat := [1, 1, 1, 2, 4, 2, 5, 2, 1, 3]
def baseStart_231987 : Nat := 118140960795 + 231987 * 2 ^ 59
def prefixEnd_231987 : Nat := 4983230072969 + 3 ^ 40 * 231987 * 2
def baseEnd_231987 : Nat := 79413891063126055663745

theorem tailTrace_231987 : CollatzResearch.WordTrace tailWord_231987 prefixEnd_231987 79413891063126055663745 := by
  unfold tailWord_231987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461261010558194070382215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5640840673705462713588143 8461261010558194070382215)
  ·
    refine ⟨12691891515837291105573323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8461261010558194070382215 12691891515837291105573323)
    ·
      refine ⟨19037837273755936658359985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12691891515837291105573323 19037837273755936658359985)
      ·
        refine ⟨14278377955316952493769989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19037837273755936658359985 14278377955316952493769989)
        ·
          refine ⟨2677195866621928592581873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14278377955316952493769989 2677195866621928592581873)
          ·
            refine ⟨2007896899966446444436405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677195866621928592581873 2007896899966446444436405)
            ·
              refine ⟨188240334371854354165913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2007896899966446444436405 188240334371854354165913)
              ·
                refine ⟨141180250778890765624435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188240334371854354165913 141180250778890765624435)
                ·
                  refine ⟨211770376168336148436653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141180250778890765624435 211770376168336148436653)
                  ·
                    refine ⟨79413891063126055663745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211770376168336148436653 79413891063126055663745)
                    ·
                      rfl

theorem cell22_231987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 2, 1, 3].length) (baseStart_231987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_231987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_231987 prefixEnd_231987 := by exact prefixLift 231987
  have htrace : WordTrace (prefixWord ++ tailWord_231987) baseStart_231987 baseEnd_231987 := by
    simpa [prefixWord, tailWord_231987, baseEnd_231987] using wordTrace_append hprefix tailTrace_231987
  have hstable : (prefixWord ++ tailWord_231987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_231987).length < 2 ^ (prefixWord ++ tailWord_231987).sum := by decide
  have hdescent : baseEnd_231987 < baseStart_231987 := by decide
  rcases family_descends (prefixWord ++ tailWord_231987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232011 : List Nat := [1, 1, 1, 1, 3, 1, 4, 4, 6]
def baseStart_232011 : Nat := 118140960795 + 232011 * 2 ^ 59
def prefixEnd_232011 : Nat := 4983230072969 + 3 ^ 40 * 232011 * 2
def baseEnd_232011 : Nat := 26474035584532664354557

theorem tailTrace_232011 : CollatzResearch.WordTrace tailWord_232011 prefixEnd_232011 26474035584532664354557 := by
  unfold tailWord_232011
  simp only [CollatzResearch.WordTrace]
  refine ⟨8462136362471246169255887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5641424241647497446170591 8462136362471246169255887)
  ·
    refine ⟨12693204543706869253883831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8462136362471246169255887 12693204543706869253883831)
    ·
      refine ⟨19039806815560303880825747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12693204543706869253883831 19039806815560303880825747)
      ·
        refine ⟨28559710223340455821238621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039806815560303880825747 28559710223340455821238621)
        ·
          refine ⟨10709891333752670932964483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28559710223340455821238621 10709891333752670932964483)
          ·
            refine ⟨16064837000629006399446725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709891333752670932964483 16064837000629006399446725)
            ·
              refine ⟨3012156937617938699896261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16064837000629006399446725 3012156937617938699896261)
              ·
                refine ⟨564779425803363506230549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3012156937617938699896261 564779425803363506230549)
                ·
                  refine ⟨26474035584532664354557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 564779425803363506230549 26474035584532664354557)
                  ·
                    rfl

theorem cell22_232011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_232011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232011 prefixEnd_232011 := by exact prefixLift 232011
  have htrace : WordTrace (prefixWord ++ tailWord_232011) baseStart_232011 baseEnd_232011 := by
    simpa [prefixWord, tailWord_232011, baseEnd_232011] using wordTrace_append hprefix tailTrace_232011
  have hstable : (prefixWord ++ tailWord_232011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232011).length < 2 ^ (prefixWord ++ tailWord_232011).sum := by decide
  have hdescent : baseEnd_232011 < baseStart_232011 := by decide
  rcases family_descends (prefixWord ++ tailWord_232011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232041 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_232041 : Nat := 118140960795 + 232041 * 2 ^ 59
def prefixEnd_232041 : Nat := 4983230072969 + 3 ^ 40 * 232041 * 2
def baseEnd_232041 : Nat := 79432376366687914813579

theorem tailTrace_232041 : CollatzResearch.WordTrace tailWord_232041 prefixEnd_232041 79432376366687914813579 := by
  unfold tailWord_232041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463230552362561292847977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5642153701575040861898651 8463230552362561292847977)
  ·
    refine ⟨6347422914271920969635983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8463230552362561292847977 6347422914271920969635983)
    ·
      refine ⟨9521134371407881454453975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6347422914271920969635983 9521134371407881454453975)
      ·
        refine ⟨14281701557111822181680963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521134371407881454453975 14281701557111822181680963)
        ·
          refine ⟨21422552335667733272521445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14281701557111822181680963 21422552335667733272521445)
          ·
            refine ⟨4016728562937699988597771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21422552335667733272521445 4016728562937699988597771)
            ·
              refine ⟨6025092844406549982896657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4016728562937699988597771 6025092844406549982896657)
              ·
                refine ⟨4518819633304912487172493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025092844406549982896657 4518819633304912487172493)
                ·
                  refine ⟨1694557362489342182689685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4518819633304912487172493 1694557362489342182689685)
                  ·
                    refine ⟨79432376366687914813579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1694557362489342182689685 79432376366687914813579)
                    ·
                      rfl

theorem cell22_232041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_232041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232041 prefixEnd_232041 := by exact prefixLift 232041
  have htrace : WordTrace (prefixWord ++ tailWord_232041) baseStart_232041 baseEnd_232041 := by
    simpa [prefixWord, tailWord_232041, baseEnd_232041] using wordTrace_append hprefix tailTrace_232041
  have hstable : (prefixWord ++ tailWord_232041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232041).length < 2 ^ (prefixWord ++ tailWord_232041).sum := by decide
  have hdescent : baseEnd_232041 < baseStart_232041 := by decide
  rcases family_descends (prefixWord ++ tailWord_232041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232060 : List Nat := [2, 2, 2, 1, 1, 2, 4, 3, 2, 3]
def baseStart_232060 : Nat := 118140960795 + 232060 * 2 ^ 59
def prefixEnd_232060 : Nat := 4983230072969 + 3 ^ 40 * 232060 * 2
def baseEnd_232060 : Nat := 79438880454978198588521

theorem tailTrace_232060 : CollatzResearch.WordTrace tailWord_232060 prefixEnd_232060 79438880454978198588521 := by
  unfold tailWord_232060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4231961769646863768894817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5642615692862485025193089 4231961769646863768894817)
  ·
    refine ⟨3173971327235147826671113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4231961769646863768894817 3173971327235147826671113)
    ·
      refine ⟨2380478495426360870003335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3173971327235147826671113 2380478495426360870003335)
      ·
        refine ⟨3570717743139541305005003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2380478495426360870003335 3570717743139541305005003)
        ·
          refine ⟨5356076614709311957507505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570717743139541305005003 5356076614709311957507505)
          ·
            refine ⟨4017057461031983968130629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5356076614709311957507505 4017057461031983968130629)
            ·
              refine ⟨753198273943496994024493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4017057461031983968130629 753198273943496994024493)
              ·
                refine ⟨282449352728811372759185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 753198273943496994024493 282449352728811372759185)
                ·
                  refine ⟨211837014546608529569389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282449352728811372759185 211837014546608529569389)
                  ·
                    refine ⟨79438880454978198588521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 211837014546608529569389 79438880454978198588521)
                    ·
                      rfl

theorem cell22_232060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_232060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232060 prefixEnd_232060 := by exact prefixLift 232060
  have htrace : WordTrace (prefixWord ++ tailWord_232060) baseStart_232060 baseEnd_232060 := by
    simpa [prefixWord, tailWord_232060, baseEnd_232060] using wordTrace_append hprefix tailTrace_232060
  have hstable : (prefixWord ++ tailWord_232060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232060).length < 2 ^ (prefixWord ++ tailWord_232060).sum := by decide
  have hdescent : baseEnd_232060 < baseStart_232060 := by decide
  rcases family_descends (prefixWord ++ tailWord_232060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232090 : List Nat := [3, 1, 1, 6, 1, 1, 9]
def baseStart_232090 : Nat := 118140960795 + 232090 * 2 ^ 59
def prefixEnd_232090 : Nat := 4983230072969 + 3 ^ 40 * 232090 * 2
def baseEnd_232090 : Nat := 2942561113632152605127

theorem tailTrace_232090 : CollatzResearch.WordTrace tailWord_232090 prefixEnd_232090 2942561113632152605127 := by
  unfold tailWord_232090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116254432296260665345431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5643345152790028440921149 2116254432296260665345431)
  ·
    refine ⟨3174381648444390998018147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116254432296260665345431 3174381648444390998018147)
    ·
      refine ⟨4761572472666586497027221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174381648444390998018147 4761572472666586497027221)
      ·
        refine ⟨223198709656246242048151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4761572472666586497027221 223198709656246242048151)
        ·
          refine ⟨334798064484369363072227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223198709656246242048151 334798064484369363072227)
          ·
            refine ⟨502197096726554044608341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334798064484369363072227 502197096726554044608341)
            ·
              refine ⟨2942561113632152605127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 502197096726554044608341 2942561113632152605127)
              ·
                rfl

theorem cell22_232090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 9].length) (baseStart_232090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232090 prefixEnd_232090 := by exact prefixLift 232090
  have htrace : WordTrace (prefixWord ++ tailWord_232090) baseStart_232090 baseEnd_232090 := by
    simpa [prefixWord, tailWord_232090, baseEnd_232090] using wordTrace_append hprefix tailTrace_232090
  have hstable : (prefixWord ++ tailWord_232090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232090).length < 2 ^ (prefixWord ++ tailWord_232090).sum := by decide
  have hdescent : baseEnd_232090 < baseStart_232090 := by decide
  rcases family_descends (prefixWord ++ tailWord_232090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232199 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 1, 4]
def baseStart_232199 : Nat := 118140960795 + 232199 * 2 ^ 59
def prefixEnd_232199 : Nat := 4983230072969 + 3 ^ 40 * 232199 * 2
def baseEnd_232199 : Nat := 79486462995628169363095

theorem tailTrace_232199 : CollatzResearch.WordTrace tailWord_232199 prefixEnd_232199 79486462995628169363095 := by
  unfold tailWord_232199
  simp only [CollatzResearch.WordTrace]
  refine ⟨8468993285790154277099651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5645995523860102851399767 8468993285790154277099651)
  ·
    refine ⟨12703489928685231415649477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8468993285790154277099651 12703489928685231415649477)
    ·
      refine ⟨2381904361628480890434277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12703489928685231415649477 2381904361628480890434277)
      ·
        refine ⟨446607067805340166956427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2381904361628480890434277 446607067805340166956427)
        ·
          refine ⟨669910601708010250434641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446607067805340166956427 669910601708010250434641)
          ·
            refine ⟨502432951281007687825981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 669910601708010250434641 502432951281007687825981)
            ·
              refine ⟨188412356730377882934743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502432951281007687825981 188412356730377882934743)
              ·
                refine ⟨282618535095566824402115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188412356730377882934743 282618535095566824402115)
                ·
                  refine ⟨423927802643350236603173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282618535095566824402115 423927802643350236603173)
                  ·
                    refine ⟨79486462995628169363095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 423927802643350236603173 79486462995628169363095)
                    ·
                      rfl

theorem cell22_232199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_232199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232199 prefixEnd_232199 := by exact prefixLift 232199
  have htrace : WordTrace (prefixWord ++ tailWord_232199) baseStart_232199 baseEnd_232199 := by
    simpa [prefixWord, tailWord_232199, baseEnd_232199] using wordTrace_append hprefix tailTrace_232199
  have hstable : (prefixWord ++ tailWord_232199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232199).length < 2 ^ (prefixWord ++ tailWord_232199).sum := by decide
  have hdescent : baseEnd_232199 < baseStart_232199 := by decide
  rcases family_descends (prefixWord ++ tailWord_232199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232274 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 1, 3]
def baseStart_232274 : Nat := 118140960795 + 232274 * 2 ^ 59
def prefixEnd_232274 : Nat := 4983230072969 + 3 ^ 40 * 232274 * 2
def baseEnd_232274 : Nat := 79512137028352973737865

theorem tailTrace_232274 : CollatzResearch.WordTrace tailWord_232274 prefixEnd_232274 79512137028352973737865 := by
  unfold tailWord_232274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117932190129610521519969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5647819173678961390719917 2117932190129610521519969)
  ·
    refine ⟨1588449142597207891139977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2117932190129610521519969 1588449142597207891139977)
    ·
      refine ⟨1191336856947905918354983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1588449142597207891139977 1191336856947905918354983)
      ·
        refine ⟨1787005285421858877532475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191336856947905918354983 1787005285421858877532475)
        ·
          refine ⟨2680507928132788316298713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787005285421858877532475 2680507928132788316298713)
          ·
            refine ⟨2010380946099591237224035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680507928132788316298713 2010380946099591237224035)
            ·
              refine ⟨3015571419149386855836053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010380946099591237224035 3015571419149386855836053)
              ·
                refine ⟨141354910272627508867315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3015571419149386855836053 141354910272627508867315)
                ·
                  refine ⟨212032365408941263300973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141354910272627508867315 212032365408941263300973)
                  ·
                    refine ⟨79512137028352973737865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212032365408941263300973 79512137028352973737865)
                    ·
                      rfl

theorem cell22_232274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_232274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232274 prefixEnd_232274 := by exact prefixLift 232274
  have htrace : WordTrace (prefixWord ++ tailWord_232274) baseStart_232274 baseEnd_232274 := by
    simpa [prefixWord, tailWord_232274, baseEnd_232274] using wordTrace_append hprefix tailTrace_232274
  have hstable : (prefixWord ++ tailWord_232274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232274).length < 2 ^ (prefixWord ++ tailWord_232274).sum := by decide
  have hdescent : baseEnd_232274 < baseStart_232274 := by decide
  rcases family_descends (prefixWord ++ tailWord_232274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232287 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 5]
def baseStart_232287 : Nat := 118140960795 + 232287 * 2 ^ 59
def prefixEnd_232287 : Nat := 4983230072969 + 3 ^ 40 * 232287 * 2
def baseEnd_232287 : Nat := 26505529064675091054275

theorem tailTrace_232287 : CollatzResearch.WordTrace tailWord_232287 prefixEnd_232287 26505529064675091054275 := by
  unfold tailWord_232287
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472202909471345306303115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5648135272980896870868743 8472202909471345306303115)
  ·
    refine ⟨12708304364207017959454673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8472202909471345306303115 12708304364207017959454673)
    ·
      refine ⟨9531228273155263469591005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12708304364207017959454673 9531228273155263469591005)
      ·
        refine ⟨3574210602433223801096627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9531228273155263469591005 3574210602433223801096627)
        ·
          refine ⟨5361315903649835701644941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574210602433223801096627 5361315903649835701644941)
          ·
            refine ⟨2010493463868688388116853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5361315903649835701644941 2010493463868688388116853)
            ·
              refine ⟨188483762237689536385955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2010493463868688388116853 188483762237689536385955)
              ·
                refine ⟨282725643356534304578933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188483762237689536385955 282725643356534304578933)
                ·
                  refine ⟨26505529064675091054275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282725643356534304578933 26505529064675091054275)
                  ·
                    rfl

theorem cell22_232287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 5].length) (baseStart_232287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232287 prefixEnd_232287 := by exact prefixLift 232287
  have htrace : WordTrace (prefixWord ++ tailWord_232287) baseStart_232287 baseEnd_232287 := by
    simpa [prefixWord, tailWord_232287, baseEnd_232287] using wordTrace_append hprefix tailTrace_232287
  have hstable : (prefixWord ++ tailWord_232287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232287).length < 2 ^ (prefixWord ++ tailWord_232287).sum := by decide
  have hdescent : baseEnd_232287 < baseStart_232287 := by decide
  rcases family_descends (prefixWord ++ tailWord_232287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232317 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_232317 : Nat := 118140960795 + 232317 * 2 ^ 59
def prefixEnd_232317 : Nat := 4983230072969 + 3 ^ 40 * 232317 * 2
def baseEnd_232317 : Nat := 79526856807115194912733

theorem tailTrace_232317 : CollatzResearch.WordTrace tailWord_232317 prefixEnd_232317 79526856807115194912733 := by
  unfold tailWord_232317
  simp only [CollatzResearch.WordTrace]
  refine ⟨8473297099362660429895205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5648864732908440286596803 8473297099362660429895205)
  ·
    refine ⟨1588743206130498830605351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8473297099362660429895205 1588743206130498830605351)
    ·
      refine ⟨2383114809195748245908027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1588743206130498830605351 2383114809195748245908027)
      ·
        refine ⟨3574672213793622368862041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383114809195748245908027 3574672213793622368862041)
        ·
          refine ⟨2681004160345216776646531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3574672213793622368862041 2681004160345216776646531)
          ·
            refine ⟨4021506240517825164969797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681004160345216776646531 4021506240517825164969797)
            ·
              refine ⟨754032420097092218431837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4021506240517825164969797 754032420097092218431837)
              ·
                refine ⟨282762157536409581911939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 754032420097092218431837 282762157536409581911939)
                ·
                  refine ⟨424143236304614372867909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282762157536409581911939 424143236304614372867909)
                  ·
                    refine ⟨79526856807115194912733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424143236304614372867909 79526856807115194912733)
                    ·
                      rfl

theorem cell22_232317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_232317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232317 prefixEnd_232317 := by exact prefixLift 232317
  have htrace : WordTrace (prefixWord ++ tailWord_232317) baseStart_232317 baseEnd_232317 := by
    simpa [prefixWord, tailWord_232317, baseEnd_232317] using wordTrace_append hprefix tailTrace_232317
  have hstable : (prefixWord ++ tailWord_232317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232317).length < 2 ^ (prefixWord ++ tailWord_232317).sum := by decide
  have hdescent : baseEnd_232317 < baseStart_232317 := by decide
  rcases family_descends (prefixWord ++ tailWord_232317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232332 : List Nat := [2, 2, 1, 2, 1, 2, 2, 6, 4]
def baseStart_232332 : Nat := 118140960795 + 232332 * 2 ^ 59
def prefixEnd_232332 : Nat := 4983230072969 + 3 ^ 40 * 232332 * 2
def baseEnd_232332 : Nat := 26510663871220051929229

theorem tailTrace_232332 : CollatzResearch.WordTrace tailWord_232332 prefixEnd_232332 26510663871220051929229 := by
  unfold tailWord_232332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236922097154158995845625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5649229462872211994460833 4236922097154158995845625)
  ·
    refine ⟨3177691572865619246884219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4236922097154158995845625 3177691572865619246884219)
    ·
      refine ⟨4766537359298428870326329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177691572865619246884219 4766537359298428870326329)
      ·
        refine ⟨3574903019473821652744747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4766537359298428870326329 3574903019473821652744747)
        ·
          refine ⟨5362354529210732479117121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574903019473821652744747 5362354529210732479117121)
          ·
            refine ⟨4021765896908049359337841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362354529210732479117121 4021765896908049359337841)
            ·
              refine ⟨3016324422681037019503381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021765896908049359337841 3016324422681037019503381)
              ·
                refine ⟨141390207313173610289221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3016324422681037019503381 141390207313173610289221)
                ·
                  refine ⟨26510663871220051929229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141390207313173610289221 26510663871220051929229)
                  ·
                    rfl

theorem cell22_232332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_232332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232332 prefixEnd_232332 := by exact prefixLift 232332
  have htrace : WordTrace (prefixWord ++ tailWord_232332) baseStart_232332 baseEnd_232332 := by
    simpa [prefixWord, tailWord_232332, baseEnd_232332] using wordTrace_append hprefix tailTrace_232332
  have hstable : (prefixWord ++ tailWord_232332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232332).length < 2 ^ (prefixWord ++ tailWord_232332).sum := by decide
  have hdescent : baseEnd_232332 < baseStart_232332 := by decide
  rcases family_descends (prefixWord ++ tailWord_232332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232338 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_232338 : Nat := 118140960795 + 232338 * 2 ^ 59
def prefixEnd_232338 : Nat := 4983230072969 + 3 ^ 40 * 232338 * 2
def baseEnd_232338 : Nat := 26511348512092713379223

theorem tailTrace_232338 : CollatzResearch.WordTrace tailWord_232338 prefixEnd_232338 26511348512092713379223 := by
  unfold tailWord_232338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118515758071645254102417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5649375354857720677606445 2118515758071645254102417)
  ·
    refine ⟨1588886818553733940576813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2118515758071645254102417 1588886818553733940576813)
    ·
      refine ⟨595832556957650227716305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1588886818553733940576813 595832556957650227716305)
      ·
        refine ⟨446874417718237670787229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595832556957650227716305 446874417718237670787229)
        ·
          refine ⟨167577906644339126545211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446874417718237670787229 167577906644339126545211)
          ·
            refine ⟨251366859966508689817817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167577906644339126545211 251366859966508689817817)
            ·
              refine ⟨188525144974881517363363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251366859966508689817817 188525144974881517363363)
              ·
                refine ⟨282787717462322276045045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188525144974881517363363 282787717462322276045045)
                ·
                  refine ⟨26511348512092713379223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282787717462322276045045 26511348512092713379223)
                  ·
                    rfl

theorem cell22_232338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_232338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232338 prefixEnd_232338 := by exact prefixLift 232338
  have htrace : WordTrace (prefixWord ++ tailWord_232338) baseStart_232338 baseEnd_232338 := by
    simpa [prefixWord, tailWord_232338, baseEnd_232338] using wordTrace_append hprefix tailTrace_232338
  have hstable : (prefixWord ++ tailWord_232338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232338).length < 2 ^ (prefixWord ++ tailWord_232338).sum := by decide
  have hdescent : baseEnd_232338 < baseStart_232338 := by decide
  rcases family_descends (prefixWord ++ tailWord_232338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232345 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_232345 : Nat := 118140960795 + 232345 * 2 ^ 59
def prefixEnd_232345 : Nat := 4983230072969 + 3 ^ 40 * 232345 * 2
def baseEnd_232345 : Nat := 79536441779332455212647

theorem tailTrace_232345 : CollatzResearch.WordTrace tailWord_232345 prefixEnd_232345 79536441779332455212647 := by
  unfold tailWord_232345
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474318343261221211914489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5649545562174147474609659 8474318343261221211914489)
  ·
    refine ⟨6355738757445915908935867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8474318343261221211914489 6355738757445915908935867)
    ·
      refine ⟨9533608136168873863403801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6355738757445915908935867 9533608136168873863403801)
      ·
        refine ⟨7150206102126655397552851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9533608136168873863403801 7150206102126655397552851)
        ·
          refine ⟨10725309153189983096329277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150206102126655397552851 10725309153189983096329277)
          ·
            refine ⟨4021990932446243661123479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10725309153189983096329277 4021990932446243661123479)
            ·
              refine ⟨6032986398669365491685219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021990932446243661123479 6032986398669365491685219)
              ·
                refine ⟨9049479598004048237527829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6032986398669365491685219 9049479598004048237527829)
                ·
                  refine ⟨424194356156439761134117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9049479598004048237527829 424194356156439761134117)
                  ·
                    refine ⟨79536441779332455212647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424194356156439761134117 79536441779332455212647)
                    ·
                      rfl

theorem cell22_232345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_232345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232345 prefixEnd_232345 := by exact prefixLift 232345
  have htrace : WordTrace (prefixWord ++ tailWord_232345) baseStart_232345 baseEnd_232345 := by
    simpa [prefixWord, tailWord_232345, baseEnd_232345] using wordTrace_append hprefix tailTrace_232345
  have hstable : (prefixWord ++ tailWord_232345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232345).length < 2 ^ (prefixWord ++ tailWord_232345).sum := by decide
  have hdescent : baseEnd_232345 < baseStart_232345 := by decide
  rcases family_descends (prefixWord ++ tailWord_232345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232381 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_232381 : Nat := 118140960795 + 232381 * 2 ^ 59
def prefixEnd_232381 : Nat := 4983230072969 + 3 ^ 40 * 232381 * 2
def baseEnd_232381 : Nat := 79548765315040361312537

theorem tailTrace_232381 : CollatzResearch.WordTrace tailWord_232381 prefixEnd_232381 79548765315040361312537 := by
  unfold tailWord_232381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8475631371130799360224997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5650420914087199573483331 8475631371130799360224997)
  ·
    refine ⟨1589180882087024880042187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8475631371130799360224997 1589180882087024880042187)
    ·
      refine ⟨2383771323130537320063281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589180882087024880042187 2383771323130537320063281)
      ·
        refine ⟨1787828492347902990047461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2383771323130537320063281 1787828492347902990047461)
        ·
          refine ⟨335217842315231810633899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1787828492347902990047461 335217842315231810633899)
          ·
            refine ⟨502826763472847715950849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335217842315231810633899 502826763472847715950849)
            ·
              refine ⟨377120072604635786963137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502826763472847715950849 377120072604635786963137)
              ·
                refine ⟨282840054453476840222353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377120072604635786963137 282840054453476840222353)
                ·
                  refine ⟨212130040840107630166765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282840054453476840222353 212130040840107630166765)
                  ·
                    refine ⟨79548765315040361312537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212130040840107630166765 79548765315040361312537)
                    ·
                      rfl

theorem cell22_232381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_232381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232381 prefixEnd_232381 := by exact prefixLift 232381
  have htrace : WordTrace (prefixWord ++ tailWord_232381) baseStart_232381 baseEnd_232381 := by
    simpa [prefixWord, tailWord_232381, baseEnd_232381] using wordTrace_append hprefix tailTrace_232381
  have hstable : (prefixWord ++ tailWord_232381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232381).length < 2 ^ (prefixWord ++ tailWord_232381).sum := by decide
  have hdescent : baseEnd_232381 < baseStart_232381 := by decide
  rcases family_descends (prefixWord ++ tailWord_232381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232409 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 3, 3]
def baseStart_232409 : Nat := 118140960795 + 232409 * 2 ^ 59
def prefixEnd_232409 : Nat := 4983230072969 + 3 ^ 40 * 232409 * 2
def baseEnd_232409 : Nat := 79558350287257621612451

theorem tailTrace_232409 : CollatzResearch.WordTrace tailWord_232409 prefixEnd_232409 79558350287257621612451 := by
  unfold tailWord_232409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476652615029360142244281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5651101743352906761496187 8476652615029360142244281)
  ·
    refine ⟨6357489461272020106683211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8476652615029360142244281 6357489461272020106683211)
    ·
      refine ⟨9536234191908030160024817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6357489461272020106683211 9536234191908030160024817)
      ·
        refine ⟨7152175643931022620018613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9536234191908030160024817 7152175643931022620018613)
        ·
          refine ⟨670516466618533370626745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7152175643931022620018613 670516466618533370626745)
          ·
            refine ⟨502887349963900027970059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670516466618533370626745 502887349963900027970059)
            ·
              refine ⟨754331024945850041955089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502887349963900027970059 754331024945850041955089)
              ·
                refine ⟨565748268709387531466317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754331024945850041955089 565748268709387531466317)
                ·
                  refine ⟨212155600766020324299869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565748268709387531466317 212155600766020324299869)
                  ·
                    refine ⟨79558350287257621612451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212155600766020324299869 79558350287257621612451)
                    ·
                      rfl

theorem cell22_232409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 3].length) (baseStart_232409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232409 prefixEnd_232409 := by exact prefixLift 232409
  have htrace : WordTrace (prefixWord ++ tailWord_232409) baseStart_232409 baseEnd_232409 := by
    simpa [prefixWord, tailWord_232409, baseEnd_232409] using wordTrace_append hprefix tailTrace_232409
  have hstable : (prefixWord ++ tailWord_232409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232409).length < 2 ^ (prefixWord ++ tailWord_232409).sum := by decide
  have hdescent : baseEnd_232409 < baseStart_232409 := by decide
  rcases family_descends (prefixWord ++ tailWord_232409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232426 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 1, 3]
def baseStart_232426 : Nat := 118140960795 + 232426 * 2 ^ 59
def prefixEnd_232426 : Nat := 4983230072969 + 3 ^ 40 * 232426 * 2
def baseEnd_232426 : Nat := 79564169734675243937399

theorem tailTrace_232426 : CollatzResearch.WordTrace tailWord_232426 prefixEnd_232426 79564169734675243937399 := by
  unfold tailWord_232426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119318163991943011403283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5651515103978514697075421 2119318163991943011403283)
  ·
    refine ⟨3178977245987914517104925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119318163991943011403283 3178977245987914517104925)
    ·
      refine ⟨1192116467245467943914347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3178977245987914517104925 1192116467245467943914347)
      ·
        refine ⟨1788174700868201915871521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192116467245467943914347 1788174700868201915871521)
        ·
          refine ⟨1341131025651151436903641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788174700868201915871521 1341131025651151436903641)
          ·
            refine ⟨1005848269238363577677731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341131025651151436903641 1005848269238363577677731)
            ·
              refine ⟨1508772403857545366516597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005848269238363577677731 1508772403857545366516597)
              ·
                refine ⟨141447412861644878110931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508772403857545366516597 141447412861644878110931)
                ·
                  refine ⟨212171119292467317166397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141447412861644878110931 212171119292467317166397)
                  ·
                    refine ⟨79564169734675243937399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212171119292467317166397 79564169734675243937399)
                    ·
                      rfl

theorem cell22_232426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_232426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232426 prefixEnd_232426 := by exact prefixLift 232426
  have htrace : WordTrace (prefixWord ++ tailWord_232426) baseStart_232426 baseEnd_232426 := by
    simpa [prefixWord, tailWord_232426, baseEnd_232426] using wordTrace_append hprefix tailTrace_232426
  have hstable : (prefixWord ++ tailWord_232426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232426).length < 2 ^ (prefixWord ++ tailWord_232426).sum := by decide
  have hdescent : baseEnd_232426 < baseStart_232426 := by decide
  rcases family_descends (prefixWord ++ tailWord_232426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232469 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_232469 : Nat := 118140960795 + 232469 * 2 ^ 59
def prefixEnd_232469 : Nat := 4983230072969 + 3 ^ 40 * 232469 * 2
def baseEnd_232469 : Nat := 79578889513437465112267

theorem tailTrace_232469 : CollatzResearch.WordTrace tailWord_232469 prefixEnd_232469 79578889513437465112267 := by
  unfold tailWord_232469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8478840994811990389428461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5652560663207993592952307 8478840994811990389428461)
  ·
    refine ⟨3179565373054496396035673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8478840994811990389428461 3179565373054496396035673)
    ·
      refine ⟨2384674029790872297026755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179565373054496396035673 2384674029790872297026755)
      ·
        refine ⟨3577011044686308445540133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384674029790872297026755 3577011044686308445540133)
        ·
          refine ⟨670689570878682833538775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3577011044686308445540133 670689570878682833538775)
          ·
            refine ⟨1006034356318024250308163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670689570878682833538775 1006034356318024250308163)
            ·
              refine ⟨1509051534477036375462245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006034356318024250308163 1509051534477036375462245)
              ·
                refine ⟨282947162714444320399171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1509051534477036375462245 282947162714444320399171)
                ·
                  refine ⟨424420744071666480598757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 282947162714444320399171 424420744071666480598757)
                  ·
                    refine ⟨79578889513437465112267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424420744071666480598757 79578889513437465112267)
                    ·
                      rfl

theorem cell22_232469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_232469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232469 prefixEnd_232469 := by exact prefixLift 232469
  have htrace : WordTrace (prefixWord ++ tailWord_232469) baseStart_232469 baseEnd_232469 := by
    simpa [prefixWord, tailWord_232469, baseEnd_232469] using wordTrace_append hprefix tailTrace_232469
  have hstable : (prefixWord ++ tailWord_232469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232469).length < 2 ^ (prefixWord ++ tailWord_232469).sum := by decide
  have hdescent : baseEnd_232469 < baseStart_232469 := by decide
  rcases family_descends (prefixWord ++ tailWord_232469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232499 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 2, 3]
def baseStart_232499 : Nat := 118140960795 + 232499 * 2 ^ 59
def prefixEnd_232499 : Nat := 4983230072969 + 3 ^ 40 * 232499 * 2
def baseEnd_232499 : Nat := 79589159126527386862175

theorem tailTrace_232499 : CollatzResearch.WordTrace tailWord_232499 prefixEnd_232499 79589159126527386862175 := by
  unfold tailWord_232499
  simp only [CollatzResearch.WordTrace]
  refine ⟨8479935184703305513020551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5653290123135537008680367 8479935184703305513020551)
  ·
    refine ⟨12719902777054958269530827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8479935184703305513020551 12719902777054958269530827)
    ·
      refine ⟨19079854165582437404296241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12719902777054958269530827 19079854165582437404296241)
      ·
        refine ⟨14309890624186828053222181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19079854165582437404296241 14309890624186828053222181)
        ·
          refine ⟨2683104492035030259979159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14309890624186828053222181 2683104492035030259979159)
          ·
            refine ⟨4024656738052545389968739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683104492035030259979159 4024656738052545389968739)
            ·
              refine ⟨6036985107078818084953109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4024656738052545389968739 6036985107078818084953109)
              ·
                refine ⟨282983676894319597732177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6036985107078818084953109 282983676894319597732177)
                ·
                  refine ⟨212237757670739698299133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282983676894319597732177 212237757670739698299133)
                  ·
                    refine ⟨79589159126527386862175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212237757670739698299133 79589159126527386862175)
                    ·
                      rfl

theorem cell22_232499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 3].length) (baseStart_232499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232499 prefixEnd_232499 := by exact prefixLift 232499
  have htrace : WordTrace (prefixWord ++ tailWord_232499) baseStart_232499 baseEnd_232499 := by
    simpa [prefixWord, tailWord_232499, baseEnd_232499] using wordTrace_append hprefix tailTrace_232499
  have hstable : (prefixWord ++ tailWord_232499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232499).length < 2 ^ (prefixWord ++ tailWord_232499).sum := by decide
  have hdescent : baseEnd_232499 < baseStart_232499 := by decide
  rcases family_descends (prefixWord ++ tailWord_232499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232512 : List Nat := [2, 1, 1, 2, 2, 3, 4, 7]
def baseStart_232512 : Nat := 118140960795 + 232512 * 2 ^ 59
def prefixEnd_232512 : Nat := 4983230072969 + 3 ^ 40 * 232512 * 2
def baseEnd_232512 : Nat := 8843734365799965143015

theorem tailTrace_232512 : CollatzResearch.WordTrace tailWord_232512 prefixEnd_232512 8843734365799965143015 := by
  unfold tailWord_232512
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240204666828104366621895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5653606222437472488829193 4240204666828104366621895)
  ·
    refine ⟨6360307000242156549932843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240204666828104366621895 6360307000242156549932843)
    ·
      refine ⟨9540460500363234824899265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360307000242156549932843 9540460500363234824899265)
      ·
        refine ⟨7155345375272426118674449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9540460500363234824899265 7155345375272426118674449)
        ·
          refine ⟨5366509031454319589005837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155345375272426118674449 5366509031454319589005837)
          ·
            refine ⟨2012440886795369845877189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5366509031454319589005837 2012440886795369845877189)
            ·
              refine ⟨377332666274131846101973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2012440886795369845877189 377332666274131846101973)
              ·
                refine ⟨8843734365799965143015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 377332666274131846101973 8843734365799965143015)
                ·
                  rfl

theorem cell22_232512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_232512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232512 prefixEnd_232512 := by exact prefixLift 232512
  have htrace : WordTrace (prefixWord ++ tailWord_232512) baseStart_232512 baseEnd_232512 := by
    simpa [prefixWord, tailWord_232512, baseEnd_232512] using wordTrace_append hprefix tailTrace_232512
  have hstable : (prefixWord ++ tailWord_232512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232512).length < 2 ^ (prefixWord ++ tailWord_232512).sum := by decide
  have hdescent : baseEnd_232512 < baseStart_232512 := by decide
  rcases family_descends (prefixWord ++ tailWord_232512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232552 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 4]
def baseStart_232552 : Nat := 118140960795 + 232552 * 2 ^ 59
def prefixEnd_232552 : Nat := 4983230072969 + 3 ^ 40 * 232552 * 2
def baseEnd_232552 : Nat := 26535767369884305095671

theorem tailTrace_232552 : CollatzResearch.WordTrace tailWord_232552 prefixEnd_232552 26535767369884305095671 := by
  unfold tailWord_232552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240934126755647782349955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5654578835674197043133273 4240934126755647782349955)
  ·
    refine ⟨6361401190133471673524933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240934126755647782349955 6361401190133471673524933)
    ·
      refine ⟨1192762723150025938785925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6361401190133471673524933 1192762723150025938785925)
      ·
        refine ⟨223643010590629863522361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1192762723150025938785925 223643010590629863522361)
        ·
          refine ⟨167732257942972397641771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223643010590629863522361 167732257942972397641771)
          ·
            refine ⟨251598386914458596462657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167732257942972397641771 251598386914458596462657)
            ·
              refine ⟨188698790185843947346993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251598386914458596462657 188698790185843947346993)
              ·
                refine ⟨141524092639382960510245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188698790185843947346993 141524092639382960510245)
                ·
                  refine ⟨26535767369884305095671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141524092639382960510245 26535767369884305095671)
                  ·
                    rfl

theorem cell22_232552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 4].length) (baseStart_232552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232552 prefixEnd_232552 := by exact prefixLift 232552
  have htrace : WordTrace (prefixWord ++ tailWord_232552) baseStart_232552 baseEnd_232552 := by
    simpa [prefixWord, tailWord_232552, baseEnd_232552] using wordTrace_append hprefix tailTrace_232552
  have hstable : (prefixWord ++ tailWord_232552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232552).length < 2 ^ (prefixWord ++ tailWord_232552).sum := by decide
  have hdescent : baseEnd_232552 < baseStart_232552 := by decide
  rcases family_descends (prefixWord ++ tailWord_232552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232606 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_232606 : Nat := 118140960795 + 232606 * 2 ^ 59
def prefixEnd_232606 : Nat := 4983230072969 + 3 ^ 40 * 232606 * 2
def baseEnd_232606 : Nat := 79625787413214774436847

theorem tailTrace_232606 : CollatzResearch.WordTrace tailWord_232606 prefixEnd_232606 79625787413214774436847 := by
  unfold tailWord_232606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060479724414457848395709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5655891863543775191443781 1060479724414457848395709)
  ·
    refine ⟨397679896655421693148391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1060479724414457848395709 397679896655421693148391)
    ·
      refine ⟨596519844983132539722587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397679896655421693148391 596519844983132539722587)
      ·
        refine ⟨894779767474698809583881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596519844983132539722587 894779767474698809583881)
        ·
          refine ⟨671084825606024107187911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894779767474698809583881 671084825606024107187911)
          ·
            refine ⟨1006627238409036160781867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671084825606024107187911 1006627238409036160781867)
            ·
              refine ⟨1509940857613554241172801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006627238409036160781867 1509940857613554241172801)
              ·
                refine ⟨1132455643210165680879601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509940857613554241172801 1132455643210165680879601)
                ·
                  refine ⟨849341732407624260659701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1132455643210165680879601 849341732407624260659701)
                  ·
                    refine ⟨79625787413214774436847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 849341732407624260659701 79625787413214774436847)
                    ·
                      rfl

theorem cell22_232606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_232606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232606 prefixEnd_232606 := by exact prefixLift 232606
  have htrace : WordTrace (prefixWord ++ tailWord_232606) baseStart_232606 baseEnd_232606 := by
    simpa [prefixWord, tailWord_232606, baseEnd_232606] using wordTrace_append hprefix tailTrace_232606
  have hstable : (prefixWord ++ tailWord_232606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232606).length < 2 ^ (prefixWord ++ tailWord_232606).sum := by decide
  have hdescent : baseEnd_232606 < baseStart_232606 := by decide
  rcases family_descends (prefixWord ++ tailWord_232606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232638 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_232638 : Nat := 118140960795 + 232638 * 2 ^ 59
def prefixEnd_232638 : Nat := 4983230072969 + 3 ^ 40 * 232638 * 2
def baseEnd_232638 : Nat := 79636741667177357636749

theorem tailTrace_232638 : CollatzResearch.WordTrace tailWord_232638 prefixEnd_232638 79636741667177357636749 := by
  unfold tailWord_232638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060625616399966531541321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5656669954133154834887045 1060625616399966531541321)
  ·
    refine ⟨795469212299974898655991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1060625616399966531541321 795469212299974898655991)
    ·
      refine ⟨1193203818449962347983987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795469212299974898655991 1193203818449962347983987)
      ·
        refine ⟨1789805727674943521975981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193203818449962347983987 1789805727674943521975981)
        ·
          refine ⟨671177147878103820740993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1789805727674943521975981 671177147878103820740993)
          ·
            refine ⟨503382860908577865555745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671177147878103820740993 503382860908577865555745)
            ·
              refine ⟨377537145681433399166809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503382860908577865555745 377537145681433399166809)
              ·
                refine ⟨283152859261075049375107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 377537145681433399166809 283152859261075049375107)
                ·
                  refine ⟨424729288891612574062661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 283152859261075049375107 424729288891612574062661)
                  ·
                    refine ⟨79636741667177357636749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 424729288891612574062661 79636741667177357636749)
                    ·
                      rfl

theorem cell22_232638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_232638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232638 prefixEnd_232638 := by exact prefixLift 232638
  have htrace : WordTrace (prefixWord ++ tailWord_232638) baseStart_232638 baseEnd_232638 := by
    simpa [prefixWord, tailWord_232638, baseEnd_232638] using wordTrace_append hprefix tailTrace_232638
  have hstable : (prefixWord ++ tailWord_232638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232638).length < 2 ^ (prefixWord ++ tailWord_232638).sum := by decide
  have hdescent : baseEnd_232638 < baseStart_232638 := by decide
  rcases family_descends (prefixWord ++ tailWord_232638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232646 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_232646 : Nat := 118140960795 + 232646 * 2 ^ 59
def prefixEnd_232646 : Nat := 4983230072969 + 3 ^ 40 * 232646 * 2
def baseEnd_232646 : Nat := 79639480230668003436725

theorem tailTrace_232646 : CollatzResearch.WordTrace tailWord_232646 prefixEnd_232646 79639480230668003436725 := by
  unfold tailWord_232646
  simp only [CollatzResearch.WordTrace]
  refine ⟨265165522349085925581931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5656864476780499745747861 265165522349085925581931)
  ·
    refine ⟨397748283523628888372897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 265165522349085925581931 397748283523628888372897)
    ·
      refine ⟨298311212642721666279673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397748283523628888372897 298311212642721666279673)
      ·
        refine ⟨223733409482041249709755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298311212642721666279673 223733409482041249709755)
        ·
          refine ⟨335600114223061874564633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223733409482041249709755 335600114223061874564633)
          ·
            refine ⟨251700085667296405923475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335600114223061874564633 251700085667296405923475)
            ·
              refine ⟨377550128500944608885213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251700085667296405923475 377550128500944608885213)
              ·
                refine ⟨141581298187854228331955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377550128500944608885213 141581298187854228331955)
                ·
                  refine ⟨212371947281781342497933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141581298187854228331955 212371947281781342497933)
                  ·
                    refine ⟨79639480230668003436725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212371947281781342497933 79639480230668003436725)
                    ·
                      rfl

theorem cell22_232646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_232646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232646 prefixEnd_232646 := by exact prefixLift 232646
  have htrace : WordTrace (prefixWord ++ tailWord_232646) baseStart_232646 baseEnd_232646 := by
    simpa [prefixWord, tailWord_232646, baseEnd_232646] using wordTrace_append hprefix tailTrace_232646
  have hstable : (prefixWord ++ tailWord_232646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232646).length < 2 ^ (prefixWord ++ tailWord_232646).sum := by decide
  have hdescent : baseEnd_232646 < baseStart_232646 := by decide
  rcases family_descends (prefixWord ++ tailWord_232646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232685 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_232685 : Nat := 118140960795 + 232685 * 2 ^ 59
def prefixEnd_232685 : Nat := 4983230072969 + 3 ^ 40 * 232685 * 2
def baseEnd_232685 : Nat := 79652830727684901711605

theorem tailTrace_232685 : CollatzResearch.WordTrace tailWord_232685 prefixEnd_232685 79652830727684901711605 := by
  unfold tailWord_232685
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486719162029459279291509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5657812774686306186194339 8486719162029459279291509)
  ·
    refine ⟨795629921440261807433579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8486719162029459279291509 795629921440261807433579)
    ·
      refine ⟨1193444882160392711150369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795629921440261807433579 1193444882160392711150369)
      ·
        refine ⟨895083661620294533362777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193444882160392711150369 895083661620294533362777)
        ·
          refine ⟨671312746215220900022083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895083661620294533362777 671312746215220900022083)
          ·
            refine ⟨1006969119322831350033125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671312746215220900022083 1006969119322831350033125)
            ·
              refine ⟨188806709873030878131211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1006969119322831350033125 188806709873030878131211)
              ·
                refine ⟨283210064809546317196817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188806709873030878131211 283210064809546317196817)
                ·
                  refine ⟨212407548607159737897613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283210064809546317196817 212407548607159737897613)
                  ·
                    refine ⟨79652830727684901711605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212407548607159737897613 79652830727684901711605)
                    ·
                      rfl

theorem cell22_232685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_232685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232685 prefixEnd_232685 := by exact prefixLift 232685
  have htrace : WordTrace (prefixWord ++ tailWord_232685) baseStart_232685 baseEnd_232685 := by
    simpa [prefixWord, tailWord_232685, baseEnd_232685] using wordTrace_append hprefix tailTrace_232685
  have hstable : (prefixWord ++ tailWord_232685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232685).length < 2 ^ (prefixWord ++ tailWord_232685).sum := by decide
  have hdescent : baseEnd_232685 < baseStart_232685 := by decide
  rcases family_descends (prefixWord ++ tailWord_232685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232713 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 1, 3]
def baseStart_232713 : Nat := 118140960795 + 232713 * 2 ^ 59
def prefixEnd_232713 : Nat := 4983230072969 + 3 ^ 40 * 232713 * 2
def baseEnd_232713 : Nat := 79662415699902162011519

theorem tailTrace_232713 : CollatzResearch.WordTrace tailWord_232713 prefixEnd_232713 79662415699902162011519 := by
  unfold tailWord_232713
  simp only [CollatzResearch.WordTrace]
  refine ⟨8487740405928020061310793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5658493603952013374207195 8487740405928020061310793)
  ·
    refine ⟨6365805304446015045983095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8487740405928020061310793 6365805304446015045983095)
    ·
      refine ⟨9548707956669022568974643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6365805304446015045983095 9548707956669022568974643)
      ·
        refine ⟨14323061935003533853461965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548707956669022568974643 14323061935003533853461965)
        ·
          refine ⟨5371148225626325195048237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14323061935003533853461965 5371148225626325195048237)
          ·
            refine ⟨2014180584609871948143089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5371148225626325195048237 2014180584609871948143089)
            ·
              refine ⟨1510635438457403961107317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014180584609871948143089 1510635438457403961107317)
              ·
                refine ⟨141622072355381621353811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1510635438457403961107317 141622072355381621353811)
                ·
                  refine ⟨212433108533072432030717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141622072355381621353811 212433108533072432030717)
                  ·
                    refine ⟨79662415699902162011519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212433108533072432030717 79662415699902162011519)
                    ·
                      rfl

theorem cell22_232713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_232713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232713 prefixEnd_232713 := by exact prefixLift 232713
  have htrace : WordTrace (prefixWord ++ tailWord_232713) baseStart_232713 baseEnd_232713 := by
    simpa [prefixWord, tailWord_232713, baseEnd_232713] using wordTrace_append hprefix tailTrace_232713
  have hstable : (prefixWord ++ tailWord_232713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232713).length < 2 ^ (prefixWord ++ tailWord_232713).sum := by decide
  have hdescent : baseEnd_232713 < baseStart_232713 := by decide
  rcases family_descends (prefixWord ++ tailWord_232713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232730 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 1, 3]
def baseStart_232730 : Nat := 118140960795 + 232730 * 2 ^ 59
def prefixEnd_232730 : Nat := 4983230072969 + 3 ^ 40 * 232730 * 2
def baseEnd_232730 : Nat := 79668235147319784336467

theorem tailTrace_232730 : CollatzResearch.WordTrace tailWord_232730 prefixEnd_232730 79668235147319784336467 := by
  unfold tailWord_232730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122090111716607991169911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5658906964577621309786429 2122090111716607991169911)
  ·
    refine ⟨3183135167574911986754867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2122090111716607991169911 3183135167574911986754867)
    ·
      refine ⟨4774702751362367980132301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183135167574911986754867 4774702751362367980132301)
      ·
        refine ⟨1790513531760887992549613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4774702751362367980132301 1790513531760887992549613)
        ·
          refine ⟨671442574410332997206105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1790513531760887992549613 671442574410332997206105)
          ·
            refine ⟨503581930807749747904579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671442574410332997206105 503581930807749747904579)
            ·
              refine ⟨755372896211624621856869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503581930807749747904579 755372896211624621856869)
              ·
                refine ⟨141632418039679616598163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 755372896211624621856869 141632418039679616598163)
                ·
                  refine ⟨212448627059519424897245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141632418039679616598163 212448627059519424897245)
                  ·
                    refine ⟨79668235147319784336467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212448627059519424897245 79668235147319784336467)
                    ·
                      rfl

theorem cell22_232730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_232730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232730 prefixEnd_232730 := by exact prefixLift 232730
  have htrace : WordTrace (prefixWord ++ tailWord_232730) baseStart_232730 baseEnd_232730 := by
    simpa [prefixWord, tailWord_232730, baseEnd_232730] using wordTrace_append hprefix tailTrace_232730
  have hstable : (prefixWord ++ tailWord_232730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232730).length < 2 ^ (prefixWord ++ tailWord_232730).sum := by decide
  have hdescent : baseEnd_232730 < baseStart_232730 := by decide
  rcases family_descends (prefixWord ++ tailWord_232730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232741 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_232741 : Nat := 118140960795 + 232741 * 2 ^ 59
def prefixEnd_232741 : Nat := 4983230072969 + 3 ^ 40 * 232741 * 2
def baseEnd_232741 : Nat := 79672000672119422311433

theorem tailTrace_232741 : CollatzResearch.WordTrace tailWord_232741 prefixEnd_232741 79672000672119422311433 := by
  unfold tailWord_232741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488761649826580843330077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5659174433217720562220051 8488761649826580843330077)
  ·
    refine ⟨3183285618684967816248779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8488761649826580843330077 3183285618684967816248779)
    ·
      refine ⟨4774928428027451724373169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183285618684967816248779 4774928428027451724373169)
      ·
        refine ⟨3581196321020588793279877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4774928428027451724373169 3581196321020588793279877)
        ·
          refine ⟨671474310191360398739977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3581196321020588793279877 671474310191360398739977)
          ·
            refine ⟨503605732643520299054983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 671474310191360398739977 503605732643520299054983)
            ·
              refine ⟨755408598965280448582475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503605732643520299054983 755408598965280448582475)
              ·
                refine ⟨1133112898447920672873713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 755408598965280448582475 1133112898447920672873713)
                ·
                  refine ⟨849834673835940504655285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1133112898447920672873713 849834673835940504655285)
                  ·
                    refine ⟨79672000672119422311433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 849834673835940504655285 79672000672119422311433)
                    ·
                      rfl

theorem cell22_232741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_232741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232741 prefixEnd_232741 := by exact prefixLift 232741
  have htrace : WordTrace (prefixWord ++ tailWord_232741) baseStart_232741 baseEnd_232741 := by
    simpa [prefixWord, tailWord_232741, baseEnd_232741] using wordTrace_append hprefix tailTrace_232741
  have hstable : (prefixWord ++ tailWord_232741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232741).length < 2 ^ (prefixWord ++ tailWord_232741).sum := by decide
  have hdescent : baseEnd_232741 < baseStart_232741 := by decide
  rcases family_descends (prefixWord ++ tailWord_232741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232788 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_232788 : Nat := 118140960795 + 232788 * 2 ^ 59
def prefixEnd_232788 : Nat := 4983230072969 + 3 ^ 40 * 232788 * 2
def baseEnd_232788 : Nat := 26562696577542322128763

theorem tailTrace_232788 : CollatzResearch.WordTrace tailWord_232788 prefixEnd_232788 26562696577542322128763 := by
  unfold tailWord_232788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4245237940328153935145509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5660317253770871913527345 4245237940328153935145509)
  ·
    refine ⟨795982113811528862839783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4245237940328153935145509 795982113811528862839783)
    ·
      refine ⟨1193973170717293294259675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795982113811528862839783 1193973170717293294259675)
      ·
        refine ⟨1790959756075939941389513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193973170717293294259675 1790959756075939941389513)
        ·
          refine ⟨1343219817056954956042135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1790959756075939941389513 1343219817056954956042135)
          ·
            refine ⟨2014829725585432434063203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1343219817056954956042135 2014829725585432434063203)
            ·
              refine ⟨3022244588378148651094805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014829725585432434063203 3022244588378148651094805)
              ·
                refine ⟨141667715080225718020069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3022244588378148651094805 141667715080225718020069)
                ·
                  refine ⟨26562696577542322128763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141667715080225718020069 26562696577542322128763)
                  ·
                    rfl

theorem cell22_232788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_232788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232788 prefixEnd_232788 := by exact prefixLift 232788
  have htrace : WordTrace (prefixWord ++ tailWord_232788) baseStart_232788 baseEnd_232788 := by
    simpa [prefixWord, tailWord_232788, baseEnd_232788] using wordTrace_append hprefix tailTrace_232788
  have hstable : (prefixWord ++ tailWord_232788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232788).length < 2 ^ (prefixWord ++ tailWord_232788).sum := by decide
  have hdescent : baseEnd_232788 < baseStart_232788 := by decide
  rcases family_descends (prefixWord ++ tailWord_232788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232799 : List Nat := [1, 1, 2, 3, 1, 2, 1, 11]
def baseStart_232799 : Nat := 118140960795 + 232799 * 2 ^ 59
def prefixEnd_232799 : Nat := 4983230072969 + 3 ^ 40 * 232799 * 2
def baseEnd_232799 : Nat := 8854650584158511595695

theorem tailTrace_232799 : CollatzResearch.WordTrace tailWord_232799 prefixEnd_232799 8854650584158511595695 := by
  unfold tailWord_232799
  simp only [CollatzResearch.WordTrace]
  refine ⟨8490877083616456748941451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660584722410971165960967 8490877083616456748941451)
  ·
    refine ⟨12736315625424685123412177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8490877083616456748941451 12736315625424685123412177)
    ·
      refine ⟨9552236719068513842559133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12736315625424685123412177 9552236719068513842559133)
      ·
        refine ⟨3582088769650692690959675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9552236719068513842559133 3582088769650692690959675)
        ·
          refine ⟨5373133154476039036439513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582088769650692690959675 5373133154476039036439513)
          ·
            refine ⟨4029849865857029277329635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373133154476039036439513 4029849865857029277329635)
            ·
              refine ⟨6044774798785543915994453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4029849865857029277329635 6044774798785543915994453)
              ·
                refine ⟨8854650584158511595695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6044774798785543915994453 8854650584158511595695)
                ·
                  rfl

theorem cell22_232799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 11].length) (baseStart_232799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232799 prefixEnd_232799 := by exact prefixLift 232799
  have htrace : WordTrace (prefixWord ++ tailWord_232799) baseStart_232799 baseEnd_232799 := by
    simpa [prefixWord, tailWord_232799, baseEnd_232799] using wordTrace_append hprefix tailTrace_232799
  have hstable : (prefixWord ++ tailWord_232799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232799).length < 2 ^ (prefixWord ++ tailWord_232799).sum := by decide
  have hdescent : baseEnd_232799 < baseStart_232799 := by decide
  rcases family_descends (prefixWord ++ tailWord_232799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232803 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 1, 5]
def baseStart_232803 : Nat := 118140960795 + 232803 * 2 ^ 59
def prefixEnd_232803 : Nat := 4983230072969 + 3 ^ 40 * 232803 * 2
def baseEnd_232803 : Nat := 79693224539171927261243

theorem tailTrace_232803 : CollatzResearch.WordTrace tailWord_232803 prefixEnd_232803 79693224539171927261243 := by
  unfold tailWord_232803
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491022975601965432087063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5660681983734643621391375 8491022975601965432087063)
  ·
    refine ⟨12736534463402948148130595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8491022975601965432087063 12736534463402948148130595)
    ·
      refine ⟨19104801695104422222195893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12736534463402948148130595 19104801695104422222195893)
      ·
        refine ⟨1791075158916039583330865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19104801695104422222195893 1791075158916039583330865)
        ·
          refine ⟨1343306369187029687498149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791075158916039583330865 1343306369187029687498149)
          ·
            refine ⟨251869944222568066405903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1343306369187029687498149 251869944222568066405903)
            ·
              refine ⟨377804916333852099608855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251869944222568066405903 377804916333852099608855)
              ·
                refine ⟨566707374500778149413283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377804916333852099608855 566707374500778149413283)
                ·
                  refine ⟨850061061751167224119925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 566707374500778149413283 850061061751167224119925)
                  ·
                    refine ⟨79693224539171927261243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 850061061751167224119925 79693224539171927261243)
                    ·
                      rfl

theorem cell22_232803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 5].length) (baseStart_232803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232803 prefixEnd_232803 := by exact prefixLift 232803
  have htrace : WordTrace (prefixWord ++ tailWord_232803) baseStart_232803 baseEnd_232803 := by
    simpa [prefixWord, tailWord_232803, baseEnd_232803] using wordTrace_append hprefix tailTrace_232803
  have hstable : (prefixWord ++ tailWord_232803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232803).length < 2 ^ (prefixWord ++ tailWord_232803).sum := by decide
  have hdescent : baseEnd_232803 < baseStart_232803 := by decide
  rcases family_descends (prefixWord ++ tailWord_232803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232833 : List Nat := [1, 2, 4, 3, 2, 2, 8]
def baseStart_232833 : Nat := 118140960795 + 232833 * 2 ^ 59
def prefixEnd_232833 : Nat := 4983230072969 + 3 ^ 40 * 232833 * 2
def baseEnd_232833 : Nat := 2951981264898587000413

theorem tailTrace_232833 : CollatzResearch.WordTrace tailWord_232833 prefixEnd_232833 2951981264898587000413 := by
  unfold tailWord_232833
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492117165493280555679153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5661411443662187037119435 8492117165493280555679153)
  ·
    refine ⟨6369087874119960416759365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8492117165493280555679153 6369087874119960416759365)
    ·
      refine ⟨1194203976397492578142381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6369087874119960416759365 1194203976397492578142381)
      ·
        refine ⟨447826491149059716803393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1194203976397492578142381 447826491149059716803393)
        ·
          refine ⟨335869868361794787602545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447826491149059716803393 335869868361794787602545)
          ·
            refine ⟨251902401271346090701909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335869868361794787602545 251902401271346090701909)
            ·
              refine ⟨2951981264898587000413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 251902401271346090701909 2951981264898587000413)
              ·
                rfl

theorem cell22_232833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 8].length) (baseStart_232833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232833 prefixEnd_232833 := by exact prefixLift 232833
  have htrace : WordTrace (prefixWord ++ tailWord_232833) baseStart_232833 baseEnd_232833 := by
    simpa [prefixWord, tailWord_232833, baseEnd_232833] using wordTrace_append hprefix tailTrace_232833
  have hstable : (prefixWord ++ tailWord_232833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232833).length < 2 ^ (prefixWord ++ tailWord_232833).sum := by decide
  have hdescent : baseEnd_232833 < baseStart_232833 := by decide
  rcases family_descends (prefixWord ++ tailWord_232833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232850 : List Nat := [3, 2, 3, 3, 1, 1, 2, 7]
def baseStart_232850 : Nat := 118140960795 + 232850 * 2 ^ 59
def prefixEnd_232850 : Nat := 4983230072969 + 3 ^ 40 * 232850 * 2
def baseEnd_232850 : Nat := 8856590399964385704011

theorem tailTrace_232850 : CollatzResearch.WordTrace tailWord_232850 prefixEnd_232850 8856590399964385704011 := by
  unfold tailWord_232850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123184301607923114762001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5661824804287794972698669 2123184301607923114762001)
  ·
    refine ⟨1592388226205942336071501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2123184301607923114762001 1592388226205942336071501)
    ·
      refine ⟨597145584827228376026813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1592388226205942336071501 597145584827228376026813)
      ·
        refine ⟨223929594310210641010055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 597145584827228376026813 223929594310210641010055)
        ·
          refine ⟨335894391465315961515083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223929594310210641010055 335894391465315961515083)
          ·
            refine ⟨503841587197973942272625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335894391465315961515083 503841587197973942272625)
            ·
              refine ⟨377881190398480456704469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503841587197973942272625 377881190398480456704469)
              ·
                refine ⟨8856590399964385704011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 377881190398480456704469 8856590399964385704011)
                ·
                  rfl

theorem cell22_232850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 7].length) (baseStart_232850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232850 prefixEnd_232850 := by exact prefixLift 232850
  have htrace : WordTrace (prefixWord ++ tailWord_232850) baseStart_232850 baseEnd_232850 := by
    simpa [prefixWord, tailWord_232850, baseEnd_232850] using wordTrace_append hprefix tailTrace_232850
  have hstable : (prefixWord ++ tailWord_232850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232850).length < 2 ^ (prefixWord ++ tailWord_232850).sum := by decide
  have hdescent : baseEnd_232850 < baseStart_232850 := by decide
  rcases family_descends (prefixWord ++ tailWord_232850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232908 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 3, 4]
def baseStart_232908 : Nat := 118140960795 + 232908 * 2 ^ 59
def prefixEnd_232908 : Nat := 4983230072969 + 3 ^ 40 * 232908 * 2
def baseEnd_232908 : Nat := 79729168184986653385921

theorem tailTrace_232908 : CollatzResearch.WordTrace tailWord_232908 prefixEnd_232908 79729168184986653385921 := by
  unfold tailWord_232908
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247426320110784182329689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5663235093481045576439585 4247426320110784182329689)
  ·
    refine ⟨3185569740083088136747267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4247426320110784182329689 3185569740083088136747267)
    ·
      refine ⟨4778354610124632205120901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185569740083088136747267 4778354610124632205120901)
      ·
        refine ⟨895941489398368538460169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4778354610124632205120901 895941489398368538460169)
        ·
          refine ⟨671956117048776403845127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 895941489398368538460169 671956117048776403845127)
          ·
            refine ⟨1007934175573164605767691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671956117048776403845127 1007934175573164605767691)
            ·
              refine ⟨1511901263359746908651537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1007934175573164605767691 1511901263359746908651537)
              ·
                refine ⟨1133925947519810181488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511901263359746908651537 1133925947519810181488653)
                ·
                  refine ⟨425222230319928818058245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133925947519810181488653 425222230319928818058245)
                  ·
                    refine ⟨79729168184986653385921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 425222230319928818058245 79729168184986653385921)
                    ·
                      rfl

theorem cell22_232908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_232908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232908 prefixEnd_232908 := by exact prefixLift 232908
  have htrace : WordTrace (prefixWord ++ tailWord_232908) baseStart_232908 baseEnd_232908 := by
    simpa [prefixWord, tailWord_232908, baseEnd_232908] using wordTrace_append hprefix tailTrace_232908
  have hstable : (prefixWord ++ tailWord_232908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232908).length < 2 ^ (prefixWord ++ tailWord_232908).sum := by decide
  have hdescent : baseEnd_232908 < baseStart_232908 := by decide
  rcases family_descends (prefixWord ++ tailWord_232908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_232972 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_232972 : Nat := 118140960795 + 232972 * 2 ^ 59
def prefixEnd_232972 : Nat := 4983230072969 + 3 ^ 40 * 232972 * 2
def baseEnd_232972 : Nat := 79751076692911819785725

theorem tailTrace_232972 : CollatzResearch.WordTrace tailWord_232972 prefixEnd_232972 79751076692911819785725 := by
  unfold tailWord_232972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248593455994853647494585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5664791274659804863326113 4248593455994853647494585)
  ·
    refine ⟨3186445091996140235620939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4248593455994853647494585 3186445091996140235620939)
    ·
      refine ⟨4779667637994210353431409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3186445091996140235620939 4779667637994210353431409)
      ·
        refine ⟨3584750728495657765073557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4779667637994210353431409 3584750728495657765073557)
        ·
          refine ⟨168035190398233957737823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3584750728495657765073557 168035190398233957737823)
          ·
            refine ⟨252052785597350936606735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168035190398233957737823 252052785597350936606735)
            ·
              refine ⟨378079178396026404910103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252052785597350936606735 378079178396026404910103)
              ·
                refine ⟨567118767594039607365155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378079178396026404910103 567118767594039607365155)
                ·
                  refine ⟨850678151391059411047733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 567118767594039607365155 850678151391059411047733)
                  ·
                    refine ⟨79751076692911819785725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 850678151391059411047733 79751076692911819785725)
                    ·
                      rfl

theorem cell22_232972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_232972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_232972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_232972 prefixEnd_232972 := by exact prefixLift 232972
  have htrace : WordTrace (prefixWord ++ tailWord_232972) baseStart_232972 baseEnd_232972 := by
    simpa [prefixWord, tailWord_232972, baseEnd_232972] using wordTrace_append hprefix tailTrace_232972
  have hstable : (prefixWord ++ tailWord_232972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_232972).length < 2 ^ (prefixWord ++ tailWord_232972).sum := by decide
  have hdescent : baseEnd_232972 < baseStart_232972 := by decide
  rcases family_descends (prefixWord ++ tailWord_232972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233013 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 7]
def baseStart_233013 : Nat := 118140960795 + 233013 * 2 ^ 59
def prefixEnd_233013 : Nat := 4983230072969 + 3 ^ 40 * 233013 * 2
def baseEnd_233013 : Nat := 26588370610267126503533

theorem tailTrace_233013 : CollatzResearch.WordTrace tailWord_233013 prefixEnd_233013 26588370610267126503533 := by
  unfold tailWord_233013
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498682304841171297231693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5665788203227447531487795 8498682304841171297231693)
  ·
    refine ⟨3187005864315439236461885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8498682304841171297231693 3187005864315439236461885)
    ·
      refine ⟨1195127199118289713673207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3187005864315439236461885 1195127199118289713673207)
      ·
        refine ⟨1792690798677434570509811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195127199118289713673207 1792690798677434570509811)
        ·
          refine ⟨2689036198016151855764717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1792690798677434570509811 2689036198016151855764717)
          ·
            refine ⟨1008388574256056945911769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2689036198016151855764717 1008388574256056945911769)
            ·
              refine ⟨756291430692042709433827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1008388574256056945911769 756291430692042709433827)
              ·
                refine ⟨1134437146038064064150741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 756291430692042709433827 1134437146038064064150741)
                ·
                  refine ⟨26588370610267126503533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1134437146038064064150741 26588370610267126503533)
                  ·
                    rfl

theorem cell22_233013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_233013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233013 prefixEnd_233013 := by exact prefixLift 233013
  have htrace : WordTrace (prefixWord ++ tailWord_233013) baseStart_233013 baseEnd_233013 := by
    simpa [prefixWord, tailWord_233013, baseEnd_233013] using wordTrace_append hprefix tailTrace_233013
  have hstable : (prefixWord ++ tailWord_233013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233013).length < 2 ^ (prefixWord ++ tailWord_233013).sum := by decide
  have hdescent : baseEnd_233013 < baseStart_233013 := by decide
  rcases family_descends (prefixWord ++ tailWord_233013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233017 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_233017 : Nat := 118140960795 + 233017 * 2 ^ 59
def prefixEnd_233017 : Nat := 4983230072969 + 3 ^ 40 * 233017 * 2
def baseEnd_233017 : Nat := 79766481112546702410587

theorem tailTrace_233017 : CollatzResearch.WordTrace tailWord_233017 prefixEnd_233017 79766481112546702410587 := by
  unfold tailWord_233017
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498828196826679980377305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5665885464551119986918203 8498828196826679980377305)
  ·
    refine ⟨6374121147620009985282979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8498828196826679980377305 6374121147620009985282979)
    ·
      refine ⟨9561181721430014977924469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6374121147620009985282979 9561181721430014977924469)
      ·
        refine ⟨896360786384063904180419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9561181721430014977924469 896360786384063904180419)
        ·
          refine ⟨1344541179576095856270629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 896360786384063904180419 1344541179576095856270629)
          ·
            refine ⟨252101471170517973050743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1344541179576095856270629 252101471170517973050743)
            ·
              refine ⟨378152206755776959576115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252101471170517973050743 378152206755776959576115)
              ·
                refine ⟨567228310133665439364173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378152206755776959576115 567228310133665439364173)
                ·
                  refine ⟨212710616300124539761565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 567228310133665439364173 212710616300124539761565)
                  ·
                    refine ⟨79766481112546702410587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212710616300124539761565 79766481112546702410587)
                    ·
                      rfl

theorem cell22_233017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_233017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233017 prefixEnd_233017 := by exact prefixLift 233017
  have htrace : WordTrace (prefixWord ++ tailWord_233017) baseStart_233017 baseEnd_233017 := by
    simpa [prefixWord, tailWord_233017, baseEnd_233017] using wordTrace_append hprefix tailTrace_233017
  have hstable : (prefixWord ++ tailWord_233017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233017).length < 2 ^ (prefixWord ++ tailWord_233017).sum := by decide
  have hdescent : baseEnd_233017 < baseStart_233017 := by decide
  rcases family_descends (prefixWord ++ tailWord_233017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233088 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 6]
def baseStart_233088 : Nat := 118140960795 + 233088 * 2 ^ 59
def prefixEnd_233088 : Nat := 4983230072969 + 3 ^ 40 * 233088 * 2
def baseEnd_233088 : Nat := 79790785863526183885369

theorem tailTrace_233088 : CollatzResearch.WordTrace tailWord_233088 prefixEnd_233088 79790785863526183885369 := by
  unfold tailWord_233088
  simp only [CollatzResearch.WordTrace]
  refine ⟨4250708889784729553105959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5667611853046306070807945 4250708889784729553105959)
  ·
    refine ⟨6376063334677094329658939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4250708889784729553105959 6376063334677094329658939)
    ·
      refine ⟨9564095002015641494488409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376063334677094329658939 9564095002015641494488409)
      ·
        refine ⟨7173071251511731120866307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9564095002015641494488409 7173071251511731120866307)
        ·
          refine ⟨10759606877267596681299461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173071251511731120866307 10759606877267596681299461)
          ·
            refine ⟨2017426289487674377743649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10759606877267596681299461 2017426289487674377743649)
            ·
              refine ⟨1513069717115755783307737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2017426289487674377743649 1513069717115755783307737)
              ·
                refine ⟨1134802287836816837480803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513069717115755783307737 1134802287836816837480803)
                ·
                  refine ⟨1702203431755225256221205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1134802287836816837480803 1702203431755225256221205)
                  ·
                    refine ⟨79790785863526183885369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1702203431755225256221205 79790785863526183885369)
                    ·
                      rfl

theorem cell22_233088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_233088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233088 prefixEnd_233088 := by exact prefixLift 233088
  have htrace : WordTrace (prefixWord ++ tailWord_233088) baseStart_233088 baseEnd_233088 := by
    simpa [prefixWord, tailWord_233088, baseEnd_233088] using wordTrace_append hprefix tailTrace_233088
  have hstable : (prefixWord ++ tailWord_233088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233088).length < 2 ^ (prefixWord ++ tailWord_233088).sum := by decide
  have hdescent : baseEnd_233088 < baseStart_233088 := by decide
  rcases family_descends (prefixWord ++ tailWord_233088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233124 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_233124 : Nat := 118140960795 + 233124 * 2 ^ 59
def prefixEnd_233124 : Nat := 4983230072969 + 3 ^ 40 * 233124 * 2
def baseEnd_233124 : Nat := 79803109399234089985259

theorem tailTrace_233124 : CollatzResearch.WordTrace tailWord_233124 prefixEnd_233124 79803109399234089985259 := by
  unfold tailWord_233124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251365403719518627261213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5668487204959358169681617 4251365403719518627261213)
  ·
    refine ⟨1594262026394819485222955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4251365403719518627261213 1594262026394819485222955)
    ·
      refine ⟨2391393039592229227834433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594262026394819485222955 2391393039592229227834433)
      ·
        refine ⟨1793544779694171920875825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2391393039592229227834433 1793544779694171920875825)
        ·
          refine ⟨1345158584770628940656869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1793544779694171920875825 1345158584770628940656869)
          ·
            refine ⟨252217234644492926373163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1345158584770628940656869 252217234644492926373163)
            ·
              refine ⟨378325851966739389559745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252217234644492926373163 378325851966739389559745)
              ·
                refine ⟨283744388975054542169809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378325851966739389559745 283744388975054542169809)
                ·
                  refine ⟨212808291731290906627357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283744388975054542169809 212808291731290906627357)
                  ·
                    refine ⟨79803109399234089985259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212808291731290906627357 79803109399234089985259)
                    ·
                      rfl

theorem cell22_233124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_233124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233124 prefixEnd_233124 := by exact prefixLift 233124
  have htrace : WordTrace (prefixWord ++ tailWord_233124) baseStart_233124 baseEnd_233124 := by
    simpa [prefixWord, tailWord_233124, baseEnd_233124] using wordTrace_append hprefix tailTrace_233124
  have hstable : (prefixWord ++ tailWord_233124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233124).length < 2 ^ (prefixWord ++ tailWord_233124).sum := by decide
  have hdescent : baseEnd_233124 < baseStart_233124 := by decide
  rcases family_descends (prefixWord ++ tailWord_233124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233141 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 2, 3]
def baseStart_233141 : Nat := 118140960795 + 233141 * 2 ^ 59
def prefixEnd_233141 : Nat := 4983230072969 + 3 ^ 40 * 233141 * 2
def baseEnd_233141 : Nat := 79808928846651712310207

theorem tailTrace_233141 : CollatzResearch.WordTrace tailWord_233141 prefixEnd_233141 79808928846651712310207 := by
  unfold tailWord_233141
  simp only [CollatzResearch.WordTrace]
  refine ⟨8503350848377449157891277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5668900565584966105260851 8503350848377449157891277)
  ·
    refine ⟨3188756568141543434209229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8503350848377449157891277 3188756568141543434209229)
    ·
      refine ⟨1195783713053078787828461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3188756568141543434209229 1195783713053078787828461)
      ·
        refine ⟨448418892394904545435673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1195783713053078787828461 448418892394904545435673)
        ·
          refine ⟨336314169296178409076755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 448418892394904545435673 336314169296178409076755)
          ·
            refine ⟨504471253944267613615133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336314169296178409076755 504471253944267613615133)
            ·
              refine ⟨189176720229100355105675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504471253944267613615133 189176720229100355105675)
              ·
                refine ⟨283765080343650532658513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189176720229100355105675 283765080343650532658513)
                ·
                  refine ⟨212823810257737899493885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283765080343650532658513 212823810257737899493885)
                  ·
                    refine ⟨79808928846651712310207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212823810257737899493885 79808928846651712310207)
                    ·
                      rfl

theorem cell22_233141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_233141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233141 prefixEnd_233141 := by exact prefixLift 233141
  have htrace : WordTrace (prefixWord ++ tailWord_233141) baseStart_233141 baseEnd_233141 := by
    simpa [prefixWord, tailWord_233141, baseEnd_233141] using wordTrace_append hprefix tailTrace_233141
  have hstable : (prefixWord ++ tailWord_233141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233141).length < 2 ^ (prefixWord ++ tailWord_233141).sum := by decide
  have hdescent : baseEnd_233141 < baseStart_233141 := by decide
  rcases family_descends (prefixWord ++ tailWord_233141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233163 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 7]
def baseStart_233163 : Nat := 118140960795 + 233163 * 2 ^ 59
def prefixEnd_233163 : Nat := 4983230072969 + 3 ^ 40 * 233163 * 2
def baseEnd_233163 : Nat := 79816459896250988260139

theorem tailTrace_233163 : CollatzResearch.WordTrace tailWord_233163 prefixEnd_233163 79816459896250988260139 := by
  unfold tailWord_233163
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504153254297746915192143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5669435502865164610128095 8504153254297746915192143)
  ·
    refine ⟨12756229881446620372788215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504153254297746915192143 12756229881446620372788215)
    ·
      refine ⟨19134344822169930559182323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756229881446620372788215 19134344822169930559182323)
      ·
        refine ⟨28701517233254895838773485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134344822169930559182323 28701517233254895838773485)
        ·
          refine ⟨10763068962470585939540057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28701517233254895838773485 10763068962470585939540057)
          ·
            refine ⟨8072301721852939454655043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10763068962470585939540057 8072301721852939454655043)
            ·
              refine ⟨12108452582779409181982565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8072301721852939454655043 12108452582779409181982565)
              ·
                refine ⟨2270334859271139221621731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12108452582779409181982565 2270334859271139221621731)
                ·
                  refine ⟨3405502288906708832432597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2270334859271139221621731 3405502288906708832432597)
                  ·
                    refine ⟨79816459896250988260139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3405502288906708832432597 79816459896250988260139)
                    ·
                      rfl

theorem cell22_233163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_233163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233163 prefixEnd_233163 := by exact prefixLift 233163
  have htrace : WordTrace (prefixWord ++ tailWord_233163) baseStart_233163 baseEnd_233163 := by
    simpa [prefixWord, tailWord_233163, baseEnd_233163] using wordTrace_append hprefix tailTrace_233163
  have hstable : (prefixWord ++ tailWord_233163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233163).length < 2 ^ (prefixWord ++ tailWord_233163).sum := by decide
  have hdescent : baseEnd_233163 < baseStart_233163 := by decide
  rcases family_descends (prefixWord ++ tailWord_233163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233169 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 1, 3]
def baseStart_233169 : Nat := 118140960795 + 233169 * 2 ^ 59
def prefixEnd_233169 : Nat := 4983230072969 + 3 ^ 40 * 233169 * 2
def baseEnd_233169 : Nat := 79818513818868972610121

theorem tailTrace_233169 : CollatzResearch.WordTrace tailWord_233169 prefixEnd_233169 79818513818868972610121 := by
  unfold tailWord_233169
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504372092276009939910561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5669581394850673293273707 8504372092276009939910561)
  ·
    refine ⟨6378279069207007454932921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8504372092276009939910561 6378279069207007454932921)
    ·
      refine ⟨4783709301905255591199691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6378279069207007454932921 4783709301905255591199691)
      ·
        refine ⟨7175563952857883386799537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4783709301905255591199691 7175563952857883386799537)
        ·
          refine ⟨5381672964643412540099653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7175563952857883386799537 5381672964643412540099653)
          ·
            refine ⟨1009063680870639851268685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5381672964643412540099653 1009063680870639851268685)
            ·
              refine ⟨378398880326489944225757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1009063680870639851268685 378398880326489944225757)
              ·
                refine ⟨141899580122433729084659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 378398880326489944225757 141899580122433729084659)
                ·
                  refine ⟨212849370183650593626989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141899580122433729084659 212849370183650593626989)
                  ·
                    refine ⟨79818513818868972610121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212849370183650593626989 79818513818868972610121)
                    ·
                      rfl

theorem cell22_233169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_233169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233169 prefixEnd_233169 := by exact prefixLift 233169
  have htrace : WordTrace (prefixWord ++ tailWord_233169) baseStart_233169 baseEnd_233169 := by
    simpa [prefixWord, tailWord_233169, baseEnd_233169] using wordTrace_append hprefix tailTrace_233169
  have hstable : (prefixWord ++ tailWord_233169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233169).length < 2 ^ (prefixWord ++ tailWord_233169).sum := by decide
  have hdescent : baseEnd_233169 < baseStart_233169 := by decide
  rcases family_descends (prefixWord ++ tailWord_233169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233272 : List Nat := [2, 1, 2, 1, 3, 4, 3, 6]
def baseStart_233272 : Nat := 118140960795 + 233272 * 2 ^ 59
def prefixEnd_233272 : Nat := 4983230072969 + 3 ^ 40 * 233272 * 2
def baseEnd_233272 : Nat := 8872641424867893031645

theorem tailTrace_233272 : CollatzResearch.WordTrace tailWord_233272 prefixEnd_233272 8872641424867893031645 := by
  unfold tailWord_233272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4254064405451429265455035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5672085873935239020606713 4254064405451429265455035)
  ·
    refine ⟨6381096608177143898182553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4254064405451429265455035 6381096608177143898182553)
    ·
      refine ⟨4785822456132857923636915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6381096608177143898182553 4785822456132857923636915)
      ·
        refine ⟨7178733684199286885455373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785822456132857923636915 7178733684199286885455373)
        ·
          refine ⟨2692025131574732582045765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7178733684199286885455373 2692025131574732582045765)
          ·
            refine ⟨504754712170262359133581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2692025131574732582045765 504754712170262359133581)
            ·
              refine ⟨189283017063848384675093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 504754712170262359133581 189283017063848384675093)
              ·
                refine ⟨8872641424867893031645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189283017063848384675093 8872641424867893031645)
                ·
                  rfl

theorem cell22_233272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 6].length) (baseStart_233272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233272 prefixEnd_233272 := by exact prefixLift 233272
  have htrace : WordTrace (prefixWord ++ tailWord_233272) baseStart_233272 baseEnd_233272 := by
    simpa [prefixWord, tailWord_233272, baseEnd_233272] using wordTrace_append hprefix tailTrace_233272
  have hstable : (prefixWord ++ tailWord_233272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233272).length < 2 ^ (prefixWord ++ tailWord_233272).sum := by decide
  have hdescent : baseEnd_233272 < baseStart_233272 := by decide
  rcases family_descends (prefixWord ++ tailWord_233272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233274 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 2, 4]
def baseStart_233274 : Nat := 118140960795 + 233274 * 2 ^ 59
def prefixEnd_233274 : Nat := 4983230072969 + 3 ^ 40 * 233274 * 2
def baseEnd_233274 : Nat := 79854457464683698734799

theorem tailTrace_233274 : CollatzResearch.WordTrace tailWord_233274 prefixEnd_233274 79854457464683698734799 := by
  unfold tailWord_233274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127050439223903218120719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5672134504597075248321917 2127050439223903218120719)
  ·
    refine ⟨3190575658835854827181079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2127050439223903218120719 3190575658835854827181079)
    ·
      refine ⟨4785863488253782240771619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190575658835854827181079 4785863488253782240771619)
      ·
        refine ⟨7178795232380673361157429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4785863488253782240771619 7178795232380673361157429)
        ·
          refine ⟨673012053035688127608509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7178795232380673361157429 673012053035688127608509)
          ·
            refine ⟨252379519888383047853191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673012053035688127608509 252379519888383047853191)
            ·
              refine ⟨378569279832574571779787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252379519888383047853191 378569279832574571779787)
              ·
                refine ⟨567853919748861857669681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 378569279832574571779787 567853919748861857669681)
                ·
                  refine ⟨425890439811646393252261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 567853919748861857669681 425890439811646393252261)
                  ·
                    refine ⟨79854457464683698734799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 425890439811646393252261 79854457464683698734799)
                    ·
                      rfl

theorem cell22_233274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_233274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233274 prefixEnd_233274 := by exact prefixLift 233274
  have htrace : WordTrace (prefixWord ++ tailWord_233274) baseStart_233274 baseEnd_233274 := by
    simpa [prefixWord, tailWord_233274, baseEnd_233274] using wordTrace_append hprefix tailTrace_233274
  have hstable : (prefixWord ++ tailWord_233274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233274).length < 2 ^ (prefixWord ++ tailWord_233274).sum := by decide
  have hdescent : baseEnd_233274 < baseStart_233274 := by decide
  rcases family_descends (prefixWord ++ tailWord_233274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233293 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_233293 : Nat := 118140960795 + 233293 * 2 ^ 59
def prefixEnd_233293 : Nat := 4983230072969 + 3 ^ 40 * 233293 * 2
def baseEnd_233293 : Nat := 79860961552973982509741

theorem tailTrace_233293 : CollatzResearch.WordTrace tailWord_233293 prefixEnd_233293 79860961552973982509741 := by
  unfold tailWord_233293
  simp only [CollatzResearch.WordTrace]
  refine ⟨8508894743826779117424533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5672596495884519411616355 8508894743826779117424533)
  ·
    refine ⟨398854441116880271129275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8508894743826779117424533 398854441116880271129275)
    ·
      refine ⟨598281661675320406693913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 398854441116880271129275 598281661675320406693913)
      ·
        refine ⟨448711246256490305020435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598281661675320406693913 448711246256490305020435)
        ·
          refine ⟨673066869384735457530653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448711246256490305020435 673066869384735457530653)
          ·
            refine ⟨252400076019275796573995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673066869384735457530653 252400076019275796573995)
            ·
              refine ⟨378600114028913694860993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252400076019275796573995 378600114028913694860993)
              ·
                refine ⟨283950085521685271145745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378600114028913694860993 283950085521685271145745)
                ·
                  refine ⟨212962564141263953359309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 283950085521685271145745 212962564141263953359309)
                  ·
                    refine ⟨79860961552973982509741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 212962564141263953359309 79860961552973982509741)
                    ·
                      rfl

theorem cell22_233293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_233293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233293 prefixEnd_233293 := by exact prefixLift 233293
  have htrace : WordTrace (prefixWord ++ tailWord_233293) baseStart_233293 baseEnd_233293 := by
    simpa [prefixWord, tailWord_233293, baseEnd_233293] using wordTrace_append hprefix tailTrace_233293
  have hstable : (prefixWord ++ tailWord_233293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233293).length < 2 ^ (prefixWord ++ tailWord_233293).sum := by decide
  have hdescent : baseEnd_233293 < baseStart_233293 := by decide
  rcases family_descends (prefixWord ++ tailWord_233293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233368 : List Nat := [2, 1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_233368 : Nat := 118140960795 + 233368 * 2 ^ 59
def prefixEnd_233368 : Nat := 4983230072969 + 3 ^ 40 * 233368 * 2
def baseEnd_233368 : Nat := 26628878528566262294837

theorem tailTrace_233368 : CollatzResearch.WordTrace tailWord_233368 prefixEnd_233368 26628878528566262294837 := by
  unfold tailWord_233368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255815109277533463202379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5674420145703377950936505 4255815109277533463202379)
  ·
    refine ⟨6383722663916300194803569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4255815109277533463202379 6383722663916300194803569)
    ·
      refine ⟨4787791997937225146102677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6383722663916300194803569 4787791997937225146102677)
      ·
        refine ⟨224427749903307428723563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4787791997937225146102677 224427749903307428723563)
        ·
          refine ⟨336641624854961143085345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224427749903307428723563 336641624854961143085345)
          ·
            refine ⟨252481218641220857314009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336641624854961143085345 252481218641220857314009)
            ·
              refine ⟨189360913980915642985507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252481218641220857314009 189360913980915642985507)
              ·
                refine ⟨284041370971373464478261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189360913980915642985507 284041370971373464478261)
                ·
                  refine ⟨26628878528566262294837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284041370971373464478261 26628878528566262294837)
                  ·
                    rfl

theorem cell22_233368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_233368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233368 prefixEnd_233368 := by exact prefixLift 233368
  have htrace : WordTrace (prefixWord ++ tailWord_233368) baseStart_233368 baseEnd_233368 := by
    simpa [prefixWord, tailWord_233368, baseEnd_233368] using wordTrace_append hprefix tailTrace_233368
  have hstable : (prefixWord ++ tailWord_233368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233368).length < 2 ^ (prefixWord ++ tailWord_233368).sum := by decide
  have hdescent : baseEnd_233368 < baseStart_233368 := by decide
  rcases family_descends (prefixWord ++ tailWord_233368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233439 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 5, 3]
def baseStart_233439 : Nat := 118140960795 + 233439 * 2 ^ 59
def prefixEnd_233439 : Nat := 4983230072969 + 3 ^ 40 * 233439 * 2
def baseEnd_233439 : Nat := 79910940336678268359293

theorem tailTrace_233439 : CollatzResearch.WordTrace tailWord_233439 prefixEnd_233439 79910940336678268359293 := by
  unfold tailWord_233439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8514219801297846052239371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676146534198564034826247 8514219801297846052239371)
  ·
    refine ⟨12771329701946769078359057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8514219801297846052239371 12771329701946769078359057)
    ·
      refine ⟨9578497276460076808769293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12771329701946769078359057 9578497276460076808769293)
      ·
        refine ⟨3591936478672528803288485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9578497276460076808769293 3591936478672528803288485)
        ·
          refine ⟨673488089751099150616591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3591936478672528803288485 673488089751099150616591)
          ·
            refine ⟨1010232134626648725924887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673488089751099150616591 1010232134626648725924887)
            ·
              refine ⟨1515348201939973088887331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1010232134626648725924887 1515348201939973088887331)
              ·
                refine ⟨2273022302909959633330997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515348201939973088887331 2273022302909959633330997)
                ·
                  refine ⟨213095840897808715624781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2273022302909959633330997 213095840897808715624781)
                  ·
                    refine ⟨79910940336678268359293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213095840897808715624781 79910940336678268359293)
                    ·
                      rfl

theorem cell22_233439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_233439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233439 prefixEnd_233439 := by exact prefixLift 233439
  have htrace : WordTrace (prefixWord ++ tailWord_233439) baseStart_233439 baseEnd_233439 := by
    simpa [prefixWord, tailWord_233439, baseEnd_233439] using wordTrace_append hprefix tailTrace_233439
  have hstable : (prefixWord ++ tailWord_233439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233439).length < 2 ^ (prefixWord ++ tailWord_233439).sum := by decide
  have hdescent : baseEnd_233439 < baseStart_233439 := by decide
  rcases family_descends (prefixWord ++ tailWord_233439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233456 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 1, 3]
def baseStart_233456 : Nat := 118140960795 + 233456 * 2 ^ 59
def prefixEnd_233456 : Nat := 4983230072969 + 3 ^ 40 * 233456 * 2
def baseEnd_233456 : Nat := 79916759784095890684241

theorem tailTrace_233456 : CollatzResearch.WordTrace tailWord_233456 prefixEnd_233456 79916759784095890684241 := by
  unfold tailWord_233456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257419921118128977804111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5676559894824171970405481 4257419921118128977804111)
  ·
    refine ⟨6386129881677193466706167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257419921118128977804111 6386129881677193466706167)
    ·
      refine ⟨9579194822515790200059251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6386129881677193466706167 9579194822515790200059251)
      ·
        refine ⟨14368792233773685300088877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9579194822515790200059251 14368792233773685300088877)
        ·
          refine ⟨5388297087665131987533329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14368792233773685300088877 5388297087665131987533329)
          ·
            refine ⟨4041222815748848990649997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5388297087665131987533329 4041222815748848990649997)
            ·
              refine ⟨1515458555905818371493749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4041222815748848990649997 1515458555905818371493749)
              ·
                refine ⟨142074239616170472327539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1515458555905818371493749 142074239616170472327539)
                ·
                  refine ⟨213111359424255708491309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142074239616170472327539 213111359424255708491309)
                  ·
                    refine ⟨79916759784095890684241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213111359424255708491309 79916759784095890684241)
                    ·
                      rfl

theorem cell22_233456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 3].length) (baseStart_233456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233456 prefixEnd_233456 := by exact prefixLift 233456
  have htrace : WordTrace (prefixWord ++ tailWord_233456) baseStart_233456 baseEnd_233456 := by
    simpa [prefixWord, tailWord_233456, baseEnd_233456] using wordTrace_append hprefix tailTrace_233456
  have hstable : (prefixWord ++ tailWord_233456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233456).length < 2 ^ (prefixWord ++ tailWord_233456).sum := by decide
  have hdescent : baseEnd_233456 < baseStart_233456 := by decide
  rcases family_descends (prefixWord ++ tailWord_233456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233467 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 2, 5]
def baseStart_233467 : Nat := 118140960795 + 233467 * 2 ^ 59
def prefixEnd_233467 : Nat := 4983230072969 + 3 ^ 40 * 233467 * 2
def baseEnd_233467 : Nat := 79920525308895528659207

theorem tailTrace_233467 : CollatzResearch.WordTrace tailWord_233467 prefixEnd_233467 79920525308895528659207 := by
  unfold tailWord_233467
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515241045196406834258655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676827363464271222839103 8515241045196406834258655)
  ·
    refine ⟨12772861567794610251387983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8515241045196406834258655 12772861567794610251387983)
    ·
      refine ⟨19159292351691915377081975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12772861567794610251387983 19159292351691915377081975)
      ·
        refine ⟨28738938527537873065622963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19159292351691915377081975 28738938527537873065622963)
        ·
          refine ⟨43108407791306809598434445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28738938527537873065622963 43108407791306809598434445)
          ·
            refine ⟨16165652921740053599412917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43108407791306809598434445 16165652921740053599412917)
            ·
              refine ⟨1515529961413130024944961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16165652921740053599412917 1515529961413130024944961)
              ·
                refine ⟨1136647471059847518708721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515529961413130024944961 1136647471059847518708721)
                ·
                  refine ⟨852485603294885639031541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1136647471059847518708721 852485603294885639031541)
                  ·
                    refine ⟨79920525308895528659207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 852485603294885639031541 79920525308895528659207)
                    ·
                      rfl

theorem cell22_233467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 5].length) (baseStart_233467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233467 prefixEnd_233467 := by exact prefixLift 233467
  have htrace : WordTrace (prefixWord ++ tailWord_233467) baseStart_233467 baseEnd_233467 := by
    simpa [prefixWord, tailWord_233467, baseEnd_233467] using wordTrace_append hprefix tailTrace_233467
  have hstable : (prefixWord ++ tailWord_233467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233467).length < 2 ^ (prefixWord ++ tailWord_233467).sum := by decide
  have hdescent : baseEnd_233467 < baseStart_233467 := by decide
  rcases family_descends (prefixWord ++ tailWord_233467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233469 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 5]
def baseStart_233469 : Nat := 118140960795 + 233469 * 2 ^ 59
def prefixEnd_233469 : Nat := 4983230072969 + 3 ^ 40 * 233469 * 2
def baseEnd_233469 : Nat := 26640403316589396703067

theorem tailTrace_233469 : CollatzResearch.WordTrace tailWord_233469 prefixEnd_233469 26640403316589396703067 := by
  unfold tailWord_233469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8515313991189161175831461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5676875994126107450554307 8515313991189161175831461)
  ·
    refine ⟨1596621373347967720468399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8515313991189161175831461 1596621373347967720468399)
    ·
      refine ⟨2394932060021951580702599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596621373347967720468399 2394932060021951580702599)
      ·
        refine ⟨3592398090032927371053899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394932060021951580702599 3592398090032927371053899)
        ·
          refine ⟨5388597135049391056580849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3592398090032927371053899 5388597135049391056580849)
          ·
            refine ⟨4041447851287043292435637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5388597135049391056580849 4041447851287043292435637)
            ·
              refine ⟨378885736058160308665841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4041447851287043292435637 378885736058160308665841)
              ·
                refine ⟨284164302043620231499381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 378885736058160308665841 284164302043620231499381)
                ·
                  refine ⟨26640403316589396703067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284164302043620231499381 26640403316589396703067)
                  ·
                    rfl

theorem cell22_233469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_233469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233469 prefixEnd_233469 := by exact prefixLift 233469
  have htrace : WordTrace (prefixWord ++ tailWord_233469) baseStart_233469 baseEnd_233469 := by
    simpa [prefixWord, tailWord_233469, baseEnd_233469] using wordTrace_append hprefix tailTrace_233469
  have hstable : (prefixWord ++ tailWord_233469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233469).length < 2 ^ (prefixWord ++ tailWord_233469).sum := by decide
  have hdescent : baseEnd_233469 < baseStart_233469 := by decide
  rcases family_descends (prefixWord ++ tailWord_233469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233486 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_233486 : Nat := 118140960795 + 233486 * 2 ^ 59
def prefixEnd_233486 : Nat := 4983230072969 + 3 ^ 40 * 233486 * 2
def baseEnd_233486 : Nat := 26642343132395270811383

theorem tailTrace_233486 : CollatzResearch.WordTrace tailWord_233486 prefixEnd_233486 26642343132395270811383 := by
  unfold tailWord_233486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1064491754015946634900039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5677289354751715386133541 1064491754015946634900039)
  ·
    refine ⟨1596737631023919952350059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1064491754015946634900039 1596737631023919952350059)
    ·
      refine ⟨2395106446535879928525089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1596737631023919952350059 2395106446535879928525089)
      ·
        refine ⟨1796329834901909946393817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2395106446535879928525089 1796329834901909946393817)
        ·
          refine ⟨1347247376176432459795363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796329834901909946393817 1347247376176432459795363)
          ·
            refine ⟨2020871064264648689693045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347247376176432459795363 2020871064264648689693045)
            ·
              refine ⟨189456662274810814658723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2020871064264648689693045 189456662274810814658723)
              ·
                refine ⟨284184993412216221988085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189456662274810814658723 284184993412216221988085)
                ·
                  refine ⟨26642343132395270811383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284184993412216221988085 26642343132395270811383)
                  ·
                    rfl

theorem cell22_233486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_233486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233486 prefixEnd_233486 := by exact prefixLift 233486
  have htrace : WordTrace (prefixWord ++ tailWord_233486) baseStart_233486 baseEnd_233486 := by
    simpa [prefixWord, tailWord_233486, baseEnd_233486] using wordTrace_append hprefix tailTrace_233486
  have hstable : (prefixWord ++ tailWord_233486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233486).length < 2 ^ (prefixWord ++ tailWord_233486).sum := by decide
  have hdescent : baseEnd_233486 < baseStart_233486 := by decide
  rcases family_descends (prefixWord ++ tailWord_233486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233608 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 3, 3]
def baseStart_233608 : Nat := 118140960795 + 233608 * 2 ^ 59
def prefixEnd_233608 : Nat := 4983230072969 + 3 ^ 40 * 233608 * 2
def baseEnd_233608 : Nat := 79968792490418160883775

theorem tailTrace_233608 : CollatzResearch.WordTrace tailWord_233608 prefixEnd_233608 79968792490418160883775 := by
  unfold tailWord_233608
  simp only [CollatzResearch.WordTrace]
  refine ⟨4260191868842793957570739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5680255825123725276760985 4260191868842793957570739)
  ·
    refine ⟨6390287803264190936356109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4260191868842793957570739 6390287803264190936356109)
    ·
      refine ⟨2396357926224071601133541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6390287803264190936356109 2396357926224071601133541)
      ·
        refine ⟨449317111167013425212539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2396357926224071601133541 449317111167013425212539)
        ·
          refine ⟨673975666750520137818809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449317111167013425212539 673975666750520137818809)
          ·
            refine ⟨505481750062890103364107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 673975666750520137818809 505481750062890103364107)
            ·
              refine ⟨758222625094335155046161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505481750062890103364107 758222625094335155046161)
              ·
                refine ⟨568666968820751366284621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758222625094335155046161 568666968820751366284621)
                ·
                  refine ⟨213250113307781762356733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 568666968820751366284621 213250113307781762356733)
                  ·
                    refine ⟨79968792490418160883775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213250113307781762356733 79968792490418160883775)
                    ·
                      rfl

theorem cell22_233608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_233608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233608 prefixEnd_233608 := by exact prefixLift 233608
  have htrace : WordTrace (prefixWord ++ tailWord_233608) baseStart_233608 baseEnd_233608 := by
    simpa [prefixWord, tailWord_233608, baseEnd_233608] using wordTrace_append hprefix tailTrace_233608
  have hstable : (prefixWord ++ tailWord_233608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233608).length < 2 ^ (prefixWord ++ tailWord_233608).sum := by decide
  have hdescent : baseEnd_233608 < baseStart_233608 := by decide
  rcases family_descends (prefixWord ++ tailWord_233608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233668 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_233668 : Nat := 118140960795 + 233668 * 2 ^ 59
def prefixEnd_233668 : Nat := 4983230072969 + 3 ^ 40 * 233668 * 2
def baseEnd_233668 : Nat := 79989331716598004383591

theorem tailTrace_233668 : CollatzResearch.WordTrace tailWord_233668 prefixEnd_233668 79989331716598004383591 := by
  unfold tailWord_233668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261286058734109081162829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5681714744978812108217105 4261286058734109081162829)
  ·
    refine ⟨1597982272025290905436061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4261286058734109081162829 1597982272025290905436061)
    ·
      refine ⟨599243352009484089538523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1597982272025290905436061 599243352009484089538523)
      ·
        refine ⟨898865028014226134307785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599243352009484089538523 898865028014226134307785)
        ·
          refine ⟨674148771010669600730839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 898865028014226134307785 674148771010669600730839)
          ·
            refine ⟨1011223156516004401096259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674148771010669600730839 1011223156516004401096259)
            ·
              refine ⟨1516834734774006601644389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1011223156516004401096259 1516834734774006601644389)
              ·
                refine ⟨284406512770126237808323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1516834734774006601644389 284406512770126237808323)
                ·
                  refine ⟨426609769155189356712485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284406512770126237808323 426609769155189356712485)
                  ·
                    refine ⟨79989331716598004383591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426609769155189356712485 79989331716598004383591)
                    ·
                      rfl

theorem cell22_233668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_233668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233668 prefixEnd_233668 := by exact prefixLift 233668
  have htrace : WordTrace (prefixWord ++ tailWord_233668) baseStart_233668 baseEnd_233668 := by
    simpa [prefixWord, tailWord_233668, baseEnd_233668] using wordTrace_append hprefix tailTrace_233668
  have hstable : (prefixWord ++ tailWord_233668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233668).length < 2 ^ (prefixWord ++ tailWord_233668).sum := by decide
  have hdescent : baseEnd_233668 < baseStart_233668 := by decide
  rcases family_descends (prefixWord ++ tailWord_233668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233679 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 6]
def baseStart_233679 : Nat := 118140960795 + 233679 * 2 ^ 59
def prefixEnd_233679 : Nat := 4983230072969 + 3 ^ 40 * 233679 * 2
def baseEnd_233679 : Nat := 79993097241397642358557

theorem tailTrace_233679 : CollatzResearch.WordTrace tailWord_233679 prefixEnd_233679 79993097241397642358557 := by
  unfold tailWord_233679
  simp only [CollatzResearch.WordTrace]
  refine ⟨8522973320428367040976091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5681982213618911360650727 8522973320428367040976091)
  ·
    refine ⟨12784459980642550561464137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8522973320428367040976091 12784459980642550561464137)
    ·
      refine ⟨9588344985481912921098103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12784459980642550561464137 9588344985481912921098103)
      ·
        refine ⟨14382517478222869381647155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588344985481912921098103 14382517478222869381647155)
        ·
          refine ⟨21573776217334304072470733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14382517478222869381647155 21573776217334304072470733)
          ·
            refine ⟨8090166081500364027176525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21573776217334304072470733 8090166081500364027176525)
            ·
              refine ⟨3033812280562636510191197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8090166081500364027176525 3033812280562636510191197)
              ·
                refine ⟨1137679605210988691321699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3033812280562636510191197 1137679605210988691321699)
                ·
                  refine ⟨1706519407816483036982549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1137679605210988691321699 1706519407816483036982549)
                  ·
                    refine ⟨79993097241397642358557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1706519407816483036982549 79993097241397642358557)
                    ·
                      rfl

theorem cell22_233679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_233679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233679 prefixEnd_233679 := by exact prefixLift 233679
  have htrace : WordTrace (prefixWord ++ tailWord_233679) baseStart_233679 baseEnd_233679 := by
    simpa [prefixWord, tailWord_233679, baseEnd_233679] using wordTrace_append hprefix tailTrace_233679
  have hstable : (prefixWord ++ tailWord_233679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233679).length < 2 ^ (prefixWord ++ tailWord_233679).sum := by decide
  have hdescent : baseEnd_233679 < baseStart_233679 := by decide
  rcases family_descends (prefixWord ++ tailWord_233679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233681 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 4, 3]
def baseStart_233681 : Nat := 118140960795 + 233681 * 2 ^ 59
def prefixEnd_233681 : Nat := 4983230072969 + 3 ^ 40 * 233681 * 2
def baseEnd_233681 : Nat := 79993781882270303808551

theorem tailTrace_233681 : CollatzResearch.WordTrace tailWord_233681 prefixEnd_233681 79993781882270303808551 := by
  unfold tailWord_233681
  simp only [CollatzResearch.WordTrace]
  refine ⟨8523046266421121382548897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5682030844280747588365931 8523046266421121382548897)
  ·
    refine ⟨6392284699815841036911673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8523046266421121382548897 6392284699815841036911673)
    ·
      refine ⟨4794213524861880777683755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6392284699815841036911673 4794213524861880777683755)
      ·
        refine ⟨7191320287292821166525633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794213524861880777683755 7191320287292821166525633)
        ·
          refine ⟨5393490215469615874894225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7191320287292821166525633 5393490215469615874894225)
          ·
            refine ⟨4045117661602211906170669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5393490215469615874894225 4045117661602211906170669)
            ·
              refine ⟨1516919123100829464814001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4045117661602211906170669 1516919123100829464814001)
              ·
                refine ⟨1137689342325622098610501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516919123100829464814001 1137689342325622098610501)
                ·
                  refine ⟨213316751686054143489469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1137689342325622098610501 213316751686054143489469)
                  ·
                    refine ⟨79993781882270303808551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213316751686054143489469 79993781882270303808551)
                    ·
                      rfl

theorem cell22_233681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_233681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233681 prefixEnd_233681 := by exact prefixLift 233681
  have htrace : WordTrace (prefixWord ++ tailWord_233681) baseStart_233681 baseEnd_233681 := by
    simpa [prefixWord, tailWord_233681, baseEnd_233681] using wordTrace_append hprefix tailTrace_233681
  have hstable : (prefixWord ++ tailWord_233681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233681).length < 2 ^ (prefixWord ++ tailWord_233681).sum := by decide
  have hdescent : baseEnd_233681 < baseStart_233681 := by decide
  rcases family_descends (prefixWord ++ tailWord_233681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233696 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 2, 4]
def baseStart_233696 : Nat := 118140960795 + 233696 * 2 ^ 59
def prefixEnd_233696 : Nat := 4983230072969 + 3 ^ 40 * 233696 * 2
def baseEnd_233696 : Nat := 79998916688815264683505

theorem tailTrace_233696 : CollatzResearch.WordTrace tailWord_233696 prefixEnd_233696 79998916688815264683505 := by
  unfold tailWord_233696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261796680683389472172471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5682395574244519296229961 4261796680683389472172471)
  ·
    refine ⟨6392695021025084208258707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261796680683389472172471 6392695021025084208258707)
    ·
      refine ⟨9589042531537626312388061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392695021025084208258707 9589042531537626312388061)
      ·
        refine ⟨3595890949326609867145523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9589042531537626312388061 3595890949326609867145523)
        ·
          refine ⟨5393836423989914800718285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595890949326609867145523 5393836423989914800718285)
          ·
            refine ⟨2022688658996218050269357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5393836423989914800718285 2022688658996218050269357)
            ·
              refine ⟨758508247123581768851009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2022688658996218050269357 758508247123581768851009)
              ·
                refine ⟨568881185342686326638257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 758508247123581768851009 568881185342686326638257)
                ·
                  refine ⟨426660889007014744978693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568881185342686326638257 426660889007014744978693)
                  ·
                    refine ⟨79998916688815264683505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426660889007014744978693 79998916688815264683505)
                    ·
                      rfl

theorem cell22_233696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_233696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233696 prefixEnd_233696 := by exact prefixLift 233696
  have htrace : WordTrace (prefixWord ++ tailWord_233696) baseStart_233696 baseEnd_233696 := by
    simpa [prefixWord, tailWord_233696, baseEnd_233696] using wordTrace_append hprefix tailTrace_233696
  have hstable : (prefixWord ++ tailWord_233696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233696).length < 2 ^ (prefixWord ++ tailWord_233696).sum := by decide
  have hdescent : baseEnd_233696 < baseStart_233696 := by decide
  rcases family_descends (prefixWord ++ tailWord_233696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233711 : List Nat := [1, 1, 2, 1, 6, 2, 2, 7]
def baseStart_233711 : Nat := 118140960795 + 233711 * 2 ^ 59
def prefixEnd_233711 : Nat := 4983230072969 + 3 ^ 40 * 233711 * 2
def baseEnd_233711 : Nat := 8889339055040025062051

theorem tailTrace_233711 : CollatzResearch.WordTrace tailWord_233711 prefixEnd_233711 8889339055040025062051 := by
  unfold tailWord_233711
  simp only [CollatzResearch.WordTrace]
  refine ⟨8524140456312436506140987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5682760304208291004093991 8524140456312436506140987)
  ·
    refine ⟨12786210684468654759211481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8524140456312436506140987 12786210684468654759211481)
    ·
      refine ⟨9589658013351491069408611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12786210684468654759211481 9589658013351491069408611)
      ·
        refine ⟨14384487020027236604112917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9589658013351491069408611 14384487020027236604112917)
        ·
          refine ⟨674272829063776715817793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14384487020027236604112917 674272829063776715817793)
          ·
            refine ⟨505704621797832536863345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674272829063776715817793 505704621797832536863345)
            ·
              refine ⟨379278466348374402647509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505704621797832536863345 379278466348374402647509)
              ·
                refine ⟨8889339055040025062051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 379278466348374402647509 8889339055040025062051)
                ·
                  rfl

theorem cell22_233711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 7].length) (baseStart_233711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233711 prefixEnd_233711 := by exact prefixLift 233711
  have htrace : WordTrace (prefixWord ++ tailWord_233711) baseStart_233711 baseEnd_233711 := by
    simpa [prefixWord, tailWord_233711, baseEnd_233711] using wordTrace_append hprefix tailTrace_233711
  have hstable : (prefixWord ++ tailWord_233711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233711).length < 2 ^ (prefixWord ++ tailWord_233711).sum := by decide
  have hdescent : baseEnd_233711 < baseStart_233711 := by decide
  rcases family_descends (prefixWord ++ tailWord_233711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233730 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_233730 : Nat := 118140960795 + 233730 * 2 ^ 59
def prefixEnd_233730 : Nat := 4983230072969 + 3 ^ 40 * 233730 * 2
def baseEnd_233730 : Nat := 80010555583650509333401

theorem tailTrace_233730 : CollatzResearch.WordTrace tailWord_233730 prefixEnd_233730 80010555583650509333401 := by
  unfold tailWord_233730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131208360810900687770661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5683222295495735167388429 2131208360810900687770661)
  ·
    refine ⟨399601567652043878956999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2131208360810900687770661 399601567652043878956999)
    ·
      refine ⟨599402351478065818435499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399601567652043878956999 599402351478065818435499)
      ·
        refine ⟨899103527217098727653249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 599402351478065818435499 899103527217098727653249)
        ·
          refine ⟨674327645412824045739937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899103527217098727653249 674327645412824045739937)
          ·
            refine ⟨505745734059618034304953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674327645412824045739937 505745734059618034304953)
            ·
              refine ⟨379309300544713525728715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505745734059618034304953 379309300544713525728715)
              ·
                refine ⟨568963950817070288593073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379309300544713525728715 568963950817070288593073)
                ·
                  refine ⟨426722963112802716444805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 568963950817070288593073 426722963112802716444805)
                  ·
                    refine ⟨80010555583650509333401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 426722963112802716444805 80010555583650509333401)
                    ·
                      rfl

theorem cell22_233730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_233730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233730 prefixEnd_233730 := by exact prefixLift 233730
  have htrace : WordTrace (prefixWord ++ tailWord_233730) baseStart_233730 baseEnd_233730 := by
    simpa [prefixWord, tailWord_233730, baseEnd_233730] using wordTrace_append hprefix tailTrace_233730
  have hstable : (prefixWord ++ tailWord_233730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233730).length < 2 ^ (prefixWord ++ tailWord_233730).sum := by decide
  have hdescent : baseEnd_233730 < baseStart_233730 := by decide
  rcases family_descends (prefixWord ++ tailWord_233730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233940 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_233940 : Nat := 118140960795 + 233940 * 2 ^ 59
def prefixEnd_233940 : Nat := 4983230072969 + 3 ^ 40 * 233940 * 2
def baseEnd_233940 : Nat := 80082442875279961582757

theorem tailTrace_233940 : CollatzResearch.WordTrace tailWord_233940 prefixEnd_233940 80082442875279961582757 := by
  unfold tailWord_233940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266246386241404308113637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5688328514988539077484849 4266246386241404308113637)
  ·
    refine ⟨799921197420263307771307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4266246386241404308113637 799921197420263307771307)
    ·
      refine ⟨1199881796130394961656961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799921197420263307771307 1199881796130394961656961)
      ·
        refine ⟨899911347097796221242721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1199881796130394961656961 899911347097796221242721)
        ·
          refine ⟨674933510323347165932041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 899911347097796221242721 674933510323347165932041)
          ·
            refine ⟨506200132742510374449031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 674933510323347165932041 506200132742510374449031)
            ·
              refine ⟨759300199113765561673547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506200132742510374449031 759300199113765561673547)
              ·
                refine ⟨1138950298670648342510321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759300199113765561673547 1138950298670648342510321)
                ·
                  refine ⟨854212724002986256882741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1138950298670648342510321 854212724002986256882741)
                  ·
                    refine ⟨80082442875279961582757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 854212724002986256882741 80082442875279961582757)
                    ·
                      rfl

theorem cell22_233940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_233940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233940 prefixEnd_233940 := by exact prefixLift 233940
  have htrace : WordTrace (prefixWord ++ tailWord_233940) baseStart_233940 baseEnd_233940 := by
    simpa [prefixWord, tailWord_233940, baseEnd_233940] using wordTrace_append hprefix tailTrace_233940
  have hstable : (prefixWord ++ tailWord_233940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233940).length < 2 ^ (prefixWord ++ tailWord_233940).sum := by decide
  have hdescent : baseEnd_233940 < baseStart_233940 := by decide
  rcases family_descends (prefixWord ++ tailWord_233940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233953 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 6]
def baseStart_233953 : Nat := 118140960795 + 233953 * 2 ^ 59
def prefixEnd_233953 : Nat := 4983230072969 + 3 ^ 40 * 233953 * 2
def baseEnd_233953 : Nat := 26695631013650753669239

theorem tailTrace_233953 : CollatzResearch.WordTrace tailWord_233953 prefixEnd_233953 26695631013650753669239 := by
  unfold tailWord_233953
  simp only [CollatzResearch.WordTrace]
  refine ⟨8532966921435711836450513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5688644614290474557633675 8532966921435711836450513)
  ·
    refine ⟨6399725191076783877337885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8532966921435711836450513 6399725191076783877337885)
    ·
      refine ⟨2399896946653793954001707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6399725191076783877337885 2399896946653793954001707)
      ·
        refine ⟨3599845419980690931002561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2399896946653793954001707 3599845419980690931002561)
        ·
          refine ⟨2699884064985518198251921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3599845419980690931002561 2699884064985518198251921)
          ·
            refine ⟨2024913048739138648688941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2699884064985518198251921 2024913048739138648688941)
            ·
              refine ⟨759342393277176993258353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2024913048739138648688941 759342393277176993258353)
              ·
                refine ⟨569506794957882744943765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759342393277176993258353 569506794957882744943765)
                ·
                  refine ⟨26695631013650753669239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 569506794957882744943765 26695631013650753669239)
                  ·
                    rfl

theorem cell22_233953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_233953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233953 prefixEnd_233953 := by exact prefixLift 233953
  have htrace : WordTrace (prefixWord ++ tailWord_233953) baseStart_233953 baseEnd_233953 := by
    simpa [prefixWord, tailWord_233953, baseEnd_233953] using wordTrace_append hprefix tailTrace_233953
  have hstable : (prefixWord ++ tailWord_233953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233953).length < 2 ^ (prefixWord ++ tailWord_233953).sum := by decide
  have hdescent : baseEnd_233953 < baseStart_233953 := by decide
  rcases family_descends (prefixWord ++ tailWord_233953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233968 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 1, 5]
def baseStart_233968 : Nat := 118140960795 + 233968 * 2 ^ 59
def prefixEnd_233968 : Nat := 4983230072969 + 3 ^ 40 * 233968 * 2
def baseEnd_233968 : Nat := 80092027847497221882671

theorem tailTrace_233968 : CollatzResearch.WordTrace tailWord_233968 prefixEnd_233968 80092027847497221882671 := by
  unfold tailWord_233968
  simp only [CollatzResearch.WordTrace]
  refine ⟨4266757008190684699123279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5689009344254246265497705 4266757008190684699123279)
  ·
    refine ⟨6400135512286027048684919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4266757008190684699123279 6400135512286027048684919)
    ·
      refine ⟨9600203268429040573027379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6400135512286027048684919 9600203268429040573027379)
      ·
        refine ⟨14400304902643560859541069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600203268429040573027379 14400304902643560859541069)
        ·
          refine ⟨5400114338491335322327901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14400304902643560859541069 5400114338491335322327901)
          ·
            refine ⟨2025042876934250745872963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5400114338491335322327901 2025042876934250745872963)
            ·
              refine ⟨3037564315401376118809445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025042876934250745872963 3037564315401376118809445)
              ·
                refine ⟨569543309137758022276771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3037564315401376118809445 569543309137758022276771)
                ·
                  refine ⟨854314963706637033415157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 569543309137758022276771 854314963706637033415157)
                  ·
                    refine ⟨80092027847497221882671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 854314963706637033415157 80092027847497221882671)
                    ·
                      rfl

theorem cell22_233968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_233968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233968 prefixEnd_233968 := by exact prefixLift 233968
  have htrace : WordTrace (prefixWord ++ tailWord_233968) baseStart_233968 baseEnd_233968 := by
    simpa [prefixWord, tailWord_233968, baseEnd_233968] using wordTrace_append hprefix tailTrace_233968
  have hstable : (prefixWord ++ tailWord_233968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233968).length < 2 ^ (prefixWord ++ tailWord_233968).sum := by decide
  have hdescent : baseEnd_233968 < baseStart_233968 := by decide
  rcases family_descends (prefixWord ++ tailWord_233968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_233983 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 4, 4]
def baseStart_233983 : Nat := 118140960795 + 233983 * 2 ^ 59
def prefixEnd_233983 : Nat := 4983230072969 + 3 ^ 40 * 233983 * 2
def baseEnd_233983 : Nat := 80097162654042182757625

theorem tailTrace_233983 : CollatzResearch.WordTrace tailWord_233983 prefixEnd_233983 80097162654042182757625 := by
  unfold tailWord_233983
  simp only [CollatzResearch.WordTrace]
  refine ⟨8534061111327026960042603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5689374074218017973361735 8534061111327026960042603)
  ·
    refine ⟨12801091666990540440063905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8534061111327026960042603 12801091666990540440063905)
    ·
      refine ⟨9600818750242905330047929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12801091666990540440063905 9600818750242905330047929)
      ·
        refine ⟨7200614062682178997535947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9600818750242905330047929 7200614062682178997535947)
        ·
          refine ⟨10800921094023268496303921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200614062682178997535947 10800921094023268496303921)
          ·
            refine ⟨8100690820517451372227941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10800921094023268496303921 8100690820517451372227941)
            ·
              refine ⟨1518879528847022132292739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8100690820517451372227941 1518879528847022132292739)
              ·
                refine ⟨2278319293270533198439109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518879528847022132292739 2278319293270533198439109)
                ·
                  refine ⟨427184867488224974707333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278319293270533198439109 427184867488224974707333)
                  ·
                    refine ⟨80097162654042182757625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427184867488224974707333 80097162654042182757625)
                    ·
                      rfl

theorem cell22_233983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_233983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_233983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_233983 prefixEnd_233983 := by exact prefixLift 233983
  have htrace : WordTrace (prefixWord ++ tailWord_233983) baseStart_233983 baseEnd_233983 := by
    simpa [prefixWord, tailWord_233983, baseEnd_233983] using wordTrace_append hprefix tailTrace_233983
  have hstable : (prefixWord ++ tailWord_233983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_233983).length < 2 ^ (prefixWord ++ tailWord_233983).sum := by decide
  have hdescent : baseEnd_233983 < baseStart_233983 := by decide
  rcases family_descends (prefixWord ++ tailWord_233983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234060 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 5]
def baseStart_234060 : Nat := 118140960795 + 234060 * 2 ^ 59
def prefixEnd_234060 : Nat := 4983230072969 + 3 ^ 40 * 234060 * 2
def baseEnd_234060 : Nat := 26707840442546549527463

theorem tailTrace_234060 : CollatzResearch.WordTrace tailWord_234060 prefixEnd_234060 26707840442546549527463 := by
  unfold tailWord_234060
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268434766024034555297817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5691246354698712740397089 4268434766024034555297817)
  ·
    refine ⟨3201326074518025916473363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4268434766024034555297817 3201326074518025916473363)
    ·
      refine ⟨4801989111777038874710045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3201326074518025916473363 4801989111777038874710045)
      ·
        refine ⟨1800745916916389578016267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4801989111777038874710045 1800745916916389578016267)
        ·
          refine ⟨2701118875374584367024401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800745916916389578016267 2701118875374584367024401)
          ·
            refine ⟨2025839156530938275268301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701118875374584367024401 2025839156530938275268301)
            ·
              refine ⟨759689683699101853225613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2025839156530938275268301 759689683699101853225613)
              ·
                refine ⟨284883631387163194959605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 759689683699101853225613 284883631387163194959605)
                ·
                  refine ⟨26707840442546549527463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284883631387163194959605 26707840442546549527463)
                  ·
                    rfl

theorem cell22_234060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_234060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234060 prefixEnd_234060 := by exact prefixLift 234060
  have htrace : WordTrace (prefixWord ++ tailWord_234060) baseStart_234060 baseEnd_234060 := by
    simpa [prefixWord, tailWord_234060, baseEnd_234060] using wordTrace_append hprefix tailTrace_234060
  have hstable : (prefixWord ++ tailWord_234060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234060).length < 2 ^ (prefixWord ++ tailWord_234060).sum := by decide
  have hdescent : baseEnd_234060 < baseStart_234060 := by decide
  rcases family_descends (prefixWord ++ tailWord_234060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234098 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 1, 3]
def baseStart_234098 : Nat := 118140960795 + 234098 * 2 ^ 59
def prefixEnd_234098 : Nat := 4983230072969 + 3 ^ 40 * 234098 * 2
def baseEnd_234098 : Nat := 80136529504220216132273

theorem tailTrace_234098 : CollatzResearch.WordTrace tailWord_234098 prefixEnd_234098 80136529504220216132273 := by
  unfold tailWord_234098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134563876477600400119737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5692170337273601066985965 2134563876477600400119737)
  ·
    refine ⟨1600922907358200300089803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2134563876477600400119737 1600922907358200300089803)
    ·
      refine ⟨2401384361037300450134705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600922907358200300089803 2401384361037300450134705)
      ·
        refine ⟨1801038270777975337601029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2401384361037300450134705 1801038270777975337601029)
        ·
          refine ⟨337694675770870375800193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1801038270777975337601029 337694675770870375800193)
          ·
            refine ⟨253271006828152781850145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337694675770870375800193 253271006828152781850145)
            ·
              refine ⟨189953255121114586387609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253271006828152781850145 189953255121114586387609)
              ·
                refine ⟨142464941340835939790707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189953255121114586387609 142464941340835939790707)
                ·
                  refine ⟨213697412011253909686061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142464941340835939790707 213697412011253909686061)
                  ·
                    refine ⟨80136529504220216132273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213697412011253909686061 80136529504220216132273)
                    ·
                      rfl

theorem cell22_234098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_234098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234098 prefixEnd_234098 := by exact prefixLift 234098
  have htrace : WordTrace (prefixWord ++ tailWord_234098) baseStart_234098 baseEnd_234098 := by
    simpa [prefixWord, tailWord_234098, baseEnd_234098] using wordTrace_append hprefix tailTrace_234098
  have hstable : (prefixWord ++ tailWord_234098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234098).length < 2 ^ (prefixWord ++ tailWord_234098).sum := by decide
  have hdescent : baseEnd_234098 < baseStart_234098 := by decide
  rcases family_descends (prefixWord ++ tailWord_234098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234122 : List Nat := [3, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_234122 : Nat := 118140960795 + 234122 * 2 ^ 59
def prefixEnd_234122 : Nat := 4983230072969 + 3 ^ 40 * 234122 * 2
def baseEnd_234122 : Nat := 26714915064897384510733

theorem tailTrace_234122 : CollatzResearch.WordTrace tailWord_234122 prefixEnd_234122 26714915064897384510733 := by
  unfold tailWord_234122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134782714455863424838155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5692753905215635799568413 2134782714455863424838155)
  ·
    refine ⟨3202174071683795137257233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134782714455863424838155 3202174071683795137257233)
    ·
      refine ⟨2401630553762846352942925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3202174071683795137257233 2401630553762846352942925)
      ·
        refine ⟨900611457661067382353597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2401630553762846352942925 900611457661067382353597)
        ·
          refine ⟨337729296622900268382599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 900611457661067382353597 337729296622900268382599)
          ·
            refine ⟨506593944934350402573899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337729296622900268382599 506593944934350402573899)
            ·
              refine ⟨759890917401525603860849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506593944934350402573899 759890917401525603860849)
              ·
                refine ⟨569918188051144202895637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 759890917401525603860849 569918188051144202895637)
                ·
                  refine ⟨26714915064897384510733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 569918188051144202895637 26714915064897384510733)
                  ·
                    rfl

theorem cell22_234122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_234122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234122 prefixEnd_234122 := by exact prefixLift 234122
  have htrace : WordTrace (prefixWord ++ tailWord_234122) baseStart_234122 baseEnd_234122 := by
    simpa [prefixWord, tailWord_234122, baseEnd_234122] using wordTrace_append hprefix tailTrace_234122
  have hstable : (prefixWord ++ tailWord_234122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234122).length < 2 ^ (prefixWord ++ tailWord_234122).sum := by decide
  have hdescent : baseEnd_234122 < baseStart_234122 := by decide
  rcases family_descends (prefixWord ++ tailWord_234122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234135 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 6]
def baseStart_234135 : Nat := 118140960795 + 234135 * 2 ^ 59
def prefixEnd_234135 : Nat := 4983230072969 + 3 ^ 40 * 234135 * 2
def baseEnd_234135 : Nat := 80149195360364452957159

theorem tailTrace_234135 : CollatzResearch.WordTrace tailWord_234135 prefixEnd_234135 80149195360364452957159 := by
  unfold tailWord_234135
  simp only [CollatzResearch.WordTrace]
  refine ⟨8539605006776356919575859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5693070004517571279717239 8539605006776356919575859)
  ·
    refine ⟨12809407510164535379363789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8539605006776356919575859 12809407510164535379363789)
    ·
      refine ⟨4803527816311700767261421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12809407510164535379363789 4803527816311700767261421)
      ·
        refine ⟨1801322931116887787723033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4803527816311700767261421 1801322931116887787723033)
        ·
          refine ⟨1350992198337665840792275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1801322931116887787723033 1350992198337665840792275)
          ·
            refine ⟨2026488297506498761188413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350992198337665840792275 2026488297506498761188413)
            ·
              refine ⟨759933111564937035445655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2026488297506498761188413 759933111564937035445655)
              ·
                refine ⟨1139899667347405553168483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759933111564937035445655 1139899667347405553168483)
                ·
                  refine ⟨1709849501021108329752725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1139899667347405553168483 1709849501021108329752725)
                  ·
                    refine ⟨80149195360364452957159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1709849501021108329752725 80149195360364452957159)
                    ·
                      rfl

theorem cell22_234135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_234135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234135 prefixEnd_234135 := by exact prefixLift 234135
  have htrace : WordTrace (prefixWord ++ tailWord_234135) baseStart_234135 baseEnd_234135 := by
    simpa [prefixWord, tailWord_234135, baseEnd_234135] using wordTrace_append hprefix tailTrace_234135
  have hstable : (prefixWord ++ tailWord_234135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234135).length < 2 ^ (prefixWord ++ tailWord_234135).sum := by decide
  have hdescent : baseEnd_234135 < baseStart_234135 := by decide
  rcases family_descends (prefixWord ++ tailWord_234135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234216 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 3, 3]
def baseStart_234216 : Nat := 118140960795 + 234216 * 2 ^ 59
def prefixEnd_234216 : Nat := 4983230072969 + 3 ^ 40 * 234216 * 2
def baseEnd_234216 : Nat := 80176923315707241681911

theorem tailTrace_234216 : CollatzResearch.WordTrace tailWord_234216 prefixEnd_234216 80176923315707241681911 := by
  unfold tailWord_234216
  simp only [CollatzResearch.WordTrace]
  refine ⟨4271279659741453876637251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5695039546321938502183001 4271279659741453876637251)
  ·
    refine ⟨6406919489612180814955877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4271279659741453876637251 6406919489612180814955877)
    ·
      refine ⟨1201297404302283902804227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6406919489612180814955877 1201297404302283902804227)
      ·
        refine ⟨1801946106453425854206341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201297404302283902804227 1801946106453425854206341)
        ·
          refine ⟨337864894960017347663689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1801946106453425854206341 337864894960017347663689)
          ·
            refine ⟨253398671220013010747767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337864894960017347663689 253398671220013010747767)
            ·
              refine ⟨380098006830019516121651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253398671220013010747767 380098006830019516121651)
              ·
                refine ⟨570147010245029274182477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380098006830019516121651 570147010245029274182477)
                ·
                  refine ⟨213805128841885977818429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 570147010245029274182477 213805128841885977818429)
                  ·
                    refine ⟨80176923315707241681911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213805128841885977818429 80176923315707241681911)
                    ·
                      rfl

theorem cell22_234216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_234216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234216 prefixEnd_234216 := by exact prefixLift 234216
  have htrace : WordTrace (prefixWord ++ tailWord_234216) baseStart_234216 baseEnd_234216 := by
    simpa [prefixWord, tailWord_234216, baseEnd_234216] using wordTrace_append hprefix tailTrace_234216
  have hstable : (prefixWord ++ tailWord_234216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234216).length < 2 ^ (prefixWord ++ tailWord_234216).sum := by decide
  have hdescent : baseEnd_234216 < baseStart_234216 := by decide
  rcases family_descends (prefixWord ++ tailWord_234216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234259 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 1, 4]
def baseStart_234259 : Nat := 118140960795 + 234259 * 2 ^ 59
def prefixEnd_234259 : Nat := 4983230072969 + 3 ^ 40 * 234259 * 2
def baseEnd_234259 : Nat := 80191643094469462856779

theorem tailTrace_234259 : CollatzResearch.WordTrace tailWord_234259 prefixEnd_234259 80191643094469462856779 := by
  unfold tailWord_234259
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544127658327126097089831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5696085105551417398059887 8544127658327126097089831)
  ·
    refine ⟨12816191487490689145634747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544127658327126097089831 12816191487490689145634747)
    ·
      refine ⟨19224287231236033718452121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816191487490689145634747 19224287231236033718452121)
      ·
        refine ⟨14418215423427025288839091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19224287231236033718452121 14418215423427025288839091)
        ·
          refine ⟨21627323135140537933258637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418215423427025288839091 21627323135140537933258637)
          ·
            refine ⟨8110246175677701724971989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21627323135140537933258637 8110246175677701724971989)
            ·
              refine ⟨190083894742446134179031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8110246175677701724971989 190083894742446134179031)
              ·
                refine ⟨285125842113669201268547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190083894742446134179031 285125842113669201268547)
                ·
                  refine ⟨427688763170503801902821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285125842113669201268547 427688763170503801902821)
                  ·
                    refine ⟨80191643094469462856779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 427688763170503801902821 80191643094469462856779)
                    ·
                      rfl

theorem cell22_234259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 4].length) (baseStart_234259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234259 prefixEnd_234259 := by exact prefixLift 234259
  have htrace : WordTrace (prefixWord ++ tailWord_234259) baseStart_234259 baseEnd_234259 := by
    simpa [prefixWord, tailWord_234259, baseEnd_234259] using wordTrace_append hprefix tailTrace_234259
  have hstable : (prefixWord ++ tailWord_234259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234259).length < 2 ^ (prefixWord ++ tailWord_234259).sum := by decide
  have hdescent : baseEnd_234259 < baseStart_234259 := by decide
  rcases family_descends (prefixWord ++ tailWord_234259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234289 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_234289 : Nat := 118140960795 + 234289 * 2 ^ 59
def prefixEnd_234289 : Nat := 4983230072969 + 3 ^ 40 * 234289 * 2
def baseEnd_234289 : Nat := 80201912707559384606687

theorem tailTrace_234289 : CollatzResearch.WordTrace tailWord_234289 prefixEnd_234289 80201912707559384606687 := by
  unfold tailWord_234289
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545221848218441220681921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5696814565478960813787947 8545221848218441220681921)
  ·
    refine ⟨6408916386163830915511441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8545221848218441220681921 6408916386163830915511441)
    ·
      refine ⟨4806687289622873186633581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6408916386163830915511441 4806687289622873186633581)
      ·
        refine ⟨1802507733608577444987593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4806687289622873186633581 1802507733608577444987593)
        ·
          refine ⟨1351880800206433083740695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1802507733608577444987593 1351880800206433083740695)
          ·
            refine ⟨2027821200309649625611043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351880800206433083740695 2027821200309649625611043)
            ·
              refine ⟨3041731800464474438416565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027821200309649625611043 3041731800464474438416565)
              ·
                refine ⟨285162356293544478601553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3041731800464474438416565 285162356293544478601553)
                ·
                  refine ⟨213871767220158358951165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285162356293544478601553 213871767220158358951165)
                  ·
                    refine ⟨80201912707559384606687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 213871767220158358951165 80201912707559384606687)
                    ·
                      rfl

theorem cell22_234289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_234289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234289 prefixEnd_234289 := by exact prefixLift 234289
  have htrace : WordTrace (prefixWord ++ tailWord_234289) baseStart_234289 baseEnd_234289 := by
    simpa [prefixWord, tailWord_234289, baseEnd_234289] using wordTrace_append hprefix tailTrace_234289
  have hstable : (prefixWord ++ tailWord_234289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234289).length < 2 ^ (prefixWord ++ tailWord_234289).sum := by decide
  have hdescent : baseEnd_234289 < baseStart_234289 := by decide
  rcases family_descends (prefixWord ++ tailWord_234289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234347 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 5]
def baseStart_234347 : Nat := 118140960795 + 234347 * 2 ^ 59
def prefixEnd_234347 : Nat := 4983230072969 + 3 ^ 40 * 234347 * 2
def baseEnd_234347 : Nat := 26740589097622188885503

theorem tailTrace_234347 : CollatzResearch.WordTrace tailWord_234347 prefixEnd_234347 26740589097622188885503 := by
  unfold tailWord_234347
  simp only [CollatzResearch.WordTrace]
  refine ⟨8547337282008317126293295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5698224854672211417528863 8547337282008317126293295)
  ·
    refine ⟨12821005923012475689439943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8547337282008317126293295 12821005923012475689439943)
    ·
      refine ⟨19231508884518713534159915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12821005923012475689439943 19231508884518713534159915)
      ·
        refine ⟨28847263326778070301239873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19231508884518713534159915 28847263326778070301239873)
        ·
          refine ⟨21635447495083552725929905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28847263326778070301239873 21635447495083552725929905)
          ·
            refine ⟨16226585621312664544447429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21635447495083552725929905 16226585621312664544447429)
            ·
              refine ⟨3042484803996124602083893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16226585621312664544447429 3042484803996124602083893)
              ·
                refine ⟨285232950374636681445365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3042484803996124602083893 285232950374636681445365)
                ·
                  refine ⟨26740589097622188885503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285232950374636681445365 26740589097622188885503)
                  ·
                    rfl

theorem cell22_234347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 5].length) (baseStart_234347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234347 prefixEnd_234347 := by exact prefixLift 234347
  have htrace : WordTrace (prefixWord ++ tailWord_234347) baseStart_234347 baseEnd_234347 := by
    simpa [prefixWord, tailWord_234347, baseEnd_234347] using wordTrace_append hprefix tailTrace_234347
  have hstable : (prefixWord ++ tailWord_234347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234347).length < 2 ^ (prefixWord ++ tailWord_234347).sum := by decide
  have hdescent : baseEnd_234347 < baseStart_234347 := by decide
  rcases family_descends (prefixWord ++ tailWord_234347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234424 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_234424 : Nat := 118140960795 + 234424 * 2 ^ 59
def prefixEnd_234424 : Nat := 4983230072969 + 3 ^ 40 * 234424 * 2
def baseEnd_234424 : Nat := 80248125966464032481273

theorem tailTrace_234424 : CollatzResearch.WordTrace tailWord_234424 prefixEnd_234424 80248125966464032481273 := by
  unfold tailWord_234424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275072851364679638423163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5700097135152906184564217 4275072851364679638423163)
  ·
    refine ⟨6412609277047019457634745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4275072851364679638423163 6412609277047019457634745)
    ·
      refine ⟨4809456957785264593226059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6412609277047019457634745 4809456957785264593226059)
      ·
        refine ⟨7214185436677896889839089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809456957785264593226059 7214185436677896889839089)
        ·
          refine ⟨5410639077508422667379317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7214185436677896889839089 5410639077508422667379317)
          ·
            refine ⟨507247413516414625066811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5410639077508422667379317 507247413516414625066811)
            ·
              refine ⟨760871120274621937600217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507247413516414625066811 760871120274621937600217)
              ·
                refine ⟨570653340205966453200163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760871120274621937600217 570653340205966453200163)
                ·
                  refine ⟨855980010308949679800245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 570653340205966453200163 855980010308949679800245)
                  ·
                    refine ⟨80248125966464032481273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 855980010308949679800245 80248125966464032481273)
                    ·
                      rfl

theorem cell22_234424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_234424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234424 prefixEnd_234424 := by exact prefixLift 234424
  have htrace : WordTrace (prefixWord ++ tailWord_234424) baseStart_234424 baseEnd_234424 := by
    simpa [prefixWord, tailWord_234424, baseEnd_234424] using wordTrace_append hprefix tailTrace_234424
  have hstable : (prefixWord ++ tailWord_234424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234424).length < 2 ^ (prefixWord ++ tailWord_234424).sum := by decide
  have hdescent : baseEnd_234424 < baseStart_234424 := by decide
  rcases family_descends (prefixWord ++ tailWord_234424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234439 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_234439 : Nat := 118140960795 + 234439 * 2 ^ 59
def prefixEnd_234439 : Nat := 4983230072969 + 3 ^ 40 * 234439 * 2
def baseEnd_234439 : Nat := 80253260773008993356227

theorem tailTrace_234439 : CollatzResearch.WordTrace tailWord_234439 prefixEnd_234439 80253260773008993356227 := by
  unfold tailWord_234439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8550692797675016838642371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5700461865116677892428247 8550692797675016838642371)
  ·
    refine ⟨12826039196512525257963557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8550692797675016838642371 12826039196512525257963557)
    ·
      refine ⟨2404882349346098485868167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12826039196512525257963557 2404882349346098485868167)
      ·
        refine ⟨3607323524019147728802251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404882349346098485868167 3607323524019147728802251)
        ·
          refine ⟨5410985286028721593203377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607323524019147728802251 5410985286028721593203377)
          ·
            refine ⟨4058238964521541194902533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5410985286028721593203377 4058238964521541194902533)
            ·
              refine ⟨760919805847788974044225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4058238964521541194902533 760919805847788974044225)
              ·
                refine ⟨570689854385841730533169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760919805847788974044225 570689854385841730533169)
                ·
                  refine ⟨428017390789381297899877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570689854385841730533169 428017390789381297899877)
                  ·
                    refine ⟨80253260773008993356227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428017390789381297899877 80253260773008993356227)
                    ·
                      rfl

theorem cell22_234439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_234439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234439 prefixEnd_234439 := by exact prefixLift 234439
  have htrace : WordTrace (prefixWord ++ tailWord_234439) baseStart_234439 baseEnd_234439 := by
    simpa [prefixWord, tailWord_234439, baseEnd_234439] using wordTrace_append hprefix tailTrace_234439
  have hstable : (prefixWord ++ tailWord_234439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234439).length < 2 ^ (prefixWord ++ tailWord_234439).sum := by decide
  have hdescent : baseEnd_234439 < baseStart_234439 := by decide
  rcases family_descends (prefixWord ++ tailWord_234439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234443 : List Nat := [1, 1, 1, 1, 3, 7, 2, 2, 4]
def baseStart_234443 : Nat := 118140960795 + 234443 * 2 ^ 59
def prefixEnd_234443 : Nat := 4983230072969 + 3 ^ 40 * 234443 * 2
def baseEnd_234443 : Nat := 26751543351584772085405

theorem tailTrace_234443 : CollatzResearch.WordTrace tailWord_234443 prefixEnd_234443 26751543351584772085405 := by
  unfold tailWord_234443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8550838689660525521787983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5700559126440350347858655 8550838689660525521787983)
  ·
    refine ⟨12826258034490788282681975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8550838689660525521787983 12826258034490788282681975)
    ·
      refine ⟨19239387051736182424022963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12826258034490788282681975 19239387051736182424022963)
      ·
        refine ⟨28859080577604273636034445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19239387051736182424022963 28859080577604273636034445)
        ·
          refine ⟨10822155216601602613512917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28859080577604273636034445 10822155216601602613512917)
          ·
            refine ⟨253644262889100061254209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10822155216601602613512917 253644262889100061254209)
            ·
              refine ⟨190233197166825045940657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253644262889100061254209 190233197166825045940657)
              ·
                refine ⟨142674897875118784455493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190233197166825045940657 142674897875118784455493)
                ·
                  refine ⟨26751543351584772085405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142674897875118784455493 26751543351584772085405)
                  ·
                    rfl

theorem cell22_234443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 4].length) (baseStart_234443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234443 prefixEnd_234443 := by exact prefixLift 234443
  have htrace : WordTrace (prefixWord ++ tailWord_234443) baseStart_234443 baseEnd_234443 := by
    simpa [prefixWord, tailWord_234443, baseEnd_234443] using wordTrace_append hprefix tailTrace_234443
  have hstable : (prefixWord ++ tailWord_234443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234443).length < 2 ^ (prefixWord ++ tailWord_234443).sum := by decide
  have hdescent : baseEnd_234443 < baseStart_234443 := by decide
  rcases family_descends (prefixWord ++ tailWord_234443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234471 : List Nat := [1, 1, 5, 2, 2, 2, 3, 6]
def baseStart_234471 : Nat := 118140960795 + 234471 * 2 ^ 59
def prefixEnd_234471 : Nat := 4983230072969 + 3 ^ 40 * 234471 * 2
def baseEnd_234471 : Nat := 8918246114107952950681

theorem tailTrace_234471 : CollatzResearch.WordTrace tailWord_234471 prefixEnd_234471 8918246114107952950681 := by
  unfold tailWord_234471
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551859933559086303807267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5701239955706057535871511 8551859933559086303807267)
  ·
    refine ⟨12827789900338629455710901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8551859933559086303807267 12827789900338629455710901)
    ·
      refine ⟨1202605303156746511472897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12827789900338629455710901 1202605303156746511472897)
      ·
        refine ⟨901953977367559883604673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1202605303156746511472897 901953977367559883604673)
        ·
          refine ⟨676465483025669912703505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 901953977367559883604673 676465483025669912703505)
          ·
            refine ⟨507349112269252434527629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 676465483025669912703505 507349112269252434527629)
            ·
              refine ⟨190255917100969662947861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507349112269252434527629 190255917100969662947861)
              ·
                refine ⟨8918246114107952950681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190255917100969662947861 8918246114107952950681)
                ·
                  rfl

theorem cell22_234471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 6].length) (baseStart_234471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234471 prefixEnd_234471 := by exact prefixLift 234471
  have htrace : WordTrace (prefixWord ++ tailWord_234471) baseStart_234471 baseEnd_234471 := by
    simpa [prefixWord, tailWord_234471, baseEnd_234471] using wordTrace_append hprefix tailTrace_234471
  have hstable : (prefixWord ++ tailWord_234471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234471).length < 2 ^ (prefixWord ++ tailWord_234471).sum := by decide
  have hdescent : baseEnd_234471 < baseStart_234471 := by decide
  rcases family_descends (prefixWord ++ tailWord_234471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234503 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 1, 3]
def baseStart_234503 : Nat := 118140960795 + 234503 * 2 ^ 59
def prefixEnd_234503 : Nat := 4983230072969 + 3 ^ 40 * 234503 * 2
def baseEnd_234503 : Nat := 80275169280934159756031

theorem tailTrace_234503 : CollatzResearch.WordTrace tailWord_234503 prefixEnd_234503 80275169280934159756031 := by
  unfold tailWord_234503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8553027069443155768972163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5702018046295437179314775 8553027069443155768972163)
  ·
    refine ⟨12829540604164733653458245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8553027069443155768972163 12829540604164733653458245)
    ·
      refine ⟨2405538863280887560023421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12829540604164733653458245 2405538863280887560023421)
      ·
        refine ⟨902077073730332835008783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2405538863280887560023421 902077073730332835008783)
        ·
          refine ⟨1353115610595499252513175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902077073730332835008783 1353115610595499252513175)
          ·
            refine ⟨2029673415893248878769763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353115610595499252513175 2029673415893248878769763)
            ·
              refine ⟨3044510123839873318154645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029673415893248878769763 3044510123839873318154645)
              ·
                refine ⟨142711412054994061788499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3044510123839873318154645 142711412054994061788499)
                ·
                  refine ⟨214067118082491092682749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142711412054994061788499 214067118082491092682749)
                  ·
                    refine ⟨80275169280934159756031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214067118082491092682749 80275169280934159756031)
                    ·
                      rfl

theorem cell22_234503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_234503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234503 prefixEnd_234503 := by exact prefixLift 234503
  have htrace : WordTrace (prefixWord ++ tailWord_234503) baseStart_234503 baseEnd_234503 := by
    simpa [prefixWord, tailWord_234503, baseEnd_234503] using wordTrace_append hprefix tailTrace_234503
  have hstable : (prefixWord ++ tailWord_234503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234503).length < 2 ^ (prefixWord ++ tailWord_234503).sum := by decide
  have hdescent : baseEnd_234503 < baseStart_234503 := by decide
  rcases family_descends (prefixWord ++ tailWord_234503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234546 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 1, 4]
def baseStart_234546 : Nat := 118140960795 + 234546 * 2 ^ 59
def prefixEnd_234546 : Nat := 4983230072969 + 3 ^ 40 * 234546 * 2
def baseEnd_234546 : Nat := 80289889059696380930899

theorem tailTrace_234546 : CollatzResearch.WordTrace tailWord_234546 prefixEnd_234546 80289889059696380930899 := by
  unfold tailWord_234546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138648852071843528196873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5703063605524916075191661 2138648852071843528196873)
  ·
    refine ⟨1603986639053882646147655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2138648852071843528196873 1603986639053882646147655)
    ·
      refine ⟨2405979958580823969221483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603986639053882646147655 2405979958580823969221483)
      ·
        refine ⟨3608969937871235953832225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405979958580823969221483 3608969937871235953832225)
        ·
          refine ⟨2706727453403426965374169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3608969937871235953832225 2706727453403426965374169)
          ·
            refine ⟨2030045590052570224030627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706727453403426965374169 2030045590052570224030627)
            ·
              refine ⟨3045068385078855336045941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030045590052570224030627 3045068385078855336045941)
              ·
                refine ⟨285475161101142687754307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3045068385078855336045941 285475161101142687754307)
                ·
                  refine ⟨428212741651714031631461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285475161101142687754307 428212741651714031631461)
                  ·
                    refine ⟨80289889059696380930899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428212741651714031631461 80289889059696380930899)
                    ·
                      rfl

theorem cell22_234546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_234546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234546 prefixEnd_234546 := by exact prefixLift 234546
  have htrace : WordTrace (prefixWord ++ tailWord_234546) baseStart_234546 baseEnd_234546 := by
    simpa [prefixWord, tailWord_234546, baseEnd_234546] using wordTrace_append hprefix tailTrace_234546
  have hstable : (prefixWord ++ tailWord_234546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234546).length < 2 ^ (prefixWord ++ tailWord_234546).sum := by decide
  have hdescent : baseEnd_234546 < baseStart_234546 := by decide
  rcases family_descends (prefixWord ++ tailWord_234546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234591 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 2, 4]
def baseStart_234591 : Nat := 118140960795 + 234591 * 2 ^ 59
def prefixEnd_234591 : Nat := 4983230072969 + 3 ^ 40 * 234591 * 2
def baseEnd_234591 : Nat := 80305293479331263555761

theorem tailTrace_234591 : CollatzResearch.WordTrace tailWord_234591 prefixEnd_234591 80305293479331263555761 := by
  unfold tailWord_234591
  simp only [CollatzResearch.WordTrace]
  refine ⟨8556236693124346798175627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5704157795416231198783751 8556236693124346798175627)
  ·
    refine ⟨12834355039686520197263441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8556236693124346798175627 12834355039686520197263441)
    ·
      refine ⟨9625766279764890147947581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12834355039686520197263441 9625766279764890147947581)
      ·
        refine ⟨3609662354911833805480343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9625766279764890147947581 3609662354911833805480343)
        ·
          refine ⟨5414493532367750708220515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609662354911833805480343 5414493532367750708220515)
          ·
            refine ⟨8121740298551626062330773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414493532367750708220515 8121740298551626062330773)
            ·
              refine ⟨380706576494607471671755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8121740298551626062330773 380706576494607471671755)
              ·
                refine ⟨571059864741911207507633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380706576494607471671755 571059864741911207507633)
                ·
                  refine ⟨428294898556433405630725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571059864741911207507633 428294898556433405630725)
                  ·
                    refine ⟨80305293479331263555761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428294898556433405630725 80305293479331263555761)
                    ·
                      rfl

theorem cell22_234591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_234591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234591 prefixEnd_234591 := by exact prefixLift 234591
  have htrace : WordTrace (prefixWord ++ tailWord_234591) baseStart_234591 baseEnd_234591 := by
    simpa [prefixWord, tailWord_234591, baseEnd_234591] using wordTrace_append hprefix tailTrace_234591
  have hstable : (prefixWord ++ tailWord_234591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234591).length < 2 ^ (prefixWord ++ tailWord_234591).sum := by decide
  have hdescent : baseEnd_234591 < baseStart_234591 := by decide
  rcases family_descends (prefixWord ++ tailWord_234591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234638 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_234638 : Nat := 118140960795 + 234638 * 2 ^ 59
def prefixEnd_234638 : Nat := 4983230072969 + 3 ^ 40 * 234638 * 2
def baseEnd_234638 : Nat := 80321382539838807630617

theorem tailTrace_234638 : CollatzResearch.WordTrace tailWord_234638 prefixEnd_234638 80321382539838807630617 := by
  unfold tailWord_234638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069743865494259228142071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5705300615969382550091045 1069743865494259228142071)
  ·
    refine ⟨1604615798241388842213107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1069743865494259228142071 1604615798241388842213107)
    ·
      refine ⟨2406923697362083263319661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604615798241388842213107 2406923697362083263319661)
      ·
        refine ⟨902596386510781223744873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2406923697362083263319661 902596386510781223744873)
        ·
          refine ⟨676947289883085917808655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902596386510781223744873 676947289883085917808655)
          ·
            refine ⟨1015420934824628876712983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676947289883085917808655 1015420934824628876712983)
            ·
              refine ⟨1523131402236943315069475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015420934824628876712983 1523131402236943315069475)
              ·
                refine ⟨2284697103355414972604213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523131402236943315069475 2284697103355414972604213)
                ·
                  refine ⟨214190353439570153681645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2284697103355414972604213 214190353439570153681645)
                  ·
                    refine ⟨80321382539838807630617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214190353439570153681645 80321382539838807630617)
                    ·
                      rfl

theorem cell22_234638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_234638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234638 prefixEnd_234638 := by exact prefixLift 234638
  have htrace : WordTrace (prefixWord ++ tailWord_234638) baseStart_234638 baseEnd_234638 := by
    simpa [prefixWord, tailWord_234638, baseEnd_234638] using wordTrace_append hprefix tailTrace_234638
  have hstable : (prefixWord ++ tailWord_234638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234638).length < 2 ^ (prefixWord ++ tailWord_234638).sum := by decide
  have hdescent : baseEnd_234638 < baseStart_234638 := by decide
  rcases family_descends (prefixWord ++ tailWord_234638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234696 : List Nat := [2, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_234696 : Nat := 118140960795 + 234696 * 2 ^ 59
def prefixEnd_234696 : Nat := 4983230072969 + 3 ^ 40 * 234696 * 2
def baseEnd_234696 : Nat := 26780412375048663226813

theorem tailTrace_234696 : CollatzResearch.WordTrace tailWord_234696 prefixEnd_234696 26780412375048663226813 := by
  unfold tailWord_234696
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280033178871974865373971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5706710905162633153831961 4280033178871974865373971)
  ·
    refine ⟨6420049768307962298060957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4280033178871974865373971 6420049768307962298060957)
    ·
      refine ⟨2407518663115485861772859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6420049768307962298060957 2407518663115485861772859)
      ·
        refine ⟨3611277994673228792659289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407518663115485861772859 3611277994673228792659289)
        ·
          refine ⟨2708458496004921594494467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3611277994673228792659289 2708458496004921594494467)
          ·
            refine ⟨4062687744007382391741701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708458496004921594494467 4062687744007382391741701)
            ·
              refine ⟨761753952001384198451569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4062687744007382391741701 761753952001384198451569)
              ·
                refine ⟨571315464001038148838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761753952001384198451569 571315464001038148838677)
                ·
                  refine ⟨26780412375048663226813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 571315464001038148838677 26780412375048663226813)
                  ·
                    rfl

theorem cell22_234696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_234696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234696 prefixEnd_234696 := by exact prefixLift 234696
  have htrace : WordTrace (prefixWord ++ tailWord_234696) baseStart_234696 baseEnd_234696 := by
    simpa [prefixWord, tailWord_234696, baseEnd_234696] using wordTrace_append hprefix tailTrace_234696
  have hstable : (prefixWord ++ tailWord_234696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234696).length < 2 ^ (prefixWord ++ tailWord_234696).sum := by decide
  have hdescent : baseEnd_234696 < baseStart_234696 := by decide
  rcases family_descends (prefixWord ++ tailWord_234696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234698 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 1, 4]
def baseStart_234698 : Nat := 118140960795 + 234698 * 2 ^ 59
def prefixEnd_234698 : Nat := 4983230072969 + 3 ^ 40 * 234698 * 2
def baseEnd_234698 : Nat := 80341921766018651130433

theorem tailTrace_234698 : CollatzResearch.WordTrace tailWord_234698 prefixEnd_234698 80341921766018651130433 := by
  unfold tailWord_234698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140034825934176018080187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5706759535824469381547165 2140034825934176018080187)
  ·
    refine ⟨3210052238901264027120281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140034825934176018080187 3210052238901264027120281)
    ·
      refine ⟨2407539179175948020340211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3210052238901264027120281 2407539179175948020340211)
      ·
        refine ⟨3611308768763922030510317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407539179175948020340211 3611308768763922030510317)
        ·
          refine ⟨1354240788286470761441369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3611308768763922030510317 1354240788286470761441369)
          ·
            refine ⟨1015680591214853071081027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354240788286470761441369 1015680591214853071081027)
            ·
              refine ⟨1523520886822279606621541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015680591214853071081027 1523520886822279606621541)
              ·
                refine ⟨285660166279177426241539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1523520886822279606621541 285660166279177426241539)
                ·
                  refine ⟨428490249418766139362309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285660166279177426241539 428490249418766139362309)
                  ·
                    refine ⟨80341921766018651130433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428490249418766139362309 80341921766018651130433)
                    ·
                      rfl

theorem cell22_234698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_234698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234698 prefixEnd_234698 := by exact prefixLift 234698
  have htrace : WordTrace (prefixWord ++ tailWord_234698) baseStart_234698 baseEnd_234698 := by
    simpa [prefixWord, tailWord_234698, baseEnd_234698] using wordTrace_append hprefix tailTrace_234698
  have hstable : (prefixWord ++ tailWord_234698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234698).length < 2 ^ (prefixWord ++ tailWord_234698).sum := by decide
  have hdescent : baseEnd_234698 < baseStart_234698 := by decide
  rcases family_descends (prefixWord ++ tailWord_234698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234711 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 1, 5]
def baseStart_234711 : Nat := 118140960795 + 234711 * 2 ^ 59
def prefixEnd_234711 : Nat := 4983230072969 + 3 ^ 40 * 234711 * 2
def baseEnd_234711 : Nat := 80346371931690950555393

theorem tailTrace_234711 : CollatzResearch.WordTrace tailWord_234711 prefixEnd_234711 80346371931690950555393 := by
  unfold tailWord_234711
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560613452689607292543987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5707075635126404861695991 8560613452689607292543987)
  ·
    refine ⟨12840920179034410938815981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8560613452689607292543987 12840920179034410938815981)
    ·
      refine ⟨4815345067137904102055993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12840920179034410938815981 4815345067137904102055993)
      ·
        refine ⟨3611508800353428076541995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4815345067137904102055993 3611508800353428076541995)
        ·
          refine ⟨5417263200530142114812993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611508800353428076541995 5417263200530142114812993)
          ·
            refine ⟨4062947400397606586109745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417263200530142114812993 4062947400397606586109745)
            ·
              refine ⟨3047210550298204939582309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062947400397606586109745 3047210550298204939582309)
              ·
                refine ⟨571351978180913426171683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3047210550298204939582309 571351978180913426171683)
                ·
                  refine ⟨857027967271370139257525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571351978180913426171683 857027967271370139257525)
                  ·
                    refine ⟨80346371931690950555393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 857027967271370139257525 80346371931690950555393)
                    ·
                      rfl

theorem cell22_234711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_234711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234711 prefixEnd_234711 := by exact prefixLift 234711
  have htrace : WordTrace (prefixWord ++ tailWord_234711) baseStart_234711 baseEnd_234711 := by
    simpa [prefixWord, tailWord_234711, baseEnd_234711] using wordTrace_append hprefix tailTrace_234711
  have hstable : (prefixWord ++ tailWord_234711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234711).length < 2 ^ (prefixWord ++ tailWord_234711).sum := by decide
  have hdescent : baseEnd_234711 < baseStart_234711 := by decide
  rcases family_descends (prefixWord ++ tailWord_234711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234728 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 4, 3]
def baseStart_234728 : Nat := 118140960795 + 234728 * 2 ^ 59
def prefixEnd_234728 : Nat := 4983230072969 + 3 ^ 40 * 234728 * 2
def baseEnd_234728 : Nat := 80352191379108572880341

theorem tailTrace_234728 : CollatzResearch.WordTrace tailWord_234728 prefixEnd_234728 80352191379108572880341 := by
  unfold tailWord_234728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280616746814009597956419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5707488995752012797275225 4280616746814009597956419)
  ·
    refine ⟨6420925120221014396934629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4280616746814009597956419 6420925120221014396934629)
    ·
      refine ⟨1203923460041440199425243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6420925120221014396934629 1203923460041440199425243)
      ·
        refine ⟨1805885190062160299137865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203923460041440199425243 1805885190062160299137865)
        ·
          refine ⟨1354413892546620224353399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805885190062160299137865 1354413892546620224353399)
          ·
            refine ⟨2031620838819930336530099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354413892546620224353399 2031620838819930336530099)
            ·
              refine ⟨3047431258229895504795149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031620838819930336530099 3047431258229895504795149)
              ·
                refine ⟨1142786721836210814298181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3047431258229895504795149 1142786721836210814298181)
                ·
                  refine ⟨214272510344289527680909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142786721836210814298181 214272510344289527680909)
                  ·
                    refine ⟨80352191379108572880341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214272510344289527680909 80352191379108572880341)
                    ·
                      rfl

theorem cell22_234728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_234728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234728 prefixEnd_234728 := by exact prefixLift 234728
  have htrace : WordTrace (prefixWord ++ tailWord_234728) baseStart_234728 baseEnd_234728 := by
    simpa [prefixWord, tailWord_234728, baseEnd_234728] using wordTrace_append hprefix tailTrace_234728
  have hstable : (prefixWord ++ tailWord_234728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234728).length < 2 ^ (prefixWord ++ tailWord_234728).sum := by decide
  have hdescent : baseEnd_234728 < baseStart_234728 := by decide
  rcases family_descends (prefixWord ++ tailWord_234728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234760 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_234760 : Nat := 118140960795 + 234760 * 2 ^ 59
def prefixEnd_234760 : Nat := 4983230072969 + 3 ^ 40 * 234760 * 2
def baseEnd_234760 : Nat := 80363145633071156080243

theorem tailTrace_234760 : CollatzResearch.WordTrace tailWord_234760 prefixEnd_234760 80363145633071156080243 := by
  unfold tailWord_234760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4281200314756044330538867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5708267086341392440718489 4281200314756044330538867)
  ·
    refine ⟨6421800472134066495808301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4281200314756044330538867 6421800472134066495808301)
    ·
      refine ⟨2408175177050274935928113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6421800472134066495808301 2408175177050274935928113)
      ·
        refine ⟨1806131382787706201946085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2408175177050274935928113 1806131382787706201946085)
        ·
          refine ⟨338649634272694912864891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1806131382787706201946085 338649634272694912864891)
          ·
            refine ⟨507974451409042369297337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338649634272694912864891 507974451409042369297337)
            ·
              refine ⟨380980838556781776973003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507974451409042369297337 380980838556781776973003)
              ·
                refine ⟨571471257835172665459505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380980838556781776973003 571471257835172665459505)
                ·
                  refine ⟨428603443376379499094629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571471257835172665459505 428603443376379499094629)
                  ·
                    refine ⟨80363145633071156080243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 428603443376379499094629 80363145633071156080243)
                    ·
                      rfl

theorem cell22_234760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_234760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234760 prefixEnd_234760 := by exact prefixLift 234760
  have htrace : WordTrace (prefixWord ++ tailWord_234760) baseStart_234760 baseEnd_234760 := by
    simpa [prefixWord, tailWord_234760, baseEnd_234760] using wordTrace_append hprefix tailTrace_234760
  have hstable : (prefixWord ++ tailWord_234760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234760).length < 2 ^ (prefixWord ++ tailWord_234760).sum := by decide
  have hdescent : baseEnd_234760 < baseStart_234760 := by decide
  rcases family_descends (prefixWord ++ tailWord_234760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234803 : List Nat := [1, 1, 1, 2, 5, 2, 2, 3, 5]
def baseStart_234803 : Nat := 118140960795 + 234803 * 2 ^ 59
def prefixEnd_234803 : Nat := 4983230072969 + 3 ^ 40 * 234803 * 2
def baseEnd_234803 : Nat := 26792621803944459085037

theorem tailTrace_234803 : CollatzResearch.WordTrace tailWord_234803 prefixEnd_234803 26792621803944459085037 := by
  unfold tailWord_234803
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563968968356307004893063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5709312645570871336595375 8563968968356307004893063)
  ·
    refine ⟨12845953452534460507339595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563968968356307004893063 12845953452534460507339595)
    ·
      refine ⟨19268930178801690761009393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12845953452534460507339595 19268930178801690761009393)
      ·
        refine ⟨14451697634101268070757045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19268930178801690761009393 14451697634101268070757045)
        ·
          refine ⟨1354846653196993881633473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14451697634101268070757045 1354846653196993881633473)
          ·
            refine ⟨1016134989897745411225105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354846653196993881633473 1016134989897745411225105)
            ·
              refine ⟨762101242423309058418829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016134989897745411225105 762101242423309058418829)
              ·
                refine ⟨285787965908740896907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762101242423309058418829 285787965908740896907061)
                ·
                  refine ⟨26792621803944459085037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285787965908740896907061 26792621803944459085037)
                  ·
                    rfl

theorem cell22_234803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 5].length) (baseStart_234803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234803 prefixEnd_234803 := by exact prefixLift 234803
  have htrace : WordTrace (prefixWord ++ tailWord_234803) baseStart_234803 baseEnd_234803 := by
    simpa [prefixWord, tailWord_234803, baseEnd_234803] using wordTrace_append hprefix tailTrace_234803
  have hstable : (prefixWord ++ tailWord_234803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234803).length < 2 ^ (prefixWord ++ tailWord_234803).sum := by decide
  have hdescent : baseEnd_234803 < baseStart_234803 := by decide
  rcases family_descends (prefixWord ++ tailWord_234803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234848 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 6]
def baseStart_234848 : Nat := 118140960795 + 234848 * 2 ^ 59
def prefixEnd_234848 : Nat := 4983230072969 + 3 ^ 40 * 234848 * 2
def baseEnd_234848 : Nat := 26797756610489419959991

theorem tailTrace_234848 : CollatzResearch.WordTrace tailWord_234848 prefixEnd_234848 26797756610489419959991 := by
  unfold tailWord_234848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4282805126596639845140599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5710406835462186460187465 4282805126596639845140599)
  ·
    refine ⟨6424207689894959767710899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4282805126596639845140599 6424207689894959767710899)
    ·
      refine ⟨9636311534842439651566349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424207689894959767710899 9636311534842439651566349)
      ·
        refine ⟨3613616825565914869337381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9636311534842439651566349 3613616825565914869337381)
        ·
          refine ⟨677553154793609038000759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3613616825565914869337381 677553154793609038000759)
          ·
            refine ⟨1016329732190413557001139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677553154793609038000759 1016329732190413557001139)
            ·
              refine ⟨1524494598285620335501709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016329732190413557001139 1524494598285620335501709)
              ·
                refine ⟨571685474357107625813141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1524494598285620335501709 571685474357107625813141)
                ·
                  refine ⟨26797756610489419959991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 571685474357107625813141 26797756610489419959991)
                  ·
                    rfl

theorem cell22_234848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 6].length) (baseStart_234848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234848 prefixEnd_234848 := by exact prefixLift 234848
  have htrace : WordTrace (prefixWord ++ tailWord_234848) baseStart_234848 baseEnd_234848 := by
    simpa [prefixWord, tailWord_234848, baseEnd_234848] using wordTrace_append hprefix tailTrace_234848
  have hstable : (prefixWord ++ tailWord_234848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234848).length < 2 ^ (prefixWord ++ tailWord_234848).sum := by decide
  have hdescent : baseEnd_234848 < baseStart_234848 := by decide
  rcases family_descends (prefixWord ++ tailWord_234848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234914 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_234914 : Nat := 118140960795 + 234914 * 2 ^ 59
def prefixEnd_234914 : Nat := 4983230072969 + 3 ^ 40 * 234914 * 2
def baseEnd_234914 : Nat := 80415862980266087729771

theorem tailTrace_234914 : CollatzResearch.WordTrace tailWord_234914 prefixEnd_234914 80415862980266087729771 := by
  unfold tailWord_234914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142004367738543240545949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5712011647302781974789197 2142004367738543240545949)
  ·
    refine ⟨803251637901953715204731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2142004367738543240545949 803251637901953715204731)
    ·
      refine ⟨1204877456852930572807097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803251637901953715204731 1204877456852930572807097)
      ·
        refine ⟨903658092639697929605323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204877456852930572807097 903658092639697929605323)
        ·
          refine ⟨1355487138959546894407985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903658092639697929605323 1355487138959546894407985)
          ·
            refine ⟨1016615354219660170805989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355487138959546894407985 1016615354219660170805989)
            ·
              refine ⟨190615378916186282026123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1016615354219660170805989 190615378916186282026123)
              ·
                refine ⟨285923068374279423039185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190615378916186282026123 285923068374279423039185)
                ·
                  refine ⟨214442301280709567279389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285923068374279423039185 214442301280709567279389)
                  ·
                    refine ⟨80415862980266087729771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214442301280709567279389 80415862980266087729771)
                    ·
                      rfl

theorem cell22_234914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_234914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234914 prefixEnd_234914 := by exact prefixLift 234914
  have htrace : WordTrace (prefixWord ++ tailWord_234914) baseStart_234914 baseEnd_234914 := by
    simpa [prefixWord, tailWord_234914, baseEnd_234914] using wordTrace_append hprefix tailTrace_234914
  have hstable : (prefixWord ++ tailWord_234914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234914).length < 2 ^ (prefixWord ++ tailWord_234914).sum := by decide
  have hdescent : baseEnd_234914 < baseStart_234914 := by decide
  rcases family_descends (prefixWord ++ tailWord_234914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234953 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 2, 5]
def baseStart_234953 : Nat := 118140960795 + 234953 * 2 ^ 59
def prefixEnd_234953 : Nat := 4983230072969 + 3 ^ 40 * 234953 * 2
def baseEnd_234953 : Nat := 80429213477282986004651

theorem tailTrace_234953 : CollatzResearch.WordTrace tailWord_234953 prefixEnd_234953 80429213477282986004651 := by
  unfold tailWord_234953
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569439917812882622853513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5712959945208588415235675 8569439917812882622853513)
  ·
    refine ⟨6427079938359661967140135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8569439917812882622853513 6427079938359661967140135)
    ·
      refine ⟨9640619907539492950710203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6427079938359661967140135 9640619907539492950710203)
      ·
        refine ⟨14460929861309239426065305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640619907539492950710203 14460929861309239426065305)
        ·
          refine ⟨10845697395981929569548979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14460929861309239426065305 10845697395981929569548979)
          ·
            refine ⟨16268546093972894354323469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845697395981929569548979 16268546093972894354323469)
            ·
              refine ⟨6100704785239835382871301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16268546093972894354323469 6100704785239835382871301)
              ·
                refine ⟨1143882147232469134288369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6100704785239835382871301 1143882147232469134288369)
                ·
                  refine ⟨857911610424351850716277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143882147232469134288369 857911610424351850716277)
                  ·
                    refine ⟨80429213477282986004651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 857911610424351850716277 80429213477282986004651)
                    ·
                      rfl

theorem cell22_234953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 5].length) (baseStart_234953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234953 prefixEnd_234953 := by exact prefixLift 234953
  have htrace : WordTrace (prefixWord ++ tailWord_234953) baseStart_234953 baseEnd_234953 := by
    simpa [prefixWord, tailWord_234953, baseEnd_234953] using wordTrace_append hprefix tailTrace_234953
  have hstable : (prefixWord ++ tailWord_234953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234953).length < 2 ^ (prefixWord ++ tailWord_234953).sum := by decide
  have hdescent : baseEnd_234953 < baseStart_234953 := by decide
  rcases family_descends (prefixWord ++ tailWord_234953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234959 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 1, 3]
def baseStart_234959 : Nat := 118140960795 + 234959 * 2 ^ 59
def prefixEnd_234959 : Nat := 4983230072969 + 3 ^ 40 * 234959 * 2
def baseEnd_234959 : Nat := 80431267399900970354633

theorem tailTrace_234959 : CollatzResearch.WordTrace tailWord_234959 prefixEnd_234959 80431267399900970354633 := by
  unfold tailWord_234959
  simp only [CollatzResearch.WordTrace]
  refine ⟨8569658755791145647571931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5713105837194097098381287 8569658755791145647571931)
  ·
    refine ⟨12854488133686718471357897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8569658755791145647571931 12854488133686718471357897)
    ·
      refine ⟨9640866100265038853518423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12854488133686718471357897 9640866100265038853518423)
      ·
        refine ⟨14461299150397558280277635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640866100265038853518423 14461299150397558280277635)
        ·
          refine ⟨21691948725596337420416453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14461299150397558280277635 21691948725596337420416453)
          ·
            refine ⟨4067240386049313266328085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21691948725596337420416453 4067240386049313266328085)
            ·
              refine ⟨190651893096061559359129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4067240386049313266328085 190651893096061559359129)
              ·
                refine ⟨142988919822046169519347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190651893096061559359129 142988919822046169519347)
                ·
                  refine ⟨214483379733069254279021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142988919822046169519347 214483379733069254279021)
                  ·
                    refine ⟨80431267399900970354633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214483379733069254279021 80431267399900970354633)
                    ·
                      rfl

theorem cell22_234959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 3].length) (baseStart_234959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234959 prefixEnd_234959 := by exact prefixLift 234959
  have htrace : WordTrace (prefixWord ++ tailWord_234959) baseStart_234959 baseEnd_234959 := by
    simpa [prefixWord, tailWord_234959, baseEnd_234959] using wordTrace_append hprefix tailTrace_234959
  have hstable : (prefixWord ++ tailWord_234959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234959).length < 2 ^ (prefixWord ++ tailWord_234959).sum := by decide
  have hdescent : baseEnd_234959 < baseStart_234959 := by decide
  rcases family_descends (prefixWord ++ tailWord_234959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_234970 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_234970 : Nat := 118140960795 + 234970 * 2 ^ 59
def prefixEnd_234970 : Nat := 4983230072969 + 3 ^ 40 * 234970 * 2
def baseEnd_234970 : Nat := 80435032924700608329599

theorem tailTrace_234970 : CollatzResearch.WordTrace tailWord_234970 prefixEnd_234970 80435032924700608329599 := by
  unfold tailWord_234970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142514989687823631555591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5713373305834196350814909 2142514989687823631555591)
  ·
    refine ⟨3213772484531735447333387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142514989687823631555591 3213772484531735447333387)
    ·
      refine ⟨4820658726797603171000081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213772484531735447333387 4820658726797603171000081)
      ·
        refine ⟨3615494045098202378250061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4820658726797603171000081 3615494045098202378250061)
        ·
          refine ⟨1355810266911825891843773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3615494045098202378250061 1355810266911825891843773)
          ·
            refine ⟨508428850091934709441415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1355810266911825891843773 508428850091934709441415)
            ·
              refine ⟨762643275137902064162123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508428850091934709441415 762643275137902064162123)
              ·
                refine ⟨1143964912706853096243185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762643275137902064162123 1143964912706853096243185)
                ·
                  refine ⟨857973684530139822182389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1143964912706853096243185 857973684530139822182389)
                  ·
                    refine ⟨80435032924700608329599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 857973684530139822182389 80435032924700608329599)
                    ·
                      rfl

theorem cell22_234970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_234970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_234970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_234970 prefixEnd_234970 := by exact prefixLift 234970
  have htrace : WordTrace (prefixWord ++ tailWord_234970) baseStart_234970 baseEnd_234970 := by
    simpa [prefixWord, tailWord_234970, baseEnd_234970] using wordTrace_append hprefix tailTrace_234970
  have hstable : (prefixWord ++ tailWord_234970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_234970).length < 2 ^ (prefixWord ++ tailWord_234970).sum := by decide
  have hdescent : baseEnd_234970 < baseStart_234970 := by decide
  rcases family_descends (prefixWord ++ tailWord_234970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235006 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_235006 : Nat := 118140960795 + 235006 * 2 ^ 59
def prefixEnd_235006 : Nat := 4983230072969 + 3 ^ 40 * 235006 * 2
def baseEnd_235006 : Nat := 26815785486802838143163

theorem tailTrace_235006 : CollatzResearch.WordTrace tailWord_235006 prefixEnd_235006 26815785486802838143163 := by
  unfold tailWord_235006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071421623327609084316609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5714248657747248449688581 1071421623327609084316609)
  ·
    refine ⟨803566217495706813237457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071421623327609084316609 803566217495706813237457)
    ·
      refine ⟨602674663121780109928093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 803566217495706813237457 602674663121780109928093)
      ·
        refine ⟨226002998670667541223035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602674663121780109928093 226002998670667541223035)
        ·
          refine ⟨339004498006001311834553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226002998670667541223035 339004498006001311834553)
          ·
            refine ⟨254253373504500983875915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339004498006001311834553 254253373504500983875915)
            ·
              refine ⟨381380060256751475813873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254253373504500983875915 381380060256751475813873)
              ·
                refine ⟨286035045192563606860405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381380060256751475813873 286035045192563606860405)
                ·
                  refine ⟨26815785486802838143163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286035045192563606860405 26815785486802838143163)
                  ·
                    rfl

theorem cell22_235006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_235006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235006 prefixEnd_235006 := by exact prefixLift 235006
  have htrace : WordTrace (prefixWord ++ tailWord_235006) baseStart_235006 baseEnd_235006 := by
    simpa [prefixWord, tailWord_235006, baseEnd_235006] using wordTrace_append hprefix tailTrace_235006
  have hstable : (prefixWord ++ tailWord_235006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235006).length < 2 ^ (prefixWord ++ tailWord_235006).sum := by decide
  have hdescent : baseEnd_235006 < baseStart_235006 := by decide
  rcases family_descends (prefixWord ++ tailWord_235006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235137 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_235137 : Nat := 118140960795 + 235137 * 2 ^ 59
def prefixEnd_235137 : Nat := 4983230072969 + 3 ^ 40 * 235137 * 2
def baseEnd_235137 : Nat := 80492200437567839404087

theorem tailTrace_235137 : CollatzResearch.WordTrace tailWord_235137 prefixEnd_235137 80492200437567839404087 := by
  unfold tailWord_235137
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576150949146282047551665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5717433966097521365034443 8576150949146282047551665)
  ·
    refine ⟨6432113211859711535663749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8576150949146282047551665 6432113211859711535663749)
    ·
      refine ⟨1206021227223695912936953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6432113211859711535663749 1206021227223695912936953)
      ·
        refine ⟨904515920417771934702715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1206021227223695912936953 904515920417771934702715)
        ·
          refine ⟨1356773880626657902054073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904515920417771934702715 1356773880626657902054073)
          ·
            refine ⟨1017580410469993426540555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356773880626657902054073 1017580410469993426540555)
            ·
              refine ⟨1526370615704990139810833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017580410469993426540555 1526370615704990139810833)
              ·
                refine ⟨1144777961778742604858125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1526370615704990139810833 1144777961778742604858125)
                ·
                  refine ⟨429291735667028476821797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144777961778742604858125 429291735667028476821797)
                  ·
                    refine ⟨80492200437567839404087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429291735667028476821797 80492200437567839404087)
                    ·
                      rfl

theorem cell22_235137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_235137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235137 prefixEnd_235137 := by exact prefixLift 235137
  have htrace : WordTrace (prefixWord ++ tailWord_235137) baseStart_235137 baseEnd_235137 := by
    simpa [prefixWord, tailWord_235137, baseEnd_235137] using wordTrace_append hprefix tailTrace_235137
  have hstable : (prefixWord ++ tailWord_235137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235137).length < 2 ^ (prefixWord ++ tailWord_235137).sum := by decide
  have hdescent : baseEnd_235137 < baseStart_235137 := by decide
  rcases family_descends (prefixWord ++ tailWord_235137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235169 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 4]
def baseStart_235169 : Nat := 118140960795 + 235169 * 2 ^ 59
def prefixEnd_235169 : Nat := 4983230072969 + 3 ^ 40 * 235169 * 2
def baseEnd_235169 : Nat := 26834384897176807534663

theorem tailTrace_235169 : CollatzResearch.WordTrace tailWord_235169 prefixEnd_235169 26834384897176807534663 := by
  unfold tailWord_235169
  simp only [CollatzResearch.WordTrace]
  refine ⟨8577318085030351512716561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5718212056686901008477707 8577318085030351512716561)
  ·
    refine ⟨6432988563772763634537421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8577318085030351512716561 6432988563772763634537421)
    ·
      refine ⟨2412370711414786362951533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6432988563772763634537421 2412370711414786362951533)
      ·
        refine ⟨904639016780544886106825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2412370711414786362951533 904639016780544886106825)
        ·
          refine ⟨678479262585408664580119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904639016780544886106825 678479262585408664580119)
          ·
            refine ⟨1017718893878112996870179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678479262585408664580119 1017718893878112996870179)
            ·
              refine ⟨1526578340817169495305269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017718893878112996870179 1526578340817169495305269)
              ·
                refine ⟨143116719451609640184869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1526578340817169495305269 143116719451609640184869)
                ·
                  refine ⟨26834384897176807534663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143116719451609640184869 26834384897176807534663)
                  ·
                    rfl

theorem cell22_235169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 4].length) (baseStart_235169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235169 prefixEnd_235169 := by exact prefixLift 235169
  have htrace : WordTrace (prefixWord ++ tailWord_235169) baseStart_235169 baseEnd_235169 := by
    simpa [prefixWord, tailWord_235169, baseEnd_235169] using wordTrace_append hprefix tailTrace_235169
  have hstable : (prefixWord ++ tailWord_235169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235169).length < 2 ^ (prefixWord ++ tailWord_235169).sum := by decide
  have hdescent : baseEnd_235169 < baseStart_235169 := by decide
  rcases family_descends (prefixWord ++ tailWord_235169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235184 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 2, 3]
def baseStart_235184 : Nat := 118140960795 + 235184 * 2 ^ 59
def prefixEnd_235184 : Nat := 4983230072969 + 3 ^ 40 * 235184 * 2
def baseEnd_235184 : Nat := 80508289498075383478943

theorem tailTrace_235184 : CollatzResearch.WordTrace tailWord_235184 prefixEnd_235184 80508289498075383478943 := by
  unfold tailWord_235184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4288932589988004537256303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5718576786650672716341737 4288932589988004537256303)
  ·
    refine ⟨6433398884982006805884455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4288932589988004537256303 6433398884982006805884455)
    ·
      refine ⟨9650098327473010208826683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433398884982006805884455 9650098327473010208826683)
      ·
        refine ⟨14475147491209515313240025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650098327473010208826683 14475147491209515313240025)
        ·
          refine ⟨10856360618407136484930019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14475147491209515313240025 10856360618407136484930019)
          ·
            refine ⟨16284540927610704727395029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10856360618407136484930019 16284540927610704727395029)
            ·
              refine ⟨381668927990875892048321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16284540927610704727395029 381668927990875892048321)
              ·
                refine ⟨286251695993156919036241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381668927990875892048321 286251695993156919036241)
                ·
                  refine ⟨214688771994867689277181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286251695993156919036241 214688771994867689277181)
                  ·
                    refine ⟨80508289498075383478943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214688771994867689277181 80508289498075383478943)
                    ·
                      rfl

theorem cell22_235184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 3].length) (baseStart_235184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235184 prefixEnd_235184 := by exact prefixLift 235184
  have htrace : WordTrace (prefixWord ++ tailWord_235184) baseStart_235184 baseEnd_235184 := by
    simpa [prefixWord, tailWord_235184, baseEnd_235184] using wordTrace_append hprefix tailTrace_235184
  have hstable : (prefixWord ++ tailWord_235184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235184).length < 2 ^ (prefixWord ++ tailWord_235184).sum := by decide
  have hdescent : baseEnd_235184 < baseStart_235184 := by decide
  rcases family_descends (prefixWord ++ tailWord_235184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235242 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 7]
def baseStart_235242 : Nat := 118140960795 + 235242 * 2 ^ 59
def prefixEnd_235242 : Nat := 4983230072969 + 3 ^ 40 * 235242 * 2
def baseEnd_235242 : Nat := 26842714694460855176255

theorem tailTrace_235242 : CollatzResearch.WordTrace tailWord_235242 prefixEnd_235242 26842714694460855176255 := by
  unfold tailWord_235242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144995153441471245030995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5719987075843923320082653 2144995153441471245030995)
  ·
    refine ⟨3217492730162206867546493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144995153441471245030995 3217492730162206867546493)
    ·
      refine ⟨1206559773810827575329935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3217492730162206867546493 1206559773810827575329935)
      ·
        refine ⟨1809839660716241362994903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206559773810827575329935 1809839660716241362994903)
        ·
          refine ⟨2714759491074362044492355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809839660716241362994903 2714759491074362044492355)
          ·
            refine ⟨4072139236611543066738533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714759491074362044492355 4072139236611543066738533)
            ·
              refine ⟨763526106864664325013475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4072139236611543066738533 763526106864664325013475)
              ·
                refine ⟨1145289160296996487520213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763526106864664325013475 1145289160296996487520213)
                ·
                  refine ⟨26842714694460855176255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1145289160296996487520213 26842714694460855176255)
                  ·
                    rfl

theorem cell22_235242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_235242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235242 prefixEnd_235242 := by exact prefixLift 235242
  have htrace : WordTrace (prefixWord ++ tailWord_235242) baseStart_235242 baseEnd_235242 := by
    simpa [prefixWord, tailWord_235242, baseEnd_235242] using wordTrace_append hprefix tailTrace_235242
  have hstable : (prefixWord ++ tailWord_235242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235242).length < 2 ^ (prefixWord ++ tailWord_235242).sum := by decide
  have hdescent : baseEnd_235242 < baseStart_235242 := by decide
  rcases family_descends (prefixWord ++ tailWord_235242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235252 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_235252 : Nat := 118140960795 + 235252 * 2 ^ 59
def prefixEnd_235252 : Nat := 4983230072969 + 3 ^ 40 * 235252 * 2
def baseEnd_235252 : Nat := 80531567287745872778735

theorem tailTrace_235252 : CollatzResearch.WordTrace tailWord_235252 prefixEnd_235252 80531567287745872778735 := by
  unfold tailWord_235252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290172671864828343994005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5720230229153104458658673 4290172671864828343994005)
  ·
    refine ⟨201101843993663828624719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4290172671864828343994005 201101843993663828624719)
    ·
      refine ⟨301652765990495742937079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201101843993663828624719 301652765990495742937079)
      ·
        refine ⟨452479148985743614405619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301652765990495742937079 452479148985743614405619)
        ·
          refine ⟨678718723478615421608429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452479148985743614405619 678718723478615421608429)
          ·
            refine ⟨254519521304480783103161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678718723478615421608429 254519521304480783103161)
            ·
              refine ⟨190889640978360587327371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254519521304480783103161 190889640978360587327371)
              ·
                refine ⟨286334461467540880991057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190889640978360587327371 286334461467540880991057)
                ·
                  refine ⟨214750846100655660743293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286334461467540880991057 214750846100655660743293)
                  ·
                    refine ⟨80531567287745872778735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214750846100655660743293 80531567287745872778735)
                    ·
                      rfl

theorem cell22_235252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_235252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235252 prefixEnd_235252 := by exact prefixLift 235252
  have htrace : WordTrace (prefixWord ++ tailWord_235252) baseStart_235252 baseEnd_235252 := by
    simpa [prefixWord, tailWord_235252, baseEnd_235252] using wordTrace_append hprefix tailTrace_235252
  have hstable : (prefixWord ++ tailWord_235252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235252).length < 2 ^ (prefixWord ++ tailWord_235252).sum := by decide
  have hdescent : baseEnd_235252 < baseStart_235252 := by decide
  rcases family_descends (prefixWord ++ tailWord_235252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235321 : List Nat := [1, 2, 1, 7, 1, 1, 1, 2, 6]
def baseStart_235321 : Nat := 118140960795 + 235321 * 2 ^ 59
def prefixEnd_235321 : Nat := 4983230072969 + 3 ^ 40 * 235321 * 2
def baseEnd_235321 : Nat := 26851729132617564267841

theorem tailTrace_235321 : CollatzResearch.WordTrace tailWord_235321 prefixEnd_235321 26851729132617564267841 := by
  unfold tailWord_235321
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582861980479681472249817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5721907986986454314833211 8582861980479681472249817)
  ·
    refine ⟨6437146485359761104187363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8582861980479681472249817 6437146485359761104187363)
    ·
      refine ⟨9655719728039641656281045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6437146485359761104187363 9655719728039641656281045)
      ·
        refine ⟨226305931125929101319087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 9655719728039641656281045 226305931125929101319087)
        ·
          refine ⟨339458896688893651978631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226305931125929101319087 339458896688893651978631)
          ·
            refine ⟨509188345033340477967947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339458896688893651978631 509188345033340477967947)
            ·
              refine ⟨763782517550010716951921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509188345033340477967947 763782517550010716951921)
              ·
                refine ⟨572836888162508037713941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763782517550010716951921 572836888162508037713941)
                ·
                  refine ⟨26851729132617564267841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 572836888162508037713941 26851729132617564267841)
                  ·
                    rfl

theorem cell22_235321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_235321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235321 prefixEnd_235321 := by exact prefixLift 235321
  have htrace : WordTrace (prefixWord ++ tailWord_235321) baseStart_235321 baseEnd_235321 := by
    simpa [prefixWord, tailWord_235321, baseEnd_235321] using wordTrace_append hprefix tailTrace_235321
  have hstable : (prefixWord ++ tailWord_235321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235321).length < 2 ^ (prefixWord ++ tailWord_235321).sum := by decide
  have hdescent : baseEnd_235321 < baseStart_235321 := by decide
  rcases family_descends (prefixWord ++ tailWord_235321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235340 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 1, 4]
def baseStart_235340 : Nat := 118140960795 + 235340 * 2 ^ 59
def prefixEnd_235340 : Nat := 4983230072969 + 3 ^ 40 * 235340 * 2
def baseEnd_235340 : Nat := 80561691486142976578465

theorem tailTrace_235340 : CollatzResearch.WordTrace tailWord_235340 prefixEnd_235340 80561691486142976578465 := by
  unfold tailWord_235340
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291777483705423858595737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5722369978273898478127649 4291777483705423858595737)
  ·
    refine ⟨3218833112779067893946803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4291777483705423858595737 3218833112779067893946803)
    ·
      refine ⟨4828249669168601840920205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218833112779067893946803 4828249669168601840920205)
      ·
        refine ⟨1810593625938225690345077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4828249669168601840920205 1810593625938225690345077)
        ·
          refine ⟨169743152431708658469851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1810593625938225690345077 169743152431708658469851)
          ·
            refine ⟨254614728647562987704777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169743152431708658469851 254614728647562987704777)
            ·
              refine ⟨190961046485672240778583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254614728647562987704777 190961046485672240778583)
              ·
                refine ⟨286441569728508361167875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190961046485672240778583 286441569728508361167875)
                ·
                  refine ⟨429662354592762541751813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286441569728508361167875 429662354592762541751813)
                  ·
                    refine ⟨80561691486142976578465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429662354592762541751813 80561691486142976578465)
                    ·
                      rfl

theorem cell22_235340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_235340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235340 prefixEnd_235340 := by exact prefixLift 235340
  have htrace : WordTrace (prefixWord ++ tailWord_235340) baseStart_235340 baseEnd_235340 := by
    simpa [prefixWord, tailWord_235340, baseEnd_235340] using wordTrace_append hprefix tailTrace_235340
  have hstable : (prefixWord ++ tailWord_235340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235340).length < 2 ^ (prefixWord ++ tailWord_235340).sum := by decide
  have hdescent : baseEnd_235340 < baseStart_235340 := by decide
  rcases family_descends (prefixWord ++ tailWord_235340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235370 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 1, 5]
def baseStart_235370 : Nat := 118140960795 + 235370 * 2 ^ 59
def prefixEnd_235370 : Nat := 4983230072969 + 3 ^ 40 * 235370 * 2
def baseEnd_235370 : Nat := 80571961099232898328373

theorem tailTrace_235370 : CollatzResearch.WordTrace tailWord_235370 prefixEnd_235370 80571961099232898328373 := by
  unfold tailWord_235370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2146162289325540710195891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5723099438201441893855709 2146162289325540710195891)
  ·
    refine ⟨3219243433988311065293837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2146162289325540710195891 3219243433988311065293837)
    ·
      refine ⟨1207216287745616649485189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3219243433988311065293837 1207216287745616649485189)
      ·
        refine ⟨226353053952303121778473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1207216287745616649485189 226353053952303121778473)
        ·
          refine ⟨169764790464227341333855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226353053952303121778473 169764790464227341333855)
          ·
            refine ⟨254647185696341012000783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169764790464227341333855 254647185696341012000783)
            ·
              refine ⟨381970778544511518001175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254647185696341012000783 381970778544511518001175)
              ·
                refine ⟨572956167816767277001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381970778544511518001175 572956167816767277001763)
                ·
                  refine ⟨859434251725150915502645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 572956167816767277001763 859434251725150915502645)
                  ·
                    refine ⟨80571961099232898328373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 859434251725150915502645 80571961099232898328373)
                    ·
                      rfl

theorem cell22_235370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_235370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235370 prefixEnd_235370 := by exact prefixLift 235370
  have htrace : WordTrace (prefixWord ++ tailWord_235370) baseStart_235370 baseEnd_235370 := by
    simpa [prefixWord, tailWord_235370, baseEnd_235370] using wordTrace_append hprefix tailTrace_235370
  have hstable : (prefixWord ++ tailWord_235370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235370).length < 2 ^ (prefixWord ++ tailWord_235370).sum := by decide
  have hdescent : baseEnd_235370 < baseStart_235370 := by decide
  rcases family_descends (prefixWord ++ tailWord_235370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235381 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_235381 : Nat := 118140960795 + 235381 * 2 ^ 59
def prefixEnd_235381 : Nat := 4983230072969 + 3 ^ 40 * 235381 * 2
def baseEnd_235381 : Nat := 80575726624032536303339

theorem tailTrace_235381 : CollatzResearch.WordTrace tailWord_235381 prefixEnd_235381 80575726624032536303339 := by
  unfold tailWord_235381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585050360262311719433997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5723366906841541146289331 8585050360262311719433997)
  ·
    refine ⟨3219393885098366894787749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8585050360262311719433997 3219393885098366894787749)
    ·
      refine ⟨603636353455943792772703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3219393885098366894787749 603636353455943792772703)
      ·
        refine ⟨905454530183915689159055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603636353455943792772703 905454530183915689159055)
        ·
          refine ⟨1358181795275873533738583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905454530183915689159055 1358181795275873533738583)
          ·
            refine ⟨2037272692913810300607875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1358181795275873533738583 2037272692913810300607875)
            ·
              refine ⟨3055909039370715450911813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037272692913810300607875 3055909039370715450911813)
              ·
                refine ⟨572982944882009147045965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3055909039370715450911813 572982944882009147045965)
                ·
                  refine ⟨214868604330753430142237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 572982944882009147045965 214868604330753430142237)
                  ·
                    refine ⟨80575726624032536303339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214868604330753430142237 80575726624032536303339)
                    ·
                      rfl

theorem cell22_235381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_235381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235381 prefixEnd_235381 := by exact prefixLift 235381
  have htrace : WordTrace (prefixWord ++ tailWord_235381) baseStart_235381 baseEnd_235381 := by
    simpa [prefixWord, tailWord_235381, baseEnd_235381] using wordTrace_append hprefix tailTrace_235381
  have hstable : (prefixWord ++ tailWord_235381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235381).length < 2 ^ (prefixWord ++ tailWord_235381).sum := by decide
  have hdescent : baseEnd_235381 < baseStart_235381 := by decide
  rcases family_descends (prefixWord ++ tailWord_235381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235407 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 10]
def baseStart_235407 : Nat := 118140960795 + 235407 * 2 ^ 59
def prefixEnd_235407 : Nat := 4983230072969 + 3 ^ 40 * 235407 * 2
def baseEnd_235407 : Nat := 80584626955377135153259

theorem tailTrace_235407 : CollatzResearch.WordTrace tailWord_235407 prefixEnd_235407 80584626955377135153259 := by
  unfold tailWord_235407
  simp only [CollatzResearch.WordTrace]
  refine ⟨8585998658168118159880475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5723999105445412106586983 8585998658168118159880475)
  ·
    refine ⟨12878997987252177239820713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8585998658168118159880475 12878997987252177239820713)
    ·
      refine ⟨9659248490439132929865535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12878997987252177239820713 9659248490439132929865535)
      ·
        refine ⟨14488872735658699394798303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659248490439132929865535 14488872735658699394798303)
        ·
          refine ⟨21733309103488049092197455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14488872735658699394798303 21733309103488049092197455)
          ·
            refine ⟨32599963655232073638296183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21733309103488049092197455 32599963655232073638296183)
            ·
              refine ⟨48899945482848110457444275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32599963655232073638296183 48899945482848110457444275)
              ·
                refine ⟨73349918224272165686166413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48899945482848110457444275 73349918224272165686166413)
                ·
                  refine ⟨27506219334102062132312405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73349918224272165686166413 27506219334102062132312405)
                  ·
                    refine ⟨80584626955377135153259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 27506219334102062132312405 80584626955377135153259)
                    ·
                      rfl

theorem cell22_235407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_235407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235407 prefixEnd_235407 := by exact prefixLift 235407
  have htrace : WordTrace (prefixWord ++ tailWord_235407) baseStart_235407 baseEnd_235407 := by
    simpa [prefixWord, tailWord_235407, baseEnd_235407] using wordTrace_append hprefix tailTrace_235407
  have hstable : (prefixWord ++ tailWord_235407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235407).length < 2 ^ (prefixWord ++ tailWord_235407).sum := by decide
  have hdescent : baseEnd_235407 < baseStart_235407 := by decide
  rcases family_descends (prefixWord ++ tailWord_235407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235415 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 1, 3]
def baseStart_235415 : Nat := 118140960795 + 235415 * 2 ^ 59
def prefixEnd_235415 : Nat := 4983230072969 + 3 ^ 40 * 235415 * 2
def baseEnd_235415 : Nat := 80587365518867780953235

theorem tailTrace_235415 : CollatzResearch.WordTrace tailWord_235415 prefixEnd_235415 80587365518867780953235 := by
  unfold tailWord_235415
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586290442139135526171699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5724193628092757017447799 8586290442139135526171699)
  ·
    refine ⟨12879435663208703289257549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8586290442139135526171699 12879435663208703289257549)
    ·
      refine ⟨4829788373703263733471581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12879435663208703289257549 4829788373703263733471581)
      ·
        refine ⟨1811170640138723900051843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4829788373703263733471581 1811170640138723900051843)
        ·
          refine ⟨2716755960208085850077765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811170640138723900051843 2716755960208085850077765)
          ·
            refine ⟨509391742539016096889581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2716755960208085850077765 509391742539016096889581)
            ·
              refine ⟨191021903452131036333593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509391742539016096889581 191021903452131036333593)
              ·
                refine ⟨143266427589098277250195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191021903452131036333593 143266427589098277250195)
                ·
                  refine ⟨214899641383647415875293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143266427589098277250195 214899641383647415875293)
                  ·
                    refine ⟨80587365518867780953235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214899641383647415875293 80587365518867780953235)
                    ·
                      rfl

theorem cell22_235415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 3].length) (baseStart_235415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235415 prefixEnd_235415 := by exact prefixLift 235415
  have htrace : WordTrace (prefixWord ++ tailWord_235415) baseStart_235415 baseEnd_235415 := by
    simpa [prefixWord, tailWord_235415, baseEnd_235415] using wordTrace_append hprefix tailTrace_235415
  have hstable : (prefixWord ++ tailWord_235415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235415).length < 2 ^ (prefixWord ++ tailWord_235415).sum := by decide
  have hdescent : baseEnd_235415 < baseStart_235415 := by decide
  rcases family_descends (prefixWord ++ tailWord_235415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235424 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 3, 4]
def baseStart_235424 : Nat := 118140960795 + 235424 * 2 ^ 59
def prefixEnd_235424 : Nat := 4983230072969 + 3 ^ 40 * 235424 * 2
def baseEnd_235424 : Nat := 80590446402794757478207

theorem tailTrace_235424 : CollatzResearch.WordTrace tailWord_235424 prefixEnd_235424 80590446402794757478207 := by
  unfold tailWord_235424
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293309349553265031624663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5724412466071020042166217 4293309349553265031624663)
  ·
    refine ⟨6439964024329897547436995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4293309349553265031624663 6439964024329897547436995)
    ·
      refine ⟨9659946036494846321155493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439964024329897547436995 9659946036494846321155493)
      ·
        refine ⟨1811239881842783685216655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9659946036494846321155493 1811239881842783685216655)
        ·
          refine ⟨2716859822764175527824983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811239881842783685216655 2716859822764175527824983)
          ·
            refine ⟨4075289734146263291737475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716859822764175527824983 4075289734146263291737475)
            ·
              refine ⟨6112934601219394937606213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075289734146263291737475 6112934601219394937606213)
              ·
                refine ⟨1146175237728636550801165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6112934601219394937606213 1146175237728636550801165)
                ·
                  refine ⟨429815714148238706550437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146175237728636550801165 429815714148238706550437)
                  ·
                    refine ⟨80590446402794757478207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429815714148238706550437 80590446402794757478207)
                    ·
                      rfl

theorem cell22_235424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_235424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235424 prefixEnd_235424 := by exact prefixLift 235424
  have htrace : WordTrace (prefixWord ++ tailWord_235424) baseStart_235424 baseEnd_235424 := by
    simpa [prefixWord, tailWord_235424, baseEnd_235424] using wordTrace_append hprefix tailTrace_235424
  have hstable : (prefixWord ++ tailWord_235424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235424).length < 2 ^ (prefixWord ++ tailWord_235424).sum := by decide
  have hdescent : baseEnd_235424 < baseStart_235424 := by decide
  rcases family_descends (prefixWord ++ tailWord_235424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235428 : List Nat := [2, 3, 1, 2, 1, 5, 2, 1, 5]
def baseStart_235428 : Nat := 118140960795 + 235428 * 2 ^ 59
def prefixEnd_235428 : Nat := 4983230072969 + 3 ^ 40 * 235428 * 2
def baseEnd_235428 : Nat := 26863938561513360126065

theorem tailTrace_235428 : CollatzResearch.WordTrace tailWord_235428 prefixEnd_235428 26863938561513360126065 := by
  unfold tailWord_235428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293382295546019373197469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5724509727394692497596625 4293382295546019373197469)
  ·
    refine ⟨1610018360829757264949051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4293382295546019373197469 1610018360829757264949051)
    ·
      refine ⟨2415027541244635897423577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610018360829757264949051 2415027541244635897423577)
      ·
        refine ⟨1811270655933476923067683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2415027541244635897423577 1811270655933476923067683)
        ·
          refine ⟨2716905983900215384601525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811270655933476923067683 2716905983900215384601525)
          ·
            refine ⟨254709935990645192306393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2716905983900215384601525 254709935990645192306393)
            ·
              refine ⟨191032451992983894229795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254709935990645192306393 191032451992983894229795)
              ·
                refine ⟨286548677989475841344693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191032451992983894229795 286548677989475841344693)
                ·
                  refine ⟨26863938561513360126065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286548677989475841344693 26863938561513360126065)
                  ·
                    rfl

theorem cell22_235428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_235428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235428 prefixEnd_235428 := by exact prefixLift 235428
  have htrace : WordTrace (prefixWord ++ tailWord_235428) baseStart_235428 baseEnd_235428 := by
    simpa [prefixWord, tailWord_235428, baseEnd_235428] using wordTrace_append hprefix tailTrace_235428
  have hstable : (prefixWord ++ tailWord_235428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235428).length < 2 ^ (prefixWord ++ tailWord_235428).sum := by decide
  have hdescent : baseEnd_235428 < baseStart_235428 := by decide
  rcases family_descends (prefixWord ++ tailWord_235428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235441 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_235441 : Nat := 118140960795 + 235441 * 2 ^ 59
def prefixEnd_235441 : Nat := 4983230072969 + 3 ^ 40 * 235441 * 2
def baseEnd_235441 : Nat := 80596265850212379803155

theorem tailTrace_235441 : CollatzResearch.WordTrace tailWord_235441 prefixEnd_235441 80596265850212379803155 := by
  unfold tailWord_235441
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587238740044941966618177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5724825826696627977745451 8587238740044941966618177)
  ·
    refine ⟨6440429055033706474963633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8587238740044941966618177 6440429055033706474963633)
    ·
      refine ⟨4830321791275279856222725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6440429055033706474963633 4830321791275279856222725)
      ·
        refine ⟨905685335864114973041761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4830321791275279856222725 905685335864114973041761)
        ·
          refine ⟨679264001898086229781321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905685335864114973041761 679264001898086229781321)
          ·
            refine ⟨509448001423564672335991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679264001898086229781321 509448001423564672335991)
            ·
              refine ⟨764172002135347008503987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509448001423564672335991 764172002135347008503987)
              ·
                refine ⟨1146258003203020512755981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764172002135347008503987 1146258003203020512755981)
                ·
                  refine ⟨429846751201132692283493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146258003203020512755981 429846751201132692283493)
                  ·
                    refine ⟨80596265850212379803155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 429846751201132692283493 80596265850212379803155)
                    ·
                      rfl

theorem cell22_235441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_235441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235441 prefixEnd_235441 := by exact prefixLift 235441
  have htrace : WordTrace (prefixWord ++ tailWord_235441) baseStart_235441 baseEnd_235441 := by
    simpa [prefixWord, tailWord_235441, baseEnd_235441] using wordTrace_append hprefix tailTrace_235441
  have hstable : (prefixWord ++ tailWord_235441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235441).length < 2 ^ (prefixWord ++ tailWord_235441).sum := by decide
  have hdescent : baseEnd_235441 < baseStart_235441 := by decide
  rcases family_descends (prefixWord ++ tailWord_235441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235456 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_235456 : Nat := 118140960795 + 235456 * 2 ^ 59
def prefixEnd_235456 : Nat := 4983230072969 + 3 ^ 40 * 235456 * 2
def baseEnd_235456 : Nat := 26867133552252446892703

theorem tailTrace_235456 : CollatzResearch.WordTrace tailWord_235456 prefixEnd_235456 26867133552252446892703 := by
  unfold tailWord_235456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293892917495299764207111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5725190556660399685609481 4293892917495299764207111)
  ·
    refine ⟨6440839376242949646310667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4293892917495299764207111 6440839376242949646310667)
    ·
      refine ⟨9661259064364424469466001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6440839376242949646310667 9661259064364424469466001)
      ·
        refine ⟨7245944298273318352099501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661259064364424469466001 7245944298273318352099501)
        ·
          refine ⟨2717229111852494382037313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7245944298273318352099501 2717229111852494382037313)
          ·
            refine ⟨2037921833889370786527985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717229111852494382037313 2037921833889370786527985)
            ·
              refine ⟨1528441375417028089895989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2037921833889370786527985 1528441375417028089895989)
              ·
                refine ⟨143291378945346383427749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1528441375417028089895989 143291378945346383427749)
                ·
                  refine ⟨26867133552252446892703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143291378945346383427749 26867133552252446892703)
                  ·
                    rfl

theorem cell22_235456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_235456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235456 prefixEnd_235456 := by exact prefixLift 235456
  have htrace : WordTrace (prefixWord ++ tailWord_235456) baseStart_235456 baseEnd_235456 := by
    simpa [prefixWord, tailWord_235456, baseEnd_235456] using wordTrace_append hprefix tailTrace_235456
  have hstable : (prefixWord ++ tailWord_235456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235456).length < 2 ^ (prefixWord ++ tailWord_235456).sum := by decide
  have hdescent : baseEnd_235456 < baseStart_235456 := by decide
  rcases family_descends (prefixWord ++ tailWord_235456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235516 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_235516 : Nat := 118140960795 + 235516 * 2 ^ 59
def prefixEnd_235516 : Nat := 4983230072969 + 3 ^ 40 * 235516 * 2
def baseEnd_235516 : Nat := 80621939882937184177925

theorem tailTrace_235516 : CollatzResearch.WordTrace tailWord_235516 prefixEnd_235516 80621939882937184177925 := by
  unfold tailWord_235516
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294987107386614887799201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5726649476515486517065601 4294987107386614887799201)
  ·
    refine ⟨3221240330539961165849401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4294987107386614887799201 3221240330539961165849401)
    ·
      refine ⟨2415930247904970874387051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3221240330539961165849401 2415930247904970874387051)
      ·
        refine ⟨3623895371857456311580577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415930247904970874387051 3623895371857456311580577)
        ·
          refine ⟨2717921528893092233685433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623895371857456311580577 2717921528893092233685433)
          ·
            refine ⟨2038441146669819175264075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717921528893092233685433 2038441146669819175264075)
            ·
              refine ⟨3057661720004728762896113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038441146669819175264075 3057661720004728762896113)
              ·
                refine ⟨2293246290003546572172085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057661720004728762896113 2293246290003546572172085)
                ·
                  refine ⟨214991839687832491141133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2293246290003546572172085 214991839687832491141133)
                  ·
                    refine ⟨80621939882937184177925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214991839687832491141133 80621939882937184177925)
                    ·
                      rfl

theorem cell22_235516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_235516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235516 prefixEnd_235516 := by exact prefixLift 235516
  have htrace : WordTrace (prefixWord ++ tailWord_235516) baseStart_235516 baseEnd_235516 := by
    simpa [prefixWord, tailWord_235516, baseEnd_235516] using wordTrace_append hprefix tailTrace_235516
  have hstable : (prefixWord ++ tailWord_235516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235516).length < 2 ^ (prefixWord ++ tailWord_235516).sum := by decide
  have hdescent : baseEnd_235516 < baseStart_235516 := by decide
  rcases family_descends (prefixWord ++ tailWord_235516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235653 : List Nat := [1, 3, 1, 1, 5, 3, 1, 7]
def baseStart_235653 : Nat := 118140960795 + 235653 * 2 ^ 59
def prefixEnd_235653 : Nat := 4983230072969 + 3 ^ 40 * 235653 * 2
def baseEnd_235653 : Nat := 8963204198079388166945

theorem tailTrace_235653 : CollatzResearch.WordTrace tailWord_235653 prefixEnd_235653 8963204198079388166945 := by
  unfold tailWord_235653
  simp only [CollatzResearch.WordTrace]
  refine ⟨8594971015276902173335613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5729980676851268115557075 8594971015276902173335613)
  ·
    refine ⟨3223114130728838315000855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8594971015276902173335613 3223114130728838315000855)
    ·
      refine ⟨4834671196093257472501283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223114130728838315000855 4834671196093257472501283)
      ·
        refine ⟨7252006794139886208751925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834671196093257472501283 7252006794139886208751925)
        ·
          refine ⟨679875636950614332070493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7252006794139886208751925 679875636950614332070493)
          ·
            refine ⟨254953363856480374526435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 679875636950614332070493 254953363856480374526435)
            ·
              refine ⟨382430045784720561789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254953363856480374526435 382430045784720561789653)
              ·
                refine ⟨8963204198079388166945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 382430045784720561789653 8963204198079388166945)
                ·
                  rfl

theorem cell22_235653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 7].length) (baseStart_235653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235653 prefixEnd_235653 := by exact prefixLift 235653
  have htrace : WordTrace (prefixWord ++ tailWord_235653) baseStart_235653 baseEnd_235653 := by
    simpa [prefixWord, tailWord_235653, baseEnd_235653] using wordTrace_append hprefix tailTrace_235653
  have hstable : (prefixWord ++ tailWord_235653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235653).length < 2 ^ (prefixWord ++ tailWord_235653).sum := by decide
  have hdescent : baseEnd_235653 < baseStart_235653 := by decide
  rcases family_descends (prefixWord ++ tailWord_235653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235672 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_235672 : Nat := 118140960795 + 235672 * 2 ^ 59
def prefixEnd_235672 : Nat := 4983230072969 + 3 ^ 40 * 235672 * 2
def baseEnd_235672 : Nat := 80675341871004777277447

theorem tailTrace_235672 : CollatzResearch.WordTrace tailWord_235672 prefixEnd_235672 80675341871004777277447 := by
  unfold tailWord_235672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4297832001104034209138635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5730442668138712278851513 4297832001104034209138635)
  ·
    refine ⟨6446748001656051313707953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4297832001104034209138635 6446748001656051313707953)
    ·
      refine ⟨4835061001242038485280965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6446748001656051313707953 4835061001242038485280965)
      ·
        refine ⟨906573937732882215990181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4835061001242038485280965 906573937732882215990181)
        ·
          refine ⟨169982613324915415498159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 906573937732882215990181 169982613324915415498159)
          ·
            refine ⟨254973919987373123247239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169982613324915415498159 254973919987373123247239)
            ·
              refine ⟨382460879981059684870859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254973919987373123247239 382460879981059684870859)
              ·
                refine ⟨573691319971589527306289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382460879981059684870859 573691319971589527306289)
                ·
                  refine ⟨430268489978692145479717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573691319971589527306289 430268489978692145479717)
                  ·
                    refine ⟨80675341871004777277447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430268489978692145479717 80675341871004777277447)
                    ·
                      rfl

theorem cell22_235672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_235672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235672 prefixEnd_235672 := by exact prefixLift 235672
  have htrace : WordTrace (prefixWord ++ tailWord_235672) baseStart_235672 baseEnd_235672 := by
    simpa [prefixWord, tailWord_235672, baseEnd_235672] using wordTrace_append hprefix tailTrace_235672
  have hstable : (prefixWord ++ tailWord_235672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235672).length < 2 ^ (prefixWord ++ tailWord_235672).sum := by decide
  have hdescent : baseEnd_235672 < baseStart_235672 := by decide
  rcases family_descends (prefixWord ++ tailWord_235672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235775 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 2, 3]
def baseStart_235775 : Nat := 118140960795 + 235775 * 2 ^ 59
def prefixEnd_235775 : Nat := 4983230072969 + 3 ^ 40 * 235775 * 2
def baseEnd_235775 : Nat := 80710600875946841952131

theorem tailTrace_235775 : CollatzResearch.WordTrace tailWord_235775 prefixEnd_235775 80710600875946841952131 := by
  unfold tailWord_235775
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599420720834917009276779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5732947147223278006184519 8599420720834917009276779)
  ·
    refine ⟨12899131081252375513915169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8599420720834917009276779 12899131081252375513915169)
    ·
      refine ⟨9674348310939281635436377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12899131081252375513915169 9674348310939281635436377)
      ·
        refine ⟨7255761233204461226577283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9674348310939281635436377 7255761233204461226577283)
        ·
          refine ⟨10883641849806691839865925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7255761233204461226577283 10883641849806691839865925)
          ·
            refine ⟨2040682846838754719974861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10883641849806691839865925 2040682846838754719974861)
            ·
              refine ⟨765256067564533019990573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040682846838754719974861 765256067564533019990573)
              ·
                refine ⟨286971025336699882496465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 765256067564533019990573 286971025336699882496465)
                ·
                  refine ⟨215228269002524911872349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286971025336699882496465 215228269002524911872349)
                  ·
                    refine ⟨80710600875946841952131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215228269002524911872349 80710600875946841952131)
                    ·
                      rfl

theorem cell22_235775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_235775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235775 prefixEnd_235775 := by exact prefixLift 235775
  have htrace : WordTrace (prefixWord ++ tailWord_235775) baseStart_235775 baseEnd_235775 := by
    simpa [prefixWord, tailWord_235775, baseEnd_235775] using wordTrace_append hprefix tailTrace_235775
  have hstable : (prefixWord ++ tailWord_235775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235775).length < 2 ^ (prefixWord ++ tailWord_235775).sum := by decide
  have hdescent : baseEnd_235775 < baseStart_235775 := by decide
  rcases family_descends (prefixWord ++ tailWord_235775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235790 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_235790 : Nat := 118140960795 + 235790 * 2 ^ 59
def prefixEnd_235790 : Nat := 4983230072969 + 3 ^ 40 * 235790 * 2
def baseEnd_235790 : Nat := 80715735682491802827085

theorem tailTrace_235790 : CollatzResearch.WordTrace tailWord_235790 prefixEnd_235790 80715735682491802827085 := by
  unfold tailWord_235790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074995976972571821384103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5733311877187049714048549 1074995976972571821384103)
  ·
    refine ⟨1612493965458857732076155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1074995976972571821384103 1612493965458857732076155)
    ·
      refine ⟨2418740948188286598114233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1612493965458857732076155 2418740948188286598114233)
      ·
        refine ⟨1814055711141214948585675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2418740948188286598114233 1814055711141214948585675)
        ·
          refine ⟨2721083566711822422878513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814055711141214948585675 2721083566711822422878513)
          ·
            refine ⟨2040812675033866817158885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721083566711822422878513 2040812675033866817158885)
            ·
              refine ⟨382652376568850028217291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2040812675033866817158885 382652376568850028217291)
              ·
                refine ⟨573978564853275042325937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382652376568850028217291 573978564853275042325937)
                ·
                  refine ⟨430483923639956281744453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573978564853275042325937 430483923639956281744453)
                  ·
                    refine ⟨80715735682491802827085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 430483923639956281744453 80715735682491802827085)
                    ·
                      rfl

theorem cell22_235790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_235790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235790 prefixEnd_235790 := by exact prefixLift 235790
  have htrace : WordTrace (prefixWord ++ tailWord_235790) baseStart_235790 baseEnd_235790 := by
    simpa [prefixWord, tailWord_235790, baseEnd_235790] using wordTrace_append hprefix tailTrace_235790
  have hstable : (prefixWord ++ tailWord_235790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235790).length < 2 ^ (prefixWord ++ tailWord_235790).sum := by decide
  have hdescent : baseEnd_235790 < baseStart_235790 := by decide
  rcases family_descends (prefixWord ++ tailWord_235790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_235805 : List Nat := [1, 4, 2, 3, 3, 9]
def baseStart_235805 : Nat := 118140960795 + 235805 * 2 ^ 59
def prefixEnd_235805 : Nat := 4983230072969 + 3 ^ 40 * 235805 * 2
def baseEnd_235805 : Nat := 996553956654774860519

theorem tailTrace_235805 : CollatzResearch.WordTrace tailWord_235805 prefixEnd_235805 996553956654774860519 := by
  unfold tailWord_235805
  simp only [CollatzResearch.WordTrace]
  refine ⟨8600514910726232132868869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5733676607150821421912579 8600514910726232132868869)
  ·
    refine ⟨1612596545761168524912913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8600514910726232132868869 1612596545761168524912913)
    ·
      refine ⟨1209447409320876393684685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612596545761168524912913 1209447409320876393684685)
      ·
        refine ⟨453542778495328647631757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1209447409320876393684685 453542778495328647631757)
        ·
          refine ⟨170078541935748242861909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 453542778495328647631757 170078541935748242861909)
          ·
            refine ⟨996553956654774860519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 170078541935748242861909 996553956654774860519)
            ·
              rfl

theorem cell22_235805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 9].length) (baseStart_235805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_235805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_235805 prefixEnd_235805 := by exact prefixLift 235805
  have htrace : WordTrace (prefixWord ++ tailWord_235805) baseStart_235805 baseEnd_235805 := by
    simpa [prefixWord, tailWord_235805, baseEnd_235805] using wordTrace_append hprefix tailTrace_235805
  have hstable : (prefixWord ++ tailWord_235805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_235805).length < 2 ^ (prefixWord ++ tailWord_235805).sum := by decide
  have hdescent : baseEnd_235805 < baseStart_235805 := by decide
  rcases family_descends (prefixWord ++ tailWord_235805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236000 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 2, 5]
def baseStart_236000 : Nat := 118140960795 + 236000 * 2 ^ 59
def prefixEnd_236000 : Nat := 4983230072969 + 3 ^ 40 * 236000 * 2
def baseEnd_236000 : Nat := 80787622974121255076441

theorem tailTrace_236000 : CollatzResearch.WordTrace tailWord_236000 prefixEnd_236000 80787622974121255076441 := by
  unfold tailWord_236000
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303813572509890218108727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5738418096679853624144969 4303813572509890218108727)
  ·
    refine ⟨6455720358764835327163091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4303813572509890218108727 6455720358764835327163091)
    ·
      refine ⟨9683580538147252990744637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6455720358764835327163091 9683580538147252990744637)
      ·
        refine ⟨3631342701805219871529239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9683580538147252990744637 3631342701805219871529239)
        ·
          refine ⟨5447014052707829807293859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3631342701805219871529239 5447014052707829807293859)
          ·
            refine ⟨8170521079061744710940789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5447014052707829807293859 8170521079061744710940789)
            ·
              refine ⟨765986351162038566650699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8170521079061744710940789 765986351162038566650699)
              ·
                refine ⟨1148979526743057849976049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765986351162038566650699 1148979526743057849976049)
                ·
                  refine ⟨861734645057293387482037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1148979526743057849976049 861734645057293387482037)
                  ·
                    refine ⟨80787622974121255076441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 861734645057293387482037 80787622974121255076441)
                    ·
                      rfl

theorem cell22_236000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_236000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236000 prefixEnd_236000 := by exact prefixLift 236000
  have htrace : WordTrace (prefixWord ++ tailWord_236000) baseStart_236000 baseEnd_236000 := by
    simpa [prefixWord, tailWord_236000, baseEnd_236000] using wordTrace_append hprefix tailTrace_236000
  have hstable : (prefixWord ++ tailWord_236000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236000).length < 2 ^ (prefixWord ++ tailWord_236000).sum := by decide
  have hdescent : baseEnd_236000 < baseStart_236000 := by decide
  rcases family_descends (prefixWord ++ tailWord_236000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236092 : List Nat := [2, 2, 2, 2, 3, 3, 8]
def baseStart_236092 : Nat := 118140960795 + 236092 * 2 ^ 59
def prefixEnd_236092 : Nat := 4983230072969 + 3 ^ 40 * 236092 * 2
def baseEnd_236092 : Nat := 2993300609417173399117

theorem tailTrace_236092 : CollatzResearch.WordTrace tailWord_236092 prefixEnd_236092 2993300609417173399117 := by
  unfold tailWord_236092
  simp only [CollatzResearch.WordTrace]
  refine ⟨4305491330343240074283265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5740655107124320099044353 4305491330343240074283265)
  ·
    refine ⟨3229118497757430055712449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4305491330343240074283265 3229118497757430055712449)
    ·
      refine ⟨2421838873318072541784337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3229118497757430055712449 2421838873318072541784337)
      ·
        refine ⟨1816379154988554406338253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2421838873318072541784337 1816379154988554406338253)
        ·
          refine ⟨681142183120707902376845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1816379154988554406338253 681142183120707902376845)
          ·
            refine ⟨255428318670265463391317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 681142183120707902376845 255428318670265463391317)
            ·
              refine ⟨2993300609417173399117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 255428318670265463391317 2993300609417173399117)
              ·
                rfl

theorem cell22_236092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 8].length) (baseStart_236092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236092 prefixEnd_236092 := by exact prefixLift 236092
  have htrace : WordTrace (prefixWord ++ tailWord_236092) baseStart_236092 baseEnd_236092 := by
    simpa [prefixWord, tailWord_236092, baseEnd_236092] using wordTrace_append hprefix tailTrace_236092
  have hstable : (prefixWord ++ tailWord_236092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236092).length < 2 ^ (prefixWord ++ tailWord_236092).sum := by decide
  have hdescent : baseEnd_236092 < baseStart_236092 := by decide
  rcases family_descends (prefixWord ++ tailWord_236092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236109 : List Nat := [1, 6, 1, 1, 2, 2, 2, 7]
def baseStart_236109 : Nat := 118140960795 + 236109 * 2 ^ 59
def prefixEnd_236109 : Nat := 4983230072969 + 3 ^ 40 * 236109 * 2
def baseEnd_236109 : Nat := 8980548433520144900123

theorem tailTrace_236109 : CollatzResearch.WordTrace tailWord_236109 prefixEnd_236109 8980548433520144900123 := by
  unfold tailWord_236109
  simp only [CollatzResearch.WordTrace]
  refine ⟨8611602701624892051935381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5741068467749928034623587 8611602701624892051935381)
  ·
    refine ⟨403668876638666814934471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8611602701624892051935381 403668876638666814934471)
    ·
      refine ⟨605503314958000222401707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403668876638666814934471 605503314958000222401707)
      ·
        refine ⟨908254972437000333602561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605503314958000222401707 908254972437000333602561)
        ·
          refine ⟨681191229327750250201921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 908254972437000333602561 681191229327750250201921)
          ·
            refine ⟨510893421995812687651441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681191229327750250201921 510893421995812687651441)
            ·
              refine ⟨383170066496859515738581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 510893421995812687651441 383170066496859515738581)
              ·
                refine ⟨8980548433520144900123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 383170066496859515738581 8980548433520144900123)
                ·
                  rfl

theorem cell22_236109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 7].length) (baseStart_236109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236109 prefixEnd_236109 := by exact prefixLift 236109
  have htrace : WordTrace (prefixWord ++ tailWord_236109) baseStart_236109 baseEnd_236109 := by
    simpa [prefixWord, tailWord_236109, baseEnd_236109] using wordTrace_append hprefix tailTrace_236109
  have hstable : (prefixWord ++ tailWord_236109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236109).length < 2 ^ (prefixWord ++ tailWord_236109).sum := by decide
  have hdescent : baseEnd_236109 < baseStart_236109 := by decide
  rcases family_descends (prefixWord ++ tailWord_236109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236167 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_236167 : Nat := 118140960795 + 236167 * 2 ^ 59
def prefixEnd_236167 : Nat := 4983230072969 + 3 ^ 40 * 236167 * 2
def baseEnd_236167 : Nat := 80844790486988486150929

theorem tailTrace_236167 : CollatzResearch.WordTrace tailWord_236167 prefixEnd_236167 80844790486988486150929 := by
  unfold tailWord_236167
  simp only [CollatzResearch.WordTrace]
  refine ⟨8613718135414767957546755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5742478756943178638364503 8613718135414767957546755)
  ·
    refine ⟨12920577203122151936320133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8613718135414767957546755 12920577203122151936320133)
    ·
      refine ⟨2422608225585403488060025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12920577203122151936320133 2422608225585403488060025)
      ·
        refine ⟨1816956169189052616045019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2422608225585403488060025 1816956169189052616045019)
        ·
          refine ⟨2725434253783578924067529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1816956169189052616045019 2725434253783578924067529)
          ·
            refine ⟨2044075690337684193050647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725434253783578924067529 2044075690337684193050647)
            ·
              refine ⟨3066113535506526289575971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2044075690337684193050647 3066113535506526289575971)
              ·
                refine ⟨4599170303259789434363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3066113535506526289575971 4599170303259789434363957)
                ·
                  refine ⟨431172215930605259471621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4599170303259789434363957 431172215930605259471621)
                  ·
                    refine ⟨80844790486988486150929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431172215930605259471621 80844790486988486150929)
                    ·
                      rfl

theorem cell22_236167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_236167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236167 prefixEnd_236167 := by exact prefixLift 236167
  have htrace : WordTrace (prefixWord ++ tailWord_236167) baseStart_236167 baseEnd_236167 := by
    simpa [prefixWord, tailWord_236167, baseEnd_236167] using wordTrace_append hprefix tailTrace_236167
  have hstable : (prefixWord ++ tailWord_236167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236167).length < 2 ^ (prefixWord ++ tailWord_236167).sum := by decide
  have hdescent : baseEnd_236167 < baseStart_236167 := by decide
  rcases family_descends (prefixWord ++ tailWord_236167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236184 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_236184 : Nat := 118140960795 + 236184 * 2 ^ 59
def prefixEnd_236184 : Nat := 4983230072969 + 3 ^ 40 * 236184 * 2
def baseEnd_236184 : Nat := 80850609934406108475877

theorem tailTrace_236184 : CollatzResearch.WordTrace tailWord_236184 prefixEnd_236184 80850609934406108475877 := by
  unfold tailWord_236184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307169088176589930457803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5742892117568786573943737 4307169088176589930457803)
  ·
    refine ⟨6460753632264884895686705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4307169088176589930457803 6460753632264884895686705)
    ·
      refine ⟨4845565224198663671765029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6460753632264884895686705 4845565224198663671765029)
      ·
        refine ⟨908543479537249438455943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4845565224198663671765029 908543479537249438455943)
        ·
          refine ⟨1362815219305874157683915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908543479537249438455943 1362815219305874157683915)
          ·
            refine ⟨2044222828958811236525873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362815219305874157683915 2044222828958811236525873)
            ·
              refine ⟨1533167121719108427394405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044222828958811236525873 1533167121719108427394405)
              ·
                refine ⟨287468835322332830136451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1533167121719108427394405 287468835322332830136451)
                ·
                  refine ⟨431203252983499245204677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 287468835322332830136451 431203252983499245204677)
                  ·
                    refine ⟨80850609934406108475877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 431203252983499245204677 80850609934406108475877)
                    ·
                      rfl

theorem cell22_236184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_236184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236184 prefixEnd_236184 := by exact prefixLift 236184
  have htrace : WordTrace (prefixWord ++ tailWord_236184) baseStart_236184 baseEnd_236184 := by
    simpa [prefixWord, tailWord_236184, baseEnd_236184] using wordTrace_append hprefix tailTrace_236184
  have hstable : (prefixWord ++ tailWord_236184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236184).length < 2 ^ (prefixWord ++ tailWord_236184).sum := by decide
  have hdescent : baseEnd_236184 < baseStart_236184 := by decide
  rcases family_descends (prefixWord ++ tailWord_236184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236272 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_236272 : Nat := 118140960795 + 236272 * 2 ^ 59
def prefixEnd_236272 : Nat := 4983230072969 + 3 ^ 40 * 236272 * 2
def baseEnd_236272 : Nat := 26960244710934404091869

theorem tailTrace_236272 : CollatzResearch.WordTrace tailWord_236272 prefixEnd_236272 26960244710934404091869 := by
  unfold tailWord_236272
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308773900017185445059535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5745031866689580593412713 4308773900017185445059535)
  ·
    refine ⟨6463160850025778167589303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4308773900017185445059535 6463160850025778167589303)
    ·
      refine ⟨9694741275038667251383955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6463160850025778167589303 9694741275038667251383955)
      ·
        refine ⟨14542111912558000877075933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9694741275038667251383955 14542111912558000877075933)
        ·
          refine ⟨5453291967209250328903475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14542111912558000877075933 5453291967209250328903475)
          ·
            refine ⟨8179937950813875493355213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5453291967209250328903475 8179937950813875493355213)
            ·
              refine ⟨3067476731555203310008205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8179937950813875493355213 3067476731555203310008205)
              ·
                refine ⟨1150303774333201241253077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3067476731555203310008205 1150303774333201241253077)
                ·
                  refine ⟨26960244710934404091869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1150303774333201241253077 26960244710934404091869)
                  ·
                    rfl

theorem cell22_236272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_236272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236272 prefixEnd_236272 := by exact prefixLift 236272
  have htrace : WordTrace (prefixWord ++ tailWord_236272) baseStart_236272 baseEnd_236272 := by
    simpa [prefixWord, tailWord_236272, baseEnd_236272] using wordTrace_append hprefix tailTrace_236272
  have hstable : (prefixWord ++ tailWord_236272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236272).length < 2 ^ (prefixWord ++ tailWord_236272).sum := by decide
  have hdescent : baseEnd_236272 < baseStart_236272 := by decide
  rcases family_descends (prefixWord ++ tailWord_236272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236287 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_236287 : Nat := 118140960795 + 236287 * 2 ^ 59
def prefixEnd_236287 : Nat := 4983230072969 + 3 ^ 40 * 236287 * 2
def baseEnd_236287 : Nat := 80885868939348173150561

theorem tailTrace_236287 : CollatzResearch.WordTrace tailWord_236287 prefixEnd_236287 80885868939348173150561 := by
  unfold tailWord_236287
  simp only [CollatzResearch.WordTrace]
  refine ⟨8618094894980028451915115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5745396596653352301276743 8618094894980028451915115)
  ·
    refine ⟨12927142342470042677872673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8618094894980028451915115 12927142342470042677872673)
    ·
      refine ⟨9695356756852532008404505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12927142342470042677872673 9695356756852532008404505)
      ·
        refine ⟨7271517567639399006303379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9695356756852532008404505 7271517567639399006303379)
        ·
          refine ⟨10907276351459098509455069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7271517567639399006303379 10907276351459098509455069)
          ·
            refine ⟨4090228631797161941045651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10907276351459098509455069 4090228631797161941045651)
            ·
              refine ⟨6135342947695742911568477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4090228631797161941045651 6135342947695742911568477)
              ·
                refine ⟨2300753605385903591838179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6135342947695742911568477 2300753605385903591838179)
                ·
                  refine ⟨3451130408078855387757269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2300753605385903591838179 3451130408078855387757269)
                  ·
                    refine ⟨80885868939348173150561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3451130408078855387757269 80885868939348173150561)
                    ·
                      rfl

theorem cell22_236287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_236287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236287 prefixEnd_236287 := by exact prefixLift 236287
  have htrace : WordTrace (prefixWord ++ tailWord_236287) baseStart_236287 baseEnd_236287 := by
    simpa [prefixWord, tailWord_236287, baseEnd_236287] using wordTrace_append hprefix tailTrace_236287
  have hstable : (prefixWord ++ tailWord_236287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236287).length < 2 ^ (prefixWord ++ tailWord_236287).sum := by decide
  have hdescent : baseEnd_236287 < baseStart_236287 := by decide
  rcases family_descends (prefixWord ++ tailWord_236287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236411 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 3, 3]
def baseStart_236411 : Nat := 118140960795 + 236411 * 2 ^ 59
def prefixEnd_236411 : Nat := 4983230072969 + 3 ^ 40 * 236411 * 2
def baseEnd_236411 : Nat := 80928316673453183050181

theorem tailTrace_236411 : CollatzResearch.WordTrace tailWord_236411 prefixEnd_236411 80928316673453183050181 := by
  unfold tailWord_236411
  simp only [CollatzResearch.WordTrace]
  refine ⟨8622617546530797629429087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5748411697687198419619391 8622617546530797629429087)
  ·
    refine ⟨12933926319796196444143631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8622617546530797629429087 12933926319796196444143631)
    ·
      refine ⟨19400889479694294666215447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12933926319796196444143631 19400889479694294666215447)
      ·
        refine ⟨29101334219541441999323171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19400889479694294666215447 29101334219541441999323171)
        ·
          refine ⟨43652001329312162998984757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29101334219541441999323171 43652001329312162998984757)
          ·
            refine ⟨4092375124623015281154821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43652001329312162998984757 4092375124623015281154821)
            ·
              refine ⟨767320335866815365216529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4092375124623015281154821 767320335866815365216529)
              ·
                refine ⟨575490251900111523912397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767320335866815365216529 575490251900111523912397)
                ·
                  refine ⟨215808844462541821467149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575490251900111523912397 215808844462541821467149)
                  ·
                    refine ⟨80928316673453183050181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215808844462541821467149 80928316673453183050181)
                    ·
                      rfl

theorem cell22_236411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 3].length) (baseStart_236411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236411 prefixEnd_236411 := by exact prefixLift 236411
  have htrace : WordTrace (prefixWord ++ tailWord_236411) baseStart_236411 baseEnd_236411 := by
    simpa [prefixWord, tailWord_236411, baseEnd_236411] using wordTrace_append hprefix tailTrace_236411
  have hstable : (prefixWord ++ tailWord_236411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236411).length < 2 ^ (prefixWord ++ tailWord_236411).sum := by decide
  have hdescent : baseEnd_236411 < baseStart_236411 := by decide
  rcases family_descends (prefixWord ++ tailWord_236411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236580 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_236580 : Nat := 118140960795 + 236580 * 2 ^ 59
def prefixEnd_236580 : Nat := 4983230072969 + 3 ^ 40 * 236580 * 2
def baseEnd_236580 : Nat := 80986168827193075574663

theorem tailTrace_236580 : CollatzResearch.WordTrace tailWord_236580 prefixEnd_236580 80986168827193075574663 := by
  unfold tailWord_236580
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314390741459269746165597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5752520988612359661554129 4314390741459269746165597)
  ·
    refine ⟨1617896528047226154812099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4314390741459269746165597 1617896528047226154812099)
    ·
      refine ⟨2426844792070839232218149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1617896528047226154812099 2426844792070839232218149)
      ·
        refine ⟨455033398513282356040903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2426844792070839232218149 455033398513282356040903)
        ·
          refine ⟨682550097769923534061355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455033398513282356040903 682550097769923534061355)
          ·
            refine ⟨1023825146654885301092033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682550097769923534061355 1023825146654885301092033)
            ·
              refine ⟨767868859991163975819025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1023825146654885301092033 767868859991163975819025)
              ·
                refine ⟨575901644993372981864269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767868859991163975819025 575901644993372981864269)
                ·
                  refine ⟨215963116872514868199101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575901644993372981864269 215963116872514868199101)
                  ·
                    refine ⟨80986168827193075574663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215963116872514868199101 80986168827193075574663)
                    ·
                      rfl

theorem cell22_236580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_236580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236580 prefixEnd_236580 := by exact prefixLift 236580
  have htrace : WordTrace (prefixWord ++ tailWord_236580) baseStart_236580 baseEnd_236580 := by
    simpa [prefixWord, tailWord_236580, baseEnd_236580] using wordTrace_append hprefix tailTrace_236580
  have hstable : (prefixWord ++ tailWord_236580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236580).length < 2 ^ (prefixWord ++ tailWord_236580).sum := by decide
  have hdescent : baseEnd_236580 < baseStart_236580 := by decide
  rcases family_descends (prefixWord ++ tailWord_236580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236614 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_236614 : Nat := 118140960795 + 236614 * 2 ^ 59
def prefixEnd_236614 : Nat := 4983230072969 + 3 ^ 40 * 236614 * 2
def baseEnd_236614 : Nat := 80997807722028320224559

theorem tailTrace_236614 : CollatzResearch.WordTrace tailWord_236614 prefixEnd_236614 80997807722028320224559 := by
  unfold tailWord_236614
  simp only [CollatzResearch.WordTrace]
  refine ⟨269688173899855103095903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5753347709863575532712597 269688173899855103095903)
  ·
    refine ⟨404532260849782654643855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 269688173899855103095903 404532260849782654643855)
    ·
      refine ⟨606798391274673981965783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404532260849782654643855 606798391274673981965783)
      ·
        refine ⟨910197586912010972948675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 606798391274673981965783 910197586912010972948675)
        ·
          refine ⟨1365296380368016459423013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910197586912010972948675 1365296380368016459423013)
          ·
            refine ⟨255993071319003086141815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1365296380368016459423013 255993071319003086141815)
            ·
              refine ⟨383989606978504629212723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255993071319003086141815 383989606978504629212723)
              ·
                refine ⟨575984410467756943819085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383989606978504629212723 575984410467756943819085)
                ·
                  refine ⟨215994153925408853932157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 575984410467756943819085 215994153925408853932157)
                  ·
                    refine ⟨80997807722028320224559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 215994153925408853932157 80997807722028320224559)
                    ·
                      rfl

theorem cell22_236614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_236614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236614 prefixEnd_236614 := by exact prefixLift 236614
  have htrace : WordTrace (prefixWord ++ tailWord_236614) baseStart_236614 baseEnd_236614 := by
    simpa [prefixWord, tailWord_236614, baseEnd_236614] using wordTrace_append hprefix tailTrace_236614
  have hstable : (prefixWord ++ tailWord_236614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236614).length < 2 ^ (prefixWord ++ tailWord_236614).sum := by decide
  have hdescent : baseEnd_236614 < baseStart_236614 := by decide
  rcases family_descends (prefixWord ++ tailWord_236614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236653 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_236653 : Nat := 118140960795 + 236653 * 2 ^ 59
def prefixEnd_236653 : Nat := 4983230072969 + 3 ^ 40 * 236653 * 2
def baseEnd_236653 : Nat := 81011158219045218499439

theorem tailTrace_236653 : CollatzResearch.WordTrace tailWord_236653 prefixEnd_236653 81011158219045218499439 := by
  unfold tailWord_236653
  simp only [CollatzResearch.WordTrace]
  refine ⟨8631444011654072959738613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5754296007769381973159075 8631444011654072959738613)
  ·
    refine ⟨809197876092569339975495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8631444011654072959738613 809197876092569339975495)
    ·
      refine ⟨1213796814138854009963243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 809197876092569339975495 1213796814138854009963243)
      ·
        refine ⟨1820695221208281014944865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213796814138854009963243 1820695221208281014944865)
        ·
          refine ⟨1365521415906210761208649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820695221208281014944865 1365521415906210761208649)
          ·
            refine ⟨1024141061929658070906487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1365521415906210761208649 1024141061929658070906487)
            ·
              refine ⟨1536211592894487106359731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1024141061929658070906487 1536211592894487106359731)
              ·
                refine ⟨2304317389341730659539597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536211592894487106359731 2304317389341730659539597)
                ·
                  refine ⟨864119021003148997327349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2304317389341730659539597 864119021003148997327349)
                  ·
                    refine ⟨81011158219045218499439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 864119021003148997327349 81011158219045218499439)
                    ·
                      rfl

theorem cell22_236653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_236653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236653 prefixEnd_236653 := by exact prefixLift 236653
  have htrace : WordTrace (prefixWord ++ tailWord_236653) baseStart_236653 baseEnd_236653 := by
    simpa [prefixWord, tailWord_236653, baseEnd_236653] using wordTrace_append hprefix tailTrace_236653
  have hstable : (prefixWord ++ tailWord_236653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236653).length < 2 ^ (prefixWord ++ tailWord_236653).sum := by decide
  have hdescent : baseEnd_236653 < baseStart_236653 := by decide
  rcases family_descends (prefixWord ++ tailWord_236653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236668 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_236668 : Nat := 118140960795 + 236668 * 2 ^ 59
def prefixEnd_236668 : Nat := 4983230072969 + 3 ^ 40 * 236668 * 2
def baseEnd_236668 : Nat := 81016293025590179374393

theorem tailTrace_236668 : CollatzResearch.WordTrace tailWord_236668 prefixEnd_236668 81016293025590179374393 := by
  unfold tailWord_236668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315995553299865260767329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5754660737733153681023105 4315995553299865260767329)
  ·
    refine ⟨3236996664974898945575497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4315995553299865260767329 3236996664974898945575497)
    ·
      refine ⟨2427747498731174209181623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236996664974898945575497 2427747498731174209181623)
      ·
        refine ⟨3641621248096761313772435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427747498731174209181623 3641621248096761313772435)
        ·
          refine ⟨5462431872145141970658653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641621248096761313772435 5462431872145141970658653)
          ·
            refine ⟨2048411952054428238996995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5462431872145141970658653 2048411952054428238996995)
            ·
              refine ⟨3072617928081642358495493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048411952054428238996995 3072617928081642358495493)
              ·
                refine ⟨576115861515307942217905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3072617928081642358495493 576115861515307942217905)
                ·
                  refine ⟨432086896136480956663429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576115861515307942217905 432086896136480956663429)
                  ·
                    refine ⟨81016293025590179374393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432086896136480956663429 81016293025590179374393)
                    ·
                      rfl

theorem cell22_236668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_236668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236668 prefixEnd_236668 := by exact prefixLift 236668
  have htrace : WordTrace (prefixWord ++ tailWord_236668) baseStart_236668 baseEnd_236668 := by
    simpa [prefixWord, tailWord_236668, baseEnd_236668] using wordTrace_append hprefix tailTrace_236668
  have hstable : (prefixWord ++ tailWord_236668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236668).length < 2 ^ (prefixWord ++ tailWord_236668).sum := by decide
  have hdescent : baseEnd_236668 < baseStart_236668 := by decide
  rcases family_descends (prefixWord ++ tailWord_236668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236700 : List Nat := [2, 2, 3, 2, 1, 3, 3, 6]
def baseStart_236700 : Nat := 118140960795 + 236700 * 2 ^ 59
def prefixEnd_236700 : Nat := 4983230072969 + 3 ^ 40 * 236700 * 2
def baseEnd_236700 : Nat := 9003027475505862508255

theorem tailTrace_236700 : CollatzResearch.WordTrace tailWord_236700 prefixEnd_236700 9003027475505862508255 := by
  unfold tailWord_236700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4316579121241899993349777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5755438828322533324466369 4316579121241899993349777)
  ·
    refine ⟨3237434340931424995012333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4316579121241899993349777 3237434340931424995012333)
    ·
      refine ⟨1214037877849284373129625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3237434340931424995012333 1214037877849284373129625)
      ·
        refine ⟨910528408386963279847219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1214037877849284373129625 910528408386963279847219)
        ·
          refine ⟨1365792612580444919770829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 910528408386963279847219 1365792612580444919770829)
          ·
            refine ⟨512172229717666844914061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1365792612580444919770829 512172229717666844914061)
            ·
              refine ⟨192064586144125066842773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512172229717666844914061 192064586144125066842773)
              ·
                refine ⟨9003027475505862508255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192064586144125066842773 9003027475505862508255)
                ·
                  rfl

theorem cell22_236700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 6].length) (baseStart_236700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236700 prefixEnd_236700 := by exact prefixLift 236700
  have htrace : WordTrace (prefixWord ++ tailWord_236700) baseStart_236700 baseEnd_236700 := by
    simpa [prefixWord, tailWord_236700, baseEnd_236700] using wordTrace_append hprefix tailTrace_236700
  have hstable : (prefixWord ++ tailWord_236700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236700).length < 2 ^ (prefixWord ++ tailWord_236700).sum := by decide
  have hdescent : baseEnd_236700 < baseStart_236700 := by decide
  rcases family_descends (prefixWord ++ tailWord_236700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236702 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_236702 : Nat := 118140960795 + 236702 * 2 ^ 59
def prefixEnd_236702 : Nat := 4983230072969 + 3 ^ 40 * 236702 * 2
def baseEnd_236702 : Nat := 81027931920425424024289

theorem tailTrace_236702 : CollatzResearch.WordTrace tailWord_236702 prefixEnd_236702 81027931920425424024289 := by
  unfold tailWord_236702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079153898559569291034045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5755487458984369552181573 1079153898559569291034045)
  ·
    refine ⟨404682711959838484137767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1079153898559569291034045 404682711959838484137767)
    ·
      refine ⟨607024067939757726206651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404682711959838484137767 607024067939757726206651)
      ·
        refine ⟨910536101909636589309977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607024067939757726206651 910536101909636589309977)
        ·
          refine ⟨682902076432227441982483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910536101909636589309977 682902076432227441982483)
          ·
            refine ⟨1024353114648341162973725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 682902076432227441982483 1024353114648341162973725)
            ·
              refine ⟨384132417993127936115147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1024353114648341162973725 384132417993127936115147)
              ·
                refine ⟨576198626989691904172721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384132417993127936115147 576198626989691904172721)
                ·
                  refine ⟨432148970242268928129541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 576198626989691904172721 432148970242268928129541)
                  ·
                    refine ⟨81027931920425424024289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 432148970242268928129541 81027931920425424024289)
                    ·
                      rfl

theorem cell22_236702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_236702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236702 prefixEnd_236702 := by exact prefixLift 236702
  have htrace : WordTrace (prefixWord ++ tailWord_236702) baseStart_236702 baseEnd_236702 := by
    simpa [prefixWord, tailWord_236702, baseEnd_236702] using wordTrace_append hprefix tailTrace_236702
  have hstable : (prefixWord ++ tailWord_236702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236702).length < 2 ^ (prefixWord ++ tailWord_236702).sum := by decide
  have hdescent : baseEnd_236702 < baseStart_236702 := by decide
  rcases family_descends (prefixWord ++ tailWord_236702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236728 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_236728 : Nat := 118140960795 + 236728 * 2 ^ 59
def prefixEnd_236728 : Nat := 4983230072969 + 3 ^ 40 * 236728 * 2
def baseEnd_236728 : Nat := 27012277417256674291403

theorem tailTrace_236728 : CollatzResearch.WordTrace tailWord_236728 prefixEnd_236728 27012277417256674291403 := by
  unfold tailWord_236728
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317089743191180384359419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5756119657588240512479225 4317089743191180384359419)
  ·
    refine ⟨6475634614786770576539129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317089743191180384359419 6475634614786770576539129)
    ·
      refine ⟨4856725961090077932404347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6475634614786770576539129 4856725961090077932404347)
      ·
        refine ⟨7285088941635116898606521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856725961090077932404347 7285088941635116898606521)
        ·
          refine ⟨5463816706226337673954891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285088941635116898606521 5463816706226337673954891)
          ·
            refine ⟨8195725059339506510932337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463816706226337673954891 8195725059339506510932337)
            ·
              refine ⟨6146793794504629883199253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8195725059339506510932337 6146793794504629883199253)
              ·
                refine ⟨288130959117404525774965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6146793794504629883199253 288130959117404525774965)
                ·
                  refine ⟨27012277417256674291403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288130959117404525774965 27012277417256674291403)
                  ·
                    rfl

theorem cell22_236728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_236728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236728 prefixEnd_236728 := by exact prefixLift 236728
  have htrace : WordTrace (prefixWord ++ tailWord_236728) baseStart_236728 baseEnd_236728 := by
    simpa [prefixWord, tailWord_236728, baseEnd_236728] using wordTrace_append hprefix tailTrace_236728
  have hstable : (prefixWord ++ tailWord_236728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236728).length < 2 ^ (prefixWord ++ tailWord_236728).sum := by decide
  have hdescent : baseEnd_236728 < baseStart_236728 := by decide
  rcases family_descends (prefixWord ++ tailWord_236728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236732 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 3, 3]
def baseStart_236732 : Nat := 118140960795 + 236732 * 2 ^ 59
def prefixEnd_236732 : Nat := 4983230072969 + 3 ^ 40 * 236732 * 2
def baseEnd_236732 : Nat := 81038201533515345774197

theorem tailTrace_236732 : CollatzResearch.WordTrace tailWord_236732 prefixEnd_236732 81038201533515345774197 := by
  unfold tailWord_236732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317162689183934725932225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5756216918911912967909633 4317162689183934725932225)
  ·
    refine ⟨3237872016887951044449169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4317162689183934725932225 3237872016887951044449169)
    ·
      refine ⟨2428404012665963283336877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3237872016887951044449169 2428404012665963283336877)
      ·
        refine ⟨910651504749736231251329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2428404012665963283336877 910651504749736231251329)
        ·
          refine ⟨682988628562302173438497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 910651504749736231251329 682988628562302173438497)
          ·
            refine ⟨512241471421726630078873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682988628562302173438497 512241471421726630078873)
            ·
              refine ⟨384181103566294972559155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 512241471421726630078873 384181103566294972559155)
              ·
                refine ⟨576271655349442458838733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 384181103566294972559155 576271655349442458838733)
                ·
                  refine ⟨216101870756040922064525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 576271655349442458838733 216101870756040922064525)
                  ·
                    refine ⟨81038201533515345774197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216101870756040922064525 81038201533515345774197)
                    ·
                      rfl

theorem cell22_236732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_236732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236732 prefixEnd_236732 := by exact prefixLift 236732
  have htrace : WordTrace (prefixWord ++ tailWord_236732) baseStart_236732 baseEnd_236732 := by
    simpa [prefixWord, tailWord_236732, baseEnd_236732] using wordTrace_append hprefix tailTrace_236732
  have hstable : (prefixWord ++ tailWord_236732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236732).length < 2 ^ (prefixWord ++ tailWord_236732).sum := by decide
  have hdescent : baseEnd_236732 < baseStart_236732 := by decide
  rcases family_descends (prefixWord ++ tailWord_236732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236738 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_236738 : Nat := 118140960795 + 236738 * 2 ^ 59
def prefixEnd_236738 : Nat := 4983230072969 + 3 ^ 40 * 236738 * 2
def baseEnd_236738 : Nat := 81040255456133330124179

theorem tailTrace_236738 : CollatzResearch.WordTrace tailWord_236738 prefixEnd_236738 81040255456133330124179 := by
  unfold tailWord_236738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158636054086533119145717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5756362810897421651055245 2158636054086533119145717)
  ·
    refine ⟨202372130070612479919911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2158636054086533119145717 202372130070612479919911)
    ·
      refine ⟨303558195105918719879867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202372130070612479919911 303558195105918719879867)
      ·
        refine ⟨455337292658878079819801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303558195105918719879867 455337292658878079819801)
        ·
          refine ⟨341502969494158559864851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 455337292658878079819801 341502969494158559864851)
          ·
            refine ⟨512254454241237839797277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341502969494158559864851 512254454241237839797277)
            ·
              refine ⟨192095420340464189923979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512254454241237839797277 192095420340464189923979)
              ·
                refine ⟨288143130510696284885969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192095420340464189923979 288143130510696284885969)
                ·
                  refine ⟨216107347883022213664477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288143130510696284885969 216107347883022213664477)
                  ·
                    refine ⟨81040255456133330124179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216107347883022213664477 81040255456133330124179)
                    ·
                      rfl

theorem cell22_236738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_236738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236738 prefixEnd_236738 := by exact prefixLift 236738
  have htrace : WordTrace (prefixWord ++ tailWord_236738) baseStart_236738 baseEnd_236738 := by
    simpa [prefixWord, tailWord_236738, baseEnd_236738] using wordTrace_append hprefix tailTrace_236738
  have hstable : (prefixWord ++ tailWord_236738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236738).length < 2 ^ (prefixWord ++ tailWord_236738).sum := by decide
  have hdescent : baseEnd_236738 < baseStart_236738 := by decide
  rcases family_descends (prefixWord ++ tailWord_236738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236848 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_236848 : Nat := 118140960795 + 236848 * 2 ^ 59
def prefixEnd_236848 : Nat := 4983230072969 + 3 ^ 40 * 236848 * 2
def baseEnd_236848 : Nat := 81077910704129709873841

theorem tailTrace_236848 : CollatzResearch.WordTrace tailWord_236848 prefixEnd_236848 81077910704129709873841 := by
  unfold tailWord_236848
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319278122973810631543599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5759037497298414175391465 4319278122973810631543599)
  ·
    refine ⟨6478917184460715947315399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319278122973810631543599 6478917184460715947315399)
    ·
      refine ⟨9718375776691073920973099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6478917184460715947315399 9718375776691073920973099)
      ·
        refine ⟨14577563665036610881459649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9718375776691073920973099 14577563665036610881459649)
        ·
          refine ⟨10933172748777458161094737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14577563665036610881459649 10933172748777458161094737)
          ·
            refine ⟨8199879561583093620821053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10933172748777458161094737 8199879561583093620821053)
            ·
              refine ⟨3074954835593660107807895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8199879561583093620821053 3074954835593660107807895)
              ·
                refine ⟨4612432253390490161711843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3074954835593660107807895 4612432253390490161711843)
                ·
                  refine ⟨6918648380085735242567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612432253390490161711843 6918648380085735242567765)
                  ·
                    refine ⟨81077910704129709873841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6918648380085735242567765 81077910704129709873841)
                    ·
                      rfl

theorem cell22_236848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_236848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236848 prefixEnd_236848 := by exact prefixLift 236848
  have htrace : WordTrace (prefixWord ++ tailWord_236848) baseStart_236848 baseEnd_236848 := by
    simpa [prefixWord, tailWord_236848, baseEnd_236848] using wordTrace_append hprefix tailTrace_236848
  have hstable : (prefixWord ++ tailWord_236848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236848).length < 2 ^ (prefixWord ++ tailWord_236848).sum := by decide
  have hdescent : baseEnd_236848 < baseStart_236848 := by decide
  rcases family_descends (prefixWord ++ tailWord_236848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236886 : List Nat := [5, 2, 3, 1, 1, 1, 9]
def baseStart_236886 : Nat := 118140960795 + 236886 * 2 ^ 59
def prefixEnd_236886 : Nat := 4983230072969 + 3 ^ 40 * 236886 * 2
def baseEnd_236886 : Nat := 3003367365952232497175

theorem tailTrace_236886 : CollatzResearch.WordTrace tailWord_236886 prefixEnd_236886 3003367365952232497175 := by
  unfold tailWord_236886
  simp only [CollatzResearch.WordTrace]
  refine ⟨539996388738122109560657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5759961479873302501980341 539996388738122109560657)
  ·
    refine ⟨404997291553591582170493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 539996388738122109560657 404997291553591582170493)
    ·
      refine ⟨151873984332596843313935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 404997291553591582170493 151873984332596843313935)
      ·
        refine ⟨227810976498895264970903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151873984332596843313935 227810976498895264970903)
        ·
          refine ⟨341716464748342897456355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227810976498895264970903 341716464748342897456355)
          ·
            refine ⟨512574697122514346184533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341716464748342897456355 512574697122514346184533)
            ·
              refine ⟨3003367365952232497175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 512574697122514346184533 3003367365952232497175)
              ·
                rfl

theorem cell22_236886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 9].length) (baseStart_236886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236886 prefixEnd_236886 := by exact prefixLift 236886
  have htrace : WordTrace (prefixWord ++ tailWord_236886) baseStart_236886 baseEnd_236886 := by
    simpa [prefixWord, tailWord_236886, baseEnd_236886] using wordTrace_append hprefix tailTrace_236886
  have hstable : (prefixWord ++ tailWord_236886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236886).length < 2 ^ (prefixWord ++ tailWord_236886).sum := by decide
  have hdescent : baseEnd_236886 < baseStart_236886 := by decide
  rcases family_descends (prefixWord ++ tailWord_236886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236925 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 6]
def baseStart_236925 : Nat := 118140960795 + 236925 * 2 ^ 59
def prefixEnd_236925 : Nat := 4983230072969 + 3 ^ 40 * 236925 * 2
def baseEnd_236925 : Nat := 27034756459242391899535

theorem tailTrace_236925 : CollatzResearch.WordTrace tailWord_236925 prefixEnd_236925 27034756459242391899535 := by
  unfold tailWord_236925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641364666668663413640229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5760909777779108942426819 8641364666668663413640229)
  ·
    refine ⟨1620255875000374390057543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8641364666668663413640229 1620255875000374390057543)
    ·
      refine ⟨2430383812500561585086315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620255875000374390057543 2430383812500561585086315)
      ·
        refine ⟨3645575718750842377629473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430383812500561585086315 3645575718750842377629473)
        ·
          refine ⟨2734181789063131783222105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645575718750842377629473 2734181789063131783222105)
          ·
            refine ⟨2050636341797348837416579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2734181789063131783222105 2050636341797348837416579)
            ·
              refine ⟨3075954512696023256124869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050636341797348837416579 3075954512696023256124869)
              ·
                refine ⟨576741471130504360523413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3075954512696023256124869 576741471130504360523413)
                ·
                  refine ⟨27034756459242391899535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 576741471130504360523413 27034756459242391899535)
                  ·
                    rfl

theorem cell22_236925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_236925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236925 prefixEnd_236925 := by exact prefixLift 236925
  have htrace : WordTrace (prefixWord ++ tailWord_236925) baseStart_236925 baseEnd_236925 := by
    simpa [prefixWord, tailWord_236925, baseEnd_236925] using wordTrace_append hprefix tailTrace_236925
  have hstable : (prefixWord ++ tailWord_236925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236925).length < 2 ^ (prefixWord ++ tailWord_236925).sum := by decide
  have hdescent : baseEnd_236925 < baseStart_236925 := by decide
  rcases family_descends (prefixWord ++ tailWord_236925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_236940 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_236940 : Nat := 118140960795 + 236940 * 2 ^ 59
def prefixEnd_236940 : Nat := 4983230072969 + 3 ^ 40 * 236940 * 2
def baseEnd_236940 : Nat := 81109404184272136573559

theorem tailTrace_236940 : CollatzResearch.WordTrace tailWord_236940 prefixEnd_236940 81109404184272136573559 := by
  unfold tailWord_236940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320955880807160487718137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5761274507742880650290849 4320955880807160487718137)
  ·
    refine ⟨3240716910605370365788603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4320955880807160487718137 3240716910605370365788603)
    ·
      refine ⟨4861075365908055548682905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3240716910605370365788603 4861075365908055548682905)
      ·
        refine ⟨3645806524431041661512179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4861075365908055548682905 3645806524431041661512179)
        ·
          refine ⟨5468709786646562492268269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3645806524431041661512179 5468709786646562492268269)
          ·
            refine ⟨2050766169992460934600601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5468709786646562492268269 2050766169992460934600601)
            ·
              refine ⟨1538074627494345700950451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050766169992460934600601 1538074627494345700950451)
              ·
                refine ⟨2307111941241518551425677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538074627494345700950451 2307111941241518551425677)
                ·
                  refine ⟨865166977965569456784629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2307111941241518551425677 865166977965569456784629)
                  ·
                    refine ⟨81109404184272136573559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 865166977965569456784629 81109404184272136573559)
                    ·
                      rfl

theorem cell22_236940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_236940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_236940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_236940 prefixEnd_236940 := by exact prefixLift 236940
  have htrace : WordTrace (prefixWord ++ tailWord_236940) baseStart_236940 baseEnd_236940 := by
    simpa [prefixWord, tailWord_236940, baseEnd_236940] using wordTrace_append hprefix tailTrace_236940
  have hstable : (prefixWord ++ tailWord_236940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_236940).length < 2 ^ (prefixWord ++ tailWord_236940).sum := by decide
  have hdescent : baseEnd_236940 < baseStart_236940 := by decide
  rcases family_descends (prefixWord ++ tailWord_236940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237015 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 7]
def baseStart_237015 : Nat := 118140960795 + 237015 * 2 ^ 59
def prefixEnd_237015 : Nat := 4983230072969 + 3 ^ 40 * 237015 * 2
def baseEnd_237015 : Nat := 27045026072332313649443

theorem tailTrace_237015 : CollatzResearch.WordTrace tailWord_237015 prefixEnd_237015 27045026072332313649443 := by
  unfold tailWord_237015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8644647236342608784416499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5763098157561739189610999 8644647236342608784416499)
  ·
    refine ⟨12966970854513913176624749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8644647236342608784416499 12966970854513913176624749)
    ·
      refine ⟨4862614070442717441234281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12966970854513913176624749 4862614070442717441234281)
      ·
        refine ⟨3646960552832038080925711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4862614070442717441234281 3646960552832038080925711)
        ·
          refine ⟨5470440829248057121388567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3646960552832038080925711 5470440829248057121388567)
          ·
            refine ⟨8205661243872085682082851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470440829248057121388567 8205661243872085682082851)
            ·
              refine ⟨12308491865808128523124277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8205661243872085682082851 12308491865808128523124277)
              ·
                refine ⟨1153921112419512049042901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12308491865808128523124277 1153921112419512049042901)
                ·
                  refine ⟨27045026072332313649443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1153921112419512049042901 27045026072332313649443)
                  ·
                    rfl

theorem cell22_237015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 7].length) (baseStart_237015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237015 prefixEnd_237015 := by exact prefixLift 237015
  have htrace : WordTrace (prefixWord ++ tailWord_237015) baseStart_237015 baseEnd_237015 := by
    simpa [prefixWord, tailWord_237015, baseEnd_237015] using wordTrace_append hprefix tailTrace_237015
  have hstable : (prefixWord ++ tailWord_237015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237015).length < 2 ^ (prefixWord ++ tailWord_237015).sum := by decide
  have hdescent : baseEnd_237015 < baseStart_237015 := by decide
  rcases family_descends (prefixWord ++ tailWord_237015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237032 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 5]
def baseStart_237032 : Nat := 118140960795 + 237032 * 2 ^ 59
def prefixEnd_237032 : Nat := 4983230072969 + 3 ^ 40 * 237032 * 2
def baseEnd_237032 : Nat := 27046965888138187757759

theorem tailTrace_237032 : CollatzResearch.WordTrace tailWord_237032 prefixEnd_237032 27046965888138187757759 := by
  unfold tailWord_237032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322633638640510343892675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5763511518187347125190233 4322633638640510343892675)
  ·
    refine ⟨6483950457960765515839013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322633638640510343892675 6483950457960765515839013)
    ·
      refine ⟨1215740710867643534219815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6483950457960765515839013 1215740710867643534219815)
      ·
        refine ⟨1823611066301465301329723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215740710867643534219815 1823611066301465301329723)
        ·
          refine ⟨2735416599452197951994585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823611066301465301329723 2735416599452197951994585)
          ·
            refine ⟨2051562449589148463995939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735416599452197951994585 2051562449589148463995939)
            ·
              refine ⟨3077343674383722695993909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051562449589148463995939 3077343674383722695993909)
              ·
                refine ⟨288500969473474002749429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3077343674383722695993909 288500969473474002749429)
                ·
                  refine ⟨27046965888138187757759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288500969473474002749429 27046965888138187757759)
                  ·
                    rfl

theorem cell22_237032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_237032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237032 prefixEnd_237032 := by exact prefixLift 237032
  have htrace : WordTrace (prefixWord ++ tailWord_237032) baseStart_237032 baseEnd_237032 := by
    simpa [prefixWord, tailWord_237032, baseEnd_237032] using wordTrace_append hprefix tailTrace_237032
  have hstable : (prefixWord ++ tailWord_237032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237032).length < 2 ^ (prefixWord ++ tailWord_237032).sum := by decide
  have hdescent : baseEnd_237032 < baseStart_237032 := by decide
  rcases family_descends (prefixWord ++ tailWord_237032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237077 : List Nat := [1, 3, 2, 1, 3, 2, 1, 3, 6]
def baseStart_237077 : Nat := 118140960795 + 237077 * 2 ^ 59
def prefixEnd_237077 : Nat := 4983230072969 + 3 ^ 40 * 237077 * 2
def baseEnd_237077 : Nat := 27052100694683148632713

theorem tailTrace_237077 : CollatzResearch.WordTrace tailWord_237077 prefixEnd_237077 27052100694683148632713 := by
  unfold tailWord_237077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8646908562117993373173485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5764605708078662248782323 8646908562117993373173485)
  ·
    refine ⟨3242590710794247514940057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8646908562117993373173485 3242590710794247514940057)
    ·
      refine ⟨2431943033095685636205043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3242590710794247514940057 2431943033095685636205043)
      ·
        refine ⟨3647914549643528454307565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431943033095685636205043 3647914549643528454307565)
        ·
          refine ⟨1367967956116323170365337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3647914549643528454307565 1367967956116323170365337)
          ·
            refine ⟨1025975967087242377774003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1367967956116323170365337 1025975967087242377774003)
            ·
              refine ⟨1538963950630863566661005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1025975967087242377774003 1538963950630863566661005)
              ·
                refine ⟨577111481486573837497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1538963950630863566661005 577111481486573837497877)
                ·
                  refine ⟨27052100694683148632713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577111481486573837497877 27052100694683148632713)
                  ·
                    rfl

theorem cell22_237077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 6].length) (baseStart_237077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237077 prefixEnd_237077 := by exact prefixLift 237077
  have htrace : WordTrace (prefixWord ++ tailWord_237077) baseStart_237077 baseEnd_237077 := by
    simpa [prefixWord, tailWord_237077, baseEnd_237077] using wordTrace_append hprefix tailTrace_237077
  have hstable : (prefixWord ++ tailWord_237077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237077).length < 2 ^ (prefixWord ++ tailWord_237077).sum := by decide
  have hdescent : baseEnd_237077 < baseStart_237077 := by decide
  rcases family_descends (prefixWord ++ tailWord_237077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237107 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 6]
def baseStart_237107 : Nat := 118140960795 + 237107 * 2 ^ 59
def prefixEnd_237107 : Nat := 4983230072969 + 3 ^ 40 * 237107 * 2
def baseEnd_237107 : Nat := 81166571697139367648047

theorem tailTrace_237107 : CollatzResearch.WordTrace tailWord_237107 prefixEnd_237107 81166571697139367648047 := by
  unfold tailWord_237107
  simp only [CollatzResearch.WordTrace]
  refine ⟨8648002752009308496765575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5765335168006205664510383 8648002752009308496765575)
  ·
    refine ⟨12972004128013962745148363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8648002752009308496765575 12972004128013962745148363)
    ·
      refine ⟨19458006192020944117722545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12972004128013962745148363 19458006192020944117722545)
      ·
        refine ⟨14593504644015708088291909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19458006192020944117722545 14593504644015708088291909)
        ·
          refine ⟨2736282120752945266554733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14593504644015708088291909 2736282120752945266554733)
          ·
            refine ⟨1026105795282354474958025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2736282120752945266554733 1026105795282354474958025)
            ·
              refine ⟨769579346461765856218519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1026105795282354474958025 769579346461765856218519)
              ·
                refine ⟨1154369019692648784327779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 769579346461765856218519 1154369019692648784327779)
                ·
                  refine ⟨1731553529538973176491669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154369019692648784327779 1731553529538973176491669)
                  ·
                    refine ⟨81166571697139367648047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1731553529538973176491669 81166571697139367648047)
                    ·
                      rfl

theorem cell22_237107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_237107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237107 prefixEnd_237107 := by exact prefixLift 237107
  have htrace : WordTrace (prefixWord ++ tailWord_237107) baseStart_237107 baseEnd_237107 := by
    simpa [prefixWord, tailWord_237107, baseEnd_237107] using wordTrace_append hprefix tailTrace_237107
  have hstable : (prefixWord ++ tailWord_237107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237107).length < 2 ^ (prefixWord ++ tailWord_237107).sum := by decide
  have hdescent : baseEnd_237107 < baseStart_237107 := by decide
  rcases family_descends (prefixWord ++ tailWord_237107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237109 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_237109 : Nat := 118140960795 + 237109 * 2 ^ 59
def prefixEnd_237109 : Nat := 4983230072969 + 3 ^ 40 * 237109 * 2
def baseEnd_237109 : Nat := 81167256338012029098041

theorem tailTrace_237109 : CollatzResearch.WordTrace tailWord_237109 prefixEnd_237109 81167256338012029098041 := by
  unfold tailWord_237109
  simp only [CollatzResearch.WordTrace]
  refine ⟨8648075698002062838338381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5765383798668041892225587 8648075698002062838338381)
  ·
    refine ⟨3243028386750773564376893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8648075698002062838338381 3243028386750773564376893)
    ·
      refine ⟨1216135645031540086641335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3243028386750773564376893 1216135645031540086641335)
      ·
        refine ⟨1824203467547310129962003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216135645031540086641335 1824203467547310129962003)
        ·
          refine ⟨2736305201320965194943005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824203467547310129962003 2736305201320965194943005)
          ·
            refine ⟨1026114450495361948103627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2736305201320965194943005 1026114450495361948103627)
            ·
              refine ⟨1539171675743042922155441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1026114450495361948103627 1539171675743042922155441)
              ·
                refine ⟨1154378756807282191616581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539171675743042922155441 1154378756807282191616581)
                ·
                  refine ⟨216446016901365410928109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1154378756807282191616581 216446016901365410928109)
                  ·
                    refine ⟨81167256338012029098041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216446016901365410928109 81167256338012029098041)
                    ·
                      rfl

theorem cell22_237109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_237109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237109 prefixEnd_237109 := by exact prefixLift 237109
  have htrace : WordTrace (prefixWord ++ tailWord_237109) baseStart_237109 baseEnd_237109 := by
    simpa [prefixWord, tailWord_237109, baseEnd_237109] using wordTrace_append hprefix tailTrace_237109
  have hstable : (prefixWord ++ tailWord_237109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237109).length < 2 ^ (prefixWord ++ tailWord_237109).sum := by decide
  have hdescent : baseEnd_237109 < baseStart_237109 := by decide
  rcases family_descends (prefixWord ++ tailWord_237109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237111 : List Nat := [1, 1, 3, 1, 2, 6, 1, 3, 4]
def baseStart_237111 : Nat := 118140960795 + 237111 * 2 ^ 59
def prefixEnd_237111 : Nat := 4983230072969 + 3 ^ 40 * 237111 * 2
def baseEnd_237111 : Nat := 27055980326294896849345

theorem tailTrace_237111 : CollatzResearch.WordTrace tailWord_237111 prefixEnd_237111 27055980326294896849345 := by
  unfold tailWord_237111
  simp only [CollatzResearch.WordTrace]
  refine ⟨8648148643994817179911187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5765432429329878119940791 8648148643994817179911187)
  ·
    refine ⟨12972222965992225769866781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8648148643994817179911187 12972222965992225769866781)
    ·
      refine ⟨4864583612247084663700043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12972222965992225769866781 4864583612247084663700043)
      ·
        refine ⟨7296875418370626995550065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864583612247084663700043 7296875418370626995550065)
        ·
          refine ⟨5472656563777970246662549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7296875418370626995550065 5472656563777970246662549)
          ·
            refine ⟨256530776427092355312307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5472656563777970246662549 256530776427092355312307)
            ·
              refine ⟨384796164640638532968461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256530776427092355312307 384796164640638532968461)
              ·
                refine ⟨144298561740239449863173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384796164640638532968461 144298561740239449863173)
                ·
                  refine ⟨27055980326294896849345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144298561740239449863173 27055980326294896849345)
                  ·
                    rfl

theorem cell22_237111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 4].length) (baseStart_237111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237111 prefixEnd_237111 := by exact prefixLift 237111
  have htrace : WordTrace (prefixWord ++ tailWord_237111) baseStart_237111 baseEnd_237111 := by
    simpa [prefixWord, tailWord_237111, baseEnd_237111] using wordTrace_append hprefix tailTrace_237111
  have hstable : (prefixWord ++ tailWord_237111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237111).length < 2 ^ (prefixWord ++ tailWord_237111).sum := by decide
  have hdescent : baseEnd_237111 < baseStart_237111 := by decide
  rcases family_descends (prefixWord ++ tailWord_237111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237143 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 2, 3]
def baseStart_237143 : Nat := 118140960795 + 237143 * 2 ^ 59
def prefixEnd_237143 : Nat := 4983230072969 + 3 ^ 40 * 237143 * 2
def baseEnd_237143 : Nat := 81178895232847273747937

theorem tailTrace_237143 : CollatzResearch.WordTrace tailWord_237143 prefixEnd_237143 81178895232847273747937 := by
  unfold tailWord_237143
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649315779878886645076083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5766210519919257763384055 8649315779878886645076083)
  ·
    refine ⟨12973973669818329967614125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8649315779878886645076083 12973973669818329967614125)
    ·
      refine ⟨4865240126181873737855297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12973973669818329967614125 4865240126181873737855297)
      ·
        refine ⟨3648930094636405303391473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4865240126181873737855297 3648930094636405303391473)
        ·
          refine ⟨2736697570977303977543605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3648930094636405303391473 2736697570977303977543605)
          ·
            refine ⟨256565397279122247894713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2736697570977303977543605 256565397279122247894713)
            ·
              refine ⟨192424047959341685921035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256565397279122247894713 192424047959341685921035)
              ·
                refine ⟨288636071939012528881553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192424047959341685921035 288636071939012528881553)
                ·
                  refine ⟨216477053954259396661165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 288636071939012528881553 216477053954259396661165)
                  ·
                    refine ⟨81178895232847273747937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 216477053954259396661165 81178895232847273747937)
                    ·
                      rfl

theorem cell22_237143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 3].length) (baseStart_237143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237143 prefixEnd_237143 := by exact prefixLift 237143
  have htrace : WordTrace (prefixWord ++ tailWord_237143) baseStart_237143 baseEnd_237143 := by
    simpa [prefixWord, tailWord_237143, baseEnd_237143] using wordTrace_append hprefix tailTrace_237143
  have hstable : (prefixWord ++ tailWord_237143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237143).length < 2 ^ (prefixWord ++ tailWord_237143).sum := by decide
  have hdescent : baseEnd_237143 < baseStart_237143 := by decide
  rcases family_descends (prefixWord ++ tailWord_237143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237184 : List Nat := [2, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_237184 : Nat := 118140960795 + 237184 * 2 ^ 59
def prefixEnd_237184 : Nat := 4983230072969 + 3 ^ 40 * 237184 * 2
def baseEnd_237184 : Nat := 27064310123578944490937

theorem tailTrace_237184 : CollatzResearch.WordTrace tailWord_237184 prefixEnd_237184 27064310123578944490937 := by
  unfold tailWord_237184
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325405586365175323659303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5767207448486900431545737 4325405586365175323659303)
  ·
    refine ⟨6488108379547762985488955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325405586365175323659303 6488108379547762985488955)
    ·
      refine ⟨9732162569321644478233433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488108379547762985488955 9732162569321644478233433)
      ·
        refine ⟨7299121926991233358675075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9732162569321644478233433 7299121926991233358675075)
        ·
          refine ⟨10948682890486850038012613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7299121926991233358675075 10948682890486850038012613)
          ·
            refine ⟨2052878041966284382127365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10948682890486850038012613 2052878041966284382127365)
            ·
              refine ⟨384914632868678321648881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2052878041966284382127365 384914632868678321648881)
              ·
                refine ⟨288685974651508741236661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 384914632868678321648881 288685974651508741236661)
                ·
                  refine ⟨27064310123578944490937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288685974651508741236661 27064310123578944490937)
                  ·
                    rfl

theorem cell22_237184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_237184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237184 prefixEnd_237184 := by exact prefixLift 237184
  have htrace : WordTrace (prefixWord ++ tailWord_237184) baseStart_237184 baseEnd_237184 := by
    simpa [prefixWord, tailWord_237184, baseEnd_237184] using wordTrace_append hprefix tailTrace_237184
  have hstable : (prefixWord ++ tailWord_237184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237184).length < 2 ^ (prefixWord ++ tailWord_237184).sum := by decide
  have hdescent : baseEnd_237184 < baseStart_237184 := by decide
  rcases family_descends (prefixWord ++ tailWord_237184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237229 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 8]
def baseStart_237229 : Nat := 118140960795 + 237229 * 2 ^ 59
def prefixEnd_237229 : Nat := 4983230072969 + 3 ^ 40 * 237229 * 2
def baseEnd_237229 : Nat := 27069444930123905365891

theorem tailTrace_237229 : CollatzResearch.WordTrace tailWord_237229 prefixEnd_237229 27069444930123905365891 := by
  unfold tailWord_237229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8652452457567323332706741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5768301638378215555137827 8652452457567323332706741)
  ·
    refine ⟨811167417896936562441257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8652452457567323332706741 811167417896936562441257)
    ·
      refine ⟨608375563422702421830943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 811167417896936562441257 608375563422702421830943)
      ·
        refine ⟨912563345134053632746415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 608375563422702421830943 912563345134053632746415)
        ·
          refine ⟨1368845017701080449119623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912563345134053632746415 1368845017701080449119623)
          ·
            refine ⟨2053267526551620673679435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368845017701080449119623 2053267526551620673679435)
            ·
              refine ⟨3079901289827431010519153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2053267526551620673679435 3079901289827431010519153)
              ·
                refine ⟨2309925967370573257889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079901289827431010519153 2309925967370573257889365)
                ·
                  refine ⟨27069444930123905365891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2309925967370573257889365 27069444930123905365891)
                  ·
                    rfl

theorem cell22_237229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_237229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237229 prefixEnd_237229 := by exact prefixLift 237229
  have htrace : WordTrace (prefixWord ++ tailWord_237229) baseStart_237229 baseEnd_237229 := by
    simpa [prefixWord, tailWord_237229, baseEnd_237229] using wordTrace_append hprefix tailTrace_237229
  have hstable : (prefixWord ++ tailWord_237229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237229).length < 2 ^ (prefixWord ++ tailWord_237229).sum := by decide
  have hdescent : baseEnd_237229 < baseStart_237229 := by decide
  rcases family_descends (prefixWord ++ tailWord_237229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237246 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_237246 : Nat := 118140960795 + 237246 * 2 ^ 59
def prefixEnd_237246 : Nat := 4983230072969 + 3 ^ 40 * 237246 * 2
def baseEnd_237246 : Nat := 27071384745929779474207

theorem tailTrace_237246 : CollatzResearch.WordTrace tailWord_237246 prefixEnd_237246 27071384745929779474207 := by
  unfold tailWord_237246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1081634062313216904509449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5768714999003823490717061 1081634062313216904509449)
  ·
    refine ⟨811225546734912678382087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1081634062313216904509449 811225546734912678382087)
    ·
      refine ⟨1216838320102369017573131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 811225546734912678382087 1216838320102369017573131)
      ·
        refine ⟨1825257480153553526359697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1216838320102369017573131 1825257480153553526359697)
        ·
          refine ⟨1368943110115165144769773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1825257480153553526359697 1368943110115165144769773)
          ·
            refine ⟨513353666293186929288665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368943110115165144769773 513353666293186929288665)
            ·
              refine ⟨385015249719890196966499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513353666293186929288665 385015249719890196966499)
              ·
                refine ⟨577522874579835295449749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385015249719890196966499 577522874579835295449749)
                ·
                  refine ⟨27071384745929779474207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577522874579835295449749 27071384745929779474207)
                  ·
                    rfl

theorem cell22_237246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_237246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237246 prefixEnd_237246 := by exact prefixLift 237246
  have htrace : WordTrace (prefixWord ++ tailWord_237246) baseStart_237246 baseEnd_237246 := by
    simpa [prefixWord, tailWord_237246, baseEnd_237246] using wordTrace_append hprefix tailTrace_237246
  have hstable : (prefixWord ++ tailWord_237246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237246).length < 2 ^ (prefixWord ++ tailWord_237246).sum := by decide
  have hdescent : baseEnd_237246 < baseStart_237246 := by decide
  rcases family_descends (prefixWord ++ tailWord_237246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237274 : List Nat := [3, 1, 1, 2, 2, 4, 1, 8]
def baseStart_237274 : Nat := 118140960795 + 237274 * 2 ^ 59
def prefixEnd_237274 : Nat := 4983230072969 + 3 ^ 40 * 237274 * 2
def baseEnd_237274 : Nat := 9024859912222955413615

theorem tailTrace_237274 : CollatzResearch.WordTrace tailWord_237274 prefixEnd_237274 9024859912222955413615 := by
  unfold tailWord_237274
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163523435601074004523719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5769395828269530678729917 2163523435601074004523719)
  ·
    refine ⟨3245285153401611006785579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2163523435601074004523719 3245285153401611006785579)
    ·
      refine ⟨4867927730102416510178369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3245285153401611006785579 4867927730102416510178369)
      ·
        refine ⟨3650945797576812382633777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4867927730102416510178369 3650945797576812382633777)
        ·
          refine ⟨2738209348182609286975333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3650945797576812382633777 2738209348182609286975333)
          ·
            refine ⟨513414252784239241307875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2738209348182609286975333 513414252784239241307875)
            ·
              refine ⟨770121379176358861961813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 513414252784239241307875 770121379176358861961813)
              ·
                refine ⟨9024859912222955413615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 770121379176358861961813 9024859912222955413615)
                ·
                  rfl

theorem cell22_237274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_237274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237274 prefixEnd_237274 := by exact prefixLift 237274
  have htrace : WordTrace (prefixWord ++ tailWord_237274) baseStart_237274 baseEnd_237274 := by
    simpa [prefixWord, tailWord_237274, baseEnd_237274] using wordTrace_append hprefix tailTrace_237274
  have hstable : (prefixWord ++ tailWord_237274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237274).length < 2 ^ (prefixWord ++ tailWord_237274).sum := by decide
  have hdescent : baseEnd_237274 < baseStart_237274 := by decide
  rcases family_descends (prefixWord ++ tailWord_237274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237409 : List Nat := [1, 2, 3, 1, 1, 1, 13]
def baseStart_237409 : Nat := 118140960795 + 237409 * 2 ^ 59
def prefixEnd_237409 : Nat := 4983230072969 + 3 ^ 40 * 237409 * 2
def baseEnd_237409 : Nat := 3009998239589305429523

theorem tailTrace_237409 : CollatzResearch.WordTrace tailWord_237409 prefixEnd_237409 3009998239589305429523 := by
  unfold tailWord_237409
  simp only [CollatzResearch.WordTrace]
  refine ⟨8659017596915214074259281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5772678397943476049506187 8659017596915214074259281)
  ·
    refine ⟨6494263197686410555694461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8659017596915214074259281 6494263197686410555694461)
    ·
      refine ⟨2435348699132403958385423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6494263197686410555694461 2435348699132403958385423)
      ·
        refine ⟨3653023048698605937578135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2435348699132403958385423 3653023048698605937578135)
        ·
          refine ⟨5479534573047908906367203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3653023048698605937578135 5479534573047908906367203)
          ·
            refine ⟨8219301859571863359550805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5479534573047908906367203 8219301859571863359550805)
            ·
              refine ⟨3009998239589305429523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 8219301859571863359550805 3009998239589305429523)
              ·
                rfl

theorem cell22_237409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 13].length) (baseStart_237409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237409 prefixEnd_237409 := by exact prefixLift 237409
  have htrace : WordTrace (prefixWord ++ tailWord_237409) baseStart_237409 baseEnd_237409 := by
    simpa [prefixWord, tailWord_237409, baseEnd_237409] using wordTrace_append hprefix tailTrace_237409
  have hstable : (prefixWord ++ tailWord_237409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237409).length < 2 ^ (prefixWord ++ tailWord_237409).sum := by decide
  have hdescent : baseEnd_237409 < baseStart_237409 := by decide
  rcases family_descends (prefixWord ++ tailWord_237409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237443 : List Nat := [1, 1, 1, 3, 4, 4, 2, 6]
def baseStart_237443 : Nat := 118140960795 + 237443 * 2 ^ 59
def prefixEnd_237443 : Nat := 4983230072969 + 3 ^ 40 * 237443 * 2
def baseEnd_237443 : Nat := 9031287929305165694113

theorem tailTrace_237443 : CollatzResearch.WordTrace tailWord_237443 prefixEnd_237443 9031287929305165694113 := by
  unfold tailWord_237443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8660257678792037880996983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5773505119194691920664655 8660257678792037880996983)
  ·
    refine ⟨12990386518188056821495475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8660257678792037880996983 12990386518188056821495475)
    ·
      refine ⟨19485579777282085232243213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12990386518188056821495475 19485579777282085232243213)
      ·
        refine ⟨7307092416480781962091205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19485579777282085232243213 7307092416480781962091205)
        ·
          refine ⟨1370079828090146617892101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7307092416480781962091205 1370079828090146617892101)
          ·
            refine ⟨256889967766902490854769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1370079828090146617892101 256889967766902490854769)
            ·
              refine ⟨192667475825176868141077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256889967766902490854769 192667475825176868141077)
              ·
                refine ⟨9031287929305165694113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192667475825176868141077 9031287929305165694113)
                ·
                  rfl

theorem cell22_237443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 6].length) (baseStart_237443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237443 prefixEnd_237443 := by exact prefixLift 237443
  have htrace : WordTrace (prefixWord ++ tailWord_237443) baseStart_237443 baseEnd_237443 := by
    simpa [prefixWord, tailWord_237443, baseEnd_237443] using wordTrace_append hprefix tailTrace_237443
  have hstable : (prefixWord ++ tailWord_237443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237443).length < 2 ^ (prefixWord ++ tailWord_237443).sum := by decide
  have hdescent : baseEnd_237443 < baseStart_237443 := by decide
  rcases family_descends (prefixWord ++ tailWord_237443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237563 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 2, 4]
def baseStart_237563 : Nat := 118140960795 + 237563 * 2 ^ 59
def prefixEnd_237563 : Nat := 4983230072969 + 3 ^ 40 * 237563 * 2
def baseEnd_237563 : Nat := 81322669816106178246649

theorem tailTrace_237563 : CollatzResearch.WordTrace tailWord_237563 prefixEnd_237563 81322669816106178246649 := by
  unfold tailWord_237563
  simp only [CollatzResearch.WordTrace]
  refine ⟨8664634438357298375365343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5776422958904865583576895 8664634438357298375365343)
  ·
    refine ⟨12996951657535947563048015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8664634438357298375365343 12996951657535947563048015)
    ·
      refine ⟨19495427486303921344572023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12996951657535947563048015 19495427486303921344572023)
      ·
        refine ⟨29243141229455882016858035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19495427486303921344572023 29243141229455882016858035)
        ·
          refine ⟨43864711844183823025287053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29243141229455882016858035 43864711844183823025287053)
          ·
            refine ⟨16449266941568933634482645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43864711844183823025287053 16449266941568933634482645)
            ·
              refine ⟨385529693943021882058187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 16449266941568933634482645 385529693943021882058187)
              ·
                refine ⟨578294540914532823087281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385529693943021882058187 578294540914532823087281)
                ·
                  refine ⟨433720905685899617315461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578294540914532823087281 433720905685899617315461)
                  ·
                    refine ⟨81322669816106178246649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433720905685899617315461 81322669816106178246649)
                    ·
                      rfl

theorem cell22_237563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 4].length) (baseStart_237563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237563 prefixEnd_237563 := by exact prefixLift 237563
  have htrace : WordTrace (prefixWord ++ tailWord_237563) baseStart_237563 baseEnd_237563 := by
    simpa [prefixWord, tailWord_237563, baseEnd_237563] using wordTrace_append hprefix tailTrace_237563
  have hstable : (prefixWord ++ tailWord_237563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237563).length < 2 ^ (prefixWord ++ tailWord_237563).sum := by decide
  have hdescent : baseEnd_237563 < baseStart_237563 := by decide
  rcases family_descends (prefixWord ++ tailWord_237563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237578 : List Nat := [3, 1, 2, 2, 4, 1, 9]
def baseStart_237578 : Nat := 118140960795 + 237578 * 2 ^ 59
def prefixEnd_237578 : Nat := 4983230072969 + 3 ^ 40 * 237578 * 2
def baseEnd_237578 : Nat := 3012140911950042189689

theorem tailTrace_237578 : CollatzResearch.WordTrace tailWord_237578 prefixEnd_237578 3012140911950042189689 := by
  unfold tailWord_237578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166295383325738984290347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5776787688868637291440925 2166295383325738984290347)
  ·
    refine ⟨3249443074988608476435521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2166295383325738984290347 3249443074988608476435521)
    ·
      refine ⟨2437082306241456357326641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3249443074988608476435521 2437082306241456357326641)
      ·
        refine ⟨1827811729681092267994981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2437082306241456357326641 1827811729681092267994981)
        ·
          refine ⟨342714699315204800249059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1827811729681092267994981 342714699315204800249059)
          ·
            refine ⟨514072048972807200373589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342714699315204800249059 514072048972807200373589)
            ·
              refine ⟨3012140911950042189689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 514072048972807200373589 3012140911950042189689)
              ·
                rfl

theorem cell22_237578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 9].length) (baseStart_237578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237578 prefixEnd_237578 := by exact prefixLift 237578
  have htrace : WordTrace (prefixWord ++ tailWord_237578) baseStart_237578 baseEnd_237578 := by
    simpa [prefixWord, tailWord_237578, baseEnd_237578] using wordTrace_append hprefix tailTrace_237578
  have hstable : (prefixWord ++ tailWord_237578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237578).length < 2 ^ (prefixWord ++ tailWord_237578).sum := by decide
  have hdescent : baseEnd_237578 < baseStart_237578 := by decide
  rcases family_descends (prefixWord ++ tailWord_237578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237668 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 6]
def baseStart_237668 : Nat := 118140960795 + 237668 * 2 ^ 59
def prefixEnd_237668 : Nat := 4983230072969 + 3 ^ 40 * 237668 * 2
def baseEnd_237668 : Nat := 27119537820640301457109

theorem tailTrace_237668 : CollatzResearch.WordTrace tailWord_237668 prefixEnd_237668 27119537820640301457109 := by
  unfold tailWord_237668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4334232051488450653968829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5778976068651267538625105 4334232051488450653968829)
  ·
    refine ⟨1625337019308168995238311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4334232051488450653968829 1625337019308168995238311)
    ·
      refine ⟨2438005528962253492857467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1625337019308168995238311 2438005528962253492857467)
      ·
        refine ⟨3657008293443380239286201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438005528962253492857467 3657008293443380239286201)
        ·
          refine ⟨2742756220082535179464651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3657008293443380239286201 2742756220082535179464651)
          ·
            refine ⟨4114134330123802769196977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2742756220082535179464651 4114134330123802769196977)
            ·
              refine ⟨3085600747592852076897733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4114134330123802769196977 3085600747592852076897733)
              ·
                refine ⟨578550140173659764418325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3085600747592852076897733 578550140173659764418325)
                ·
                  refine ⟨27119537820640301457109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 578550140173659764418325 27119537820640301457109)
                  ·
                    rfl

theorem cell22_237668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_237668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237668 prefixEnd_237668 := by exact prefixLift 237668
  have htrace : WordTrace (prefixWord ++ tailWord_237668) baseStart_237668 baseEnd_237668 := by
    simpa [prefixWord, tailWord_237668, baseEnd_237668] using wordTrace_append hprefix tailTrace_237668
  have hstable : (prefixWord ++ tailWord_237668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237668).length < 2 ^ (prefixWord ++ tailWord_237668).sum := by decide
  have hdescent : baseEnd_237668 < baseStart_237668 := by decide
  rcases family_descends (prefixWord ++ tailWord_237668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237687 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 1, 4]
def baseStart_237687 : Nat := 118140960795 + 237687 * 2 ^ 59
def prefixEnd_237687 : Nat := 4983230072969 + 3 ^ 40 * 237687 * 2
def baseEnd_237687 : Nat := 81365117550211188146269

theorem tailTrace_237687 : CollatzResearch.WordTrace tailWord_237687 prefixEnd_237687 81365117550211188146269 := by
  unfold tailWord_237687
  simp only [CollatzResearch.WordTrace]
  refine ⟨8669157089908067552879315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5779438059938711701919543 8669157089908067552879315)
  ·
    refine ⟨13003735634862101329318973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8669157089908067552879315 13003735634862101329318973)
    ·
      refine ⟨4876400863073287998494615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13003735634862101329318973 4876400863073287998494615)
      ·
        refine ⟨7314601294609931997741923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4876400863073287998494615 7314601294609931997741923)
        ·
          refine ⟨10971901941914897996612885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7314601294609931997741923 10971901941914897996612885)
          ·
            refine ⟨514307903527260843591229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10971901941914897996612885 514307903527260843591229)
            ·
              refine ⟨192865463822722816346711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514307903527260843591229 192865463822722816346711)
              ·
                refine ⟨289298195734084224520067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192865463822722816346711 289298195734084224520067)
                ·
                  refine ⟨433947293601126336780101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289298195734084224520067 433947293601126336780101)
                  ·
                    refine ⟨81365117550211188146269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 433947293601126336780101 81365117550211188146269)
                    ·
                      rfl

theorem cell22_237687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_237687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237687 prefixEnd_237687 := by exact prefixLift 237687
  have htrace : WordTrace (prefixWord ++ tailWord_237687) baseStart_237687 baseEnd_237687 := by
    simpa [prefixWord, tailWord_237687, baseEnd_237687] using wordTrace_append hprefix tailTrace_237687
  have hstable : (prefixWord ++ tailWord_237687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237687).length < 2 ^ (prefixWord ++ tailWord_237687).sum := by decide
  have hdescent : baseEnd_237687 < baseStart_237687 := by decide
  rcases family_descends (prefixWord ++ tailWord_237687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237738 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 1, 4]
def baseStart_237738 : Nat := 118140960795 + 237738 * 2 ^ 59
def prefixEnd_237738 : Nat := 4983230072969 + 3 ^ 40 * 237738 * 2
def baseEnd_237738 : Nat := 81382575892464055121113

theorem tailTrace_237738 : CollatzResearch.WordTrace tailWord_237738 prefixEnd_237738 81382575892464055121113 := by
  unfold tailWord_237738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167754303180825815746467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5780678141815535508657245 2167754303180825815746467)
  ·
    refine ⟨3251631454771238723619701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2167754303180825815746467 3251631454771238723619701)
    ·
      refine ⟨304840448884803630339347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3251631454771238723619701 304840448884803630339347)
      ·
        refine ⟨457260673327205445509021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304840448884803630339347 457260673327205445509021)
        ·
          refine ⟨171472752497702042065883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457260673327205445509021 171472752497702042065883)
          ·
            refine ⟨257209128746553063098825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171472752497702042065883 257209128746553063098825)
            ·
              refine ⟨192906846559914797324119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257209128746553063098825 192906846559914797324119)
              ·
                refine ⟨289360269839872195986179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192906846559914797324119 289360269839872195986179)
                ·
                  refine ⟨434040404759808293979269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289360269839872195986179 434040404759808293979269)
                  ·
                    refine ⟨81382575892464055121113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434040404759808293979269 81382575892464055121113)
                    ·
                      rfl

theorem cell22_237738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_237738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237738 prefixEnd_237738 := by exact prefixLift 237738
  have htrace : WordTrace (prefixWord ++ tailWord_237738) baseStart_237738 baseEnd_237738 := by
    simpa [prefixWord, tailWord_237738, baseEnd_237738] using wordTrace_append hprefix tailTrace_237738
  have hstable : (prefixWord ++ tailWord_237738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237738).length < 2 ^ (prefixWord ++ tailWord_237738).sum := by decide
  have hdescent : baseEnd_237738 < baseStart_237738 := by decide
  rcases family_descends (prefixWord ++ tailWord_237738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237822 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_237822 : Nat := 118140960795 + 237822 * 2 ^ 59
def prefixEnd_237822 : Nat := 4983230072969 + 3 ^ 40 * 237822 * 2
def baseEnd_237822 : Nat := 81411330809115836020855

theorem tailTrace_237822 : CollatzResearch.WordTrace tailWord_237822 prefixEnd_237822 81411330809115836020855 := by
  unfold tailWord_237822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084260118052373201130465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5782720629612657072695813 1084260118052373201130465)
  ·
    refine ⟨813195088539279900847849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1084260118052373201130465 813195088539279900847849)
    ·
      refine ⟨609896316404459925635887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813195088539279900847849 609896316404459925635887)
      ·
        refine ⟨914844474606689888453831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609896316404459925635887 914844474606689888453831)
        ·
          refine ⟨1372266711910034832680747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914844474606689888453831 1372266711910034832680747)
          ·
            refine ⟨2058400067865052249021121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1372266711910034832680747 2058400067865052249021121)
            ·
              refine ⟨1543800050898789186765841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058400067865052249021121 1543800050898789186765841)
              ·
                refine ⟨1157850038174091890074381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1543800050898789186765841 1157850038174091890074381)
                ·
                  refine ⟨434193764315284458777893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1157850038174091890074381 434193764315284458777893)
                  ·
                    refine ⟨81411330809115836020855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434193764315284458777893 81411330809115836020855)
                    ·
                      rfl

theorem cell22_237822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_237822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237822 prefixEnd_237822 := by exact prefixLift 237822
  have htrace : WordTrace (prefixWord ++ tailWord_237822) baseStart_237822 baseEnd_237822 := by
    simpa [prefixWord, tailWord_237822, baseEnd_237822] using wordTrace_append hprefix tailTrace_237822
  have hstable : (prefixWord ++ tailWord_237822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237822).length < 2 ^ (prefixWord ++ tailWord_237822).sum := by decide
  have hdescent : baseEnd_237822 < baseStart_237822 := by decide
  rcases family_descends (prefixWord ++ tailWord_237822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237826 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_237826 : Nat := 118140960795 + 237826 * 2 ^ 59
def prefixEnd_237826 : Nat := 4983230072969 + 3 ^ 40 * 237826 * 2
def baseEnd_237826 : Nat := 27137566696953719640281

theorem tailTrace_237826 : CollatzResearch.WordTrace tailWord_237826 prefixEnd_237826 27137566696953719640281 := by
  unfold tailWord_237826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168556709101123573047333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5782817890936329528126221 2168556709101123573047333)
  ·
    refine ⟨406604382956460669946375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2168556709101123573047333 406604382956460669946375)
    ·
      refine ⟨609906574434691004919563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406604382956460669946375 609906574434691004919563)
      ·
        refine ⟨914859861652036507379345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609906574434691004919563 914859861652036507379345)
        ·
          refine ⟨686144896239027380534509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914859861652036507379345 686144896239027380534509)
          ·
            refine ⟨257304336089635267700441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 686144896239027380534509 257304336089635267700441)
            ·
              refine ⟨192978252067226450775331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257304336089635267700441 192978252067226450775331)
              ·
                refine ⟨289467378100839676162997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192978252067226450775331 289467378100839676162997)
                ·
                  refine ⟨27137566696953719640281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289467378100839676162997 27137566696953719640281)
                  ·
                    rfl

theorem cell22_237826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_237826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237826 prefixEnd_237826 := by exact prefixLift 237826
  have htrace : WordTrace (prefixWord ++ tailWord_237826) baseStart_237826 baseEnd_237826 := by
    simpa [prefixWord, tailWord_237826, baseEnd_237826] using wordTrace_append hprefix tailTrace_237826
  have hstable : (prefixWord ++ tailWord_237826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237826).length < 2 ^ (prefixWord ++ tailWord_237826).sum := by decide
  have hdescent : baseEnd_237826 < baseStart_237826 := by decide
  rcases family_descends (prefixWord ++ tailWord_237826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237835 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_237835 : Nat := 118140960795 + 237835 * 2 ^ 59
def prefixEnd_237835 : Nat := 4983230072969 + 3 ^ 40 * 237835 * 2
def baseEnd_237835 : Nat := 81415780974788135445815

theorem tailTrace_237835 : CollatzResearch.WordTrace tailWord_237835 prefixEnd_237835 81415780974788135445815 := by
  unfold tailWord_237835
  simp only [CollatzResearch.WordTrace]
  refine ⟨8674555093371888829266959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5783036728914592552844639 8674555093371888829266959)
  ·
    refine ⟨13011832640057833243900439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8674555093371888829266959 13011832640057833243900439)
    ·
      refine ⟨19517748960086749865850659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13011832640057833243900439 19517748960086749865850659)
      ·
        refine ⟨29276623440130124798775989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19517748960086749865850659 29276623440130124798775989)
        ·
          refine ⟨2744683447512199199885249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29276623440130124798775989 2744683447512199199885249)
          ·
            refine ⟨2058512585634149399913937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2744683447512199199885249 2058512585634149399913937)
            ·
              refine ⟨1543884439225612049935453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2058512585634149399913937 1543884439225612049935453)
              ·
                refine ⟨578956664709604518725795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1543884439225612049935453 578956664709604518725795)
                ·
                  refine ⟨868434997064406778088693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578956664709604518725795 868434997064406778088693)
                  ·
                    refine ⟨81415780974788135445815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 868434997064406778088693 81415780974788135445815)
                    ·
                      rfl

theorem cell22_237835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_237835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237835 prefixEnd_237835 := by exact prefixLift 237835
  have htrace : WordTrace (prefixWord ++ tailWord_237835) baseStart_237835 baseEnd_237835 := by
    simpa [prefixWord, tailWord_237835, baseEnd_237835] using wordTrace_append hprefix tailTrace_237835
  have hstable : (prefixWord ++ tailWord_237835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237835).length < 2 ^ (prefixWord ++ tailWord_237835).sum := by decide
  have hdescent : baseEnd_237835 < baseStart_237835 := by decide
  rcases family_descends (prefixWord ++ tailWord_237835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237882 : List Nat := [3, 1, 1, 1, 4, 4, 1, 7]
def baseStart_237882 : Nat := 118140960795 + 237882 * 2 ^ 59
def prefixEnd_237882 : Nat := 4983230072969 + 3 ^ 40 * 237882 * 2
def baseEnd_237882 : Nat := 9047985559477297724519

theorem tailTrace_237882 : CollatzResearch.WordTrace tailWord_237882 prefixEnd_237882 9047985559477297724519 := by
  unfold tailWord_237882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169067331050403964056975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5784179549467743904151933 2169067331050403964056975)
  ·
    refine ⟨3253600996575605946085463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2169067331050403964056975 3253600996575605946085463)
    ·
      refine ⟨4880401494863408919128195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3253600996575605946085463 4880401494863408919128195)
      ·
        refine ⟨7320602242295113378692293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4880401494863408919128195 7320602242295113378692293)
        ·
          refine ⟨1372612920430333758504805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7320602242295113378692293 1372612920430333758504805)
          ·
            refine ⟨257364922580687579719651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1372612920430333758504805 257364922580687579719651)
            ·
              refine ⟨386047383871031369579477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257364922580687579719651 386047383871031369579477)
              ·
                refine ⟨9047985559477297724519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386047383871031369579477 9047985559477297724519)
                ·
                  rfl

theorem cell22_237882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_237882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237882 prefixEnd_237882 := by exact prefixLift 237882
  have htrace : WordTrace (prefixWord ++ tailWord_237882) baseStart_237882 baseEnd_237882 := by
    simpa [prefixWord, tailWord_237882, baseEnd_237882] using wordTrace_append hprefix tailTrace_237882
  have hstable : (prefixWord ++ tailWord_237882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237882).length < 2 ^ (prefixWord ++ tailWord_237882).sum := by decide
  have hdescent : baseEnd_237882 < baseStart_237882 := by decide
  rcases family_descends (prefixWord ++ tailWord_237882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237895 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_237895 : Nat := 118140960795 + 237895 * 2 ^ 59
def prefixEnd_237895 : Nat := 4983230072969 + 3 ^ 40 * 237895 * 2
def baseEnd_237895 : Nat := 81436320200967978945631

theorem tailTrace_237895 : CollatzResearch.WordTrace tailWord_237895 prefixEnd_237895 81436320200967978945631 := by
  unfold tailWord_237895
  simp only [CollatzResearch.WordTrace]
  refine ⟨8676743473154519076451139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5784495648769679384300759 8676743473154519076451139)
  ·
    refine ⟨13015115209731778614676709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8676743473154519076451139 13015115209731778614676709)
    ·
      refine ⟨2440334101824708490251883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13015115209731778614676709 2440334101824708490251883)
      ·
        refine ⟨3660501152737062735377825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2440334101824708490251883 3660501152737062735377825)
        ·
          refine ⟨2745375864552797051533369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3660501152737062735377825 2745375864552797051533369)
          ·
            refine ⟨2059031898414597788650027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2745375864552797051533369 2059031898414597788650027)
            ·
              refine ⟨3088547847621896682975041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2059031898414597788650027 3088547847621896682975041)
              ·
                refine ⟨2316410885716422512231281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3088547847621896682975041 2316410885716422512231281)
                ·
                  refine ⟨1737308164287316884173461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2316410885716422512231281 1737308164287316884173461)
                  ·
                    refine ⟨81436320200967978945631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1737308164287316884173461 81436320200967978945631)
                    ·
                      rfl

theorem cell22_237895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_237895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237895 prefixEnd_237895 := by exact prefixLift 237895
  have htrace : WordTrace (prefixWord ++ tailWord_237895) baseStart_237895 baseEnd_237895 := by
    simpa [prefixWord, tailWord_237895, baseEnd_237895] using wordTrace_append hprefix tailTrace_237895
  have hstable : (prefixWord ++ tailWord_237895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237895).length < 2 ^ (prefixWord ++ tailWord_237895).sum := by decide
  have hdescent : baseEnd_237895 < baseStart_237895 := by decide
  rcases family_descends (prefixWord ++ tailWord_237895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_237927 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 7]
def baseStart_237927 : Nat := 118140960795 + 237927 * 2 ^ 59
def prefixEnd_237927 : Nat := 4983230072969 + 3 ^ 40 * 237927 * 2
def baseEnd_237927 : Nat := 27149091484976854048511

theorem tailTrace_237927 : CollatzResearch.WordTrace tailWord_237927 prefixEnd_237927 27149091484976854048511 := by
  unfold tailWord_237927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8677910609038588541616035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5785273739359059027744023 8677910609038588541616035)
  ·
    refine ⟨13016865913557882812424053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8677910609038588541616035 13016865913557882812424053)
    ·
      refine ⟨1220331179396051513664755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13016865913557882812424053 1220331179396051513664755)
      ·
        refine ⟨1830496769094077270497133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1220331179396051513664755 1830496769094077270497133)
        ·
          refine ⟨686436288410278976436425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1830496769094077270497133 686436288410278976436425)
          ·
            refine ⟨514827216307709232327319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686436288410278976436425 514827216307709232327319)
            ·
              refine ⟨772240824461563848490979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514827216307709232327319 772240824461563848490979)
              ·
                refine ⟨1158361236692345772736469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 772240824461563848490979 1158361236692345772736469)
                ·
                  refine ⟨27149091484976854048511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1158361236692345772736469 27149091484976854048511)
                  ·
                    rfl

theorem cell22_237927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 7].length) (baseStart_237927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_237927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_237927 prefixEnd_237927 := by exact prefixLift 237927
  have htrace : WordTrace (prefixWord ++ tailWord_237927) baseStart_237927 baseEnd_237927 := by
    simpa [prefixWord, tailWord_237927, baseEnd_237927] using wordTrace_append hprefix tailTrace_237927
  have hstable : (prefixWord ++ tailWord_237927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_237927).length < 2 ^ (prefixWord ++ tailWord_237927).sum := by decide
  have hdescent : baseEnd_237927 < baseStart_237927 := by decide
  rcases family_descends (prefixWord ++ tailWord_237927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238002 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 4, 4]
def baseStart_238002 : Nat := 118140960795 + 238002 * 2 ^ 59
def prefixEnd_238002 : Nat := 4983230072969 + 3 ^ 40 * 238002 * 2
def baseEnd_238002 : Nat := 81472948487655366520303

theorem tailTrace_238002 : CollatzResearch.WordTrace tailWord_238002 prefixEnd_238002 81472948487655366520303 := by
  unfold tailWord_238002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170161520941719087649065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5787097389177917567064173 2170161520941719087649065)
  ·
    refine ⟨1627621140706289315736799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2170161520941719087649065 1627621140706289315736799)
    ·
      refine ⟨2441431711059433973605199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627621140706289315736799 2441431711059433973605199)
      ·
        refine ⟨3662147566589150960407799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441431711059433973605199 3662147566589150960407799)
        ·
          refine ⟨5493221349883726440611699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3662147566589150960407799 5493221349883726440611699)
          ·
            refine ⟨8239832024825589660917549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5493221349883726440611699 8239832024825589660917549)
            ·
              refine ⟨3089937009309596122844081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8239832024825589660917549 3089937009309596122844081)
              ·
                refine ⟨2317452756982197092133061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3089937009309596122844081 2317452756982197092133061)
                ·
                  refine ⟨434522391934161954774949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2317452756982197092133061 434522391934161954774949)
                  ·
                    refine ⟨81472948487655366520303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434522391934161954774949 81472948487655366520303)
                    ·
                      rfl

theorem cell22_238002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_238002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238002 prefixEnd_238002 := by exact prefixLift 238002
  have htrace : WordTrace (prefixWord ++ tailWord_238002) baseStart_238002 baseEnd_238002 := by
    simpa [prefixWord, tailWord_238002, baseEnd_238002] using wordTrace_append hprefix tailTrace_238002
  have hstable : (prefixWord ++ tailWord_238002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238002).length < 2 ^ (prefixWord ++ tailWord_238002).sum := by decide
  have hdescent : baseEnd_238002 < baseStart_238002 := by decide
  rcases family_descends (prefixWord ++ tailWord_238002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238034 : List Nat := [3, 2, 2, 4, 1, 10]
def baseStart_238034 : Nat := 118140960795 + 238034 * 2 ^ 59
def prefixEnd_238034 : Nat := 4983230072969 + 3 ^ 40 * 238034 * 2
def baseEnd_238034 : Nat := 1005974107921209255805

theorem tailTrace_238034 : CollatzResearch.WordTrace tailWord_238034 prefixEnd_238034 1005974107921209255805 := by
  unfold tailWord_238034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170453304912736453940289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5787875479767297210507437 2170453304912736453940289)
  ·
    refine ⟨1627839978684552340455217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2170453304912736453940289 1627839978684552340455217)
    ·
      refine ⟨1220879984013414255341413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1627839978684552340455217 1220879984013414255341413)
      ·
        refine ⟨228914997002515172876515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1220879984013414255341413 228914997002515172876515)
        ·
          refine ⟨343372495503772759314773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228914997002515172876515 343372495503772759314773)
          ·
            refine ⟨1005974107921209255805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 343372495503772759314773 1005974107921209255805)
            ·
              rfl

theorem cell22_238034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 10].length) (baseStart_238034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238034 prefixEnd_238034 := by exact prefixLift 238034
  have htrace : WordTrace (prefixWord ++ tailWord_238034) baseStart_238034 baseEnd_238034 := by
    simpa [prefixWord, tailWord_238034, baseEnd_238034] using wordTrace_append hprefix tailTrace_238034
  have hstable : (prefixWord ++ tailWord_238034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238034).length < 2 ^ (prefixWord ++ tailWord_238034).sum := by decide
  have hdescent : baseEnd_238034 < baseStart_238034 := by decide
  rcases family_descends (prefixWord ++ tailWord_238034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238038 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_238038 : Nat := 118140960795 + 238038 * 2 ^ 59
def prefixEnd_238038 : Nat := 4983230072969 + 3 ^ 40 * 238038 * 2
def baseEnd_238038 : Nat := 81485272023363272620193

theorem tailTrace_238038 : CollatzResearch.WordTrace tailWord_238038 prefixEnd_238038 81485272023363272620193 := by
  unfold tailWord_238038
  simp only [CollatzResearch.WordTrace]
  refine ⟨542622444477278406181673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5787972741090969665937845 542622444477278406181673)
  ·
    refine ⟨406966833357958804636255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 542622444477278406181673 406966833357958804636255)
    ·
      refine ⟨610450250036938206954383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406966833357958804636255 610450250036938206954383)
      ·
        refine ⟨915675375055407310431575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610450250036938206954383 915675375055407310431575)
        ·
          refine ⟨1373513062583110965647363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915675375055407310431575 1373513062583110965647363)
          ·
            refine ⟨2060269593874666448471045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1373513062583110965647363 2060269593874666448471045)
            ·
              refine ⟨386300548851499959088321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2060269593874666448471045 386300548851499959088321)
              ·
                refine ⟨289725411638624969316241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386300548851499959088321 289725411638624969316241)
                ·
                  refine ⟨217294058728968726987181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289725411638624969316241 217294058728968726987181)
                  ·
                    refine ⟨81485272023363272620193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217294058728968726987181 81485272023363272620193)
                    ·
                      rfl

theorem cell22_238038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_238038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238038 prefixEnd_238038 := by exact prefixLift 238038
  have htrace : WordTrace (prefixWord ++ tailWord_238038) baseStart_238038 baseEnd_238038 := by
    simpa [prefixWord, tailWord_238038, baseEnd_238038] using wordTrace_append hprefix tailTrace_238038
  have hstable : (prefixWord ++ tailWord_238038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238038).length < 2 ^ (prefixWord ++ tailWord_238038).sum := by decide
  have hdescent : baseEnd_238038 < baseStart_238038 := by decide
  rcases family_descends (prefixWord ++ tailWord_238038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238047 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 6]
def baseStart_238047 : Nat := 118140960795 + 238047 * 2 ^ 59
def prefixEnd_238047 : Nat := 4983230072969 + 3 ^ 40 * 238047 * 2
def baseEnd_238047 : Nat := 81488352907290249145165

theorem tailTrace_238047 : CollatzResearch.WordTrace tailWord_238047 prefixEnd_238047 81488352907290249145165 := by
  unfold tailWord_238047
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682287368603849035984395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788191579069232690656263 8682287368603849035984395)
  ·
    refine ⟨13023431052905773553976593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8682287368603849035984395 13023431052905773553976593)
    ·
      refine ⟨9767573289679330165482445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13023431052905773553976593 9767573289679330165482445)
      ·
        refine ⟨3662839983629748812055917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9767573289679330165482445 3662839983629748812055917)
        ·
          refine ⟨1373564993861155804520969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3662839983629748812055917 1373564993861155804520969)
          ·
            refine ⟨1030173745395866853390727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1373564993861155804520969 1030173745395866853390727)
            ·
              refine ⟨1545260618093800280086091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030173745395866853390727 1545260618093800280086091)
              ·
                refine ⟨2317890927140700420129137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545260618093800280086091 2317890927140700420129137)
                ·
                  refine ⟨1738418195355525315096853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2317890927140700420129137 1738418195355525315096853)
                  ·
                    refine ⟨81488352907290249145165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1738418195355525315096853 81488352907290249145165)
                    ·
                      rfl

theorem cell22_238047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_238047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238047 prefixEnd_238047 := by exact prefixLift 238047
  have htrace : WordTrace (prefixWord ++ tailWord_238047) baseStart_238047 baseEnd_238047 := by
    simpa [prefixWord, tailWord_238047, baseEnd_238047] using wordTrace_append hprefix tailTrace_238047
  have hstable : (prefixWord ++ tailWord_238047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238047).length < 2 ^ (prefixWord ++ tailWord_238047).sum := by decide
  have hdescent : baseEnd_238047 < baseStart_238047 := by decide
  rcases family_descends (prefixWord ++ tailWord_238047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238049 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 3, 3]
def baseStart_238049 : Nat := 118140960795 + 238049 * 2 ^ 59
def prefixEnd_238049 : Nat := 4983230072969 + 3 ^ 40 * 238049 * 2
def baseEnd_238049 : Nat := 81489037548162910595159

theorem tailTrace_238049 : CollatzResearch.WordTrace tailWord_238049 prefixEnd_238049 81489037548162910595159 := by
  unfold tailWord_238049
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682360314596603377557201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788240209731068918371467 8682360314596603377557201)
  ·
    refine ⟨6511770235947452533167901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8682360314596603377557201 6511770235947452533167901)
    ·
      refine ⟨2441913838480294699937963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6511770235947452533167901 2441913838480294699937963)
      ·
        refine ⟨3662870757720442049906945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2441913838480294699937963 3662870757720442049906945)
        ·
          refine ⟨2747153068290331537430209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3662870757720442049906945 2747153068290331537430209)
          ·
            refine ⟨2060364801217748653072657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2747153068290331537430209 2060364801217748653072657)
            ·
              refine ⟨1545273600913311489804493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2060364801217748653072657 1545273600913311489804493)
              ·
                refine ⟨579477600342491808676685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1545273600913311489804493 579477600342491808676685)
                ·
                  refine ⟨217304100128434428253757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 579477600342491808676685 217304100128434428253757)
                  ·
                    refine ⟨81489037548162910595159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217304100128434428253757 81489037548162910595159)
                    ·
                      rfl

theorem cell22_238049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_238049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238049 prefixEnd_238049 := by exact prefixLift 238049
  have htrace : WordTrace (prefixWord ++ tailWord_238049) baseStart_238049 baseEnd_238049 := by
    simpa [prefixWord, tailWord_238049, baseEnd_238049] using wordTrace_append hprefix tailTrace_238049
  have hstable : (prefixWord ++ tailWord_238049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238049).length < 2 ^ (prefixWord ++ tailWord_238049).sum := by decide
  have hdescent : baseEnd_238049 < baseStart_238049 := by decide
  rcases family_descends (prefixWord ++ tailWord_238049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238051 : List Nat := [1, 1, 1, 6, 4, 1, 1, 7]
def baseStart_238051 : Nat := 118140960795 + 238051 * 2 ^ 59
def prefixEnd_238051 : Nat := 4983230072969 + 3 ^ 40 * 238051 * 2
def baseEnd_238051 : Nat := 9054413576559508005017

theorem tailTrace_238051 : CollatzResearch.WordTrace tailWord_238051 prefixEnd_238051 9054413576559508005017 := by
  unfold tailWord_238051
  simp only [CollatzResearch.WordTrace]
  refine ⟨8682433260589357719130007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788288840392905146086671 8682433260589357719130007)
  ·
    refine ⟨13023649890884036578695011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8682433260589357719130007 13023649890884036578695011)
    ·
      refine ⟨19535474836326054868042517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13023649890884036578695011 19535474836326054868042517)
      ·
        refine ⟨915725382952783821939493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19535474836326054868042517 915725382952783821939493)
        ·
          refine ⟨171698509303646966613655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 915725382952783821939493 171698509303646966613655)
          ·
            refine ⟨257547763955470449920483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171698509303646966613655 257547763955470449920483)
            ·
              refine ⟨386321645933205674880725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257547763955470449920483 386321645933205674880725)
              ·
                refine ⟨9054413576559508005017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386321645933205674880725 9054413576559508005017)
                ·
                  rfl

theorem cell22_238051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 7].length) (baseStart_238051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238051 prefixEnd_238051 := by exact prefixLift 238051
  have htrace : WordTrace (prefixWord ++ tailWord_238051) baseStart_238051 baseEnd_238051 := by
    simpa [prefixWord, tailWord_238051, baseEnd_238051] using wordTrace_append hprefix tailTrace_238051
  have hstable : (prefixWord ++ tailWord_238051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238051).length < 2 ^ (prefixWord ++ tailWord_238051).sum := by decide
  have hdescent : baseEnd_238051 < baseStart_238051 := by decide
  rcases family_descends (prefixWord ++ tailWord_238051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238077 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_238077 : Nat := 118140960795 + 238077 * 2 ^ 59
def prefixEnd_238077 : Nat := 4983230072969 + 3 ^ 40 * 238077 * 2
def baseEnd_238077 : Nat := 81498622520380170895073

theorem tailTrace_238077 : CollatzResearch.WordTrace tailWord_238077 prefixEnd_238077 81498622520380170895073 := by
  unfold tailWord_238077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8683381558495164159576485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5788921038996776106384323 8683381558495164159576485)
  ·
    refine ⟨1628134042217843279920591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8683381558495164159576485 1628134042217843279920591)
    ·
      refine ⟨2442201063326764919880887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628134042217843279920591 2442201063326764919880887)
      ·
        refine ⟨3663301594990147379821331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442201063326764919880887 3663301594990147379821331)
        ·
          refine ⟨5494952392485221069731997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3663301594990147379821331 5494952392485221069731997)
          ·
            refine ⟨2060607147181957901149499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5494952392485221069731997 2060607147181957901149499)
            ·
              refine ⟨3090910720772936851724249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2060607147181957901149499 3090910720772936851724249)
              ·
                refine ⟨2318183040579702638793187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3090910720772936851724249 2318183040579702638793187)
                ·
                  refine ⟨3477274560869553958189781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2318183040579702638793187 3477274560869553958189781)
                  ·
                    refine ⟨81498622520380170895073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3477274560869553958189781 81498622520380170895073)
                    ·
                      rfl

theorem cell22_238077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_238077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238077 prefixEnd_238077 := by exact prefixLift 238077
  have htrace : WordTrace (prefixWord ++ tailWord_238077) baseStart_238077 baseEnd_238077 := by
    simpa [prefixWord, tailWord_238077, baseEnd_238077] using wordTrace_append hprefix tailTrace_238077
  have hstable : (prefixWord ++ tailWord_238077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238077).length < 2 ^ (prefixWord ++ tailWord_238077).sum := by decide
  have hdescent : baseEnd_238077 < baseStart_238077 := by decide
  rcases family_descends (prefixWord ++ tailWord_238077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238094 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_238094 : Nat := 118140960795 + 238094 * 2 ^ 59
def prefixEnd_238094 : Nat := 4983230072969 + 3 ^ 40 * 238094 * 2
def baseEnd_238094 : Nat := 81504441967797793220021

theorem tailTrace_238094 : CollatzResearch.WordTrace tailWord_238094 prefixEnd_238094 81504441967797793220021 := by
  unfold tailWord_238094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085500199929197007868167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5789334399622384041963557 1085500199929197007868167)
  ·
    refine ⟨1628250299893795511802251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1085500199929197007868167 1628250299893795511802251)
    ·
      refine ⟨2442375449840693267703377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628250299893795511802251 2442375449840693267703377)
      ·
        refine ⟨1831781587380519950777533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2442375449840693267703377 1831781587380519950777533)
        ·
          refine ⟨686918095267694981541575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1831781587380519950777533 686918095267694981541575)
          ·
            refine ⟨1030377142901542472312363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686918095267694981541575 1030377142901542472312363)
            ·
              refine ⟨1545565714352313708468545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030377142901542472312363 1545565714352313708468545)
              ·
                refine ⟨1159174285764235281351409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1545565714352313708468545 1159174285764235281351409)
                ·
                  refine ⟨869380714323176461013557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1159174285764235281351409 869380714323176461013557)
                  ·
                    refine ⟨81504441967797793220021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 869380714323176461013557 81504441967797793220021)
                    ·
                      rfl

theorem cell22_238094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_238094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238094 prefixEnd_238094 := by exact prefixLift 238094
  have htrace : WordTrace (prefixWord ++ tailWord_238094) baseStart_238094 baseEnd_238094 := by
    simpa [prefixWord, tailWord_238094, baseEnd_238094] using wordTrace_append hprefix tailTrace_238094
  have hstable : (prefixWord ++ tailWord_238094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238094).length < 2 ^ (prefixWord ++ tailWord_238094).sum := by decide
  have hdescent : baseEnd_238094 < baseStart_238094 := by decide
  rcases family_descends (prefixWord ++ tailWord_238094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238100 : List Nat := [2, 4, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_238100 : Nat := 118140960795 + 238100 * 2 ^ 59
def prefixEnd_238100 : Nat := 4983230072969 + 3 ^ 40 * 238100 * 2
def baseEnd_238100 : Nat := 81506495890415777570003

theorem tailTrace_238100 : CollatzResearch.WordTrace tailWord_238100 prefixEnd_238100 81506495890415777570003 := by
  unfold tailWord_238100
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342110218705919543831877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5789480291607892725109169 4342110218705919543831877)
  ·
    refine ⟨814145666007359914468477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4342110218705919543831877 814145666007359914468477)
    ·
      refine ⟨305304624752759967925679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 814145666007359914468477 305304624752759967925679)
      ·
        refine ⟨457956937129139951888519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305304624752759967925679 457956937129139951888519)
        ·
          refine ⟨686935405693709927832779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457956937129139951888519 686935405693709927832779)
          ·
            refine ⟨1030403108540564891749169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686935405693709927832779 1030403108540564891749169)
            ·
              refine ⟨772802331405423668811877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1030403108540564891749169 772802331405423668811877)
              ·
                refine ⟨144900437138516937902227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 772802331405423668811877 144900437138516937902227)
                ·
                  refine ⟨217350655707775406853341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144900437138516937902227 217350655707775406853341)
                  ·
                    refine ⟨81506495890415777570003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217350655707775406853341 81506495890415777570003)
                    ·
                      rfl

theorem cell22_238100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_238100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238100 prefixEnd_238100 := by exact prefixLift 238100
  have htrace : WordTrace (prefixWord ++ tailWord_238100) baseStart_238100 baseEnd_238100 := by
    simpa [prefixWord, tailWord_238100, baseEnd_238100] using wordTrace_append hprefix tailTrace_238100
  have hstable : (prefixWord ++ tailWord_238100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238100).length < 2 ^ (prefixWord ++ tailWord_238100).sum := by decide
  have hdescent : baseEnd_238100 < baseStart_238100 := by decide
  rcases family_descends (prefixWord ++ tailWord_238100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238154 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 4, 4]
def baseStart_238154 : Nat := 118140960795 + 238154 * 2 ^ 59
def prefixEnd_238154 : Nat := 4983230072969 + 3 ^ 40 * 238154 * 2
def baseEnd_238154 : Nat := 81524981193977636719837

theorem tailTrace_238154 : CollatzResearch.WordTrace tailWord_238154 prefixEnd_238154 81524981193977636719837 := by
  unfold tailWord_238154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2171547494804051577532379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5790793319477470873419677 2171547494804051577532379)
  ·
    refine ⟨3257321242206077366298569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2171547494804051577532379 3257321242206077366298569)
    ·
      refine ⟨2442990931654558024723927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3257321242206077366298569 2442990931654558024723927)
      ·
        refine ⟨3664486397481837037085891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2442990931654558024723927 3664486397481837037085891)
        ·
          refine ⟨5496729596222755555628837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3664486397481837037085891 5496729596222755555628837)
          ·
            refine ⟨1030636799291766666680407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5496729596222755555628837 1030636799291766666680407)
            ·
              refine ⟨1545955198937650000020611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1030636799291766666680407 1545955198937650000020611)
              ·
                refine ⟨2318932798406475000030917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1545955198937650000020611 2318932798406475000030917)
                ·
                  refine ⟨434799899701214062505797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2318932798406475000030917 434799899701214062505797)
                  ·
                    refine ⟨81524981193977636719837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 434799899701214062505797 81524981193977636719837)
                    ·
                      rfl

theorem cell22_238154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_238154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238154 prefixEnd_238154 := by exact prefixLift 238154
  have htrace : WordTrace (prefixWord ++ tailWord_238154) baseStart_238154 baseEnd_238154 := by
    simpa [prefixWord, tailWord_238154, baseEnd_238154] using wordTrace_append hprefix tailTrace_238154
  have hstable : (prefixWord ++ tailWord_238154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238154).length < 2 ^ (prefixWord ++ tailWord_238154).sum := by decide
  have hdescent : baseEnd_238154 < baseStart_238154 := by decide
  rcases family_descends (prefixWord ++ tailWord_238154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238156 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_238156 : Nat := 118140960795 + 238156 * 2 ^ 59
def prefixEnd_238156 : Nat := 4983230072969 + 3 ^ 40 * 238156 * 2
def baseEnd_238156 : Nat := 81525665834850298169831

theorem tailTrace_238156 : CollatzResearch.WordTrace tailWord_238156 prefixEnd_238156 81525665834850298169831 := by
  unfold tailWord_238156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4343131462604480325851161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5790841950139307101134881 4343131462604480325851161)
  ·
    refine ⟨3257348596953360244388371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4343131462604480325851161 3257348596953360244388371)
    ·
      refine ⟨4886022895430040366582557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3257348596953360244388371 4886022895430040366582557)
      ·
        refine ⟨1832258585786265137468459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4886022895430040366582557 1832258585786265137468459)
        ·
          refine ⟨2748387878679397706202689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1832258585786265137468459 2748387878679397706202689)
          ·
            refine ⟨2061290909009548279652017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2748387878679397706202689 2061290909009548279652017)
            ·
              refine ⟨1545968181757161209739013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2061290909009548279652017 1545968181757161209739013)
              ·
                refine ⟨289869034079467726826065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1545968181757161209739013 289869034079467726826065)
                ·
                  refine ⟨217401775559600795119549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289869034079467726826065 217401775559600795119549)
                  ·
                    refine ⟨81525665834850298169831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217401775559600795119549 81525665834850298169831)
                    ·
                      rfl

theorem cell22_238156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_238156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238156 prefixEnd_238156 := by exact prefixLift 238156
  have htrace : WordTrace (prefixWord ++ tailWord_238156) baseStart_238156 baseEnd_238156 := by
    simpa [prefixWord, tailWord_238156, baseEnd_238156] using wordTrace_append hprefix tailTrace_238156
  have hstable : (prefixWord ++ tailWord_238156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238156).length < 2 ^ (prefixWord ++ tailWord_238156).sum := by decide
  have hdescent : baseEnd_238156 < baseStart_238156 := by decide
  rcases family_descends (prefixWord ++ tailWord_238156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238276 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_238276 : Nat := 118140960795 + 238276 * 2 ^ 59
def prefixEnd_238276 : Nat := 4983230072969 + 3 ^ 40 * 238276 * 2
def baseEnd_238276 : Nat := 27188914762403328389821

theorem tailTrace_238276 : CollatzResearch.WordTrace tailWord_238276 prefixEnd_238276 27188914762403328389821 := by
  unfold tailWord_238276
  simp only [CollatzResearch.WordTrace]
  refine ⟨4345319842387110573035341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5793759789849480764047121 4345319842387110573035341)
  ·
    refine ⟨1629494940895166464888253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4345319842387110573035341 1629494940895166464888253)
    ·
      refine ⟨611060602835687424333095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1629494940895166464888253 611060602835687424333095)
      ·
        refine ⟨916590904253531136499643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611060602835687424333095 916590904253531136499643)
        ·
          refine ⟨1374886356380296704749465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916590904253531136499643 1374886356380296704749465)
          ·
            refine ⟨1031164767285222528562099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1374886356380296704749465 1031164767285222528562099)
            ·
              refine ⟨1546747150927833792843149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1031164767285222528562099 1546747150927833792843149)
              ·
                refine ⟨580030181597937672316181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1546747150927833792843149 580030181597937672316181)
                ·
                  refine ⟨27188914762403328389821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 580030181597937672316181 27188914762403328389821)
                  ·
                    rfl

theorem cell22_238276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_238276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238276 prefixEnd_238276 := by exact prefixLift 238276
  have htrace : WordTrace (prefixWord ++ tailWord_238276) baseStart_238276 baseEnd_238276 := by
    simpa [prefixWord, tailWord_238276, baseEnd_238276] using wordTrace_append hprefix tailTrace_238276
  have hstable : (prefixWord ++ tailWord_238276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238276).length < 2 ^ (prefixWord ++ tailWord_238276).sum := by decide
  have hdescent : baseEnd_238276 < baseStart_238276 := by decide
  rcases family_descends (prefixWord ++ tailWord_238276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238289 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 3, 6]
def baseStart_238289 : Nat := 118140960795 + 238289 * 2 ^ 59
def prefixEnd_238289 : Nat := 4983230072969 + 3 ^ 40 * 238289 * 2
def baseEnd_238289 : Nat := 81571194452882284594423

theorem tailTrace_238289 : CollatzResearch.WordTrace tailWord_238289 prefixEnd_238289 81571194452882284594423 := by
  unfold tailWord_238289
  simp only [CollatzResearch.WordTrace]
  refine ⟨8691113833727124366293921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5794075889151416244195947 8691113833727124366293921)
  ·
    refine ⟨6518335375295343274720441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8691113833727124366293921 6518335375295343274720441)
    ·
      refine ⟨4888751531471507456040331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6518335375295343274720441 4888751531471507456040331)
      ·
        refine ⟨7333127297207261184060497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4888751531471507456040331 7333127297207261184060497)
        ·
          refine ⟨5499845472905445888045373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7333127297207261184060497 5499845472905445888045373)
          ·
            refine ⟨2062442052339542208017015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5499845472905445888045373 2062442052339542208017015)
            ·
              refine ⟨3093663078509313312025523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062442052339542208017015 3093663078509313312025523)
              ·
                refine ⟨4640494617763969968038285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3093663078509313312025523 4640494617763969968038285)
                ·
                  refine ⟨1740185481661488738014357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4640494617763969968038285 1740185481661488738014357)
                  ·
                    refine ⟨81571194452882284594423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1740185481661488738014357 81571194452882284594423)
                    ·
                      rfl

theorem cell22_238289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_238289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238289 prefixEnd_238289 := by exact prefixLift 238289
  have htrace : WordTrace (prefixWord ++ tailWord_238289) baseStart_238289 baseEnd_238289 := by
    simpa [prefixWord, tailWord_238289, baseEnd_238289] using wordTrace_append hprefix tailTrace_238289
  have hstable : (prefixWord ++ tailWord_238289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238289).length < 2 ^ (prefixWord ++ tailWord_238289).sum := by decide
  have hdescent : baseEnd_238289 < baseStart_238289 := by decide
  rcases family_descends (prefixWord ++ tailWord_238289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238338 : List Nat := [3, 4, 1, 1, 1, 3, 2, 7]
def baseStart_238338 : Nat := 118140960795 + 238338 * 2 ^ 59
def prefixEnd_238338 : Nat := 4983230072969 + 3 ^ 40 * 238338 * 2
def baseEnd_238338 : Nat := 9065329794918054457697

theorem tailTrace_238338 : CollatzResearch.WordTrace tailWord_238338 prefixEnd_238338 9065329794918054457697 := by
  unfold tailWord_238338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2173225252637401433706917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5795267340366403823218445 2173225252637401433706917)
  ·
    refine ⟨407479734869512768820047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2173225252637401433706917 407479734869512768820047)
    ·
      refine ⟨611219602304269153230071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 407479734869512768820047 611219602304269153230071)
      ·
        refine ⟨916829403456403729845107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 611219602304269153230071 916829403456403729845107)
        ·
          refine ⟨1375244105184605594767661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 916829403456403729845107 1375244105184605594767661)
          ·
            refine ⟨515716539444227098037873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1375244105184605594767661 515716539444227098037873)
            ·
              refine ⟨386787404583170323528405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515716539444227098037873 386787404583170323528405)
              ·
                refine ⟨9065329794918054457697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 386787404583170323528405 9065329794918054457697)
                ·
                  rfl

theorem cell22_238338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_238338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238338 prefixEnd_238338 := by exact prefixLift 238338
  have htrace : WordTrace (prefixWord ++ tailWord_238338) baseStart_238338 baseEnd_238338 := by
    simpa [prefixWord, tailWord_238338, baseEnd_238338] using wordTrace_append hprefix tailTrace_238338
  have hstable : (prefixWord ++ tailWord_238338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238338).length < 2 ^ (prefixWord ++ tailWord_238338).sum := by decide
  have hdescent : baseEnd_238338 < baseStart_238338 := by decide
  rcases family_descends (prefixWord ++ tailWord_238338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238387 : List Nat := [1, 1, 1, 2, 6, 1, 4, 2, 1, 3]
def baseStart_238387 : Nat := 118140960795 + 238387 * 2 ^ 59
def prefixEnd_238387 : Nat := 4983230072969 + 3 ^ 40 * 238387 * 2
def baseEnd_238387 : Nat := 81604741855642695644123

theorem tailTrace_238387 : CollatzResearch.WordTrace tailWord_238387 prefixEnd_238387 81604741855642695644123 := by
  unfold tailWord_238387
  simp only [CollatzResearch.WordTrace]
  refine ⟨8694688187372087103361415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5796458791581391402240943 8694688187372087103361415)
  ·
    refine ⟨13042032281058130655042123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8694688187372087103361415 13042032281058130655042123)
    ·
      refine ⟨19563048421587195982563185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13042032281058130655042123 19563048421587195982563185)
      ·
        refine ⟨14672286316190396986922389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19563048421587195982563185 14672286316190396986922389)
        ·
          refine ⟨687763421071424858761987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14672286316190396986922389 687763421071424858761987)
          ·
            refine ⟨1031645131607137288142981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 687763421071424858761987 1031645131607137288142981)
            ·
              refine ⟨193433462176338241526809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1031645131607137288142981 193433462176338241526809)
              ·
                refine ⟨145075096632253681145107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193433462176338241526809 145075096632253681145107)
                ·
                  refine ⟨217612644948380521717661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145075096632253681145107 217612644948380521717661)
                  ·
                    refine ⟨81604741855642695644123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217612644948380521717661 81604741855642695644123)
                    ·
                      rfl

theorem cell22_238387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 3].length) (baseStart_238387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238387 prefixEnd_238387 := by exact prefixLift 238387
  have htrace : WordTrace (prefixWord ++ tailWord_238387) baseStart_238387 baseEnd_238387 := by
    simpa [prefixWord, tailWord_238387, baseEnd_238387] using wordTrace_append hprefix tailTrace_238387
  have hstable : (prefixWord ++ tailWord_238387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238387).length < 2 ^ (prefixWord ++ tailWord_238387).sum := by decide
  have hdescent : baseEnd_238387 < baseStart_238387 := by decide
  rcases family_descends (prefixWord ++ tailWord_238387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238473 : List Nat := [1, 2, 1, 1, 5, 2, 4, 6]
def baseStart_238473 : Nat := 118140960795 + 238473 * 2 ^ 59
def prefixEnd_238473 : Nat := 4983230072969 + 3 ^ 40 * 238473 * 2
def baseEnd_238473 : Nat := 9070464601463015332651

theorem tailTrace_238473 : CollatzResearch.WordTrace tailWord_238473 prefixEnd_238473 9070464601463015332651 := by
  unfold tailWord_238473
  simp only [CollatzResearch.WordTrace]
  refine ⟨8697824865060523790992073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5798549910040349193994715 8697824865060523790992073)
  ·
    refine ⟨6523368648795392843244055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8697824865060523790992073 6523368648795392843244055)
    ·
      refine ⟨9785052973193089264866083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6523368648795392843244055 9785052973193089264866083)
      ·
        refine ⟨14677579459789633897299125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9785052973193089264866083 14677579459789633897299125)
        ·
          refine ⟨1376023074355278177871793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14677579459789633897299125 1376023074355278177871793)
          ·
            refine ⟨1032017305766458633403845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1376023074355278177871793 1032017305766458633403845)
            ·
              refine ⟨193503244831210993763221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1032017305766458633403845 193503244831210993763221)
              ·
                refine ⟨9070464601463015332651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193503244831210993763221 9070464601463015332651)
                ·
                  rfl

theorem cell22_238473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 6].length) (baseStart_238473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238473 prefixEnd_238473 := by exact prefixLift 238473
  have htrace : WordTrace (prefixWord ++ tailWord_238473) baseStart_238473 baseEnd_238473 := by
    simpa [prefixWord, tailWord_238473, baseEnd_238473] using wordTrace_append hprefix tailTrace_238473
  have hstable : (prefixWord ++ tailWord_238473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238473).length < 2 ^ (prefixWord ++ tailWord_238473).sum := by decide
  have hdescent : baseEnd_238473 < baseStart_238473 := by decide
  rcases family_descends (prefixWord ++ tailWord_238473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238490 : List Nat := [3, 1, 1, 4, 4, 1, 8]
def baseStart_238490 : Nat := 118140960795 + 238490 * 2 ^ 59
def prefixEnd_238490 : Nat := 4983230072969 + 3 ^ 40 * 238490 * 2
def baseEnd_238490 : Nat := 3023703735577213345141

theorem tailTrace_238490 : CollatzResearch.WordTrace tailWord_238490 prefixEnd_238490 3023703735577213345141 := by
  unfold tailWord_238490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174611226499733923590231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5798963270665957129573949 2174611226499733923590231)
  ·
    refine ⟨3261916839749600885385347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2174611226499733923590231 3261916839749600885385347)
    ·
      refine ⟨4892875259624401328078021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3261916839749600885385347 4892875259624401328078021)
      ·
        refine ⟨917414111179575249014629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4892875259624401328078021 917414111179575249014629)
        ·
          refine ⟨172015145846170359190243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 917414111179575249014629 172015145846170359190243)
          ·
            refine ⟨258022718769255538785365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172015145846170359190243 258022718769255538785365)
            ·
              refine ⟨3023703735577213345141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 258022718769255538785365 3023703735577213345141)
              ·
                rfl

theorem cell22_238490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 8].length) (baseStart_238490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238490 prefixEnd_238490 := by exact prefixLift 238490
  have htrace : WordTrace (prefixWord ++ tailWord_238490) baseStart_238490 baseEnd_238490 := by
    simpa [prefixWord, tailWord_238490, baseEnd_238490] using wordTrace_append hprefix tailTrace_238490
  have hstable : (prefixWord ++ tailWord_238490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238490).length < 2 ^ (prefixWord ++ tailWord_238490).sum := by decide
  have hdescent : baseEnd_238490 < baseStart_238490 := by decide
  rcases family_descends (prefixWord ++ tailWord_238490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238531 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_238531 : Nat := 118140960795 + 238531 * 2 ^ 59
def prefixEnd_238531 : Nat := 4983230072969 + 3 ^ 40 * 238531 * 2
def baseEnd_238531 : Nat := 81654035998474320043681

theorem tailTrace_238531 : CollatzResearch.WordTrace tailWord_238531 prefixEnd_238531 81654035998474320043681 := by
  unfold tailWord_238531
  simp only [CollatzResearch.WordTrace]
  refine ⟨8699940298850399696603447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5799960199233599797735631 8699940298850399696603447)
  ·
    refine ⟨13049910448275599544905171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8699940298850399696603447 13049910448275599544905171)
    ·
      refine ⟨19574865672413399317357757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13049910448275599544905171 19574865672413399317357757)
      ·
        refine ⟨7340574627155024744009159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19574865672413399317357757 7340574627155024744009159)
        ·
          refine ⟨11010861940732537116013739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7340574627155024744009159 11010861940732537116013739)
          ·
            refine ⟨16516292911098805674020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11010861940732537116013739 16516292911098805674020609)
            ·
              refine ⟨12387219683324104255515457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16516292911098805674020609 12387219683324104255515457)
              ·
                refine ⟨9290414762493078191636593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12387219683324104255515457 9290414762493078191636593)
                ·
                  refine ⟨6967811071869808643727445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9290414762493078191636593 6967811071869808643727445)
                  ·
                    refine ⟨81654035998474320043681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6967811071869808643727445 81654035998474320043681)
                    ·
                      rfl

theorem cell22_238531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_238531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238531 prefixEnd_238531 := by exact prefixLift 238531
  have htrace : WordTrace (prefixWord ++ tailWord_238531) baseStart_238531 baseEnd_238531 := by
    simpa [prefixWord, tailWord_238531, baseEnd_238531] using wordTrace_append hprefix tailTrace_238531
  have hstable : (prefixWord ++ tailWord_238531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238531).length < 2 ^ (prefixWord ++ tailWord_238531).sum := by decide
  have hdescent : baseEnd_238531 < baseStart_238531 := by decide
  rcases family_descends (prefixWord ++ tailWord_238531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238563 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 6]
def baseStart_238563 : Nat := 118140960795 + 238563 * 2 ^ 59
def prefixEnd_238563 : Nat := 4983230072969 + 3 ^ 40 * 238563 * 2
def baseEnd_238563 : Nat := 27221663417478967747861

theorem tailTrace_238563 : CollatzResearch.WordTrace tailWord_238563 prefixEnd_238563 27221663417478967747861 := by
  unfold tailWord_238563
  simp only [CollatzResearch.WordTrace]
  refine ⟨8701107434734469161768343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5800738289822979441178895 8701107434734469161768343)
  ·
    refine ⟨13051661152101703742652515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8701107434734469161768343 13051661152101703742652515)
    ·
      refine ⟨19577491728152555613978773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13051661152101703742652515 19577491728152555613978773)
      ·
        refine ⟨917694924757151044405255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19577491728152555613978773 917694924757151044405255)
        ·
          refine ⟨1376542387135726566607883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 917694924757151044405255 1376542387135726566607883)
          ·
            refine ⟨2064813580703589849911825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1376542387135726566607883 2064813580703589849911825)
            ·
              refine ⟨1548610185527692387433869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2064813580703589849911825 1548610185527692387433869)
              ·
                refine ⟨580728819572884645287701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1548610185527692387433869 580728819572884645287701)
                ·
                  refine ⟨27221663417478967747861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 580728819572884645287701 27221663417478967747861)
                  ·
                    rfl

theorem cell22_238563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 6].length) (baseStart_238563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238563 prefixEnd_238563 := by exact prefixLift 238563
  have htrace : WordTrace (prefixWord ++ tailWord_238563) baseStart_238563 baseEnd_238563 := by
    simpa [prefixWord, tailWord_238563, baseEnd_238563] using wordTrace_append hprefix tailTrace_238563
  have hstable : (prefixWord ++ tailWord_238563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238563).length < 2 ^ (prefixWord ++ tailWord_238563).sum := by decide
  have hdescent : baseEnd_238563 < baseStart_238563 := by decide
  rcases family_descends (prefixWord ++ tailWord_238563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238640 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 3, 3]
def baseStart_238640 : Nat := 118140960795 + 238640 * 2 ^ 59
def prefixEnd_238640 : Nat := 4983230072969 + 3 ^ 40 * 238640 * 2
def baseEnd_238640 : Nat := 81691348926034369068347

theorem tailTrace_238640 : CollatzResearch.WordTrace tailWord_238640 prefixEnd_238640 81691348926034369068347 := by
  unfold tailWord_238640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4351957927727755656160687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5802610570303674208214249 4351957927727755656160687)
  ·
    refine ⟨6527936891591633484241031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4351957927727755656160687 6527936891591633484241031)
    ·
      refine ⟨9791905337387450226361547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6527936891591633484241031 9791905337387450226361547)
      ·
        refine ⟨14687858006081175339542321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791905337387450226361547 14687858006081175339542321)
        ·
          refine ⟨11015893504560881504656741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14687858006081175339542321 11015893504560881504656741)
          ·
            refine ⟨2065480032105165282123139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11015893504560881504656741 2065480032105165282123139)
            ·
              refine ⟨3098220048157747923184709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2065480032105165282123139 3098220048157747923184709)
              ·
                refine ⟨580916259029577735597133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3098220048157747923184709 580916259029577735597133)
                ·
                  refine ⟨217843597136091650848925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580916259029577735597133 217843597136091650848925)
                  ·
                    refine ⟨81691348926034369068347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217843597136091650848925 81691348926034369068347)
                    ·
                      rfl

theorem cell22_238640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 3, 3].length) (baseStart_238640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238640 prefixEnd_238640 := by exact prefixLift 238640
  have htrace : WordTrace (prefixWord ++ tailWord_238640) baseStart_238640 baseEnd_238640 := by
    simpa [prefixWord, tailWord_238640, baseEnd_238640] using wordTrace_append hprefix tailTrace_238640
  have hstable : (prefixWord ++ tailWord_238640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238640).length < 2 ^ (prefixWord ++ tailWord_238640).sum := by decide
  have hdescent : baseEnd_238640 < baseStart_238640 := by decide
  rcases family_descends (prefixWord ++ tailWord_238640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238670 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_238670 : Nat := 118140960795 + 238670 * 2 ^ 59
def prefixEnd_238670 : Nat := 4983230072969 + 3 ^ 40 * 238670 * 2
def baseEnd_238670 : Nat := 27233872846374763606085

theorem tailTrace_238670 : CollatzResearch.WordTrace tailWord_238670 prefixEnd_238670 27233872846374763606085 := by
  unfold tailWord_238670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088126255668353304489183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5803340030231217623942309 1088126255668353304489183)
  ·
    refine ⟨1632189383502529956733775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1088126255668353304489183 1632189383502529956733775)
    ·
      refine ⟨2448284075253794935100663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1632189383502529956733775 2448284075253794935100663)
      ·
        refine ⟨3672426112880692402650995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448284075253794935100663 3672426112880692402650995)
        ·
          refine ⟨5508639169321038603976493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3672426112880692402650995 5508639169321038603976493)
          ·
            refine ⟨2065739688495389476491185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5508639169321038603976493 2065739688495389476491185)
            ·
              refine ⟨1549304766371542107368389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2065739688495389476491185 1549304766371542107368389)
              ·
                refine ⟨290494643694664145131573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1549304766371542107368389 290494643694664145131573)
                ·
                  refine ⟨27233872846374763606085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290494643694664145131573 27233872846374763606085)
                  ·
                    rfl

theorem cell22_238670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_238670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238670 prefixEnd_238670 := by exact prefixLift 238670
  have htrace : WordTrace (prefixWord ++ tailWord_238670) baseStart_238670 baseEnd_238670 := by
    simpa [prefixWord, tailWord_238670, baseEnd_238670] using wordTrace_append hprefix tailTrace_238670
  have hstable : (prefixWord ++ tailWord_238670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238670).length < 2 ^ (prefixWord ++ tailWord_238670).sum := by decide
  have hdescent : baseEnd_238670 < baseStart_238670 := by decide
  rcases family_descends (prefixWord ++ tailWord_238670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238674 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_238674 : Nat := 118140960795 + 238674 * 2 ^ 59
def prefixEnd_238674 : Nat := 4983230072969 + 3 ^ 40 * 238674 * 2
def baseEnd_238674 : Nat := 81702987820869613718243

theorem tailTrace_238674 : CollatzResearch.WordTrace tailWord_238674 prefixEnd_238674 81702987820869613718243 := by
  unfold tailWord_238674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176288984333083779764769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5803437291554890079372717 2176288984333083779764769)
  ·
    refine ⟨1632216738249812834823577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2176288984333083779764769 1632216738249812834823577)
    ·
      refine ⟨1224162553687359626117683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1632216738249812834823577 1224162553687359626117683)
      ·
        refine ⟨1836243830531039439176525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224162553687359626117683 1836243830531039439176525)
        ·
          refine ⟨688591436449139789691197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1836243830531039439176525 688591436449139789691197)
          ·
            refine ⟨258221788668427421134199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 688591436449139789691197 258221788668427421134199)
            ·
              refine ⟨387332683002641131701299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258221788668427421134199 387332683002641131701299)
              ·
                refine ⟨580999024503961697551949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387332683002641131701299 580999024503961697551949)
                ·
                  refine ⟨217874634188985636581981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 580999024503961697551949 217874634188985636581981)
                  ·
                    refine ⟨81702987820869613718243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217874634188985636581981 81702987820869613718243)
                    ·
                      rfl

theorem cell22_238674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_238674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238674 prefixEnd_238674 := by exact prefixLift 238674
  have htrace : WordTrace (prefixWord ++ tailWord_238674) baseStart_238674 baseEnd_238674 := by
    simpa [prefixWord, tailWord_238674, baseEnd_238674] using wordTrace_append hprefix tailTrace_238674
  have hstable : (prefixWord ++ tailWord_238674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238674).length < 2 ^ (prefixWord ++ tailWord_238674).sum := by decide
  have hdescent : baseEnd_238674 < baseStart_238674 := by decide
  rcases family_descends (prefixWord ++ tailWord_238674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238700 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_238700 : Nat := 118140960795 + 238700 * 2 ^ 59
def prefixEnd_238700 : Nat := 4983230072969 + 3 ^ 40 * 238700 * 2
def baseEnd_238700 : Nat := 81711888152214212568163

theorem tailTrace_238700 : CollatzResearch.WordTrace tailWord_238700 prefixEnd_238700 81711888152214212568163 := by
  unfold tailWord_238700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4353052117619070779752777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5804069490158761039670369 4353052117619070779752777)
  ·
    refine ⟨3264789088214303084814583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4353052117619070779752777 3264789088214303084814583)
    ·
      refine ⟨4897183632321454627221875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3264789088214303084814583 4897183632321454627221875)
      ·
        refine ⟨7345775448482181940832813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4897183632321454627221875 7345775448482181940832813)
        ·
          refine ⟨2754665793180818227812305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7345775448482181940832813 2754665793180818227812305)
          ·
            refine ⟨2065999344885613670859229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2754665793180818227812305 2065999344885613670859229)
            ·
              refine ⟨774749754332105126572211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2065999344885613670859229 774749754332105126572211)
              ·
                refine ⟨1162124631498157689858317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 774749754332105126572211 1162124631498157689858317)
                ·
                  refine ⟨435796736811809133696869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1162124631498157689858317 435796736811809133696869)
                  ·
                    refine ⟨81711888152214212568163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 435796736811809133696869 81711888152214212568163)
                    ·
                      rfl

theorem cell22_238700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_238700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238700 prefixEnd_238700 := by exact prefixLift 238700
  have htrace : WordTrace (prefixWord ++ tailWord_238700) baseStart_238700 baseEnd_238700 := by
    simpa [prefixWord, tailWord_238700, baseEnd_238700] using wordTrace_append hprefix tailTrace_238700
  have hstable : (prefixWord ++ tailWord_238700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238700).length < 2 ^ (prefixWord ++ tailWord_238700).sum := by decide
  have hdescent : baseEnd_238700 < baseStart_238700 := by decide
  rcases family_descends (prefixWord ++ tailWord_238700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238730 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_238730 : Nat := 118140960795 + 238730 * 2 ^ 59
def prefixEnd_238730 : Nat := 4983230072969 + 3 ^ 40 * 238730 * 2
def baseEnd_238730 : Nat := 81722157765304134318071

theorem tailTrace_238730 : CollatzResearch.WordTrace tailWord_238730 prefixEnd_238730 81722157765304134318071 := by
  unfold tailWord_238730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176799606282364170774411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5804798950086304455398429 2176799606282364170774411)
  ·
    refine ⟨3265199409423546256161617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176799606282364170774411 3265199409423546256161617)
    ·
      refine ⟨2448899557067659692121213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3265199409423546256161617 2448899557067659692121213)
      ·
        refine ⟨918337333900372384545455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2448899557067659692121213 918337333900372384545455)
        ·
          refine ⟨1377506000850558576818183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918337333900372384545455 1377506000850558576818183)
          ·
            refine ⟨2066259001275837865227275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1377506000850558576818183 2066259001275837865227275)
            ·
              refine ⟨3099388501913756797840913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2066259001275837865227275 3099388501913756797840913)
              ·
                refine ⟨2324541376435317598380685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099388501913756797840913 2324541376435317598380685)
                ·
                  refine ⟨871703016163244099392757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2324541376435317598380685 871703016163244099392757)
                  ·
                    refine ⟨81722157765304134318071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 871703016163244099392757 81722157765304134318071)
                    ·
                      rfl

theorem cell22_238730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_238730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238730 prefixEnd_238730 := by exact prefixLift 238730
  have htrace : WordTrace (prefixWord ++ tailWord_238730) baseStart_238730 baseEnd_238730 := by
    simpa [prefixWord, tailWord_238730, baseEnd_238730] using wordTrace_append hprefix tailTrace_238730
  have hstable : (prefixWord ++ tailWord_238730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238730).length < 2 ^ (prefixWord ++ tailWord_238730).sum := by decide
  have hdescent : baseEnd_238730 < baseStart_238730 := by decide
  rcases family_descends (prefixWord ++ tailWord_238730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238792 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_238792 : Nat := 118140960795 + 238792 * 2 ^ 59
def prefixEnd_238792 : Nat := 4983230072969 + 3 ^ 40 * 238792 * 2
def baseEnd_238792 : Nat := 81743381632356639267881

theorem tailTrace_238792 : CollatzResearch.WordTrace tailWord_238792 prefixEnd_238792 81743381632356639267881 := by
  unfold tailWord_238792
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354729875452420635927315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5806306500603227514569753 4354729875452420635927315)
  ·
    refine ⟨6532094813178630953890973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4354729875452420635927315 6532094813178630953890973)
    ·
      refine ⟨2449535554941986607709115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6532094813178630953890973 2449535554941986607709115)
      ·
        refine ⟨3674303332412979911563673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449535554941986607709115 3674303332412979911563673)
        ·
          refine ⟨2755727499309734933672755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3674303332412979911563673 2755727499309734933672755)
          ·
            refine ⟨4133591248964602400509133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2755727499309734933672755 4133591248964602400509133)
            ·
              refine ⟨1550096718361725900190925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4133591248964602400509133 1550096718361725900190925)
              ·
                refine ⟨581286269385647212571597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1550096718361725900190925 581286269385647212571597)
                ·
                  refine ⟨217982351019617704714349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581286269385647212571597 217982351019617704714349)
                  ·
                    refine ⟨81743381632356639267881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 217982351019617704714349 81743381632356639267881)
                    ·
                      rfl

theorem cell22_238792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_238792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238792 prefixEnd_238792 := by exact prefixLift 238792
  have htrace : WordTrace (prefixWord ++ tailWord_238792) baseStart_238792 baseEnd_238792 := by
    simpa [prefixWord, tailWord_238792, baseEnd_238792] using wordTrace_append hprefix tailTrace_238792
  have hstable : (prefixWord ++ tailWord_238792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238792).length < 2 ^ (prefixWord ++ tailWord_238792).sum := by decide
  have hdescent : baseEnd_238792 < baseStart_238792 := by decide
  rcases family_descends (prefixWord ++ tailWord_238792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238820 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_238820 : Nat := 118140960795 + 238820 * 2 ^ 59
def prefixEnd_238820 : Nat := 4983230072969 + 3 ^ 40 * 238820 * 2
def baseEnd_238820 : Nat := 81752966604573899567795

theorem tailTrace_238820 : CollatzResearch.WordTrace tailWord_238820 prefixEnd_238820 81752966604573899567795 := by
  unfold tailWord_238820
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355240497401701026936957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5806987329868934702582609 4355240497401701026936957)
  ·
    refine ⟨1633215186525637885101359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4355240497401701026936957 1633215186525637885101359)
    ·
      refine ⟨2449822779788456827652039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633215186525637885101359 2449822779788456827652039)
      ·
        refine ⟨3674734169682685241478059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449822779788456827652039 3674734169682685241478059)
        ·
          refine ⟨5512101254524027862217089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3674734169682685241478059 5512101254524027862217089)
          ·
            refine ⟨4134075940893020896662817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5512101254524027862217089 4134075940893020896662817)
            ·
              refine ⟨3100556955669765672497113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4134075940893020896662817 3100556955669765672497113)
              ·
                refine ⟨2325417716752324254372835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100556955669765672497113 2325417716752324254372835)
                ·
                  refine ⟨3488126575128486381559253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325417716752324254372835 3488126575128486381559253)
                  ·
                    refine ⟨81752966604573899567795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3488126575128486381559253 81752966604573899567795)
                    ·
                      rfl

theorem cell22_238820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_238820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238820 prefixEnd_238820 := by exact prefixLift 238820
  have htrace : WordTrace (prefixWord ++ tailWord_238820) baseStart_238820 baseEnd_238820 := by
    simpa [prefixWord, tailWord_238820, baseEnd_238820] using wordTrace_append hprefix tailTrace_238820
  have hstable : (prefixWord ++ tailWord_238820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238820).length < 2 ^ (prefixWord ++ tailWord_238820).sum := by decide
  have hdescent : baseEnd_238820 < baseStart_238820 := by decide
  rcases family_descends (prefixWord ++ tailWord_238820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238826 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 1, 3]
def baseStart_238826 : Nat := 118140960795 + 238826 * 2 ^ 59
def prefixEnd_238826 : Nat := 4983230072969 + 3 ^ 40 * 238826 * 2
def baseEnd_238826 : Nat := 81755020527191883917777

theorem tailTrace_238826 : CollatzResearch.WordTrace tailWord_238826 prefixEnd_238826 81755020527191883917777 := by
  unfold tailWord_238826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177674958195416269648083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5807133221854443385728221 2177674958195416269648083)
  ·
    refine ⟨3266512437293124404472125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2177674958195416269648083 3266512437293124404472125)
    ·
      refine ⟨1224942163984921651677047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3266512437293124404472125 1224942163984921651677047)
      ·
        refine ⟨1837413245977382477515571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1224942163984921651677047 1837413245977382477515571)
        ·
          refine ⟨2756119868966073716273357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1837413245977382477515571 2756119868966073716273357)
          ·
            refine ⟨1033544950862277643602509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2756119868966073716273357 1033544950862277643602509)
            ·
              refine ⟨387579356573354116350941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033544950862277643602509 387579356573354116350941)
              ·
                refine ⟨145342258715007793631603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 387579356573354116350941 145342258715007793631603)
                ·
                  refine ⟨218013388072511690447405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145342258715007793631603 218013388072511690447405)
                  ·
                    refine ⟨81755020527191883917777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218013388072511690447405 81755020527191883917777)
                    ·
                      rfl

theorem cell22_238826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_238826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238826 prefixEnd_238826 := by exact prefixLift 238826
  have htrace : WordTrace (prefixWord ++ tailWord_238826) baseStart_238826 baseEnd_238826 := by
    simpa [prefixWord, tailWord_238826, baseEnd_238826] using wordTrace_append hprefix tailTrace_238826
  have hstable : (prefixWord ++ tailWord_238826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238826).length < 2 ^ (prefixWord ++ tailWord_238826).sum := by decide
  have hdescent : baseEnd_238826 < baseStart_238826 := by decide
  rcases family_descends (prefixWord ++ tailWord_238826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238856 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 5]
def baseStart_238856 : Nat := 118140960795 + 238856 * 2 ^ 59
def prefixEnd_238856 : Nat := 4983230072969 + 3 ^ 40 * 238856 * 2
def baseEnd_238856 : Nat := 27255096713427268555895

theorem tailTrace_238856 : CollatzResearch.WordTrace tailWord_238856 prefixEnd_238856 27255096713427268555895 := by
  unfold tailWord_238856
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355897011336490101092211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5807862681781986801456281 4355897011336490101092211)
  ·
    refine ⟨6533845517004735151638317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4355897011336490101092211 6533845517004735151638317)
    ·
      refine ⟨2450192068876775681864369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6533845517004735151638317 2450192068876775681864369)
      ·
        refine ⟨1837644051657581761398277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2450192068876775681864369 1837644051657581761398277)
        ·
          refine ⟨344558259685796580262177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1837644051657581761398277 344558259685796580262177)
          ·
            refine ⟨258418694764347435196633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 344558259685796580262177 258418694764347435196633)
            ·
              refine ⟨193814021073260576397475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258418694764347435196633 193814021073260576397475)
              ·
                refine ⟨290721031609890864596213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193814021073260576397475 290721031609890864596213)
                ·
                  refine ⟨27255096713427268555895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290721031609890864596213 27255096713427268555895)
                  ·
                    rfl

theorem cell22_238856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 5].length) (baseStart_238856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238856 prefixEnd_238856 := by exact prefixLift 238856
  have htrace : WordTrace (prefixWord ++ tailWord_238856) baseStart_238856 baseEnd_238856 := by
    simpa [prefixWord, tailWord_238856, baseEnd_238856] using wordTrace_append hprefix tailTrace_238856
  have hstable : (prefixWord ++ tailWord_238856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238856).length < 2 ^ (prefixWord ++ tailWord_238856).sum := by decide
  have hdescent : baseEnd_238856 < baseStart_238856 := by decide
  rcases family_descends (prefixWord ++ tailWord_238856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238884 : List Nat := [2, 3, 1, 3, 1, 1, 2, 5, 4]
def baseStart_238884 : Nat := 118140960795 + 238884 * 2 ^ 59
def prefixEnd_238884 : Nat := 4983230072969 + 3 ^ 40 * 238884 * 2
def baseEnd_238884 : Nat := 27258291704166355322533

theorem tailTrace_238884 : CollatzResearch.WordTrace tailWord_238884 prefixEnd_238884 27258291704166355322533 := by
  unfold tailWord_238884
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356407633285770492101853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5808543511047693989469137 4356407633285770492101853)
  ·
    refine ⟨1633652862482163934538195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4356407633285770492101853 1633652862482163934538195)
    ·
      refine ⟨2450479293723245901807293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633652862482163934538195 2450479293723245901807293)
      ·
        refine ⟨918929735146217213177735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2450479293723245901807293 918929735146217213177735)
        ·
          refine ⟨1378394602719325819766603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918929735146217213177735 1378394602719325819766603)
          ·
            refine ⟨2067591904078988729649905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1378394602719325819766603 2067591904078988729649905)
            ·
              refine ⟨1550693928059241547237429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2067591904078988729649905 1550693928059241547237429)
              ·
                refine ⟨145377555755553895053509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1550693928059241547237429 145377555755553895053509)
                ·
                  refine ⟨27258291704166355322533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145377555755553895053509 27258291704166355322533)
                  ·
                    rfl

theorem cell22_238884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_238884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238884 prefixEnd_238884 := by exact prefixLift 238884
  have htrace : WordTrace (prefixWord ++ tailWord_238884) baseStart_238884 baseEnd_238884 := by
    simpa [prefixWord, tailWord_238884, baseEnd_238884] using wordTrace_append hprefix tailTrace_238884
  have hstable : (prefixWord ++ tailWord_238884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238884).length < 2 ^ (prefixWord ++ tailWord_238884).sum := by decide
  have hdescent : baseEnd_238884 < baseStart_238884 := by decide
  rcases family_descends (prefixWord ++ tailWord_238884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238899 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 2, 3]
def baseStart_238899 : Nat := 118140960795 + 238899 * 2 ^ 59
def prefixEnd_238899 : Nat := 4983230072969 + 3 ^ 40 * 238899 * 2
def baseEnd_238899 : Nat := 81780009919044026842553

theorem tailTrace_238899 : CollatzResearch.WordTrace tailWord_238899 prefixEnd_238899 81780009919044026842553 := by
  unfold tailWord_238899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713362361517198545999751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5808908241011465697333167 8713362361517198545999751)
  ·
    refine ⟨13070043542275797818999627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8713362361517198545999751 13070043542275797818999627)
    ·
      refine ⟨19605065313413696728499441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13070043542275797818999627 19605065313413696728499441)
      ·
        refine ⟨14703798985060272546374581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19605065313413696728499441 14703798985060272546374581)
        ·
          refine ⟨1378481154849400551222617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14703798985060272546374581 1378481154849400551222617)
          ·
            refine ⟨1033860866137050413416963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378481154849400551222617 1033860866137050413416963)
            ·
              refine ⟨1550791299205575620125445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1033860866137050413416963 1550791299205575620125445)
              ·
                refine ⟨290773368601045428773521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1550791299205575620125445 290773368601045428773521)
                ·
                  refine ⟨218080026450784071580141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 290773368601045428773521 218080026450784071580141)
                  ·
                    refine ⟨81780009919044026842553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218080026450784071580141 81780009919044026842553)
                    ·
                      rfl

theorem cell22_238899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 3].length) (baseStart_238899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238899 prefixEnd_238899 := by exact prefixLift 238899
  have htrace : WordTrace (prefixWord ++ tailWord_238899) baseStart_238899 baseEnd_238899 := by
    simpa [prefixWord, tailWord_238899, baseEnd_238899] using wordTrace_append hprefix tailTrace_238899
  have hstable : (prefixWord ++ tailWord_238899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238899).length < 2 ^ (prefixWord ++ tailWord_238899).sum := by decide
  have hdescent : baseEnd_238899 < baseStart_238899 := by decide
  rcases family_descends (prefixWord ++ tailWord_238899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238901 : List Nat := [1, 3, 3, 1, 2, 2, 4, 2, 4]
def baseStart_238901 : Nat := 118140960795 + 238901 * 2 ^ 59
def prefixEnd_238901 : Nat := 4983230072969 + 3 ^ 40 * 238901 * 2
def baseEnd_238901 : Nat := 27260231519972229430849

theorem tailTrace_238901 : CollatzResearch.WordTrace tailWord_238901 prefixEnd_238901 27260231519972229430849 := by
  unfold tailWord_238901
  simp only [CollatzResearch.WordTrace]
  refine ⟨8713435307509952887572557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5808956871673301925048371 8713435307509952887572557)
  ·
    refine ⟨3267538240316232332839709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8713435307509952887572557 3267538240316232332839709)
    ·
      refine ⟨1225326840118587124814891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3267538240316232332839709 1225326840118587124814891)
      ·
        refine ⟨1837990260177880687222337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1225326840118587124814891 1837990260177880687222337)
        ·
          refine ⟨1378492695133410515416753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1837990260177880687222337 1378492695133410515416753)
          ·
            refine ⟨1033869521350057886562565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378492695133410515416753 1033869521350057886562565)
            ·
              refine ⟨193850535253135853730481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1033869521350057886562565 193850535253135853730481)
              ·
                refine ⟨145387901439851890297861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193850535253135853730481 145387901439851890297861)
                ·
                  refine ⟨27260231519972229430849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145387901439851890297861 27260231519972229430849)
                  ·
                    rfl

theorem cell22_238901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 4].length) (baseStart_238901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238901 prefixEnd_238901 := by exact prefixLift 238901
  have htrace : WordTrace (prefixWord ++ tailWord_238901) baseStart_238901 baseEnd_238901 := by
    simpa [prefixWord, tailWord_238901, baseEnd_238901] using wordTrace_append hprefix tailTrace_238901
  have hstable : (prefixWord ++ tailWord_238901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238901).length < 2 ^ (prefixWord ++ tailWord_238901).sum := by decide
  have hdescent : baseEnd_238901 < baseStart_238901 := by decide
  rcases family_descends (prefixWord ++ tailWord_238901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238916 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_238916 : Nat := 118140960795 + 238916 * 2 ^ 59
def prefixEnd_238916 : Nat := 4983230072969 + 3 ^ 40 * 238916 * 2
def baseEnd_238916 : Nat := 81785829366461649167501

theorem tailTrace_238916 : CollatzResearch.WordTrace tailWord_238916 prefixEnd_238916 81785829366461649167501 := by
  unfold tailWord_238916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356991201227805224684301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5809321601637073632912401 4356991201227805224684301)
  ·
    refine ⟨1633871700460426959256613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4356991201227805224684301 1633871700460426959256613)
    ·
      refine ⟨306350943836330054860615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1633871700460426959256613 306350943836330054860615)
      ·
        refine ⟨459526415754495082290923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306350943836330054860615 459526415754495082290923)
        ·
          refine ⟨689289623631742623436385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459526415754495082290923 689289623631742623436385)
          ·
            refine ⟨516967217723806967577289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689289623631742623436385 516967217723806967577289)
            ·
              refine ⟨387725413292855225682967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 516967217723806967577289 387725413292855225682967)
              ·
                refine ⟨581588119939282838524451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387725413292855225682967 581588119939282838524451)
                ·
                  refine ⟨872382179908924257786677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 581588119939282838524451 872382179908924257786677)
                  ·
                    refine ⟨81785829366461649167501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 872382179908924257786677 81785829366461649167501)
                    ·
                      rfl

theorem cell22_238916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_238916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238916 prefixEnd_238916 := by exact prefixLift 238916
  have htrace : WordTrace (prefixWord ++ tailWord_238916) baseStart_238916 baseEnd_238916 := by
    simpa [prefixWord, tailWord_238916, baseEnd_238916] using wordTrace_append hprefix tailTrace_238916
  have hstable : (prefixWord ++ tailWord_238916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238916).length < 2 ^ (prefixWord ++ tailWord_238916).sum := by decide
  have hdescent : baseEnd_238916 < baseStart_238916 := by decide
  rcases family_descends (prefixWord ++ tailWord_238916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238918 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_238918 : Nat := 118140960795 + 238918 * 2 ^ 59
def prefixEnd_238918 : Nat := 4983230072969 + 3 ^ 40 * 238918 * 2
def baseEnd_238918 : Nat := 27262171335778103539165

theorem tailTrace_238918 : CollatzResearch.WordTrace tailWord_238918 prefixEnd_238918 27262171335778103539165 := by
  unfold tailWord_238918
  simp only [CollatzResearch.WordTrace]
  refine ⟨272314229639011399716919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5809370232298909860627605 272314229639011399716919)
  ·
    refine ⟨408471344458517099575379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272314229639011399716919 408471344458517099575379)
    ·
      refine ⟨612707016687775649363069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408471344458517099575379 612707016687775649363069)
      ·
        refine ⟨229765131257915868511151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 612707016687775649363069 229765131257915868511151)
        ·
          refine ⟨344647696886873802766727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229765131257915868511151 344647696886873802766727)
          ·
            refine ⟨516971545330310704150091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344647696886873802766727 516971545330310704150091)
            ·
              refine ⟨775457317995466056225137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 516971545330310704150091 775457317995466056225137)
              ·
                refine ⟨581592988496599542168853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775457317995466056225137 581592988496599542168853)
                ·
                  refine ⟨27262171335778103539165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 581592988496599542168853 27262171335778103539165)
                  ·
                    rfl

theorem cell22_238918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_238918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238918 prefixEnd_238918 := by exact prefixLift 238918
  have htrace : WordTrace (prefixWord ++ tailWord_238918) baseStart_238918 baseEnd_238918 := by
    simpa [prefixWord, tailWord_238918, baseEnd_238918] using wordTrace_append hprefix tailTrace_238918
  have hstable : (prefixWord ++ tailWord_238918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238918).length < 2 ^ (prefixWord ++ tailWord_238918).sum := by decide
  have hdescent : baseEnd_238918 < baseStart_238918 := by decide
  rcases family_descends (prefixWord ++ tailWord_238918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238961 : List Nat := [1, 2, 2, 2, 1, 2, 4, 4, 1, 3]
def baseStart_238961 : Nat := 118140960795 + 238961 * 2 ^ 59
def prefixEnd_238961 : Nat := 4983230072969 + 3 ^ 40 * 238961 * 2
def baseEnd_238961 : Nat := 81801233786096531792363

theorem tailTrace_238961 : CollatzResearch.WordTrace tailWord_238961 prefixEnd_238961 81801233786096531792363 := by
  unfold tailWord_238961
  simp only [CollatzResearch.WordTrace]
  refine ⟨8715623687292583134756737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5810415791528388756504491 8715623687292583134756737)
  ·
    refine ⟨6536717765469437351067553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8715623687292583134756737 6536717765469437351067553)
    ·
      refine ⟨4902538324102078013300665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6536717765469437351067553 4902538324102078013300665)
      ·
        refine ⟨3676903743076558509975499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4902538324102078013300665 3676903743076558509975499)
        ·
          refine ⟨5515355614614837764963249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676903743076558509975499 5515355614614837764963249)
          ·
            refine ⟨4136516710961128323722437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5515355614614837764963249 4136516710961128323722437)
            ·
              refine ⟨775596883305211560697957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4136516710961128323722437 775596883305211560697957)
              ·
                refine ⟨145424415619727167630867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 775596883305211560697957 145424415619727167630867)
                ·
                  refine ⟨218136623429590751446301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145424415619727167630867 218136623429590751446301)
                  ·
                    refine ⟨81801233786096531792363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218136623429590751446301 81801233786096531792363)
                    ·
                      rfl

theorem cell22_238961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_238961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238961 prefixEnd_238961 := by exact prefixLift 238961
  have htrace : WordTrace (prefixWord ++ tailWord_238961) baseStart_238961 baseEnd_238961 := by
    simpa [prefixWord, tailWord_238961, baseEnd_238961] using wordTrace_append hprefix tailTrace_238961
  have hstable : (prefixWord ++ tailWord_238961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238961).length < 2 ^ (prefixWord ++ tailWord_238961).sum := by decide
  have hdescent : baseEnd_238961 < baseStart_238961 := by decide
  rcases family_descends (prefixWord ++ tailWord_238961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238972 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_238972 : Nat := 118140960795 + 238972 * 2 ^ 59
def prefixEnd_238972 : Nat := 4983230072969 + 3 ^ 40 * 238972 * 2
def baseEnd_238972 : Nat := 81804999310896169767329

theorem tailTrace_238972 : CollatzResearch.WordTrace tailWord_238972 prefixEnd_238972 81804999310896169767329 := by
  unfold tailWord_238972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358012445126366006703585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5810683260168488008938113 4358012445126366006703585)
  ·
    refine ⟨3268509333844774505027689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4358012445126366006703585 3268509333844774505027689)
    ·
      refine ⟨2451382000383580878770767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3268509333844774505027689 2451382000383580878770767)
      ·
        refine ⟨3677073000575371318156151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451382000383580878770767 3677073000575371318156151)
        ·
          refine ⟨5515609500863056977234227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677073000575371318156151 5515609500863056977234227)
          ·
            refine ⟨8273414251294585465851341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515609500863056977234227 8273414251294585465851341)
            ·
              refine ⟨3102530344235469549694253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8273414251294585465851341 3102530344235469549694253)
              ·
                refine ⟨1163448879088301081135345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3102530344235469549694253 1163448879088301081135345)
                ·
                  refine ⟨872586659316225810851509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1163448879088301081135345 872586659316225810851509)
                  ·
                    refine ⟨81804999310896169767329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 872586659316225810851509 81804999310896169767329)
                    ·
                      rfl

theorem cell22_238972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_238972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238972 prefixEnd_238972 := by exact prefixLift 238972
  have htrace : WordTrace (prefixWord ++ tailWord_238972) baseStart_238972 baseEnd_238972 := by
    simpa [prefixWord, tailWord_238972, baseEnd_238972] using wordTrace_append hprefix tailTrace_238972
  have hstable : (prefixWord ++ tailWord_238972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238972).length < 2 ^ (prefixWord ++ tailWord_238972).sum := by decide
  have hdescent : baseEnd_238972 < baseStart_238972 := by decide
  rcases family_descends (prefixWord ++ tailWord_238972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_238978 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_238978 : Nat := 118140960795 + 238978 * 2 ^ 59
def prefixEnd_238978 : Nat := 4983230072969 + 3 ^ 40 * 238978 * 2
def baseEnd_238978 : Nat := 81807053233514154117311

theorem tailTrace_238978 : CollatzResearch.WordTrace tailWord_238978 prefixEnd_238978 81807053233514154117311 := by
  unfold tailWord_238978
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179060932057748759531397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5810829152153996692083725 2179060932057748759531397)
  ·
    refine ⟨408573924760827892412137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2179060932057748759531397 408573924760827892412137)
    ·
      refine ⟨306430443570620919309103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 408573924760827892412137 306430443570620919309103)
      ·
        refine ⟨459645665355931378963655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 306430443570620919309103 459645665355931378963655)
        ·
          refine ⟨689468498033897068445483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459645665355931378963655 689468498033897068445483)
          ·
            refine ⟨1034202747050845602668225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689468498033897068445483 1034202747050845602668225)
            ·
              refine ⟨775652060288134202001169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1034202747050845602668225 775652060288134202001169)
              ·
                refine ⟨581739045216100651500877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 775652060288134202001169 581739045216100651500877)
                ·
                  refine ⟨218152141956037744312829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 581739045216100651500877 218152141956037744312829)
                  ·
                    refine ⟨81807053233514154117311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218152141956037744312829 81807053233514154117311)
                    ·
                      rfl

theorem cell22_238978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_238978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_238978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_238978 prefixEnd_238978 := by exact prefixLift 238978
  have htrace : WordTrace (prefixWord ++ tailWord_238978) baseStart_238978 baseEnd_238978 := by
    simpa [prefixWord, tailWord_238978, baseEnd_238978] using wordTrace_append hprefix tailTrace_238978
  have hstable : (prefixWord ++ tailWord_238978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_238978).length < 2 ^ (prefixWord ++ tailWord_238978).sum := by decide
  have hdescent : baseEnd_238978 < baseStart_238978 := by decide
  rcases family_descends (prefixWord ++ tailWord_238978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239032 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_239032 : Nat := 118140960795 + 239032 * 2 ^ 59
def prefixEnd_239032 : Nat := 4983230072969 + 3 ^ 40 * 239032 * 2
def baseEnd_239032 : Nat := 81825538537076013267145

theorem tailTrace_239032 : CollatzResearch.WordTrace tailWord_239032 prefixEnd_239032 81825538537076013267145 := by
  unfold tailWord_239032
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359106635017681130295675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5812142180023574840394233 4359106635017681130295675)
  ·
    refine ⟨6538659952526521695443513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4359106635017681130295675 6538659952526521695443513)
    ·
      refine ⟨4903994964394891271582635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6538659952526521695443513 4903994964394891271582635)
      ·
        refine ⟨7355992446592336907373953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903994964394891271582635 7355992446592336907373953)
        ·
          refine ⟨5516994334944252680530465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7355992446592336907373953 5516994334944252680530465)
          ·
            refine ⟨4137745751208189510397849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516994334944252680530465 4137745751208189510397849)
            ·
              refine ⟨3103309313406142132798387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137745751208189510397849 3103309313406142132798387)
              ·
                refine ⟨4654963970109213199197581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103309313406142132798387 4654963970109213199197581)
                ·
                  refine ⟨1745611488790954949699093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4654963970109213199197581 1745611488790954949699093)
                  ·
                    refine ⟨81825538537076013267145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1745611488790954949699093 81825538537076013267145)
                    ·
                      rfl

theorem cell22_239032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_239032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239032 prefixEnd_239032 := by exact prefixLift 239032
  have htrace : WordTrace (prefixWord ++ tailWord_239032) baseStart_239032 baseEnd_239032 := by
    simpa [prefixWord, tailWord_239032, baseEnd_239032] using wordTrace_append hprefix tailTrace_239032
  have hstable : (prefixWord ++ tailWord_239032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239032).length < 2 ^ (prefixWord ++ tailWord_239032).sum := by decide
  have hdescent : baseEnd_239032 < baseStart_239032 := by decide
  rcases family_descends (prefixWord ++ tailWord_239032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239047 : List Nat := [1, 1, 4, 1, 1, 3, 1, 10]
def baseStart_239047 : Nat := 118140960795 + 239047 * 2 ^ 59
def prefixEnd_239047 : Nat := 4983230072969 + 3 ^ 40 * 239047 * 2
def baseEnd_239047 : Nat := 9092297038180108238011

theorem tailTrace_239047 : CollatzResearch.WordTrace tailWord_239047 prefixEnd_239047 9092297038180108238011 := by
  unfold tailWord_239047
  simp only [CollatzResearch.WordTrace]
  refine ⟨8718760364981019822387395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5812506909987346548258263 8718760364981019822387395)
  ·
    refine ⟨13078140547471529733581093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8718760364981019822387395 13078140547471529733581093)
    ·
      refine ⟨2452151352650911825046455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13078140547471529733581093 2452151352650911825046455)
      ·
        refine ⟨3678227028976367737569683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2452151352650911825046455 3678227028976367737569683)
        ·
          refine ⟨5517340543464551606354525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678227028976367737569683 5517340543464551606354525)
          ·
            refine ⟨2069002703799206852382947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5517340543464551606354525 2069002703799206852382947)
            ·
              refine ⟨3103504055698810278574421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2069002703799206852382947 3103504055698810278574421)
              ·
                refine ⟨9092297038180108238011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3103504055698810278574421 9092297038180108238011)
                ·
                  rfl

theorem cell22_239047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 10].length) (baseStart_239047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239047 prefixEnd_239047 := by exact prefixLift 239047
  have htrace : WordTrace (prefixWord ++ tailWord_239047) baseStart_239047 baseEnd_239047 := by
    simpa [prefixWord, tailWord_239047, baseEnd_239047] using wordTrace_append hprefix tailTrace_239047
  have hstable : (prefixWord ++ tailWord_239047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239047).length < 2 ^ (prefixWord ++ tailWord_239047).sum := by decide
  have hdescent : baseEnd_239047 < baseStart_239047 := by decide
  rcases family_descends (prefixWord ++ tailWord_239047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239096 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 3, 3]
def baseStart_239096 : Nat := 118140960795 + 239096 * 2 ^ 59
def prefixEnd_239096 : Nat := 4983230072969 + 3 ^ 40 * 239096 * 2
def baseEnd_239096 : Nat := 81847447045001179666949

theorem tailTrace_239096 : CollatzResearch.WordTrace tailWord_239096 prefixEnd_239096 81847447045001179666949 := by
  unfold tailWord_239096
  simp only [CollatzResearch.WordTrace]
  refine ⟨4360273770901750595460571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5813698361202334127280761 4360273770901750595460571)
  ·
    refine ⟨6540410656352625893190857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4360273770901750595460571 6540410656352625893190857)
    ·
      refine ⟨4905307992264469419893143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6540410656352625893190857 4905307992264469419893143)
      ·
        refine ⟨7357961988396704129839715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905307992264469419893143 7357961988396704129839715)
        ·
          refine ⟨11036942982595056194759573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7357961988396704129839715 11036942982595056194759573)
          ·
            refine ⟨517356702309143259129355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11036942982595056194759573 517356702309143259129355)
            ·
              refine ⟨776035053463714888694033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517356702309143259129355 776035053463714888694033)
              ·
                refine ⟨582026290097786166520525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 776035053463714888694033 582026290097786166520525)
                ·
                  refine ⟨218259858786669812445197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 582026290097786166520525 218259858786669812445197)
                  ·
                    refine ⟨81847447045001179666949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218259858786669812445197 81847447045001179666949)
                    ·
                      rfl

theorem cell22_239096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 3, 3].length) (baseStart_239096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239096 prefixEnd_239096 := by exact prefixLift 239096
  have htrace : WordTrace (prefixWord ++ tailWord_239096) baseStart_239096 baseEnd_239096 := by
    simpa [prefixWord, tailWord_239096, baseEnd_239096] using wordTrace_append hprefix tailTrace_239096
  have hstable : (prefixWord ++ tailWord_239096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239096).length < 2 ^ (prefixWord ++ tailWord_239096).sum := by decide
  have hdescent : baseEnd_239096 < baseStart_239096 := by decide
  rcases family_descends (prefixWord ++ tailWord_239096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239113 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 1, 3]
def baseStart_239113 : Nat := 118140960795 + 239113 * 2 ^ 59
def prefixEnd_239113 : Nat := 4983230072969 + 3 ^ 40 * 239113 * 2
def baseEnd_239113 : Nat := 81853266492418801991897

theorem tailTrace_239113 : CollatzResearch.WordTrace tailWord_239113 prefixEnd_239113 81853266492418801991897 := by
  unfold tailWord_239113
  simp only [CollatzResearch.WordTrace]
  refine ⟨8721167582741913094289993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5814111721827942062859995 8721167582741913094289993)
  ·
    refine ⟨6540875687056434820717495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8721167582741913094289993 6540875687056434820717495)
    ·
      refine ⟨9811313530584652231076243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6540875687056434820717495 9811313530584652231076243)
      ·
        refine ⟨14716970295876978346614365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811313530584652231076243 14716970295876978346614365)
        ·
          refine ⟨5518863860953866879980387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14716970295876978346614365 5518863860953866879980387)
          ·
            refine ⟨8278295791430800319970581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518863860953866879980387 8278295791430800319970581)
            ·
              refine ⟨388045115223318764998621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8278295791430800319970581 388045115223318764998621)
              ·
                refine ⟨145516918208744536874483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388045115223318764998621 145516918208744536874483)
                ·
                  refine ⟨218275377313116805311725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145516918208744536874483 218275377313116805311725)
                  ·
                    refine ⟨81853266492418801991897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218275377313116805311725 81853266492418801991897)
                    ·
                      rfl

theorem cell22_239113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_239113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239113 prefixEnd_239113 := by exact prefixLift 239113
  have htrace : WordTrace (prefixWord ++ tailWord_239113) baseStart_239113 baseEnd_239113 := by
    simpa [prefixWord, tailWord_239113, baseEnd_239113] using wordTrace_append hprefix tailTrace_239113
  have hstable : (prefixWord ++ tailWord_239113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239113).length < 2 ^ (prefixWord ++ tailWord_239113).sum := by decide
  have hdescent : baseEnd_239113 < baseStart_239113 := by decide
  rcases family_descends (prefixWord ++ tailWord_239113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239203 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 2, 3]
def baseStart_239203 : Nat := 118140960795 + 239203 * 2 ^ 59
def prefixEnd_239203 : Nat := 4983230072969 + 3 ^ 40 * 239203 * 2
def baseEnd_239203 : Nat := 81884075331688567241621

theorem tailTrace_239203 : CollatzResearch.WordTrace tailWord_239203 prefixEnd_239203 81884075331688567241621 := by
  unfold tailWord_239203
  simp only [CollatzResearch.WordTrace]
  refine ⟨8724450152415858465066263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5816300101610572310044175 8724450152415858465066263)
  ·
    refine ⟨13086675228623787697599395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8724450152415858465066263 13086675228623787697599395)
    ·
      refine ⟨19630012842935681546399093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13086675228623787697599395 19630012842935681546399093)
      ·
        refine ⟨1840313704025220144974915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19630012842935681546399093 1840313704025220144974915)
        ·
          refine ⟨2760470556037830217462373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1840313704025220144974915 2760470556037830217462373)
          ·
            refine ⟨517588229257093165774195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2760470556037830217462373 517588229257093165774195)
            ·
              refine ⟨776382343885639748661293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 517588229257093165774195 776382343885639748661293)
              ·
                refine ⟨291143378957114905747985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 776382343885639748661293 291143378957114905747985)
                ·
                  refine ⟨218357534217836179310989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291143378957114905747985 218357534217836179310989)
                  ·
                    refine ⟨81884075331688567241621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218357534217836179310989 81884075331688567241621)
                    ·
                      rfl

theorem cell22_239203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3].length) (baseStart_239203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239203 prefixEnd_239203 := by exact prefixLift 239203
  have htrace : WordTrace (prefixWord ++ tailWord_239203) baseStart_239203 baseEnd_239203 := by
    simpa [prefixWord, tailWord_239203, baseEnd_239203] using wordTrace_append hprefix tailTrace_239203
  have hstable : (prefixWord ++ tailWord_239203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239203).length < 2 ^ (prefixWord ++ tailWord_239203).sum := by decide
  have hdescent : baseEnd_239203 < baseStart_239203 := by decide
  rcases family_descends (prefixWord ++ tailWord_239203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239218 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_239218 : Nat := 118140960795 + 239218 * 2 ^ 59
def prefixEnd_239218 : Nat := 4983230072969 + 3 ^ 40 * 239218 * 2
def baseEnd_239218 : Nat := 81889210138233528116575

theorem tailTrace_239218 : CollatzResearch.WordTrace tailWord_239218 prefixEnd_239218 81889210138233528116575 := by
  unfold tailWord_239218
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181249311840379006715577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5816664831574344017908205 2181249311840379006715577)
  ·
    refine ⟨1635936983880284255036683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181249311840379006715577 1635936983880284255036683)
    ·
      refine ⟨2453905475820426382555025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1635936983880284255036683 2453905475820426382555025)
      ·
        refine ⟨1840429106865319786916269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2453905475820426382555025 1840429106865319786916269)
        ·
          refine ⟨690160915074494920093601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1840429106865319786916269 690160915074494920093601)
          ·
            refine ⟨517620686305871190070201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 690160915074494920093601 517620686305871190070201)
            ·
              refine ⟨388215514729403392552651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 517620686305871190070201 388215514729403392552651)
              ·
                refine ⟨582323272094105088828977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 388215514729403392552651 582323272094105088828977)
                ·
                  refine ⟨436742454070578816621733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 582323272094105088828977 436742454070578816621733)
                  ·
                    refine ⟨81889210138233528116575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 436742454070578816621733 81889210138233528116575)
                    ·
                      rfl

theorem cell22_239218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_239218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239218 prefixEnd_239218 := by exact prefixLift 239218
  have htrace : WordTrace (prefixWord ++ tailWord_239218) baseStart_239218 baseEnd_239218 := by
    simpa [prefixWord, tailWord_239218, baseEnd_239218] using wordTrace_append hprefix tailTrace_239218
  have hstable : (prefixWord ++ tailWord_239218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239218).length < 2 ^ (prefixWord ++ tailWord_239218).sum := by decide
  have hdescent : baseEnd_239218 < baseStart_239218 := by decide
  rcases family_descends (prefixWord ++ tailWord_239218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239246 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_239246 : Nat := 118140960795 + 239246 * 2 ^ 59
def prefixEnd_239246 : Nat := 4983230072969 + 3 ^ 40 * 239246 * 2
def baseEnd_239246 : Nat := 81898795110450788416489

theorem tailTrace_239246 : CollatzResearch.WordTrace tailWord_239246 prefixEnd_239246 81898795110450788416489 := by
  unfold tailWord_239246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090752311407509601110199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5817345660840051205921061 1090752311407509601110199)
  ·
    refine ⟨1636128467111264401665299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1090752311407509601110199 1636128467111264401665299)
    ·
      refine ⟨2454192700666896602497949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1636128467111264401665299 2454192700666896602497949)
      ·
        refine ⟨920322262750086225936731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2454192700666896602497949 920322262750086225936731)
        ·
          refine ⟨1380483394125129338905097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 920322262750086225936731 1380483394125129338905097)
          ·
            refine ⟨1035362545593847004178823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1380483394125129338905097 1035362545593847004178823)
            ·
              refine ⟨1553043818390770506268235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1035362545593847004178823 1553043818390770506268235)
              ·
                refine ⟨2329565727586155759402353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1553043818390770506268235 2329565727586155759402353)
                ·
                  refine ⟨1747174295689616819551765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2329565727586155759402353 1747174295689616819551765)
                  ·
                    refine ⟨81898795110450788416489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1747174295689616819551765 81898795110450788416489)
                    ·
                      rfl

theorem cell22_239246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_239246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239246 prefixEnd_239246 := by exact prefixLift 239246
  have htrace : WordTrace (prefixWord ++ tailWord_239246) baseStart_239246 baseEnd_239246 := by
    simpa [prefixWord, tailWord_239246, baseEnd_239246] using wordTrace_append hprefix tailTrace_239246
  have hstable : (prefixWord ++ tailWord_239246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239246).length < 2 ^ (prefixWord ++ tailWord_239246).sum := by decide
  have hdescent : baseEnd_239246 < baseStart_239246 := by decide
  rcases family_descends (prefixWord ++ tailWord_239246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239250 : List Nat := [3, 2, 3, 1, 4, 1, 1, 7]
def baseStart_239250 : Nat := 118140960795 + 239250 * 2 ^ 59
def prefixEnd_239250 : Nat := 4983230072969 + 3 ^ 40 * 239250 * 2
def baseEnd_239250 : Nat := 9100018265799567924053

theorem tailTrace_239250 : CollatzResearch.WordTrace tailWord_239250 prefixEnd_239250 9100018265799567924053 := by
  unfold tailWord_239250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181541095811396373006801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5817442922163723661351469 2181541095811396373006801)
  ·
    refine ⟨1636155821858547279755101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181541095811396373006801 1636155821858547279755101)
    ·
      refine ⟨613558433196955229908163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1636155821858547279755101 613558433196955229908163)
      ·
        refine ⟨920337649795432844862245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 613558433196955229908163 920337649795432844862245)
        ·
          refine ⟨172563309336643658411671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 920337649795432844862245 172563309336643658411671)
          ·
            refine ⟨258844964004965487617507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172563309336643658411671 258844964004965487617507)
            ·
              refine ⟨388267446007448231426261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258844964004965487617507 388267446007448231426261)
              ·
                refine ⟨9100018265799567924053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 388267446007448231426261 9100018265799567924053)
                ·
                  rfl

theorem cell22_239250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_239250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239250 prefixEnd_239250 := by exact prefixLift 239250
  have htrace : WordTrace (prefixWord ++ tailWord_239250) baseStart_239250 baseEnd_239250 := by
    simpa [prefixWord, tailWord_239250, baseEnd_239250] using wordTrace_append hprefix tailTrace_239250
  have hstable : (prefixWord ++ tailWord_239250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239250).length < 2 ^ (prefixWord ++ tailWord_239250).sum := by decide
  have hdescent : baseEnd_239250 < baseStart_239250 := by decide
  rcases family_descends (prefixWord ++ tailWord_239250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239338 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_239338 : Nat := 118140960795 + 239338 * 2 ^ 59
def prefixEnd_239338 : Nat := 4983230072969 + 3 ^ 40 * 239338 * 2
def baseEnd_239338 : Nat := 81930288590593215116207

theorem tailTrace_239338 : CollatzResearch.WordTrace tailWord_239338 prefixEnd_239338 81930288590593215116207 := by
  unfold tailWord_239338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2182343501731694130307667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5819582671284517680820445 2182343501731694130307667)
  ·
    refine ⟨3273515252597541195461501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2182343501731694130307667 3273515252597541195461501)
    ·
      refine ⟨1227568219724077948298063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3273515252597541195461501 1227568219724077948298063)
      ·
        refine ⟨1841352329586116922447095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227568219724077948298063 1841352329586116922447095)
        ·
          refine ⟨2762028494379175383670643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841352329586116922447095 2762028494379175383670643)
          ·
            refine ⟨4143042741568763075505965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2762028494379175383670643 4143042741568763075505965)
            ·
              refine ⟨1553641028088286153314737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4143042741568763075505965 1553641028088286153314737)
              ·
                refine ⟨1165230771066214614986053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1553641028088286153314737 1165230771066214614986053)
                ·
                  refine ⟨218480769574915240309885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1165230771066214614986053 218480769574915240309885)
                  ·
                    refine ⟨81930288590593215116207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218480769574915240309885 81930288590593215116207)
                    ·
                      rfl

theorem cell22_239338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_239338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239338 prefixEnd_239338 := by exact prefixLift 239338
  have htrace : WordTrace (prefixWord ++ tailWord_239338) baseStart_239338 baseEnd_239338 := by
    simpa [prefixWord, tailWord_239338, baseEnd_239338] using wordTrace_append hprefix tailTrace_239338
  have hstable : (prefixWord ++ tailWord_239338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239338).length < 2 ^ (prefixWord ++ tailWord_239338).sum := by decide
  have hdescent : baseEnd_239338 < baseStart_239338 := by decide
  rcases family_descends (prefixWord ++ tailWord_239338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239522 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_239522 : Nat := 118140960795 + 239522 * 2 ^ 59
def prefixEnd_239522 : Nat := 4983230072969 + 3 ^ 40 * 239522 * 2
def baseEnd_239522 : Nat := 81993275550878068515643

theorem tailTrace_239522 : CollatzResearch.WordTrace tailWord_239522 prefixEnd_239522 81993275550878068515643 := by
  unfold tailWord_239522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2184021259565043986482205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5824056692173450630619213 2184021259565043986482205)
  ·
    refine ⟨819007972336891494930827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2184021259565043986482205 819007972336891494930827)
    ·
      refine ⟨1228511958505337242396241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819007972336891494930827 1228511958505337242396241)
      ·
        refine ⟨921383968879002931797181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1228511958505337242396241 921383968879002931797181)
        ·
          refine ⟨345518988329626099423943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 921383968879002931797181 345518988329626099423943)
          ·
            refine ⟨518278482494439149135915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345518988329626099423943 518278482494439149135915)
            ·
              refine ⟨777417723741658723703873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518278482494439149135915 777417723741658723703873)
              ·
                refine ⟨583063292806244042777905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 777417723741658723703873 583063292806244042777905)
                ·
                  refine ⟨437297469604683032083429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 583063292806244042777905 437297469604683032083429)
                  ·
                    refine ⟨81993275550878068515643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437297469604683032083429 81993275550878068515643)
                    ·
                      rfl

theorem cell22_239522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_239522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239522 prefixEnd_239522 := by exact prefixLift 239522
  have htrace : WordTrace (prefixWord ++ tailWord_239522) baseStart_239522 baseEnd_239522 := by
    simpa [prefixWord, tailWord_239522, baseEnd_239522] using wordTrace_append hprefix tailTrace_239522
  have hstable : (prefixWord ++ tailWord_239522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239522).length < 2 ^ (prefixWord ++ tailWord_239522).sum := by decide
  have hdescent : baseEnd_239522 < baseStart_239522 := by decide
  rcases family_descends (prefixWord ++ tailWord_239522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239627 : List Nat := [1, 1, 1, 1, 6, 1, 4, 3, 4]
def baseStart_239627 : Nat := 118140960795 + 239627 * 2 ^ 59
def prefixEnd_239627 : Nat := 4983230072969 + 3 ^ 40 * 239627 * 2
def baseEnd_239627 : Nat := 27343073065564264880107

theorem tailTrace_239627 : CollatzResearch.WordTrace tailWord_239627 prefixEnd_239627 27343073065564264880107 := by
  unfold tailWord_239627
  simp only [CollatzResearch.WordTrace]
  refine ⟨8739914702879778878501135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5826609801919852585667423 8739914702879778878501135)
  ·
    refine ⟨13109872054319668317751703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8739914702879778878501135 13109872054319668317751703)
    ·
      refine ⟨19664808081479502476627555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13109872054319668317751703 19664808081479502476627555)
      ·
        refine ⟨29497212122219253714941333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19664808081479502476627555 29497212122219253714941333)
        ·
          refine ⟨1382681818229027517887875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29497212122219253714941333 1382681818229027517887875)
          ·
            refine ⟨2074022727343541276831813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382681818229027517887875 2074022727343541276831813)
            ·
              refine ⟨388879261376913989405965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2074022727343541276831813 388879261376913989405965)
              ·
                refine ⟨145829723016342746027237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388879261376913989405965 145829723016342746027237)
                ·
                  refine ⟨27343073065564264880107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145829723016342746027237 27343073065564264880107)
                  ·
                    rfl

theorem cell22_239627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 4].length) (baseStart_239627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239627 prefixEnd_239627 := by exact prefixLift 239627
  have htrace : WordTrace (prefixWord ++ tailWord_239627) baseStart_239627 baseEnd_239627 := by
    simpa [prefixWord, tailWord_239627, baseEnd_239627] using wordTrace_append hprefix tailTrace_239627
  have hstable : (prefixWord ++ tailWord_239627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239627).length < 2 ^ (prefixWord ++ tailWord_239627).sum := by decide
  have hdescent : baseEnd_239627 < baseStart_239627 := by decide
  rcases family_descends (prefixWord ++ tailWord_239627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239640 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_239640 : Nat := 118140960795 + 239640 * 2 ^ 59
def prefixEnd_239640 : Nat := 4983230072969 + 3 ^ 40 * 239640 * 2
def baseEnd_239640 : Nat := 82033669362365094065281

theorem tailTrace_239640 : CollatzResearch.WordTrace tailWord_239640 prefixEnd_239640 82033669362365094065281 := by
  unfold tailWord_239640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4370194425916341049362187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5826925901221788065816249 4370194425916341049362187)
  ·
    refine ⟨6555291638874511574043281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4370194425916341049362187 6555291638874511574043281)
    ·
      refine ⟨4916468729155883680532461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6555291638874511574043281 4916468729155883680532461)
      ·
        refine ⟨1843675773433456380199673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4916468729155883680532461 1843675773433456380199673)
        ·
          refine ⟨1382756830075092285149755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843675773433456380199673 1382756830075092285149755)
          ·
            refine ⟨2074135245112638427724633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382756830075092285149755 2074135245112638427724633)
            ·
              refine ⟨1555601433834478820793475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074135245112638427724633 1555601433834478820793475)
              ·
                refine ⟨2333402150751718231190213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555601433834478820793475 2333402150751718231190213)
                ·
                  refine ⟨437512903265947168348165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2333402150751718231190213 437512903265947168348165)
                  ·
                    refine ⟨82033669362365094065281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437512903265947168348165 82033669362365094065281)
                    ·
                      rfl

theorem cell22_239640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_239640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239640 prefixEnd_239640 := by exact prefixLift 239640
  have htrace : WordTrace (prefixWord ++ tailWord_239640) baseStart_239640 baseEnd_239640 := by
    simpa [prefixWord, tailWord_239640, baseEnd_239640] using wordTrace_append hprefix tailTrace_239640
  have hstable : (prefixWord ++ tailWord_239640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239640).length < 2 ^ (prefixWord ++ tailWord_239640).sum := by decide
  have hdescent : baseEnd_239640 < baseStart_239640 := by decide
  rcases family_descends (prefixWord ++ tailWord_239640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239642 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 4, 3]
def baseStart_239642 : Nat := 118140960795 + 239642 * 2 ^ 59
def prefixEnd_239642 : Nat := 4983230072969 + 3 ^ 40 * 239642 * 2
def baseEnd_239642 : Nat := 82034354003237755515275

theorem tailTrace_239642 : CollatzResearch.WordTrace tailWord_239642 prefixEnd_239642 82034354003237755515275 := by
  unfold tailWord_239642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185115449456359110074295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5826974531883624293531453 2185115449456359110074295)
  ·
    refine ⟨3277673174184538665111443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185115449456359110074295 3277673174184538665111443)
    ·
      refine ⟨4916509761276807997667165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3277673174184538665111443 4916509761276807997667165)
      ·
        refine ⟨1843691160478802999125187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4916509761276807997667165 1843691160478802999125187)
        ·
          refine ⟨2765536740718204498687781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843691160478802999125187 2765536740718204498687781)
          ·
            refine ⟨518538138884663343503959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2765536740718204498687781 518538138884663343503959)
            ·
              refine ⟨777807208326995015255939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518538138884663343503959 777807208326995015255939)
              ·
                refine ⟨1166710812490492522883909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 777807208326995015255939 1166710812490492522883909)
                ·
                  refine ⟨218758277341967348040733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1166710812490492522883909 218758277341967348040733)
                  ·
                    refine ⟨82034354003237755515275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218758277341967348040733 82034354003237755515275)
                    ·
                      rfl

theorem cell22_239642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_239642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239642 prefixEnd_239642 := by exact prefixLift 239642
  have htrace : WordTrace (prefixWord ++ tailWord_239642) baseStart_239642 baseEnd_239642 := by
    simpa [prefixWord, tailWord_239642, baseEnd_239642] using wordTrace_append hprefix tailTrace_239642
  have hstable : (prefixWord ++ tailWord_239642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239642).length < 2 ^ (prefixWord ++ tailWord_239642).sum := by decide
  have hdescent : baseEnd_239642 < baseStart_239642 := by decide
  rcases family_descends (prefixWord ++ tailWord_239642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239678 : List Nat := [4, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_239678 : Nat := 118140960795 + 239678 * 2 ^ 59
def prefixEnd_239678 : Nat := 4983230072969 + 3 ^ 40 * 239678 * 2
def baseEnd_239678 : Nat := 27348892512981887205055

theorem tailTrace_239678 : CollatzResearch.WordTrace tailWord_239678 prefixEnd_239678 27348892512981887205055 := by
  unfold tailWord_239678
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092721853211876823575961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5827849883796676392405125 1092721853211876823575961)
  ·
    refine ⟨819541389908907617681971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1092721853211876823575961 819541389908907617681971)
    ·
      refine ⟨1229312084863361426522957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819541389908907617681971 1229312084863361426522957)
      ·
        refine ⟨460992031823760534946109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1229312084863361426522957 460992031823760534946109)
        ·
          refine ⟨172872011933910200604791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460992031823760534946109 172872011933910200604791)
          ·
            refine ⟨259308017900865300907187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172872011933910200604791 259308017900865300907187)
            ·
              refine ⟨388962026851297951360781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259308017900865300907187 388962026851297951360781)
              ·
                refine ⟨145860760069236731760293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 388962026851297951360781 145860760069236731760293)
                ·
                  refine ⟨27348892512981887205055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145860760069236731760293 27348892512981887205055)
                  ·
                    rfl

theorem cell22_239678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_239678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239678 prefixEnd_239678 := by exact prefixLift 239678
  have htrace : WordTrace (prefixWord ++ tailWord_239678) baseStart_239678 baseEnd_239678 := by
    simpa [prefixWord, tailWord_239678, baseEnd_239678] using wordTrace_append hprefix tailTrace_239678
  have hstable : (prefixWord ++ tailWord_239678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239678).length < 2 ^ (prefixWord ++ tailWord_239678).sum := by decide
  have hdescent : baseEnd_239678 < baseStart_239678 := by decide
  rcases family_descends (prefixWord ++ tailWord_239678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239704 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_239704 : Nat := 118140960795 + 239704 * 2 ^ 59
def prefixEnd_239704 : Nat := 4983230072969 + 3 ^ 40 * 239704 * 2
def baseEnd_239704 : Nat := 82055577870290260465085

theorem tailTrace_239704 : CollatzResearch.WordTrace tailWord_239704 prefixEnd_239704 82055577870290260465085 := by
  unfold tailWord_239704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4371361561800410514527083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5828482082400547352702777 4371361561800410514527083)
  ·
    refine ⟨6557042342700615771790625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4371361561800410514527083 6557042342700615771790625)
    ·
      refine ⟨4917781757025461828842969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6557042342700615771790625 4917781757025461828842969)
      ·
        refine ⟨3688336317769096371632227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4917781757025461828842969 3688336317769096371632227)
        ·
          refine ⟨5532504476653644557448341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688336317769096371632227 5532504476653644557448341)
          ·
            refine ⟨259336147343139588630391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5532504476653644557448341 259336147343139588630391)
            ·
              refine ⟨389004221014709382945587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259336147343139588630391 389004221014709382945587)
              ·
                refine ⟨583506331522064074418381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389004221014709382945587 583506331522064074418381)
                ·
                  refine ⟨218814874320774027906893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 583506331522064074418381 218814874320774027906893)
                  ·
                    refine ⟨82055577870290260465085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218814874320774027906893 82055577870290260465085)
                    ·
                      rfl

theorem cell22_239704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_239704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239704 prefixEnd_239704 := by exact prefixLift 239704
  have htrace : WordTrace (prefixWord ++ tailWord_239704) baseStart_239704 baseEnd_239704 := by
    simpa [prefixWord, tailWord_239704, baseEnd_239704] using wordTrace_append hprefix tailTrace_239704
  have hstable : (prefixWord ++ tailWord_239704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239704).length < 2 ^ (prefixWord ++ tailWord_239704).sum := by decide
  have hdescent : baseEnd_239704 < baseStart_239704 := by decide
  rcases family_descends (prefixWord ++ tailWord_239704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239715 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_239715 : Nat := 118140960795 + 239715 * 2 ^ 59
def prefixEnd_239715 : Nat := 4983230072969 + 3 ^ 40 * 239715 * 2
def baseEnd_239715 : Nat := 82059343395089898440051

theorem tailTrace_239715 : CollatzResearch.WordTrace tailWord_239715 prefixEnd_239715 82059343395089898440051 := by
  unfold tailWord_239715
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743124326560969907704599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828749551040646605136399 8743124326560969907704599)
  ·
    refine ⟨13114686489841454861556899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8743124326560969907704599 13114686489841454861556899)
    ·
      refine ⟨19672029734762182292335349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13114686489841454861556899 19672029734762182292335349)
      ·
        refine ⟨1844252787633954589906439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19672029734762182292335349 1844252787633954589906439)
        ·
          refine ⟨2766379181450931884859659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844252787633954589906439 2766379181450931884859659)
          ·
            refine ⟨4149568772176397827289489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2766379181450931884859659 4149568772176397827289489)
            ·
              refine ⟨3112176579132298370467117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149568772176397827289489 3112176579132298370467117)
              ·
                refine ⟨1167066217174611888925169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112176579132298370467117 1167066217174611888925169)
                ·
                  refine ⟨875299662880958916693877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1167066217174611888925169 875299662880958916693877)
                  ·
                    refine ⟨82059343395089898440051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 875299662880958916693877 82059343395089898440051)
                    ·
                      rfl

theorem cell22_239715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_239715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239715 prefixEnd_239715 := by exact prefixLift 239715
  have htrace : WordTrace (prefixWord ++ tailWord_239715) baseStart_239715 baseEnd_239715 := by
    simpa [prefixWord, tailWord_239715, baseEnd_239715] using wordTrace_append hprefix tailTrace_239715
  have hstable : (prefixWord ++ tailWord_239715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239715).length < 2 ^ (prefixWord ++ tailWord_239715).sum := by decide
  have hdescent : baseEnd_239715 < baseStart_239715 := by decide
  rcases family_descends (prefixWord ++ tailWord_239715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239717 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 5]
def baseStart_239717 : Nat := 118140960795 + 239717 * 2 ^ 59
def prefixEnd_239717 : Nat := 4983230072969 + 3 ^ 40 * 239717 * 2
def baseEnd_239717 : Nat := 27353342678654186630015

theorem tailTrace_239717 : CollatzResearch.WordTrace tailWord_239717 prefixEnd_239717 27353342678654186630015 := by
  unfold tailWord_239717
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743197272553724249277405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5828798181702482832851603 8743197272553724249277405)
  ·
    refine ⟨3278698977207646593479027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8743197272553724249277405 3278698977207646593479027)
    ·
      refine ⟨4918048465811469890218541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278698977207646593479027 4918048465811469890218541)
      ·
        refine ⟨1844268174679301208831953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4918048465811469890218541 1844268174679301208831953)
        ·
          refine ⟨1383201131009475906623965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844268174679301208831953 1383201131009475906623965)
          ·
            refine ⟨518700424128553464983987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1383201131009475906623965 518700424128553464983987)
            ·
              refine ⟨778050636192830197475981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518700424128553464983987 778050636192830197475981)
              ·
                refine ⟨291768988572311324053493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 778050636192830197475981 291768988572311324053493)
                ·
                  refine ⟨27353342678654186630015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291768988572311324053493 27353342678654186630015)
                  ·
                    rfl

theorem cell22_239717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_239717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239717 prefixEnd_239717 := by exact prefixLift 239717
  have htrace : WordTrace (prefixWord ++ tailWord_239717) baseStart_239717 baseEnd_239717 := by
    simpa [prefixWord, tailWord_239717, baseEnd_239717] using wordTrace_append hprefix tailTrace_239717
  have hstable : (prefixWord ++ tailWord_239717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239717).length < 2 ^ (prefixWord ++ tailWord_239717).sum := by decide
  have hdescent : baseEnd_239717 < baseStart_239717 := by decide
  rcases family_descends (prefixWord ++ tailWord_239717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239760 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_239760 : Nat := 118140960795 + 239760 * 2 ^ 59
def prefixEnd_239760 : Nat := 4983230072969 + 3 ^ 40 * 239760 * 2
def baseEnd_239760 : Nat := 82074747814724781064913

theorem tailTrace_239760 : CollatzResearch.WordTrace tailWord_239760 prefixEnd_239760 82074747814724781064913 := by
  unfold tailWord_239760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4372382805698971296546367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5829843740931961728728489 4372382805698971296546367)
  ·
    refine ⟨6558574208548456944819551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4372382805698971296546367 6558574208548456944819551)
    ·
      refine ⟨9837861312822685417229327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6558574208548456944819551 9837861312822685417229327)
      ·
        refine ⟨14756791969234028125843991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9837861312822685417229327 14756791969234028125843991)
        ·
          refine ⟨22135187953851042188765987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14756791969234028125843991 22135187953851042188765987)
          ·
            refine ⟨33202781930776563283148981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22135187953851042188765987 33202781930776563283148981)
            ·
              refine ⟨3112760806010302807795217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33202781930776563283148981 3112760806010302807795217)
              ·
                refine ⟨2334570604507727105846413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3112760806010302807795217 2334570604507727105846413)
                ·
                  refine ⟨875463976690397664692405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2334570604507727105846413 875463976690397664692405)
                  ·
                    refine ⟨82074747814724781064913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 875463976690397664692405 82074747814724781064913)
                    ·
                      rfl

theorem cell22_239760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_239760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239760 prefixEnd_239760 := by exact prefixLift 239760
  have htrace : WordTrace (prefixWord ++ tailWord_239760) baseStart_239760 baseEnd_239760 := by
    simpa [prefixWord, tailWord_239760, baseEnd_239760] using wordTrace_append hprefix tailTrace_239760
  have hstable : (prefixWord ++ tailWord_239760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239760).length < 2 ^ (prefixWord ++ tailWord_239760).sum := by decide
  have hdescent : baseEnd_239760 < baseStart_239760 := by decide
  rcases family_descends (prefixWord ++ tailWord_239760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239762 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_239762 : Nat := 118140960795 + 239762 * 2 ^ 59
def prefixEnd_239762 : Nat := 4983230072969 + 3 ^ 40 * 239762 * 2
def baseEnd_239762 : Nat := 27358477485199147504969

theorem tailTrace_239762 : CollatzResearch.WordTrace tailWord_239762 prefixEnd_239762 27358477485199147504969 := by
  unfold tailWord_239762
  simp only [CollatzResearch.WordTrace]
  refine ⟨2186209639347674233666385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5829892371593797956443693 2186209639347674233666385)
  ·
    refine ⟨1639657229510755675249789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2186209639347674233666385 1639657229510755675249789)
    ·
      refine ⟨614871461066533378218671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1639657229510755675249789 614871461066533378218671)
      ·
        refine ⟨922307191599800067328007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 614871461066533378218671 922307191599800067328007)
        ·
          refine ⟨1383460787399700100992011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922307191599800067328007 1383460787399700100992011)
          ·
            refine ⟨2075191181099550151488017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383460787399700100992011 2075191181099550151488017)
            ·
              refine ⟨1556393385824662613616013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075191181099550151488017 1556393385824662613616013)
              ·
                refine ⟨583647519684248480106005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556393385824662613616013 583647519684248480106005)
                ·
                  refine ⟨27358477485199147504969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 583647519684248480106005 27358477485199147504969)
                  ·
                    rfl

theorem cell22_239762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_239762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239762 prefixEnd_239762 := by exact prefixLift 239762
  have htrace : WordTrace (prefixWord ++ tailWord_239762) baseStart_239762 baseEnd_239762 := by
    simpa [prefixWord, tailWord_239762, baseEnd_239762] using wordTrace_append hprefix tailTrace_239762
  have hstable : (prefixWord ++ tailWord_239762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239762).length < 2 ^ (prefixWord ++ tailWord_239762).sum := by decide
  have hdescent : baseEnd_239762 < baseStart_239762 := by decide
  rcases family_descends (prefixWord ++ tailWord_239762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239777 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_239777 : Nat := 118140960795 + 239777 * 2 ^ 59
def prefixEnd_239777 : Nat := 4983230072969 + 3 ^ 40 * 239777 * 2
def baseEnd_239777 : Nat := 82080567262142403389861

theorem tailTrace_239777 : CollatzResearch.WordTrace tailWord_239777 prefixEnd_239777 82080567262142403389861 := by
  unfold tailWord_239777
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745385652336354496461585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5830257101557569664307723 8745385652336354496461585)
  ·
    refine ⟨6559039239252265872346189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8745385652336354496461585 6559039239252265872346189)
    ·
      refine ⟨2459639714719599702129821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6559039239252265872346189 2459639714719599702129821)
      ·
        refine ⟨922364893019849888298683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2459639714719599702129821 922364893019849888298683)
        ·
          refine ⟨1383547339529774832448025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 922364893019849888298683 1383547339529774832448025)
          ·
            refine ⟨1037660504647331124336019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1383547339529774832448025 1037660504647331124336019)
            ·
              refine ⟨1556490756970996686504029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1037660504647331124336019 1556490756970996686504029)
              ·
                refine ⟨583684033864123757439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1556490756970996686504029 583684033864123757439011)
                ·
                  refine ⟨875526050796185636158517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 583684033864123757439011 875526050796185636158517)
                  ·
                    refine ⟨82080567262142403389861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 875526050796185636158517 82080567262142403389861)
                    ·
                      rfl

theorem cell22_239777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_239777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239777 prefixEnd_239777 := by exact prefixLift 239777
  have htrace : WordTrace (prefixWord ++ tailWord_239777) baseStart_239777 baseEnd_239777 := by
    simpa [prefixWord, tailWord_239777, baseEnd_239777] using wordTrace_append hprefix tailTrace_239777
  have hstable : (prefixWord ++ tailWord_239777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239777).length < 2 ^ (prefixWord ++ tailWord_239777).sum := by decide
  have hdescent : baseEnd_239777 < baseStart_239777 := by decide
  rcases family_descends (prefixWord ++ tailWord_239777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239835 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 9]
def baseStart_239835 : Nat := 118140960795 + 239835 * 2 ^ 59
def prefixEnd_239835 : Nat := 4983230072969 + 3 ^ 40 * 239835 * 2
def baseEnd_239835 : Nat := 27366807282483195146561

theorem tailTrace_239835 : CollatzResearch.WordTrace tailWord_239835 prefixEnd_239835 27366807282483195146561 := by
  unfold tailWord_239835
  simp only [CollatzResearch.WordTrace]
  refine ⟨8747501086126230402072959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5831667390750820268048639 8747501086126230402072959)
  ·
    refine ⟨13121251629189345603109439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8747501086126230402072959 13121251629189345603109439)
    ·
      refine ⟨19681877443784018404664159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121251629189345603109439 19681877443784018404664159)
      ·
        refine ⟨29522816165676027606996239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19681877443784018404664159 29522816165676027606996239)
        ·
          refine ⟨44284224248514041410494359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29522816165676027606996239 44284224248514041410494359)
          ·
            refine ⟨66426336372771062115741539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44284224248514041410494359 66426336372771062115741539)
            ·
              refine ⟨99639504559156593173612309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66426336372771062115741539 99639504559156593173612309)
              ·
                refine ⟨4670601776210465305013077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99639504559156593173612309 4670601776210465305013077)
                ·
                  refine ⟨27366807282483195146561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4670601776210465305013077 27366807282483195146561)
                  ·
                    rfl

theorem cell22_239835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_239835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239835 prefixEnd_239835 := by exact prefixLift 239835
  have htrace : WordTrace (prefixWord ++ tailWord_239835) baseStart_239835 baseEnd_239835 := by
    simpa [prefixWord, tailWord_239835, baseEnd_239835] using wordTrace_append hprefix tailTrace_239835
  have hstable : (prefixWord ++ tailWord_239835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239835).length < 2 ^ (prefixWord ++ tailWord_239835).sum := by decide
  have hdescent : baseEnd_239835 < baseStart_239835 := by decide
  rcases family_descends (prefixWord ++ tailWord_239835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239873 : List Nat := [1, 2, 4, 1, 1, 2, 5, 2, 1, 3]
def baseStart_239873 : Nat := 118140960795 + 239873 * 2 ^ 59
def prefixEnd_239873 : Nat := 4983230072969 + 3 ^ 40 * 239873 * 2
def baseEnd_239873 : Nat := 82113430024030152989567

theorem tailTrace_239873 : CollatzResearch.WordTrace tailWord_239873 prefixEnd_239873 82113430024030152989567 := by
  unfold tailWord_239873
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748887059988562891956273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5832591373325708594637515 8748887059988562891956273)
  ·
    refine ⟨6561665294991422168967205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8748887059988562891956273 6561665294991422168967205)
    ·
      refine ⟨1230312242810891656681351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6561665294991422168967205 1230312242810891656681351)
      ·
        refine ⟨1845468364216337485022027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230312242810891656681351 1845468364216337485022027)
        ·
          refine ⟨2768202546324506227533041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845468364216337485022027 2768202546324506227533041)
          ·
            refine ⟨2076151909743379670649781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768202546324506227533041 2076151909743379670649781)
            ·
              refine ⟨194639241538441844123417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2076151909743379670649781 194639241538441844123417)
              ·
                refine ⟨145979431153831383092563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194639241538441844123417 145979431153831383092563)
                ·
                  refine ⟨218969146730747074638845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145979431153831383092563 218969146730747074638845)
                  ·
                    refine ⟨82113430024030152989567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 218969146730747074638845 82113430024030152989567)
                    ·
                      rfl

theorem cell22_239873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_239873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239873 prefixEnd_239873 := by exact prefixLift 239873
  have htrace : WordTrace (prefixWord ++ tailWord_239873) baseStart_239873 baseEnd_239873 := by
    simpa [prefixWord, tailWord_239873, baseEnd_239873] using wordTrace_append hprefix tailTrace_239873
  have hstable : (prefixWord ++ tailWord_239873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239873).length < 2 ^ (prefixWord ++ tailWord_239873).sum := by decide
  have hdescent : baseEnd_239873 < baseStart_239873 := by decide
  rcases family_descends (prefixWord ++ tailWord_239873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239899 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 1, 4]
def baseStart_239899 : Nat := 118140960795 + 239899 * 2 ^ 59
def prefixEnd_239899 : Nat := 4983230072969 + 3 ^ 40 * 239899 * 2
def baseEnd_239899 : Nat := 82122330355374751839487

theorem tailTrace_239899 : CollatzResearch.WordTrace tailWord_239899 prefixEnd_239899 82122330355374751839487 := by
  unfold tailWord_239899
  simp only [CollatzResearch.WordTrace]
  refine ⟨8749835357894369332402751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5833223571929579554935167 8749835357894369332402751)
  ·
    refine ⟨13124753036841553998604127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8749835357894369332402751 13124753036841553998604127)
    ·
      refine ⟨19687129555262330997906191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124753036841553998604127 19687129555262330997906191)
      ·
        refine ⟨29530694332893496496859287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687129555262330997906191 29530694332893496496859287)
        ·
          refine ⟨44296041499340244745288931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29530694332893496496859287 44296041499340244745288931)
          ·
            refine ⟨66444062249010367117933397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44296041499340244745288931 66444062249010367117933397)
            ·
              refine ⟨389320677240295119831641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 66444062249010367117933397 389320677240295119831641)
              ·
                refine ⟨291990507930221339873731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389320677240295119831641 291990507930221339873731)
                ·
                  refine ⟨437985761895332009810597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 291990507930221339873731 437985761895332009810597)
                  ·
                    refine ⟨82122330355374751839487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 437985761895332009810597 82122330355374751839487)
                    ·
                      rfl

theorem cell22_239899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4].length) (baseStart_239899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239899 prefixEnd_239899 := by exact prefixLift 239899
  have htrace : WordTrace (prefixWord ++ tailWord_239899) baseStart_239899 baseEnd_239899 := by
    simpa [prefixWord, tailWord_239899, baseEnd_239899] using wordTrace_append hprefix tailTrace_239899
  have hstable : (prefixWord ++ tailWord_239899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239899).length < 2 ^ (prefixWord ++ tailWord_239899).sum := by decide
  have hdescent : baseEnd_239899 < baseStart_239899 := by decide
  rcases family_descends (prefixWord ++ tailWord_239899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239959 : List Nat := [1, 1, 3, 2, 3, 1, 5, 6]
def baseStart_239959 : Nat := 118140960795 + 239959 * 2 ^ 59
def prefixEnd_239959 : Nat := 4983230072969 + 3 ^ 40 * 239959 * 2
def baseEnd_239959 : Nat := 9126985509061621704367

theorem tailTrace_239959 : CollatzResearch.WordTrace tailWord_239959 prefixEnd_239959 9126985509061621704367 := by
  unfold tailWord_239959
  simp only [CollatzResearch.WordTrace]
  refine ⟨8752023737676999579586931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5834682491784666386391287 8752023737676999579586931)
  ·
    refine ⟨13128035606515499369380397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8752023737676999579586931 13128035606515499369380397)
    ·
      refine ⟨4923013352443312263517649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13128035606515499369380397 4923013352443312263517649)
      ·
        refine ⟨3692260014332484197638237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4923013352443312263517649 3692260014332484197638237)
        ·
          refine ⟨1384597505374681574114339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3692260014332484197638237 1384597505374681574114339)
          ·
            refine ⟨2076896258062022361171509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384597505374681574114339 2076896258062022361171509)
            ·
              refine ⟨194709024193314596359829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2076896258062022361171509 194709024193314596359829)
              ·
                refine ⟨9126985509061621704367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194709024193314596359829 9126985509061621704367)
                ·
                  rfl

theorem cell22_239959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 6].length) (baseStart_239959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239959 prefixEnd_239959 := by exact prefixLift 239959
  have htrace : WordTrace (prefixWord ++ tailWord_239959) baseStart_239959 baseEnd_239959 := by
    simpa [prefixWord, tailWord_239959, baseEnd_239959] using wordTrace_append hprefix tailTrace_239959
  have hstable : (prefixWord ++ tailWord_239959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239959).length < 2 ^ (prefixWord ++ tailWord_239959).sum := by decide
  have hdescent : baseEnd_239959 < baseStart_239959 := by decide
  rcases family_descends (prefixWord ++ tailWord_239959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239980 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_239980 : Nat := 118140960795 + 239980 * 2 ^ 59
def prefixEnd_239980 : Nat := 4983230072969 + 3 ^ 40 * 239980 * 2
def baseEnd_239980 : Nat := 82150058310717540564239

theorem tailTrace_239980 : CollatzResearch.WordTrace tailWord_239980 prefixEnd_239980 82150058310717540564239 := by
  unfold tailWord_239980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376394835300460083050697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5835193113733946777400929 4376394835300460083050697)
  ·
    refine ⟨3282296126475345062288023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4376394835300460083050697 3282296126475345062288023)
    ·
      refine ⟨4923444189713017593432035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282296126475345062288023 4923444189713017593432035)
      ·
        refine ⟨7385166284569526390148053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923444189713017593432035 7385166284569526390148053)
        ·
          refine ⟨173089834794598274769095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 7385166284569526390148053 173089834794598274769095)
          ·
            refine ⟨259634752191897412153643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173089834794598274769095 259634752191897412153643)
            ·
              refine ⟨389452128287846118230465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259634752191897412153643 389452128287846118230465)
              ·
                refine ⟨292089096215884588672849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 389452128287846118230465 292089096215884588672849)
                ·
                  refine ⟨219066822161913441504637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292089096215884588672849 219066822161913441504637)
                  ·
                    refine ⟨82150058310717540564239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219066822161913441504637 82150058310717540564239)
                    ·
                      rfl

theorem cell22_239980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_239980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239980 prefixEnd_239980 := by exact prefixLift 239980
  have htrace : WordTrace (prefixWord ++ tailWord_239980) baseStart_239980 baseEnd_239980 := by
    simpa [prefixWord, tailWord_239980, baseEnd_239980] using wordTrace_append hprefix tailTrace_239980
  have hstable : (prefixWord ++ tailWord_239980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239980).length < 2 ^ (prefixWord ++ tailWord_239980).sum := by decide
  have hdescent : baseEnd_239980 < baseStart_239980 := by decide
  rcases family_descends (prefixWord ++ tailWord_239980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_239987 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 7]
def baseStart_239987 : Nat := 118140960795 + 239987 * 2 ^ 59
def prefixEnd_239987 : Nat := 4983230072969 + 3 ^ 40 * 239987 * 2
def baseEnd_239987 : Nat := 27384151517923951879739

theorem tailTrace_239987 : CollatzResearch.WordTrace tailWord_239987 prefixEnd_239987 27384151517923951879739 := by
  unfold tailWord_239987
  simp only [CollatzResearch.WordTrace]
  refine ⟨8753044981575560361606215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5835363321050373574404143 8753044981575560361606215)
  ·
    refine ⟨13129567472363340542409323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8753044981575560361606215 13129567472363340542409323)
    ·
      refine ⟨19694351208545010813613985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129567472363340542409323 19694351208545010813613985)
      ·
        refine ⟨14770763406408758110210489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19694351208545010813613985 14770763406408758110210489)
        ·
          refine ⟨11078072554806568582657867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14770763406408758110210489 11078072554806568582657867)
          ·
            refine ⟨16617108832209852873986801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078072554806568582657867 16617108832209852873986801)
            ·
              refine ⟨12462831624157389655490101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16617108832209852873986801 12462831624157389655490101)
              ·
                refine ⟨1168390464764755280202197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12462831624157389655490101 1168390464764755280202197)
                ·
                  refine ⟨27384151517923951879739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1168390464764755280202197 27384151517923951879739)
                  ·
                    rfl

theorem cell22_239987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_239987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_239987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_239987 prefixEnd_239987 := by exact prefixLift 239987
  have htrace : WordTrace (prefixWord ++ tailWord_239987) baseStart_239987 baseEnd_239987 := by
    simpa [prefixWord, tailWord_239987, baseEnd_239987] using wordTrace_append hprefix tailTrace_239987
  have hstable : (prefixWord ++ tailWord_239987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_239987).length < 2 ^ (prefixWord ++ tailWord_239987).sum := by decide
  have hdescent : baseEnd_239987 < baseStart_239987 := by decide
  rcases family_descends (prefixWord ++ tailWord_239987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240010 : List Nat := [3, 1, 2, 5, 2, 1, 2, 6]
def baseStart_240010 : Nat := 118140960795 + 240010 * 2 ^ 59
def prefixEnd_240010 : Nat := 4983230072969 + 3 ^ 40 * 240010 * 2
def baseEnd_240010 : Nat := 9128925324867495812683

theorem tailTrace_240010 : CollatzResearch.WordTrace tailWord_240010 prefixEnd_240010 9128925324867495812683 := by
  unfold tailWord_240010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188470965123058822423371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5835922573661490193128989 2188470965123058822423371)
  ·
    refine ⟨3282706447684588233635057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188470965123058822423371 3282706447684588233635057)
    ·
      refine ⟨2462029835763441175226293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3282706447684588233635057 2462029835763441175226293)
      ·
        refine ⟨230815297102822610177465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2462029835763441175226293 230815297102822610177465)
        ·
          refine ⟨173111472827116957633099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230815297102822610177465 173111472827116957633099)
          ·
            refine ⟨259667209240675436449649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173111472827116957633099 259667209240675436449649)
            ·
              refine ⟨194750406930506577337237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259667209240675436449649 194750406930506577337237)
              ·
                refine ⟨9128925324867495812683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194750406930506577337237 9128925324867495812683)
                ·
                  rfl

theorem cell22_240010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_240010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240010 prefixEnd_240010 := by exact prefixLift 240010
  have htrace : WordTrace (prefixWord ++ tailWord_240010) baseStart_240010 baseEnd_240010 := by
    simpa [prefixWord, tailWord_240010, baseEnd_240010] using wordTrace_append hprefix tailTrace_240010
  have hstable : (prefixWord ++ tailWord_240010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240010).length < 2 ^ (prefixWord ++ tailWord_240010).sum := by decide
  have hdescent : baseEnd_240010 < baseStart_240010 := by decide
  rcases family_descends (prefixWord ++ tailWord_240010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240064 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_240064 : Nat := 118140960795 + 240064 * 2 ^ 59
def prefixEnd_240064 : Nat := 4983230072969 + 3 ^ 40 * 240064 * 2
def baseEnd_240064 : Nat := 82178813227369321463981

theorem tailTrace_240064 : CollatzResearch.WordTrace tailWord_240064 prefixEnd_240064 82178813227369321463981 := by
  unfold tailWord_240064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377926701148301256079623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5837235601531068341439497 4377926701148301256079623)
  ·
    refine ⟨6566890051722451884119435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4377926701148301256079623 6566890051722451884119435)
    ·
      refine ⟨9850335077583677826179153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6566890051722451884119435 9850335077583677826179153)
      ·
        refine ⟨7387751308187758369634365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9850335077583677826179153 7387751308187758369634365)
        ·
          refine ⟨2770406740570409388612887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7387751308187758369634365 2770406740570409388612887)
          ·
            refine ⟨4155610110855614082919331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770406740570409388612887 4155610110855614082919331)
            ·
              refine ⟨6233415166283421124378997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155610110855614082919331 6233415166283421124378997)
              ·
                refine ⟨584382671839070730410531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6233415166283421124378997 584382671839070730410531)
                ·
                  refine ⟨876574007758606095615797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 584382671839070730410531 876574007758606095615797)
                  ·
                    refine ⟨82178813227369321463981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 876574007758606095615797 82178813227369321463981)
                    ·
                      rfl

theorem cell22_240064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_240064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240064 prefixEnd_240064 := by exact prefixLift 240064
  have htrace : WordTrace (prefixWord ++ tailWord_240064) baseStart_240064 baseEnd_240064 := by
    simpa [prefixWord, tailWord_240064, baseEnd_240064] using wordTrace_append hprefix tailTrace_240064
  have hstable : (prefixWord ++ tailWord_240064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240064).length < 2 ^ (prefixWord ++ tailWord_240064).sum := by decide
  have hdescent : baseEnd_240064 < baseStart_240064 := by decide
  rcases family_descends (prefixWord ++ tailWord_240064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240068 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_240068 : Nat := 118140960795 + 240068 * 2 ^ 59
def prefixEnd_240068 : Nat := 4983230072969 + 3 ^ 40 * 240068 * 2
def baseEnd_240068 : Nat := 82180182509114644363969

theorem tailTrace_240068 : CollatzResearch.WordTrace tailWord_240068 prefixEnd_240068 82180182509114644363969 := by
  unfold tailWord_240068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4377999647141055597652429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5837332862854740796869905 4377999647141055597652429)
  ·
    refine ⟨1641749867677895849119661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4377999647141055597652429 1641749867677895849119661)
    ·
      refine ⟨615656200379210943419873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1641749867677895849119661 615656200379210943419873)
      ·
        refine ⟨461742150284408207564905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 615656200379210943419873 461742150284408207564905)
        ·
          refine ⟨346306612713306155673679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461742150284408207564905 346306612713306155673679)
          ·
            refine ⟨519459919069959233510519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346306612713306155673679 519459919069959233510519)
            ·
              refine ⟨779189878604938850265779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519459919069959233510519 779189878604938850265779)
              ·
                refine ⟨1168784817907408275398669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779189878604938850265779 1168784817907408275398669)
                ·
                  refine ⟨438294306715278103274501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1168784817907408275398669 438294306715278103274501)
                  ·
                    refine ⟨82180182509114644363969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438294306715278103274501 82180182509114644363969)
                    ·
                      rfl

theorem cell22_240068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_240068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240068 prefixEnd_240068 := by exact prefixLift 240068
  have htrace : WordTrace (prefixWord ++ tailWord_240068) baseStart_240068 baseEnd_240068 := by
    simpa [prefixWord, tailWord_240068, baseEnd_240068] using wordTrace_append hprefix tailTrace_240068
  have hstable : (prefixWord ++ tailWord_240068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240068).length < 2 ^ (prefixWord ++ tailWord_240068).sum := by decide
  have hdescent : baseEnd_240068 < baseStart_240068 := by decide
  rcases family_descends (prefixWord ++ tailWord_240068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240124 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_240124 : Nat := 118140960795 + 240124 * 2 ^ 59
def prefixEnd_240124 : Nat := 4983230072969 + 3 ^ 40 * 240124 * 2
def baseEnd_240124 : Nat := 82199352453549164963797

theorem tailTrace_240124 : CollatzResearch.WordTrace tailWord_240124 prefixEnd_240124 82199352453549164963797 := by
  unfold tailWord_240124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379020891039616379671713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5838694521386155172895617 4379020891039616379671713)
  ·
    refine ⟨3284265668279712284753785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4379020891039616379671713 3284265668279712284753785)
    ·
      refine ⟨2463199251209784213565339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3284265668279712284753785 2463199251209784213565339)
      ·
        refine ⟨3694798876814676320348009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2463199251209784213565339 3694798876814676320348009)
        ·
          refine ⟨2771099157611007240261007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3694798876814676320348009 2771099157611007240261007)
          ·
            refine ⟨4156648736416510860391511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771099157611007240261007 4156648736416510860391511)
            ·
              refine ⟨6234973104624766290587267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4156648736416510860391511 6234973104624766290587267)
              ·
                refine ⟨9352459656937149435880901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234973104624766290587267 9352459656937149435880901)
                ·
                  refine ⟨1753586185675715519227669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9352459656937149435880901 1753586185675715519227669)
                  ·
                    refine ⟨82199352453549164963797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1753586185675715519227669 82199352453549164963797)
                    ·
                      rfl

theorem cell22_240124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_240124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240124 prefixEnd_240124 := by exact prefixLift 240124
  have htrace : WordTrace (prefixWord ++ tailWord_240124) baseStart_240124 baseEnd_240124 := by
    simpa [prefixWord, tailWord_240124, baseEnd_240124] using wordTrace_append hprefix tailTrace_240124
  have hstable : (prefixWord ++ tailWord_240124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240124).length < 2 ^ (prefixWord ++ tailWord_240124).sum := by decide
  have hdescent : baseEnd_240124 < baseStart_240124 := by decide
  rcases family_descends (prefixWord ++ tailWord_240124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240134 : List Nat := [6, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_240134 : Nat := 118140960795 + 240134 * 2 ^ 59
def prefixEnd_240134 : Nat := 4983230072969 + 3 ^ 40 * 240134 * 2
def baseEnd_240134 : Nat := 27400925219304157404589

theorem tailTrace_240134 : CollatzResearch.WordTrace tailWord_240134 prefixEnd_240134 27400925219304157404589 := by
  unfold tailWord_240134
  simp only [CollatzResearch.WordTrace]
  refine ⟨273700203501343889600233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5838937674695336311471637 273700203501343889600233)
  ·
    refine ⟨205275152626007917200175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273700203501343889600233 205275152626007917200175)
    ·
      refine ⟨307912728939011875800263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205275152626007917200175 307912728939011875800263)
      ·
        refine ⟨461869093408517813700395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307912728939011875800263 461869093408517813700395)
        ·
          refine ⟨692803640112776720550593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461869093408517813700395 692803640112776720550593)
          ·
            refine ⟨519602730084582540412945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692803640112776720550593 519602730084582540412945)
            ·
              refine ⟨389702047563436905309709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519602730084582540412945 389702047563436905309709)
              ·
                refine ⟨146138267836288839491141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389702047563436905309709 146138267836288839491141)
                ·
                  refine ⟨27400925219304157404589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146138267836288839491141 27400925219304157404589)
                  ·
                    rfl

theorem cell22_240134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_240134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240134 prefixEnd_240134 := by exact prefixLift 240134
  have htrace : WordTrace (prefixWord ++ tailWord_240134) baseStart_240134 baseEnd_240134 := by
    simpa [prefixWord, tailWord_240134, baseEnd_240134] using wordTrace_append hprefix tailTrace_240134
  have hstable : (prefixWord ++ tailWord_240134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240134).length < 2 ^ (prefixWord ++ tailWord_240134).sum := by decide
  have hdescent : baseEnd_240134 < baseStart_240134 := by decide
  rcases family_descends (prefixWord ++ tailWord_240134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240143 : List Nat := [1, 1, 2, 1, 1, 1, 2, 9, 1, 3]
def baseStart_240143 : Nat := 118140960795 + 240143 * 2 ^ 59
def prefixEnd_240143 : Nat := 4983230072969 + 3 ^ 40 * 240143 * 2
def baseEnd_240143 : Nat := 82205856541839448738739

theorem tailTrace_240143 : CollatzResearch.WordTrace tailWord_240143 prefixEnd_240143 82205856541839448738739 := by
  unfold tailWord_240143
  simp only [CollatzResearch.WordTrace]
  refine ⟨8758734769010399004285083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5839156512673599336190055 8758734769010399004285083)
  ·
    refine ⟨13138102153515598506427625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8758734769010399004285083 13138102153515598506427625)
    ·
      refine ⟨9853576615136698879820719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13138102153515598506427625 9853576615136698879820719)
      ·
        refine ⟨14780364922705048319731079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9853576615136698879820719 14780364922705048319731079)
        ·
          refine ⟨22170547384057572479596619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14780364922705048319731079 22170547384057572479596619)
          ·
            refine ⟨33255821076086358719394929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22170547384057572479596619 33255821076086358719394929)
            ·
              refine ⟨24941865807064769039546197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33255821076086358719394929 24941865807064769039546197)
              ·
                refine ⟨146143744963270131091091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24941865807064769039546197 146143744963270131091091)
                ·
                  refine ⟨219215617444905196636637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146143744963270131091091 219215617444905196636637)
                  ·
                    refine ⟨82205856541839448738739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219215617444905196636637 82205856541839448738739)
                    ·
                      rfl

theorem cell22_240143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 1, 3].length) (baseStart_240143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240143 prefixEnd_240143 := by exact prefixLift 240143
  have htrace : WordTrace (prefixWord ++ tailWord_240143) baseStart_240143 baseEnd_240143 := by
    simpa [prefixWord, tailWord_240143, baseEnd_240143] using wordTrace_append hprefix tailTrace_240143
  have hstable : (prefixWord ++ tailWord_240143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240143).length < 2 ^ (prefixWord ++ tailWord_240143).sum := by decide
  have hdescent : baseEnd_240143 < baseStart_240143 := by decide
  rcases family_descends (prefixWord ++ tailWord_240143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240156 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_240156 : Nat := 118140960795 + 240156 * 2 ^ 59
def prefixEnd_240156 : Nat := 4983230072969 + 3 ^ 40 * 240156 * 2
def baseEnd_240156 : Nat := 27403435569170582721233

theorem tailTrace_240156 : CollatzResearch.WordTrace tailWord_240156 prefixEnd_240156 27403435569170582721233 := by
  unfold tailWord_240156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379604458981651112254161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5839472611975534816338881 4379604458981651112254161)
  ·
    refine ⟨3284703344236238334190621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4379604458981651112254161 3284703344236238334190621)
    ·
      refine ⟨1231763754088589375321483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3284703344236238334190621 1231763754088589375321483)
      ·
        refine ⟨1847645631132884062982225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231763754088589375321483 1847645631132884062982225)
        ·
          refine ⟨1385734223349663047236669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1847645631132884062982225 1385734223349663047236669)
          ·
            refine ⟨519650333756123642713751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1385734223349663047236669 519650333756123642713751)
            ·
              refine ⟨779475500634185464070627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519650333756123642713751 779475500634185464070627)
              ·
                refine ⟨1169213250951278196105941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 779475500634185464070627 1169213250951278196105941)
                ·
                  refine ⟨27403435569170582721233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1169213250951278196105941 27403435569170582721233)
                  ·
                    rfl

theorem cell22_240156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_240156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240156 prefixEnd_240156 := by exact prefixLift 240156
  have htrace : WordTrace (prefixWord ++ tailWord_240156) baseStart_240156 baseEnd_240156 := by
    simpa [prefixWord, tailWord_240156, baseEnd_240156] using wordTrace_append hprefix tailTrace_240156
  have hstable : (prefixWord ++ tailWord_240156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240156).length < 2 ^ (prefixWord ++ tailWord_240156).sum := by decide
  have hdescent : baseEnd_240156 < baseStart_240156 := by decide
  rcases family_descends (prefixWord ++ tailWord_240156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240160 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_240160 : Nat := 118140960795 + 240160 * 2 ^ 59
def prefixEnd_240160 : Nat := 4983230072969 + 3 ^ 40 * 240160 * 2
def baseEnd_240160 : Nat := 82211675989257071063687

theorem tailTrace_240160 : CollatzResearch.WordTrace tailWord_240160 prefixEnd_240160 82211675989257071063687 := by
  unfold tailWord_240160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4379677404974405453826967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5839569873299207271769289 4379677404974405453826967)
  ·
    refine ⟨6569516107461608180740451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4379677404974405453826967 6569516107461608180740451)
    ·
      refine ⟨9854274161192412271110677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6569516107461608180740451 9854274161192412271110677)
      ·
        refine ⟨461919101305894325208313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9854274161192412271110677 461919101305894325208313)
        ·
          refine ⟨346439325979420743906235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461919101305894325208313 346439325979420743906235)
          ·
            refine ⟨519658988969131115859353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346439325979420743906235 519658988969131115859353)
            ·
              refine ⟨389744241726848336894515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 519658988969131115859353 389744241726848336894515)
              ·
                refine ⟨584616362590272505341773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 389744241726848336894515 584616362590272505341773)
                ·
                  refine ⟨219231135971352189503165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 584616362590272505341773 219231135971352189503165)
                  ·
                    refine ⟨82211675989257071063687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219231135971352189503165 82211675989257071063687)
                    ·
                      rfl

theorem cell22_240160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_240160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240160 prefixEnd_240160 := by exact prefixLift 240160
  have htrace : WordTrace (prefixWord ++ tailWord_240160) baseStart_240160 baseEnd_240160 := by
    simpa [prefixWord, tailWord_240160, baseEnd_240160] using wordTrace_append hprefix tailTrace_240160
  have hstable : (prefixWord ++ tailWord_240160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240160).length < 2 ^ (prefixWord ++ tailWord_240160).sum := by decide
  have hdescent : baseEnd_240160 < baseStart_240160 := by decide
  rcases family_descends (prefixWord ++ tailWord_240160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240231 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_240231 : Nat := 118140960795 + 240231 * 2 ^ 59
def prefixEnd_240231 : Nat := 4983230072969 + 3 ^ 40 * 240231 * 2
def baseEnd_240231 : Nat := 82235980740236552538469

theorem tailTrace_240231 : CollatzResearch.WordTrace tailWord_240231 prefixEnd_240231 82235980740236552538469 := by
  unfold tailWord_240231
  simp only [CollatzResearch.WordTrace]
  refine ⟨8761944392691590033488547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5841296261794393355659031 8761944392691590033488547)
  ·
    refine ⟨13142916589037385050232821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8761944392691590033488547 13142916589037385050232821)
    ·
      refine ⟨1232148430222254848459327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13142916589037385050232821 1232148430222254848459327)
      ·
        refine ⟨1848222645333382272688991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232148430222254848459327 1848222645333382272688991)
        ·
          refine ⟨2772333968000073409033487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1848222645333382272688991 2772333968000073409033487)
          ·
            refine ⟨4158500952000110113550231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772333968000073409033487 4158500952000110113550231)
            ·
              refine ⟨6237751428000165170325347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158500952000110113550231 6237751428000165170325347)
              ·
                refine ⟨9356627142000247755488021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237751428000165170325347 9356627142000247755488021)
                ·
                  refine ⟨438591897281261613538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9356627142000247755488021 438591897281261613538501)
                  ·
                    refine ⟨82235980740236552538469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438591897281261613538501 82235980740236552538469)
                    ·
                      rfl

theorem cell22_240231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_240231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240231 prefixEnd_240231 := by exact prefixLift 240231
  have htrace : WordTrace (prefixWord ++ tailWord_240231) baseStart_240231 baseEnd_240231 := by
    simpa [prefixWord, tailWord_240231, baseEnd_240231] using wordTrace_append hprefix tailTrace_240231
  have hstable : (prefixWord ++ tailWord_240231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240231).length < 2 ^ (prefixWord ++ tailWord_240231).sum := by decide
  have hdescent : baseEnd_240231 < baseStart_240231 := by decide
  rcases family_descends (prefixWord ++ tailWord_240231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240306 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_240306 : Nat := 118140960795 + 240306 * 2 ^ 59
def prefixEnd_240306 : Nat := 4983230072969 + 3 ^ 40 * 240306 * 2
def baseEnd_240306 : Nat := 82261654772961356913239

theorem tailTrace_240306 : CollatzResearch.WordTrace tailWord_240306 prefixEnd_240306 82261654772961356913239 := by
  unfold tailWord_240306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191169966854969460617193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5843119911613251894979181 2191169966854969460617193)
  ·
    refine ⟨1643377475141227095462895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2191169966854969460617193 1643377475141227095462895)
    ·
      refine ⟨2465066212711840643194343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643377475141227095462895 2465066212711840643194343)
      ·
        refine ⟨3697599319067760964791515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465066212711840643194343 3697599319067760964791515)
        ·
          refine ⟨5546398978601641447187273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3697599319067760964791515 5546398978601641447187273)
          ·
            refine ⟨4159799233951231085390455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5546398978601641447187273 4159799233951231085390455)
            ·
              refine ⟨6239698850926846628085683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4159799233951231085390455 6239698850926846628085683)
              ·
                refine ⟨9359548276390269942128525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6239698850926846628085683 9359548276390269942128525)
                ·
                  refine ⟨3509830603646351228298197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9359548276390269942128525 3509830603646351228298197)
                  ·
                    refine ⟨82261654772961356913239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3509830603646351228298197 82261654772961356913239)
                    ·
                      rfl

theorem cell22_240306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_240306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240306 prefixEnd_240306 := by exact prefixLift 240306
  have htrace : WordTrace (prefixWord ++ tailWord_240306) baseStart_240306 baseEnd_240306 := by
    simpa [prefixWord, tailWord_240306, baseEnd_240306] using wordTrace_append hprefix tailTrace_240306
  have hstable : (prefixWord ++ tailWord_240306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240306).length < 2 ^ (prefixWord ++ tailWord_240306).sum := by decide
  have hdescent : baseEnd_240306 < baseStart_240306 := by decide
  rcases family_descends (prefixWord ++ tailWord_240306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240353 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 6]
def baseStart_240353 : Nat := 118140960795 + 240353 * 2 ^ 59
def prefixEnd_240353 : Nat := 4983230072969 + 3 ^ 40 * 240353 * 2
def baseEnd_240353 : Nat := 27425914611156300329365

theorem tailTrace_240353 : CollatzResearch.WordTrace tailWord_240353 prefixEnd_240353 27425914611156300329365 := by
  unfold tailWord_240353
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766394098249604869429713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5844262732166403246286475 8766394098249604869429713)
  ·
    refine ⟨6574795573687203652072285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8766394098249604869429713 6574795573687203652072285)
    ·
      refine ⟨2465548340132701369527107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6574795573687203652072285 2465548340132701369527107)
      ·
        refine ⟨3698322510199052054290661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465548340132701369527107 3698322510199052054290661)
        ·
          refine ⟨693435470662322260179499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3698322510199052054290661 693435470662322260179499)
          ·
            refine ⟨1040153205993483390269249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693435470662322260179499 1040153205993483390269249)
            ·
              refine ⟨780114904495112542701937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040153205993483390269249 780114904495112542701937)
              ·
                refine ⟨585086178371334407026453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 780114904495112542701937 585086178371334407026453)
                ·
                  refine ⟨27425914611156300329365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 585086178371334407026453 27425914611156300329365)
                  ·
                    rfl

theorem cell22_240353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_240353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240353 prefixEnd_240353 := by exact prefixLift 240353
  have htrace : WordTrace (prefixWord ++ tailWord_240353) baseStart_240353 baseEnd_240353 := by
    simpa [prefixWord, tailWord_240353, baseEnd_240353] using wordTrace_append hprefix tailTrace_240353
  have hstable : (prefixWord ++ tailWord_240353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240353).length < 2 ^ (prefixWord ++ tailWord_240353).sum := by decide
  have hdescent : baseEnd_240353 < baseStart_240353 := by decide
  rcases family_descends (prefixWord ++ tailWord_240353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240355 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 1, 4]
def baseStart_240355 : Nat := 118140960795 + 240355 * 2 ^ 59
def prefixEnd_240355 : Nat := 4983230072969 + 3 ^ 40 * 240355 * 2
def baseEnd_240355 : Nat := 82278428474341562438089

theorem tailTrace_240355 : CollatzResearch.WordTrace tailWord_240355 prefixEnd_240355 82278428474341562438089 := by
  unfold tailWord_240355
  simp only [CollatzResearch.WordTrace]
  refine ⟨8766467044242359211002519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5844311362828239474001679 8766467044242359211002519)
  ·
    refine ⟨13149700566363538816503779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8766467044242359211002519 13149700566363538816503779)
    ·
      refine ⟨19724550849545308224755669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13149700566363538816503779 19724550849545308224755669)
      ·
        refine ⟨462294160536218161517711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 19724550849545308224755669 462294160536218161517711)
        ·
          refine ⟨693441240804327242276567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 462294160536218161517711 693441240804327242276567)
          ·
            refine ⟨1040161861206490863414851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693441240804327242276567 1040161861206490863414851)
            ·
              refine ⟨1560242791809736295122277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1040161861206490863414851 1560242791809736295122277)
              ·
                refine ⟨292545523464325555335427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1560242791809736295122277 292545523464325555335427)
                ·
                  refine ⟨438818285196488333003141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 292545523464325555335427 438818285196488333003141)
                  ·
                    refine ⟨82278428474341562438089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 438818285196488333003141 82278428474341562438089)
                    ·
                      rfl

theorem cell22_240355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4].length) (baseStart_240355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240355 prefixEnd_240355 := by exact prefixLift 240355
  have htrace : WordTrace (prefixWord ++ tailWord_240355) baseStart_240355 baseEnd_240355 := by
    simpa [prefixWord, tailWord_240355, baseEnd_240355] using wordTrace_append hprefix tailTrace_240355
  have hstable : (prefixWord ++ tailWord_240355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240355).length < 2 ^ (prefixWord ++ tailWord_240355).sum := by decide
  have hdescent : baseEnd_240355 < baseStart_240355 := by decide
  rcases family_descends (prefixWord ++ tailWord_240355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240368 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 6, 3]
def baseStart_240368 : Nat := 118140960795 + 240368 * 2 ^ 59
def prefixEnd_240368 : Nat := 4983230072969 + 3 ^ 40 * 240368 * 2
def baseEnd_240368 : Nat := 82282878640013861863049

theorem tailTrace_240368 : CollatzResearch.WordTrace tailWord_240368 prefixEnd_240368 82282878640013861863049 := by
  unfold tailWord_240368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383470596597631215612879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5844627462130174954150505 4383470596597631215612879)
  ·
    refine ⟨6575205894896446823419319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383470596597631215612879 6575205894896446823419319)
    ·
      refine ⟨9862808842344670235128979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575205894896446823419319 9862808842344670235128979)
      ·
        refine ⟨14794213263517005352693469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9862808842344670235128979 14794213263517005352693469)
        ·
          refine ⟨5547829973818877007260051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14794213263517005352693469 5547829973818877007260051)
          ·
            refine ⟨8321744960728315510890077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5547829973818877007260051 8321744960728315510890077)
            ·
              refine ⟨3120654360273118316583779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8321744960728315510890077 3120654360273118316583779)
              ·
                refine ⟨4680981540409677474875669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3120654360273118316583779 4680981540409677474875669)
                ·
                  refine ⟨219421009706703631634797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4680981540409677474875669 219421009706703631634797)
                  ·
                    refine ⟨82282878640013861863049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219421009706703631634797 82282878640013861863049)
                    ·
                      rfl

theorem cell22_240368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 6, 3].length) (baseStart_240368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240368 prefixEnd_240368 := by exact prefixLift 240368
  have htrace : WordTrace (prefixWord ++ tailWord_240368) baseStart_240368 baseEnd_240368 := by
    simpa [prefixWord, tailWord_240368, baseEnd_240368] using wordTrace_append hprefix tailTrace_240368
  have hstable : (prefixWord ++ tailWord_240368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240368).length < 2 ^ (prefixWord ++ tailWord_240368).sum := by decide
  have hdescent : baseEnd_240368 < baseStart_240368 := by decide
  rcases family_descends (prefixWord ++ tailWord_240368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240385 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_240385 : Nat := 118140960795 + 240385 * 2 ^ 59
def prefixEnd_240385 : Nat := 4983230072969 + 3 ^ 40 * 240385 * 2
def baseEnd_240385 : Nat := 82288698087431484187997

theorem tailTrace_240385 : CollatzResearch.WordTrace tailWord_240385 prefixEnd_240385 82288698087431484187997 := by
  unfold tailWord_240385
  simp only [CollatzResearch.WordTrace]
  refine ⟨8767561234133674334594609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5845040822755782889729739 8767561234133674334594609)
  ·
    refine ⟨6575670925600255750945957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8767561234133674334594609 6575670925600255750945957)
    ·
      refine ⟨1232938298550047953302367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6575670925600255750945957 1232938298550047953302367)
      ·
        refine ⟨1849407447825071929953551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1232938298550047953302367 1849407447825071929953551)
        ·
          refine ⟨2774111171737607894930327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1849407447825071929953551 2774111171737607894930327)
          ·
            refine ⟨4161166757606411842395491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2774111171737607894930327 4161166757606411842395491)
            ·
              refine ⟨6241750136409617763593237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4161166757606411842395491 6241750136409617763593237)
              ·
                refine ⟨292582037644200832668433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6241750136409617763593237 292582037644200832668433)
                ·
                  refine ⟨219436528233150624501325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292582037644200832668433 219436528233150624501325)
                  ·
                    refine ⟨82288698087431484187997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219436528233150624501325 82288698087431484187997)
                    ·
                      rfl

theorem cell22_240385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_240385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240385 prefixEnd_240385 := by exact prefixLift 240385
  have htrace : WordTrace (prefixWord ++ tailWord_240385) baseStart_240385 baseEnd_240385 := by
    simpa [prefixWord, tailWord_240385, baseEnd_240385] using wordTrace_append hprefix tailTrace_240385
  have hstable : (prefixWord ++ tailWord_240385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240385).length < 2 ^ (prefixWord ++ tailWord_240385).sum := by decide
  have hdescent : baseEnd_240385 < baseStart_240385 := by decide
  rcases family_descends (prefixWord ++ tailWord_240385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240438 : List Nat := [5, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_240438 : Nat := 118140960795 + 240438 * 2 ^ 59
def prefixEnd_240438 : Nat := 4983230072969 + 3 ^ 40 * 240438 * 2
def baseEnd_240438 : Nat := 27435613690185670870945

theorem tailTrace_240438 : CollatzResearch.WordTrace tailWord_240438 prefixEnd_240438 27435613690185670870945 := by
  unfold tailWord_240438
  simp only [CollatzResearch.WordTrace]
  refine ⟨548093393933854024142123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5846329535294442924182645 548093393933854024142123)
  ·
    refine ⟨822140090900781036213185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 548093393933854024142123 822140090900781036213185)
    ·
      refine ⟨616605068175585777159889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 822140090900781036213185 616605068175585777159889)
      ·
        refine ⟨462453801131689332869917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 616605068175585777159889 462453801131689332869917)
        ·
          refine ⟨173420175424383499826219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 462453801131689332869917 173420175424383499826219)
          ·
            refine ⟨260130263136575249739329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173420175424383499826219 260130263136575249739329)
            ·
              refine ⟨195097697352431437304497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260130263136575249739329 195097697352431437304497)
              ·
                refine ⟨146323273014323577978373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195097697352431437304497 146323273014323577978373)
                ·
                  refine ⟨27435613690185670870945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146323273014323577978373 27435613690185670870945)
                  ·
                    rfl

theorem cell22_240438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_240438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240438 prefixEnd_240438 := by exact prefixLift 240438
  have htrace : WordTrace (prefixWord ++ tailWord_240438) baseStart_240438 baseEnd_240438 := by
    simpa [prefixWord, tailWord_240438, baseEnd_240438] using wordTrace_append hprefix tailTrace_240438
  have hstable : (prefixWord ++ tailWord_240438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240438).length < 2 ^ (prefixWord ++ tailWord_240438).sum := by decide
  have hdescent : baseEnd_240438 < baseStart_240438 := by decide
  rcases family_descends (prefixWord ++ tailWord_240438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240449 : List Nat := [1, 2, 5, 3, 2, 1, 1, 7]
def baseStart_240449 : Nat := 118140960795 + 240449 * 2 ^ 59
def prefixEnd_240449 : Nat := 4983230072969 + 3 ^ 40 * 240449 * 2
def baseEnd_240449 : Nat := 9145622955039627843089

theorem tailTrace_240449 : CollatzResearch.WordTrace tailWord_240449 prefixEnd_240449 9145622955039627843089 := by
  unfold tailWord_240449
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769895505901813264924401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5846597003934542176616267 8769895505901813264924401)
  ·
    refine ⟨6577421629426359948693301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8769895505901813264924401 6577421629426359948693301)
    ·
      refine ⟨616633277758721245189997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6577421629426359948693301 616633277758721245189997)
      ·
        refine ⟨231237479159520466946249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 616633277758721245189997 231237479159520466946249)
        ·
          refine ⟨173428109369640350209687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231237479159520466946249 173428109369640350209687)
          ·
            refine ⟨260142164054460525314531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173428109369640350209687 260142164054460525314531)
            ·
              refine ⟨390213246081690787971797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260142164054460525314531 390213246081690787971797)
              ·
                refine ⟨9145622955039627843089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 390213246081690787971797 9145622955039627843089)
                ·
                  rfl

theorem cell22_240449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 7].length) (baseStart_240449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240449 prefixEnd_240449 := by exact prefixLift 240449
  have htrace : WordTrace (prefixWord ++ tailWord_240449) baseStart_240449 baseEnd_240449 := by
    simpa [prefixWord, tailWord_240449, baseEnd_240449] using wordTrace_append hprefix tailTrace_240449
  have hstable : (prefixWord ++ tailWord_240449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240449).length < 2 ^ (prefixWord ++ tailWord_240449).sum := by decide
  have hdescent : baseEnd_240449 < baseStart_240449 := by decide
  rcases family_descends (prefixWord ++ tailWord_240449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240460 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_240460 : Nat := 118140960795 + 240460 * 2 ^ 59
def prefixEnd_240460 : Nat := 4983230072969 + 3 ^ 40 * 240460 * 2
def baseEnd_240460 : Nat := 27438124040052096187589

theorem tailTrace_240460 : CollatzResearch.WordTrace tailWord_240460 prefixEnd_240460 27438124040052096187589 := by
  unfold tailWord_240460
  simp only [CollatzResearch.WordTrace]
  refine ⟨4385148354430981071787417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5846864472574641429049889 4385148354430981071787417)
  ·
    refine ⟨3288861265823235803840563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4385148354430981071787417 3288861265823235803840563)
    ·
      refine ⟨4933291898734853705760845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3288861265823235803840563 4933291898734853705760845)
      ·
        refine ⟨1849984462025570139660317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4933291898734853705760845 1849984462025570139660317)
        ·
          refine ⟨693744173259588802372619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1849984462025570139660317 693744173259588802372619)
          ·
            refine ⟨1040616259889383203558929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 693744173259588802372619 1040616259889383203558929)
            ·
              refine ⟨780462194917037402669197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1040616259889383203558929 780462194917037402669197)
              ·
                refine ⟨292673323093889026000949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 780462194917037402669197 292673323093889026000949)
                ·
                  refine ⟨27438124040052096187589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292673323093889026000949 27438124040052096187589)
                  ·
                    rfl

theorem cell22_240460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_240460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240460 prefixEnd_240460 := by exact prefixLift 240460
  have htrace : WordTrace (prefixWord ++ tailWord_240460) baseStart_240460 baseEnd_240460 := by
    simpa [prefixWord, tailWord_240460, baseEnd_240460] using wordTrace_append hprefix tailTrace_240460
  have hstable : (prefixWord ++ tailWord_240460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240460).length < 2 ^ (prefixWord ++ tailWord_240460).sum := by decide
  have hdescent : baseEnd_240460 < baseStart_240460 := by decide
  rcases family_descends (prefixWord ++ tailWord_240460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240494 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_240494 : Nat := 118140960795 + 240494 * 2 ^ 59
def prefixEnd_240494 : Nat := 4983230072969 + 3 ^ 40 * 240494 * 2
def baseEnd_240494 : Nat := 27442003671663844404221

theorem tailTrace_240494 : CollatzResearch.WordTrace tailWord_240494 prefixEnd_240494 27442003671663844404221 := by
  unfold tailWord_240494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096442098842348243789067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5847691193825857300208357 1096442098842348243789067)
  ·
    refine ⟨1644663148263522365683601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1096442098842348243789067 1644663148263522365683601)
    ·
      refine ⟨1233497361197641774262701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644663148263522365683601 1233497361197641774262701)
      ·
        refine ⟨462561510449115665348513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1233497361197641774262701 462561510449115665348513)
        ·
          refine ⟨346921132836836749011385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462561510449115665348513 346921132836836749011385)
          ·
            refine ⟨260190849627627561758539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346921132836836749011385 260190849627627561758539)
            ·
              refine ⟨390286274441441342637809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260190849627627561758539 390286274441441342637809)
              ·
                refine ⟨292714705831081006978357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 390286274441441342637809 292714705831081006978357)
                ·
                  refine ⟨27442003671663844404221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 292714705831081006978357 27442003671663844404221)
                  ·
                    rfl

theorem cell22_240494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_240494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240494 prefixEnd_240494 := by exact prefixLift 240494
  have htrace : WordTrace (prefixWord ++ tailWord_240494) baseStart_240494 baseEnd_240494 := by
    simpa [prefixWord, tailWord_240494, baseEnd_240494] using wordTrace_append hprefix tailTrace_240494
  have hstable : (prefixWord ++ tailWord_240494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240494).length < 2 ^ (prefixWord ++ tailWord_240494).sum := by decide
  have hdescent : baseEnd_240494 < baseStart_240494 := by decide
  rcases family_descends (prefixWord ++ tailWord_240494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240503 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_240503 : Nat := 118140960795 + 240503 * 2 ^ 59
def prefixEnd_240503 : Nat := 4983230072969 + 3 ^ 40 * 240503 * 2
def baseEnd_240503 : Nat := 82329091898918509737635

theorem tailTrace_240503 : CollatzResearch.WordTrace tailWord_240503 prefixEnd_240503 82329091898918509737635 := by
  unfold tailWord_240503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771865047706180487390163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5847910031804120324926775 8771865047706180487390163)
  ·
    refine ⟨13157797571559270731085245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8771865047706180487390163 13157797571559270731085245)
    ·
      refine ⟨4934174089334726524156967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13157797571559270731085245 4934174089334726524156967)
      ·
        refine ⟨7401261134002089786235451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934174089334726524156967 7401261134002089786235451)
        ·
          refine ⟨11101891701003134679353177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7401261134002089786235451 11101891701003134679353177)
          ·
            refine ⟨8326418775752351009514883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11101891701003134679353177 8326418775752351009514883)
            ·
              refine ⟨12489628163628526514272325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326418775752351009514883 12489628163628526514272325)
              ·
                refine ⟨2341805280680348721426061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12489628163628526514272325 2341805280680348721426061)
                ·
                  refine ⟨878176980255130770534773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2341805280680348721426061 878176980255130770534773)
                  ·
                    refine ⟨82329091898918509737635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 878176980255130770534773 82329091898918509737635)
                    ·
                      rfl

theorem cell22_240503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_240503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240503 prefixEnd_240503 := by exact prefixLift 240503
  have htrace : WordTrace (prefixWord ++ tailWord_240503) baseStart_240503 baseEnd_240503 := by
    simpa [prefixWord, tailWord_240503, baseEnd_240503] using wordTrace_append hprefix tailTrace_240503
  have hstable : (prefixWord ++ tailWord_240503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240503).length < 2 ^ (prefixWord ++ tailWord_240503).sum := by decide
  have hdescent : baseEnd_240503 < baseStart_240503 := by decide
  rcases family_descends (prefixWord ++ tailWord_240503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240505 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 6]
def baseStart_240505 : Nat := 118140960795 + 240505 * 2 ^ 59
def prefixEnd_240505 : Nat := 4983230072969 + 3 ^ 40 * 240505 * 2
def baseEnd_240505 : Nat := 27443258846597057062543

theorem tailTrace_240505 : CollatzResearch.WordTrace tailWord_240505 prefixEnd_240505 27443258846597057062543 := by
  unfold tailWord_240505
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771937993698934828962969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5847958662465956552641979 8771937993698934828962969)
  ·
    refine ⟨6578953495274201121722227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8771937993698934828962969 6578953495274201121722227)
    ·
      refine ⟨9868430242911301682583341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6578953495274201121722227 9868430242911301682583341)
      ·
        refine ⟨3700661341091738130968753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9868430242911301682583341 3700661341091738130968753)
        ·
          refine ⟨2775496005818803598226565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3700661341091738130968753 2775496005818803598226565)
          ·
            refine ⟨520405501091025674667481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2775496005818803598226565 520405501091025674667481)
            ·
              refine ⟨390304125818269256000611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 520405501091025674667481 390304125818269256000611)
              ·
                refine ⟨585456188727403884000917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 390304125818269256000611 585456188727403884000917)
                ·
                  refine ⟨27443258846597057062543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 585456188727403884000917 27443258846597057062543)
                  ·
                    rfl

theorem cell22_240505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_240505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240505 prefixEnd_240505 := by exact prefixLift 240505
  have htrace : WordTrace (prefixWord ++ tailWord_240505) baseStart_240505 baseEnd_240505 := by
    simpa [prefixWord, tailWord_240505, baseEnd_240505] using wordTrace_append hprefix tailTrace_240505
  have hstable : (prefixWord ++ tailWord_240505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240505).length < 2 ^ (prefixWord ++ tailWord_240505).sum := by decide
  have hdescent : baseEnd_240505 < baseStart_240505 := by decide
  rcases family_descends (prefixWord ++ tailWord_240505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240535 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_240535 : Nat := 118140960795 + 240535 * 2 ^ 59
def prefixEnd_240535 : Nat := 4983230072969 + 3 ^ 40 * 240535 * 2
def baseEnd_240535 : Nat := 82340046152881092937537

theorem tailTrace_240535 : CollatzResearch.WordTrace tailWord_240535 prefixEnd_240535 82340046152881092937537 := by
  unfold tailWord_240535
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773032183590249952555059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5848688122393499968370039 8773032183590249952555059)
  ·
    refine ⟨13159548275385374928832589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8773032183590249952555059 13159548275385374928832589)
    ·
      refine ⟨4934830603269515598312221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13159548275385374928832589 4934830603269515598312221)
      ·
        refine ⟨1850561476226068349367083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4934830603269515598312221 1850561476226068349367083)
        ·
          refine ⟨2775842214339102524050625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1850561476226068349367083 2775842214339102524050625)
          ·
            refine ⟨2081881660754326893037969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2775842214339102524050625 2081881660754326893037969)
            ·
              refine ⟨1561411245565745169778477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2081881660754326893037969 1561411245565745169778477)
              ·
                refine ⟨585529217087154438666929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1561411245565745169778477 585529217087154438666929)
                ·
                  refine ⟨439146912815365829000197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 585529217087154438666929 439146912815365829000197)
                  ·
                    refine ⟨82340046152881092937537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439146912815365829000197 82340046152881092937537)
                    ·
                      rfl

theorem cell22_240535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_240535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240535 prefixEnd_240535 := by exact prefixLift 240535
  have htrace : WordTrace (prefixWord ++ tailWord_240535) baseStart_240535 baseEnd_240535 := by
    simpa [prefixWord, tailWord_240535, baseEnd_240535] using wordTrace_append hprefix tailTrace_240535
  have hstable : (prefixWord ++ tailWord_240535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240535).length < 2 ^ (prefixWord ++ tailWord_240535).sum := by decide
  have hdescent : baseEnd_240535 < baseStart_240535 := by decide
  rcases family_descends (prefixWord ++ tailWord_240535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240616 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 1, 3]
def baseStart_240616 : Nat := 118140960795 + 240616 * 2 ^ 59
def prefixEnd_240616 : Nat := 4983230072969 + 3 ^ 40 * 240616 * 2
def baseEnd_240616 : Nat := 82367774108223881662289

theorem tailTrace_240616 : CollatzResearch.WordTrace tailWord_240616 prefixEnd_240616 82367774108223881662289 := by
  unfold tailWord_240616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4387993248148400393126851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5850657664197867190835801 4387993248148400393126851)
  ·
    refine ⟨6581989872222600589690277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4387993248148400393126851 6581989872222600589690277)
    ·
      refine ⟨1234123101041737610566927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6581989872222600589690277 1234123101041737610566927)
      ·
        refine ⟨1851184651562606415850391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234123101041737610566927 1851184651562606415850391)
        ·
          refine ⟨2776776977343909623775587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851184651562606415850391 2776776977343909623775587)
          ·
            refine ⟨4165165466015864435663381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2776776977343909623775587 4165165466015864435663381)
            ·
              refine ⟨195242131219493645421721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4165165466015864435663381 195242131219493645421721)
              ·
                refine ⟨146431598414620234066291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195242131219493645421721 146431598414620234066291)
                ·
                  refine ⟨219647397621930351099437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146431598414620234066291 219647397621930351099437)
                  ·
                    refine ⟨82367774108223881662289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 219647397621930351099437 82367774108223881662289)
                    ·
                      rfl

theorem cell22_240616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_240616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240616 prefixEnd_240616 := by exact prefixLift 240616
  have htrace : WordTrace (prefixWord ++ tailWord_240616) baseStart_240616 baseEnd_240616 := by
    simpa [prefixWord, tailWord_240616, baseEnd_240616] using wordTrace_append hprefix tailTrace_240616
  have hstable : (prefixWord ++ tailWord_240616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240616).length < 2 ^ (prefixWord ++ tailWord_240616).sum := by decide
  have hdescent : baseEnd_240616 < baseStart_240616 := by decide
  rcases family_descends (prefixWord ++ tailWord_240616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240674 : List Nat := [3, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_240674 : Nat := 118140960795 + 240674 * 2 ^ 59
def prefixEnd_240674 : Nat := 4983230072969 + 3 ^ 40 * 240674 * 2
def baseEnd_240674 : Nat := 27462542897843687904037

theorem tailTrace_240674 : CollatzResearch.WordTrace tailWord_240674 prefixEnd_240674 27462542897843687904037 := by
  unfold tailWord_240674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194525482521669172966269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5852067953391117794576717 2194525482521669172966269)
  ·
    refine ⟨822947055945625939862351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2194525482521669172966269 822947055945625939862351)
    ·
      refine ⟨1234420583918438909793527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822947055945625939862351 1234420583918438909793527)
      ·
        refine ⟨1851630875877658364690291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1234420583918438909793527 1851630875877658364690291)
        ·
          refine ⟨2777446313816487547035437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1851630875877658364690291 2777446313816487547035437)
          ·
            refine ⟨1041542367681182830138289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2777446313816487547035437 1041542367681182830138289)
            ·
              refine ⟨781156775760887122603717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1041542367681182830138289 781156775760887122603717)
              ·
                refine ⟨146466895455166335488197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 781156775760887122603717 146466895455166335488197)
                ·
                  refine ⟨27462542897843687904037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146466895455166335488197 27462542897843687904037)
                  ·
                    rfl

theorem cell22_240674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_240674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240674 prefixEnd_240674 := by exact prefixLift 240674
  have htrace : WordTrace (prefixWord ++ tailWord_240674) baseStart_240674 baseEnd_240674 := by
    simpa [prefixWord, tailWord_240674, baseEnd_240674] using wordTrace_append hprefix tailTrace_240674
  have hstable : (prefixWord ++ tailWord_240674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240674).length < 2 ^ (prefixWord ++ tailWord_240674).sum := by decide
  have hdescent : baseEnd_240674 < baseStart_240674 := by decide
  rcases family_descends (prefixWord ++ tailWord_240674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240732 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_240732 : Nat := 118140960795 + 240732 * 2 ^ 59
def prefixEnd_240732 : Nat := 4983230072969 + 3 ^ 40 * 240732 * 2
def baseEnd_240732 : Nat := 82407483278838245761933

theorem tailTrace_240732 : CollatzResearch.WordTrace tailWord_240732 prefixEnd_240732 82407483278838245761933 := by
  unfold tailWord_240732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4390108681938276298738225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5853478242584368398317633 4390108681938276298738225)
  ·
    refine ⟨3292581511453707224053669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4390108681938276298738225 3292581511453707224053669)
    ·
      refine ⟨617359033397570104510063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3292581511453707224053669 617359033397570104510063)
      ·
        refine ⟨926038550096355156765095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617359033397570104510063 926038550096355156765095)
        ·
          refine ⟨1389057825144532735147643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926038550096355156765095 1389057825144532735147643)
          ·
            refine ⟨2083586737716799102721465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1389057825144532735147643 2083586737716799102721465)
            ·
              refine ⟨1562690053287599327041099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2083586737716799102721465 1562690053287599327041099)
              ·
                refine ⟨2344035079931398990561649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1562690053287599327041099 2344035079931398990561649)
                ·
                  refine ⟨1758026309948549242921237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2344035079931398990561649 1758026309948549242921237)
                  ·
                    refine ⟨82407483278838245761933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1758026309948549242921237 82407483278838245761933)
                    ·
                      rfl

theorem cell22_240732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_240732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240732 prefixEnd_240732 := by exact prefixLift 240732
  have htrace : WordTrace (prefixWord ++ tailWord_240732) baseStart_240732 baseEnd_240732 := by
    simpa [prefixWord, tailWord_240732, baseEnd_240732] using wordTrace_append hprefix tailTrace_240732
  have hstable : (prefixWord ++ tailWord_240732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240732).length < 2 ^ (prefixWord ++ tailWord_240732).sum := by decide
  have hdescent : baseEnd_240732 < baseStart_240732 := by decide
  rcases family_descends (prefixWord ++ tailWord_240732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240794 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_240794 : Nat := 118140960795 + 240794 * 2 ^ 59
def prefixEnd_240794 : Nat := 4983230072969 + 3 ^ 40 * 240794 * 2
def baseEnd_240794 : Nat := 82428707145890750711743

theorem tailTrace_240794 : CollatzResearch.WordTrace tailWord_240794 prefixEnd_240794 82428707145890750711743 := by
  unfold tailWord_240794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195619672412984296558359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5854985793101291457488957 2195619672412984296558359)
  ·
    refine ⟨3293429508619476444837539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2195619672412984296558359 3293429508619476444837539)
    ·
      refine ⟨4940144262929214667256309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3293429508619476444837539 4940144262929214667256309)
      ·
        refine ⟨463138524649613875055279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4940144262929214667256309 463138524649613875055279)
        ·
          refine ⟨694707786974420812582919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463138524649613875055279 694707786974420812582919)
          ·
            refine ⟨1042061680461631218874379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 694707786974420812582919 1042061680461631218874379)
            ·
              refine ⟨1563092520692446828311569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042061680461631218874379 1563092520692446828311569)
              ·
                refine ⟨1172319390519335121233677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1563092520692446828311569 1172319390519335121233677)
                ·
                  refine ⟨439619771444750670462629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1172319390519335121233677 439619771444750670462629)
                  ·
                    refine ⟨82428707145890750711743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439619771444750670462629 82428707145890750711743)
                    ·
                      rfl

theorem cell22_240794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_240794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240794 prefixEnd_240794 := by exact prefixLift 240794
  have htrace : WordTrace (prefixWord ++ tailWord_240794) baseStart_240794 baseEnd_240794 := by
    simpa [prefixWord, tailWord_240794, baseEnd_240794] using wordTrace_append hprefix tailTrace_240794
  have hstable : (prefixWord ++ tailWord_240794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240794).length < 2 ^ (prefixWord ++ tailWord_240794).sum := by decide
  have hdescent : baseEnd_240794 < baseStart_240794 := by decide
  rcases family_descends (prefixWord ++ tailWord_240794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240828 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 1, 4]
def baseStart_240828 : Nat := 118140960795 + 240828 * 2 ^ 59
def prefixEnd_240828 : Nat := 4983230072969 + 3 ^ 40 * 240828 * 2
def baseEnd_240828 : Nat := 82440346040725995361639

theorem tailTrace_240828 : CollatzResearch.WordTrace tailWord_240828 prefixEnd_240828 82440346040725995361639 := by
  unfold tailWord_240828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4391859385764380496485569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5855812514352507328647425 4391859385764380496485569)
  ·
    refine ⟨3293894539323285372364177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4391859385764380496485569 3293894539323285372364177)
    ·
      refine ⟨2470420904492464029273133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3293894539323285372364177 2470420904492464029273133)
      ·
        refine ⟨926407839184674010977425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2470420904492464029273133 926407839184674010977425)
        ·
          refine ⟨694805879388505508233069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 926407839184674010977425 694805879388505508233069)
          ·
            refine ⟨260552204770689565587401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694805879388505508233069 260552204770689565587401)
            ·
              refine ⟨195414153578017174190551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260552204770689565587401 195414153578017174190551)
              ·
                refine ⟨293121230367025761285827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 195414153578017174190551 293121230367025761285827)
                ·
                  refine ⟨439681845550538641928741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 293121230367025761285827 439681845550538641928741)
                  ·
                    refine ⟨82440346040725995361639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 439681845550538641928741 82440346040725995361639)
                    ·
                      rfl

theorem cell22_240828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_240828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240828 prefixEnd_240828 := by exact prefixLift 240828
  have htrace : WordTrace (prefixWord ++ tailWord_240828) baseStart_240828 baseEnd_240828 := by
    simpa [prefixWord, tailWord_240828, baseEnd_240828] using wordTrace_append hprefix tailTrace_240828
  have hstable : (prefixWord ++ tailWord_240828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240828).length < 2 ^ (prefixWord ++ tailWord_240828).sum := by decide
  have hdescent : baseEnd_240828 < baseStart_240828 := by decide
  rcases family_descends (prefixWord ++ tailWord_240828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240950 : List Nat := [5, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_240950 : Nat := 118140960795 + 240950 * 2 ^ 59
def prefixEnd_240950 : Nat := 4983230072969 + 3 ^ 40 * 240950 * 2
def baseEnd_240950 : Nat := 27494036377986114603755

theorem tailTrace_240950 : CollatzResearch.WordTrace tailWord_240950 prefixEnd_240950 27494036377986114603755 := by
  unfold tailWord_240950
  simp only [CollatzResearch.WordTrace]
  refine ⟨549260529817923489307019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5858778984724517219274869 549260529817923489307019)
  ·
    refine ⟨823890794726885233960529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549260529817923489307019 823890794726885233960529)
    ·
      refine ⟨617918096045163925470397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 823890794726885233960529 617918096045163925470397)
      ·
        refine ⟨231719286016936472051399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 617918096045163925470397 231719286016936472051399)
        ·
          refine ⟨347578929025404708077099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231719286016936472051399 347578929025404708077099)
          ·
            refine ⟨521368393538107062115649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347578929025404708077099 521368393538107062115649)
            ·
              refine ⟨391026295153580296586737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521368393538107062115649 391026295153580296586737)
              ·
                refine ⟨293269721365185222440053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 391026295153580296586737 293269721365185222440053)
                ·
                  refine ⟨27494036377986114603755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 293269721365185222440053 27494036377986114603755)
                  ·
                    rfl

theorem cell22_240950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_240950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240950 prefixEnd_240950 := by exact prefixLift 240950
  have htrace : WordTrace (prefixWord ++ tailWord_240950) baseStart_240950 baseEnd_240950 := by
    simpa [prefixWord, tailWord_240950, baseEnd_240950] using wordTrace_append hprefix tailTrace_240950
  have hstable : (prefixWord ++ tailWord_240950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240950).length < 2 ^ (prefixWord ++ tailWord_240950).sum := by decide
  have hdescent : baseEnd_240950 < baseStart_240950 := by decide
  rcases family_descends (prefixWord ++ tailWord_240950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_240974 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_240974 : Nat := 118140960795 + 240974 * 2 ^ 59
def prefixEnd_240974 : Nat := 4983230072969 + 3 ^ 40 * 240974 * 2
def baseEnd_240974 : Nat := 82490324824430281211191

theorem tailTrace_240974 : CollatzResearch.WordTrace tailWord_240974 prefixEnd_240974 82490324824430281211191 := by
  unfold tailWord_240974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1098630478624978490973247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5859362552666551951857317 1098630478624978490973247)
  ·
    refine ⟨1647945717937467736459871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1098630478624978490973247 1647945717937467736459871)
    ·
      refine ⟨2471918576906201604689807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1647945717937467736459871 2471918576906201604689807)
      ·
        refine ⟨3707877865359302407034711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2471918576906201604689807 3707877865359302407034711)
        ·
          refine ⟨5561816798038953610552067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3707877865359302407034711 5561816798038953610552067)
          ·
            refine ⟨8342725197058430415828101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5561816798038953610552067 8342725197058430415828101)
            ·
              refine ⟨1564260974448455702967769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8342725197058430415828101 1564260974448455702967769)
              ·
                refine ⟨1173195730836341777225827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1564260974448455702967769 1173195730836341777225827)
                ·
                  refine ⟨1759793596254512665838741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1173195730836341777225827 1759793596254512665838741)
                  ·
                    refine ⟨82490324824430281211191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1759793596254512665838741 82490324824430281211191)
                    ·
                      rfl

theorem cell22_240974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_240974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_240974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_240974 prefixEnd_240974 := by exact prefixLift 240974
  have htrace : WordTrace (prefixWord ++ tailWord_240974) baseStart_240974 baseEnd_240974 := by
    simpa [prefixWord, tailWord_240974, baseEnd_240974] using wordTrace_append hprefix tailTrace_240974
  have hstable : (prefixWord ++ tailWord_240974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_240974).length < 2 ^ (prefixWord ++ tailWord_240974).sum := by decide
  have hdescent : baseEnd_240974 < baseStart_240974 := by decide
  rcases family_descends (prefixWord ++ tailWord_240974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
