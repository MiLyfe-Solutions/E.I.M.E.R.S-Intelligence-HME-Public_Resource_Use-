import V185TrunkScan19Chunk005

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_60586 : List Nat := [3, 1, 5, 1, 1, 8]
def baseStart_60586 : Nat := 118140960795 + 60586 * 2 ^ 59
def prefixEnd_60586 : Nat := 4983230072969 + 3 ^ 40 * 60586 * 2
def baseEnd_60586 : Nat := 2048377872158366465605

theorem tailTrace_60586 : CollatzResearch.WordTrace tailWord_60586 prefixEnd_60586 2048377872158366465605 := by
  unfold tailWord_60586
  simp only [CollatzResearch.WordTrace]
  refine ⟨552438239628686027530403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1473168639009829406747741 552438239628686027530403)
  ·
    refine ⟨828657359443029041295605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552438239628686027530403 828657359443029041295605)
    ·
      refine ⟨77686627447783972621463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 828657359443029041295605 77686627447783972621463)
      ·
        refine ⟨116529941171675958932195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77686627447783972621463 116529941171675958932195)
        ·
          refine ⟨174794911757513938398293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116529941171675958932195 174794911757513938398293)
          ·
            refine ⟨2048377872158366465605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 174794911757513938398293 2048377872158366465605)
            ·
              rfl

theorem cell19_60586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_60586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60586 prefixEnd_60586 := by exact prefixLift 60586
  have htrace : WordTrace (prefixWord ++ tailWord_60586) baseStart_60586 baseEnd_60586 := by
    simpa [prefixWord, tailWord_60586, baseEnd_60586] using wordTrace_append hprefix tailTrace_60586
  have hstable : (prefixWord ++ tailWord_60586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60586).length < 2 ^ (prefixWord ++ tailWord_60586).sum := by decide
  have hdescent : baseEnd_60586 < baseStart_60586 := by decide
  rcases family_descends (prefixWord ++ tailWord_60586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60607 : List Nat := [1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_60607 : Nat := 118140960795 + 60607 * 2 ^ 59
def prefixEnd_60607 : Nat := 4983230072969 + 3 ^ 40 * 60607 * 2
def baseEnd_60607 : Nat := 18441790830903471723721

theorem tailTrace_60607 : CollatzResearch.WordTrace tailWord_60607 prefixEnd_60607 18441790830903471723721 := by
  unfold tailWord_60607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210518891438664696636075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1473679260959109797757383 2210518891438664696636075)
  ·
    refine ⟨3315778337157997044954113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210518891438664696636075 3315778337157997044954113)
    ·
      refine ⟨2486833752868497783715585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3315778337157997044954113 2486833752868497783715585)
      ·
        refine ⟨1865125314651373337786689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2486833752868497783715585 1865125314651373337786689)
        ·
          refine ⟨1398843985988530003340017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1865125314651373337786689 1398843985988530003340017)
          ·
            refine ⟨1049132989491397502505013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1398843985988530003340017 1049132989491397502505013)
            ·
              refine ⟨98356217764818515859845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1049132989491397502505013 98356217764818515859845)
              ·
                refine ⟨18441790830903471723721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98356217764818515859845 18441790830903471723721)
                ·
                  rfl

theorem cell19_60607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_60607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60607 prefixEnd_60607 := by exact prefixLift 60607
  have htrace : WordTrace (prefixWord ++ tailWord_60607) baseStart_60607 baseEnd_60607 := by
    simpa [prefixWord, tailWord_60607, baseEnd_60607] using wordTrace_append hprefix tailTrace_60607
  have hstable : (prefixWord ++ tailWord_60607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60607).length < 2 ^ (prefixWord ++ tailWord_60607).sum := by decide
  have hdescent : baseEnd_60607 < baseStart_60607 := by decide
  rcases family_descends (prefixWord ++ tailWord_60607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60622 : List Nat := [4, 1, 1, 1, 5, 1, 3, 3]
def baseStart_60622 : Nat := 118140960795 + 60622 * 2 ^ 59
def prefixEnd_60622 : Nat := 4983230072969 + 3 ^ 40 * 60622 * 2
def baseEnd_60622 : Nat := 18446355103387881390347

theorem tailTrace_60622 : CollatzResearch.WordTrace tailWord_60622 prefixEnd_60622 18446355103387881390347 := by
  unfold tailWord_60622
  simp only [CollatzResearch.WordTrace]
  refine ⟨276383248298040282304015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1474043990922881505621413 276383248298040282304015)
  ·
    refine ⟨414574872447060423456023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276383248298040282304015 414574872447060423456023)
    ·
      refine ⟨621862308670590635184035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 414574872447060423456023 621862308670590635184035)
      ·
        refine ⟨932793463005885952776053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 621862308670590635184035 932793463005885952776053)
        ·
          refine ⟨87449387156801808072755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 932793463005885952776053 87449387156801808072755)
          ·
            refine ⟨131174080735202712109133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87449387156801808072755 131174080735202712109133)
            ·
              refine ⟨49190280275701017040925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131174080735202712109133 49190280275701017040925)
              ·
                refine ⟨18446355103387881390347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49190280275701017040925 18446355103387881390347)
                ·
                  rfl

theorem cell19_60622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_60622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60622 prefixEnd_60622 := by exact prefixLift 60622
  have htrace : WordTrace (prefixWord ++ tailWord_60622) baseStart_60622 baseEnd_60622 := by
    simpa [prefixWord, tailWord_60622, baseEnd_60622] using wordTrace_append hprefix tailTrace_60622
  have hstable : (prefixWord ++ tailWord_60622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60622).length < 2 ^ (prefixWord ++ tailWord_60622).sum := by decide
  have hdescent : baseEnd_60622 < baseStart_60622 := by decide
  rcases family_descends (prefixWord ++ tailWord_60622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60683 : List Nat := [1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_60683 : Nat := 118140960795 + 60683 * 2 ^ 59
def prefixEnd_60683 : Nat := 4983230072969 + 3 ^ 40 * 60683 * 2
def baseEnd_60683 : Nat := 18464916478157814034625

theorem tailTrace_60683 : CollatzResearch.WordTrace tailWord_60683 prefixEnd_60683 18464916478157814034625 := by
  unfold tailWord_60683
  simp only [CollatzResearch.WordTrace]
  refine ⟨2213290839163329676402703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1475527226108886450935135 2213290839163329676402703)
  ·
    refine ⟨3319936258744994514604055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2213290839163329676402703 3319936258744994514604055)
    ·
      refine ⟨4979904388117491771906083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3319936258744994514604055 4979904388117491771906083)
      ·
        refine ⟨7469856582176237657859125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4979904388117491771906083 7469856582176237657859125)
        ·
          refine ⟨700299054579022280424293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7469856582176237657859125 700299054579022280424293)
          ·
            refine ⟨131306072733566677579555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 700299054579022280424293 131306072733566677579555)
            ·
              refine ⟨196959109100350016369333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131306072733566677579555 196959109100350016369333)
              ·
                refine ⟨18464916478157814034625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 196959109100350016369333 18464916478157814034625)
                ·
                  rfl

theorem cell19_60683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_60683 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60683 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60683 prefixEnd_60683 := by exact prefixLift 60683
  have htrace : WordTrace (prefixWord ++ tailWord_60683) baseStart_60683 baseEnd_60683 := by
    simpa [prefixWord, tailWord_60683, baseEnd_60683] using wordTrace_append hprefix tailTrace_60683
  have hstable : (prefixWord ++ tailWord_60683).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60683).length < 2 ^ (prefixWord ++ tailWord_60683).sum := by decide
  have hdescent : baseEnd_60683 < baseStart_60683 := by decide
  rcases family_descends (prefixWord ++ tailWord_60683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60717 : List Nat := [1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_60717 : Nat := 118140960795 + 60717 * 2 ^ 59
def prefixEnd_60717 : Nat := 4983230072969 + 3 ^ 40 * 60717 * 2
def baseEnd_60717 : Nat := 18475262162455809278977

theorem tailTrace_60717 : CollatzResearch.WordTrace tailWord_60717 prefixEnd_60717 18475262162455809278977 := by
  unfold tailWord_60717
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214530921040153483140405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1476353947360102322093603 2214530921040153483140405)
  ·
    refine ⟨207612273847514389044413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2214530921040153483140405 207612273847514389044413)
    ·
      refine ⟨77854602692817895891655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207612273847514389044413 77854602692817895891655)
      ·
        refine ⟨116781904039226843837483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77854602692817895891655 116781904039226843837483)
        ·
          refine ⟨175172856058840265756225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116781904039226843837483 175172856058840265756225)
          ·
            refine ⟨131379642044130199317169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175172856058840265756225 131379642044130199317169)
            ·
              refine ⟨98534731533097649487877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131379642044130199317169 98534731533097649487877)
              ·
                refine ⟨18475262162455809278977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98534731533097649487877 18475262162455809278977)
                ·
                  rfl

theorem cell19_60717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_60717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60717 prefixEnd_60717 := by exact prefixLift 60717
  have htrace : WordTrace (prefixWord ++ tailWord_60717) baseStart_60717 baseEnd_60717 := by
    simpa [prefixWord, tailWord_60717, baseEnd_60717] using wordTrace_append hprefix tailTrace_60717
  have hstable : (prefixWord ++ tailWord_60717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60717).length < 2 ^ (prefixWord ++ tailWord_60717).sum := by decide
  have hdescent : baseEnd_60717 < baseStart_60717 := by decide
  rcases family_descends (prefixWord ++ tailWord_60717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60721 : List Nat := [1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_60721 : Nat := 118140960795 + 60721 * 2 ^ 59
def prefixEnd_60721 : Nat := 4983230072969 + 3 ^ 40 * 60721 * 2
def baseEnd_60721 : Nat := 18476479301784985190077

theorem tailTrace_60721 : CollatzResearch.WordTrace tailWord_60721 prefixEnd_60721 18476479301784985190077 := by
  unfold tailWord_60721
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214676813025662166286017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1476451208683774777524011 2214676813025662166286017)
  ·
    refine ⟨1661007609769246624714513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2214676813025662166286017 1661007609769246624714513)
    ·
      refine ⟨1245755707326934968535885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1661007609769246624714513 1245755707326934968535885)
      ·
        refine ⟨467158390247600613200957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1245755707326934968535885 467158390247600613200957)
        ·
          refine ⟨175184396342850229950359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 467158390247600613200957 175184396342850229950359)
          ·
            refine ⟨262776594514275344925539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175184396342850229950359 262776594514275344925539)
            ·
              refine ⟨394164891771413017388309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262776594514275344925539 394164891771413017388309)
              ·
                refine ⟨18476479301784985190077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 394164891771413017388309 18476479301784985190077)
                ·
                  rfl

theorem cell19_60721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_60721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60721 prefixEnd_60721 := by exact prefixLift 60721
  have htrace : WordTrace (prefixWord ++ tailWord_60721) baseStart_60721 baseEnd_60721 := by
    simpa [prefixWord, tailWord_60721, baseEnd_60721] using wordTrace_append hprefix tailTrace_60721
  have hstable : (prefixWord ++ tailWord_60721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60721).length < 2 ^ (prefixWord ++ tailWord_60721).sum := by decide
  have hdescent : baseEnd_60721 < baseStart_60721 := by decide
  rcases family_descends (prefixWord ++ tailWord_60721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60814 : List Nat := [4, 1, 1, 4, 2, 1, 6]
def baseStart_60814 : Nat := 118140960795 + 60814 * 2 ^ 59
def prefixEnd_60814 : Nat := 4983230072969 + 3 ^ 40 * 60814 * 2
def baseEnd_60814 : Nat := 6168259263729441707719

theorem tailTrace_60814 : CollatzResearch.WordTrace tailWord_60814 prefixEnd_60814 6168259263729441707719 := by
  unfold tailWord_60814
  simp only [CollatzResearch.WordTrace]
  refine ⟨277258600211092381177687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1478712534459159366280997 277258600211092381177687)
  ·
    refine ⟨415887900316638571766531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 277258600211092381177687 415887900316638571766531)
    ·
      refine ⟨623831850474957857649797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 415887900316638571766531 623831850474957857649797)
      ·
        refine ⟨116968471964054598309337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 623831850474957857649797 116968471964054598309337)
        ·
          refine ⟨87726353973040948732003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116968471964054598309337 87726353973040948732003)
          ·
            refine ⟨131589530959561423098005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87726353973040948732003 131589530959561423098005)
            ·
              refine ⟨6168259263729441707719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 131589530959561423098005 6168259263729441707719)
              ·
                rfl

theorem cell19_60814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_60814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60814 prefixEnd_60814 := by exact prefixLift 60814
  have htrace : WordTrace (prefixWord ++ tailWord_60814) baseStart_60814 baseEnd_60814 := by
    simpa [prefixWord, tailWord_60814, baseEnd_60814] using wordTrace_append hprefix tailTrace_60814
  have hstable : (prefixWord ++ tailWord_60814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60814).length < 2 ^ (prefixWord ++ tailWord_60814).sum := by decide
  have hdescent : baseEnd_60814 < baseStart_60814 := by decide
  rcases family_descends (prefixWord ++ tailWord_60814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60875 : List Nat := [1, 1, 1, 1, 3, 3, 9]
def baseStart_60875 : Nat := 118140960795 + 60875 * 2 ^ 59
def prefixEnd_60875 : Nat := 4983230072969 + 3 ^ 40 * 60875 * 2
def baseEnd_60875 : Nat := 6174446388652752589145

theorem tailTrace_60875 : CollatzResearch.WordTrace tailWord_60875 prefixEnd_60875 6174446388652752589145 := by
  unfold tailWord_60875
  simp only [CollatzResearch.WordTrace]
  refine ⟨2220293654467746467392079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1480195769645164311594719 2220293654467746467392079)
  ·
    refine ⟨3330440481701619701088119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2220293654467746467392079 3330440481701619701088119)
    ·
      refine ⟨4995660722552429551632179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3330440481701619701088119 4995660722552429551632179)
      ·
        refine ⟨7493491083828644327448269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4995660722552429551632179 7493491083828644327448269)
        ·
          refine ⟨2810059156435741622793101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7493491083828644327448269 2810059156435741622793101)
          ·
            refine ⟨1053772183663403108547413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2810059156435741622793101 1053772183663403108547413)
            ·
              refine ⟨6174446388652752589145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1053772183663403108547413 6174446388652752589145)
              ·
                rfl

theorem cell19_60875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_60875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60875 prefixEnd_60875 := by exact prefixLift 60875
  have htrace : WordTrace (prefixWord ++ tailWord_60875) baseStart_60875 baseEnd_60875 := by
    simpa [prefixWord, tailWord_60875, baseEnd_60875] using wordTrace_append hprefix tailTrace_60875
  have hstable : (prefixWord ++ tailWord_60875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60875).length < 2 ^ (prefixWord ++ tailWord_60875).sum := by decide
  have hdescent : baseEnd_60875 < baseStart_60875 := by decide
  rcases family_descends (prefixWord ++ tailWord_60875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60926 : List Nat := [4, 2, 2, 3, 2, 6]
def baseStart_60926 : Nat := 118140960795 + 60926 * 2 ^ 59
def prefixEnd_60926 : Nat := 4983230072969 + 3 ^ 40 * 60926 * 2
def baseEnd_60926 : Nat := 2059873076933916737107

theorem tailTrace_60926 : CollatzResearch.WordTrace tailWord_60926 prefixEnd_60926 2059873076933916737107 := by
  unfold tailWord_60926
  simp only [CollatzResearch.WordTrace]
  refine ⟨277769222160372772187329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1481435851521988118332421 277769222160372772187329)
  ·
    refine ⟨208326916620279579140497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 277769222160372772187329 208326916620279579140497)
    ·
      refine ⟨156245187465209684355373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208326916620279579140497 156245187465209684355373)
      ·
        refine ⟨58591945299453631633265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156245187465209684355373 58591945299453631633265)
        ·
          refine ⟨43943958974590223724949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58591945299453631633265 43943958974590223724949)
          ·
            refine ⟨2059873076933916737107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43943958974590223724949 2059873076933916737107)
            ·
              rfl

theorem cell19_60926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_60926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60926 prefixEnd_60926 := by exact prefixLift 60926
  have htrace : WordTrace (prefixWord ++ tailWord_60926) baseStart_60926 baseEnd_60926 := by
    simpa [prefixWord, tailWord_60926, baseEnd_60926] using wordTrace_append hprefix tailTrace_60926
  have hstable : (prefixWord ++ tailWord_60926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60926).length < 2 ^ (prefixWord ++ tailWord_60926).sum := by decide
  have hdescent : baseEnd_60926 < baseStart_60926 := by decide
  rcases family_descends (prefixWord ++ tailWord_60926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60941 : List Nat := [1, 7, 1, 1, 3, 1, 1, 4]
def baseStart_60941 : Nat := 118140960795 + 60941 * 2 ^ 59
def prefixEnd_60941 : Nat := 4983230072969 + 3 ^ 40 * 60941 * 2
def baseEnd_60941 : Nat := 18543421964889660300589

theorem tailTrace_60941 : CollatzResearch.WordTrace tailWord_60941 prefixEnd_60941 18543421964889660300589 := by
  unfold tailWord_60941
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222700872228639739294677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1481800581485759826196451 2222700872228639739294677)
  ·
    refine ⟨52094551692858743889719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2222700872228639739294677 52094551692858743889719)
    ·
      refine ⟨78141827539288115834579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52094551692858743889719 78141827539288115834579)
      ·
        refine ⟨117212741308932173751869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78141827539288115834579 117212741308932173751869)
        ·
          refine ⟨43954777990849565156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117212741308932173751869 43954777990849565156951)
          ·
            refine ⟨65932166986274347735427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43954777990849565156951 65932166986274347735427)
            ·
              refine ⟨98898250479411521603141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65932166986274347735427 98898250479411521603141)
              ·
                refine ⟨18543421964889660300589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98898250479411521603141 18543421964889660300589)
                ·
                  rfl

theorem cell19_60941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 4].length) (baseStart_60941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60941 prefixEnd_60941 := by exact prefixLift 60941
  have htrace : WordTrace (prefixWord ++ tailWord_60941) baseStart_60941 baseEnd_60941 := by
    simpa [prefixWord, tailWord_60941, baseEnd_60941] using wordTrace_append hprefix tailTrace_60941
  have hstable : (prefixWord ++ tailWord_60941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60941).length < 2 ^ (prefixWord ++ tailWord_60941).sum := by decide
  have hdescent : baseEnd_60941 < baseStart_60941 := by decide
  rcases family_descends (prefixWord ++ tailWord_60941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60949 : List Nat := [1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_60949 : Nat := 118140960795 + 60949 * 2 ^ 59
def prefixEnd_60949 : Nat := 4983230072969 + 3 ^ 40 * 60949 * 2
def baseEnd_60949 : Nat := 18545856243548012122789

theorem tailTrace_60949 : CollatzResearch.WordTrace tailWord_60949 prefixEnd_60949 18545856243548012122789 := by
  unfold tailWord_60949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2222992656199657105585901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1481995104133104737057267 2222992656199657105585901)
  ·
    refine ⟨833622246074871414594713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2222992656199657105585901 833622246074871414594713)
    ·
      refine ⟨625216684556153560946035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 833622246074871414594713 625216684556153560946035)
      ·
        refine ⟨937825026834230341419053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 625216684556153560946035 937825026834230341419053)
        ·
          refine ⟨351684385062836378032145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 937825026834230341419053 351684385062836378032145)
          ·
            refine ⟨263763288797127283524109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 351684385062836378032145 263763288797127283524109)
            ·
              refine ⟨98911233298922731321541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 263763288797127283524109 98911233298922731321541)
              ·
                refine ⟨18545856243548012122789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98911233298922731321541 18545856243548012122789)
                ·
                  rfl

theorem cell19_60949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_60949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_60949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_60949 prefixEnd_60949 := by exact prefixLift 60949
  have htrace : WordTrace (prefixWord ++ tailWord_60949) baseStart_60949 baseEnd_60949 := by
    simpa [prefixWord, tailWord_60949, baseEnd_60949] using wordTrace_append hprefix tailTrace_60949
  have hstable : (prefixWord ++ tailWord_60949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60949).length < 2 ^ (prefixWord ++ tailWord_60949).sum := by decide
  have hdescent : baseEnd_60949 < baseStart_60949 := by decide
  rcases family_descends (prefixWord ++ tailWord_60949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61008 : List Nat := [2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_61008 : Nat := 118140960795 + 61008 * 2 ^ 59
def prefixEnd_61008 : Nat := 4983230072969 + 3 ^ 40 * 61008 * 2
def baseEnd_61008 : Nat := 18563809048653356811517

theorem tailTrace_61008 : CollatzResearch.WordTrace tailWord_61008 prefixEnd_61008 18563809048653356811517 := by
  unfold tailWord_61008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1112572281492955090991839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1483429708657273454655785 1112572281492955090991839)
  ·
    refine ⟨1668858422239432636487759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1112572281492955090991839 1668858422239432636487759)
    ·
      refine ⟨2503287633359148954731639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1668858422239432636487759 2503287633359148954731639)
      ·
        refine ⟨3754931450038723432097459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2503287633359148954731639 3754931450038723432097459)
        ·
          refine ⟨5632397175058085148146189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754931450038723432097459 5632397175058085148146189)
          ·
            refine ⟨2112148940646781930554821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5632397175058085148146189 2112148940646781930554821)
            ·
              refine ⟨396027926371271611979029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2112148940646781930554821 396027926371271611979029)
              ·
                refine ⟨18563809048653356811517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396027926371271611979029 18563809048653356811517)
                ·
                  rfl

theorem cell19_61008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_61008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61008 prefixEnd_61008 := by exact prefixLift 61008
  have htrace : WordTrace (prefixWord ++ tailWord_61008) baseStart_61008 baseEnd_61008 := by
    simpa [prefixWord, tailWord_61008, baseEnd_61008] using wordTrace_append hprefix tailTrace_61008
  have hstable : (prefixWord ++ tailWord_61008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61008).length < 2 ^ (prefixWord ++ tailWord_61008).sum := by decide
  have hdescent : baseEnd_61008 < baseStart_61008 := by decide
  rcases family_descends (prefixWord ++ tailWord_61008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61021 : List Nat := [1, 4, 4, 2, 1, 1, 1, 5]
def baseStart_61021 : Nat := 118140960795 + 61021 * 2 ^ 59
def prefixEnd_61021 : Nat := 4983230072969 + 3 ^ 40 * 61021 * 2
def baseEnd_61021 : Nat := 18567764751473178522593

theorem tailTrace_61021 : CollatzResearch.WordTrace tailWord_61021 prefixEnd_61021 18567764751473178522593 := by
  unfold tailWord_61021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2225618711938813402206917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1483745807959208934804611 2225618711938813402206917)
  ·
    refine ⟨417303508488527512913797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2225618711938813402206917 417303508488527512913797)
    ·
      refine ⟨78244407841598908671337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 417303508488527512913797 78244407841598908671337)
      ·
        refine ⟨58683305881199181503503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78244407841598908671337 58683305881199181503503)
        ·
          refine ⟨88024958821798772255255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58683305881199181503503 88024958821798772255255)
          ·
            refine ⟨132037438232698158382883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88024958821798772255255 132037438232698158382883)
            ·
              refine ⟨198056157349047237574325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132037438232698158382883 198056157349047237574325)
              ·
                refine ⟨18567764751473178522593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198056157349047237574325 18567764751473178522593)
                ·
                  rfl

theorem cell19_61021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_61021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61021 prefixEnd_61021 := by exact prefixLift 61021
  have htrace : WordTrace (prefixWord ++ tailWord_61021) baseStart_61021 baseEnd_61021 := by
    simpa [prefixWord, tailWord_61021, baseEnd_61021] using wordTrace_append hprefix tailTrace_61021
  have hstable : (prefixWord ++ tailWord_61021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61021).length < 2 ^ (prefixWord ++ tailWord_61021).sum := by decide
  have hdescent : baseEnd_61021 < baseStart_61021 := by decide
  rcases family_descends (prefixWord ++ tailWord_61021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61063 : List Nat := [1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_61063 : Nat := 118140960795 + 61063 * 2 ^ 59
def prefixEnd_61063 : Nat := 4983230072969 + 3 ^ 40 * 61063 * 2
def baseEnd_61063 : Nat := 18580544714429525589145

theorem tailTrace_61063 : CollatzResearch.WordTrace tailWord_61063 prefixEnd_61063 18580544714429525589145 := by
  unfold tailWord_61063
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227150577786654575235843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1484767051857769716823895 2227150577786654575235843)
  ·
    refine ⟨3340725866679981862853765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2227150577786654575235843 3340725866679981862853765)
    ·
      refine ⟨626386100002496599285081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3340725866679981862853765 626386100002496599285081)
      ·
        refine ⟨469789575001872449463811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 626386100002496599285081 469789575001872449463811)
        ·
          refine ⟨704684362502808674195717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469789575001872449463811 704684362502808674195717)
          ·
            refine ⟨132128317969276626411697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 704684362502808674195717 132128317969276626411697)
            ·
              refine ⟨99096238476957469808773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132128317969276626411697 99096238476957469808773)
              ·
                refine ⟨18580544714429525589145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99096238476957469808773 18580544714429525589145)
                ·
                  rfl

theorem cell19_61063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_61063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61063 prefixEnd_61063 := by exact prefixLift 61063
  have htrace : WordTrace (prefixWord ++ tailWord_61063) baseStart_61063 baseEnd_61063 := by
    simpa [prefixWord, tailWord_61063, baseEnd_61063] using wordTrace_append hprefix tailTrace_61063
  have hstable : (prefixWord ++ tailWord_61063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61063).length < 2 ^ (prefixWord ++ tailWord_61063).sum := by decide
  have hdescent : baseEnd_61063 < baseStart_61063 := by decide
  rcases family_descends (prefixWord ++ tailWord_61063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61065 : List Nat := [1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_61065 : Nat := 118140960795 + 61065 * 2 ^ 59
def prefixEnd_61065 : Nat := 4983230072969 + 3 ^ 40 * 61065 * 2
def baseEnd_61065 : Nat := 18581153284094113544695

theorem tailTrace_61065 : CollatzResearch.WordTrace tailWord_61065 prefixEnd_61065 18581153284094113544695 := by
  unfold tailWord_61065
  simp only [CollatzResearch.WordTrace]
  refine ⟨2227223523779408916808649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1484815682519605944539099 2227223523779408916808649)
  ·
    refine ⟨1670417642834556687606487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2227223523779408916808649 1670417642834556687606487)
    ·
      refine ⟨2505626464251835031409731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670417642834556687606487 2505626464251835031409731)
      ·
        refine ⟨3758439696377752547114597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505626464251835031409731 3758439696377752547114597)
        ·
          refine ⟨704707443070828602583987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3758439696377752547114597 704707443070828602583987)
          ·
            refine ⟨1057061164606242903875981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 704707443070828602583987 1057061164606242903875981)
            ·
              refine ⟨396397936727341088953493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1057061164606242903875981 396397936727341088953493)
              ·
                refine ⟨18581153284094113544695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 396397936727341088953493 18581153284094113544695)
                ·
                  rfl

theorem cell19_61065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_61065 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61065 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61065 prefixEnd_61065 := by exact prefixLift 61065
  have htrace : WordTrace (prefixWord ++ tailWord_61065) baseStart_61065 baseEnd_61065 := by
    simpa [prefixWord, tailWord_61065, baseEnd_61065] using wordTrace_append hprefix tailTrace_61065
  have hstable : (prefixWord ++ tailWord_61065).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61065).length < 2 ^ (prefixWord ++ tailWord_61065).sum := by decide
  have hdescent : baseEnd_61065 < baseStart_61065 := by decide
  rcases family_descends (prefixWord ++ tailWord_61065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61118 : List Nat := [4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_61118 : Nat := 118140960795 + 61118 * 2 ^ 59
def prefixEnd_61118 : Nat := 4983230072969 + 3 ^ 40 * 61118 * 2
def baseEnd_61118 : Nat := 18597280380205694366773

theorem tailTrace_61118 : CollatzResearch.WordTrace tailWord_61118 prefixEnd_61118 18597280380205694366773 := by
  unfold tailWord_61118
  simp only [CollatzResearch.WordTrace]
  refine ⟨278644574073424871061001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1486104395058265978992005 278644574073424871061001)
  ·
    refine ⟨208983430555068653295751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 278644574073424871061001 208983430555068653295751)
    ·
      refine ⟨313475145832602979943627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208983430555068653295751 313475145832602979943627)
      ·
        refine ⟨470212718748904469915441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313475145832602979943627 470212718748904469915441)
        ·
          refine ⟨352659539061678352436581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470212718748904469915441 352659539061678352436581)
          ·
            refine ⟨66123663574064691081859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352659539061678352436581 66123663574064691081859)
            ·
              refine ⟨99185495361097036622789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66123663574064691081859 99185495361097036622789)
              ·
                refine ⟨18597280380205694366773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99185495361097036622789 18597280380205694366773)
                ·
                  rfl

theorem cell19_61118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_61118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61118 prefixEnd_61118 := by exact prefixLift 61118
  have htrace : WordTrace (prefixWord ++ tailWord_61118) baseStart_61118 baseEnd_61118 := by
    simpa [prefixWord, tailWord_61118, baseEnd_61118] using wordTrace_append hprefix tailTrace_61118
  have hstable : (prefixWord ++ tailWord_61118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61118).length < 2 ^ (prefixWord ++ tailWord_61118).sum := by decide
  have hdescent : baseEnd_61118 < baseStart_61118 := by decide
  rcases family_descends (prefixWord ++ tailWord_61118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61194 : List Nat := [3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_61194 : Nat := 118140960795 + 61194 * 2 ^ 59
def prefixEnd_61194 : Nat := 4983230072969 + 3 ^ 40 * 61194 * 2
def baseEnd_61194 : Nat := 18620406027460036677677

theorem tailTrace_61194 : CollatzResearch.WordTrace tailWord_61194 prefixEnd_61194 18620406027460036677677 := by
  unfold tailWord_61194
  simp only [CollatzResearch.WordTrace]
  refine ⟨557982135078015987063659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1487952360208042632169757 557982135078015987063659)
  ·
    refine ⟨836973202617023980595489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 557982135078015987063659 836973202617023980595489)
    ·
      refine ⟨627729901962767985446617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 836973202617023980595489 627729901962767985446617)
      ·
        refine ⟨470797426472075989084963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627729901962767985446617 470797426472075989084963)
        ·
          refine ⟨706196139708113983627445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470797426472075989084963 706196139708113983627445)
          ·
            refine ⟨66205888097635685965073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 706196139708113983627445 66205888097635685965073)
            ·
              refine ⟨49654416073226764473805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66205888097635685965073 49654416073226764473805)
              ·
                refine ⟨18620406027460036677677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49654416073226764473805 18620406027460036677677)
                ·
                  rfl

theorem cell19_61194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_61194 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61194 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61194 prefixEnd_61194 := by exact prefixLift 61194
  have htrace : WordTrace (prefixWord ++ tailWord_61194) baseStart_61194 baseEnd_61194 := by
    simpa [prefixWord, tailWord_61194, baseEnd_61194] using wordTrace_append hprefix tailTrace_61194
  have hstable : (prefixWord ++ tailWord_61194).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61194).length < 2 ^ (prefixWord ++ tailWord_61194).sum := by decide
  have hdescent : baseEnd_61194 < baseStart_61194 := by decide
  rcases family_descends (prefixWord ++ tailWord_61194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61196 : List Nat := [2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_61196 : Nat := 118140960795 + 61196 * 2 ^ 59
def prefixEnd_61196 : Nat := 4983230072969 + 3 ^ 40 * 61196 * 2
def baseEnd_61196 : Nat := 18621014597124624633227

theorem tailTrace_61196 : CollatzResearch.WordTrace tailWord_61196 prefixEnd_61196 18621014597124624633227 := by
  unfold tailWord_61196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116000743152409144913721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1488000990869878859884961 1116000743152409144913721)
  ·
    refine ⟨837000557364306858685291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116000743152409144913721 837000557364306858685291)
    ·
      refine ⟨1255500836046460288027937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837000557364306858685291 1255500836046460288027937)
      ·
        refine ⟨941625627034845216020953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1255500836046460288027937 941625627034845216020953)
        ·
          refine ⟨706219220276133912015715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941625627034845216020953 706219220276133912015715)
          ·
            refine ⟨1059328830414200868023573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706219220276133912015715 1059328830414200868023573)
            ·
              refine ⟨49656038925665665688605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1059328830414200868023573 49656038925665665688605)
              ·
                refine ⟨18621014597124624633227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49656038925665665688605 18621014597124624633227)
                ·
                  rfl

theorem cell19_61196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_61196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61196 prefixEnd_61196 := by exact prefixLift 61196
  have htrace : WordTrace (prefixWord ++ tailWord_61196) baseStart_61196 baseEnd_61196 := by
    simpa [prefixWord, tailWord_61196, baseEnd_61196] using wordTrace_append hprefix tailTrace_61196
  have hstable : (prefixWord ++ tailWord_61196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61196).length < 2 ^ (prefixWord ++ tailWord_61196).sum := by decide
  have hdescent : baseEnd_61196 < baseStart_61196 := by decide
  rcases family_descends (prefixWord ++ tailWord_61196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61217 : List Nat := [1, 2, 3, 2, 1, 3, 7]
def baseStart_61217 : Nat := 118140960795 + 61217 * 2 ^ 59
def prefixEnd_61217 : Nat := 4983230072969 + 3 ^ 40 * 61217 * 2
def baseEnd_61217 : Nat := 6209134859534266055501

theorem tailTrace_61217 : CollatzResearch.WordTrace tailWord_61217 prefixEnd_61217 6209134859534266055501 := by
  unfold tailWord_61217
  simp only [CollatzResearch.WordTrace]
  refine ⟨2232767419228738876341905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1488511612819159250894603 2232767419228738876341905)
  ·
    refine ⟨1674575564421554157256429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2232767419228738876341905 1674575564421554157256429)
    ·
      refine ⟨627965836658082808971161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1674575564421554157256429 627965836658082808971161)
      ·
        refine ⟨470974377493562106728371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 627965836658082808971161 470974377493562106728371)
        ·
          refine ⟨706461566240343160092557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470974377493562106728371 706461566240343160092557)
          ·
            refine ⟨264923087340128685034709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 706461566240343160092557 264923087340128685034709)
            ·
              refine ⟨6209134859534266055501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 264923087340128685034709 6209134859534266055501)
              ·
                rfl

theorem cell19_61217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_61217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61217 prefixEnd_61217 := by exact prefixLift 61217
  have htrace : WordTrace (prefixWord ++ tailWord_61217) baseStart_61217 baseEnd_61217 := by
    simpa [prefixWord, tailWord_61217, baseEnd_61217] using wordTrace_append hprefix tailTrace_61217
  have hstable : (prefixWord ++ tailWord_61217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61217).length < 2 ^ (prefixWord ++ tailWord_61217).sum := by decide
  have hdescent : baseEnd_61217 < baseStart_61217 := by decide
  rcases family_descends (prefixWord ++ tailWord_61217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61234 : List Nat := [3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_61234 : Nat := 118140960795 + 61234 * 2 ^ 59
def prefixEnd_61234 : Nat := 4983230072969 + 3 ^ 40 * 61234 * 2
def baseEnd_61234 : Nat := 18632577420751795788679

theorem tailTrace_61234 : CollatzResearch.WordTrace tailWord_61234 prefixEnd_61234 18632577420751795788679 := by
  unfold tailWord_61234
  simp only [CollatzResearch.WordTrace]
  refine ⟨558346865041787694927689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1488924973444767186473837 558346865041787694927689)
  ·
    refine ⟨418760148781340771195767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 558346865041787694927689 418760148781340771195767)
    ·
      refine ⟨628140223172011156793651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 418760148781340771195767 628140223172011156793651)
      ·
        refine ⟨942210334758016735190477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628140223172011156793651 942210334758016735190477)
        ·
          refine ⟨353328875534256275696429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 942210334758016735190477 353328875534256275696429)
          ·
            refine ⟨132498328325346103386161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 353328875534256275696429 132498328325346103386161)
            ·
              refine ⟨99373746244009577539621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132498328325346103386161 99373746244009577539621)
              ·
                refine ⟨18632577420751795788679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99373746244009577539621 18632577420751795788679)
                ·
                  rfl

theorem cell19_61234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_61234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61234 prefixEnd_61234 := by exact prefixLift 61234
  have htrace : WordTrace (prefixWord ++ tailWord_61234) baseStart_61234 baseEnd_61234 := by
    simpa [prefixWord, tailWord_61234, baseEnd_61234] using wordTrace_append hprefix tailTrace_61234
  have hstable : (prefixWord ++ tailWord_61234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61234).length < 2 ^ (prefixWord ++ tailWord_61234).sum := by decide
  have hdescent : baseEnd_61234 < baseStart_61234 := by decide
  rcases family_descends (prefixWord ++ tailWord_61234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61255 : List Nat := [1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_61255 : Nat := 118140960795 + 61255 * 2 ^ 59
def prefixEnd_61255 : Nat := 4983230072969 + 3 ^ 40 * 61255 * 2
def baseEnd_61255 : Nat := 18638967402229969321955

theorem tailTrace_61255 : CollatzResearch.WordTrace tailWord_61255 prefixEnd_61255 18638967402229969321955 := by
  unfold tailWord_61255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2234153393091071366225219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1489435595394047577483479 2234153393091071366225219)
  ·
    refine ⟨3351230089636607049337829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2234153393091071366225219 3351230089636607049337829)
    ·
      refine ⟨628355641806863821750843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3351230089636607049337829 628355641806863821750843)
      ·
        refine ⟨942533462710295732626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 628355641806863821750843 942533462710295732626265)
        ·
          refine ⟨706900097032721799469699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 942533462710295732626265 706900097032721799469699)
          ·
            refine ⟨1060350145549082699204549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706900097032721799469699 1060350145549082699204549)
            ·
              refine ⟨198815652290453006100853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1060350145549082699204549 198815652290453006100853)
              ·
                refine ⟨18638967402229969321955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198815652290453006100853 18638967402229969321955)
                ·
                  rfl

theorem cell19_61255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_61255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61255 prefixEnd_61255 := by exact prefixLift 61255
  have htrace : WordTrace (prefixWord ++ tailWord_61255) baseStart_61255 baseEnd_61255 := by
    simpa [prefixWord, tailWord_61255, baseEnd_61255] using wordTrace_append hprefix tailTrace_61255
  have hstable : (prefixWord ++ tailWord_61255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61255).length < 2 ^ (prefixWord ++ tailWord_61255).sum := by decide
  have hdescent : baseEnd_61255 < baseStart_61255 := by decide
  rcases family_descends (prefixWord ++ tailWord_61255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61365 : List Nat := [1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_61365 : Nat := 118140960795 + 61365 * 2 ^ 59
def prefixEnd_61365 : Nat := 4983230072969 + 3 ^ 40 * 61365 * 2
def baseEnd_61365 : Nat := 18672438733782306877211

theorem tailTrace_61365 : CollatzResearch.WordTrace tailWord_61365 prefixEnd_61365 18672438733782306877211 := by
  unfold tailWord_61365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238165422692560152729549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1492110281795040101819699 2238165422692560152729549)
  ·
    refine ⟨839312033509710057273581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2238165422692560152729549 839312033509710057273581)
    ·
      refine ⟨314742012566141271477593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 839312033509710057273581 314742012566141271477593)
      ·
        refine ⟨236056509424605953608195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314742012566141271477593 236056509424605953608195)
        ·
          refine ⟨354084764136908930412293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236056509424605953608195 354084764136908930412293)
          ·
            refine ⟨66390893275670424452305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354084764136908930412293 66390893275670424452305)
            ·
              refine ⟨49793169956752818339229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66390893275670424452305 49793169956752818339229)
              ·
                refine ⟨18672438733782306877211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49793169956752818339229 18672438733782306877211)
                ·
                  rfl

theorem cell19_61365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_61365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61365 prefixEnd_61365 := by exact prefixLift 61365
  have htrace : WordTrace (prefixWord ++ tailWord_61365) baseStart_61365 baseEnd_61365 := by
    simpa [prefixWord, tailWord_61365, baseEnd_61365] using wordTrace_append hprefix tailTrace_61365
  have hstable : (prefixWord ++ tailWord_61365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61365).length < 2 ^ (prefixWord ++ tailWord_61365).sum := by decide
  have hdescent : baseEnd_61365 < baseStart_61365 := by decide
  rcases family_descends (prefixWord ++ tailWord_61365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61369 : List Nat := [1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_61369 : Nat := 118140960795 + 61369 * 2 ^ 59
def prefixEnd_61369 : Nat := 4983230072969 + 3 ^ 40 * 61369 * 2
def baseEnd_61369 : Nat := 18673655873111482788311

theorem tailTrace_61369 : CollatzResearch.WordTrace tailWord_61369 prefixEnd_61369 18673655873111482788311 := by
  unfold tailWord_61369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238311314678068835875161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1492207543118712557250107 2238311314678068835875161)
  ·
    refine ⟨1678733486008551626906371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2238311314678068835875161 1678733486008551626906371)
    ·
      refine ⟨2518100229012827440359557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1678733486008551626906371 2518100229012827440359557)
      ·
        refine ⟨472143792939905145067417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2518100229012827440359557 472143792939905145067417)
        ·
          refine ⟨354107844704928858800563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472143792939905145067417 354107844704928858800563)
          ·
            refine ⟨531161767057393288200845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354107844704928858800563 531161767057393288200845)
            ·
              refine ⟨199185662646522483075317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 531161767057393288200845 199185662646522483075317)
              ·
                refine ⟨18673655873111482788311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199185662646522483075317 18673655873111482788311)
                ·
                  rfl

theorem cell19_61369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_61369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61369 prefixEnd_61369 := by exact prefixLift 61369
  have htrace : WordTrace (prefixWord ++ tailWord_61369) baseStart_61369 baseEnd_61369 := by
    simpa [prefixWord, tailWord_61369, baseEnd_61369] using wordTrace_append hprefix tailTrace_61369
  have hstable : (prefixWord ++ tailWord_61369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61369).length < 2 ^ (prefixWord ++ tailWord_61369).sum := by decide
  have hdescent : baseEnd_61369 < baseStart_61369 := by decide
  rcases family_descends (prefixWord ++ tailWord_61369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61388 : List Nat := [2, 2, 1, 4, 1, 2, 7]
def baseStart_61388 : Nat := 118140960795 + 61388 * 2 ^ 59
def prefixEnd_61388 : Nat := 4983230072969 + 3 ^ 40 * 61388 * 2
def baseEnd_61388 : Nat := 6226479094975022788679

theorem tailTrace_61388 : CollatzResearch.WordTrace tailWord_61388 prefixEnd_61388 6226479094975022788679 := by
  unfold tailWord_61388
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119502150804617540408409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1492669534406156720544545 1119502150804617540408409)
  ·
    refine ⟨839626613103463155306307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119502150804617540408409 839626613103463155306307)
    ·
      refine ⟨1259439919655194732959461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 839626613103463155306307 1259439919655194732959461)
      ·
        refine ⟨236144984935349012429899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1259439919655194732959461 236144984935349012429899)
        ·
          refine ⟨354217477403023518644849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236144984935349012429899 354217477403023518644849)
          ·
            refine ⟨265663108052267638983637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354217477403023518644849 265663108052267638983637)
            ·
              refine ⟨6226479094975022788679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 265663108052267638983637 6226479094975022788679)
              ·
                rfl

theorem cell19_61388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_61388 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61388 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61388 prefixEnd_61388 := by exact prefixLift 61388
  have htrace : WordTrace (prefixWord ++ tailWord_61388) baseStart_61388 baseEnd_61388 := by
    simpa [prefixWord, tailWord_61388, baseEnd_61388] using wordTrace_append hprefix tailTrace_61388
  have hstable : (prefixWord ++ tailWord_61388).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61388).length < 2 ^ (prefixWord ++ tailWord_61388).sum := by decide
  have hdescent : baseEnd_61388 < baseStart_61388 := by decide
  rcases family_descends (prefixWord ++ tailWord_61388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61407 : List Nat := [1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_61407 : Nat := 118140960795 + 61407 * 2 ^ 59
def prefixEnd_61407 : Nat := 4983230072969 + 3 ^ 40 * 61407 * 2
def baseEnd_61407 : Nat := 18685218696738653943763

theorem tailTrace_61407 : CollatzResearch.WordTrace tailWord_61407 prefixEnd_61407 18685218696738653943763 := by
  unfold tailWord_61407
  simp only [CollatzResearch.WordTrace]
  refine ⟨2239697288540401325758475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1493131525693600883838983 2239697288540401325758475)
  ·
    refine ⟨3359545932810601988637713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2239697288540401325758475 3359545932810601988637713)
    ·
      refine ⟨2519659449607951491478285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3359545932810601988637713 2519659449607951491478285)
      ·
        refine ⟨944872293602981809304357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2519659449607951491478285 944872293602981809304357)
        ·
          refine ⟨177163555050559089244567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 944872293602981809304357 177163555050559089244567)
          ·
            refine ⟨265745332575838633866851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177163555050559089244567 265745332575838633866851)
            ·
              refine ⟨398617998863757950800277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265745332575838633866851 398617998863757950800277)
              ·
                refine ⟨18685218696738653943763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 398617998863757950800277 18685218696738653943763)
                ·
                  rfl

theorem cell19_61407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_61407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61407 prefixEnd_61407 := by exact prefixLift 61407
  have htrace : WordTrace (prefixWord ++ tailWord_61407) baseStart_61407 baseEnd_61407 := by
    simpa [prefixWord, tailWord_61407, baseEnd_61407] using wordTrace_append hprefix tailTrace_61407
  have hstable : (prefixWord ++ tailWord_61407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61407).length < 2 ^ (prefixWord ++ tailWord_61407).sum := by decide
  have hdescent : baseEnd_61407 < baseStart_61407 := by decide
  rcases family_descends (prefixWord ++ tailWord_61407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61534 : List Nat := [4, 4, 1, 1, 2, 1, 1, 5]
def baseStart_61534 : Nat := 118140960795 + 61534 * 2 ^ 59
def prefixEnd_61534 : Nat := 4983230072969 + 3 ^ 40 * 61534 * 2
def baseEnd_61534 : Nat := 18723862870439989121195

theorem tailTrace_61534 : CollatzResearch.WordTrace tailWord_61534 prefixEnd_61534 18723862870439989121195 := by
  unfold tailWord_61534
  simp only [CollatzResearch.WordTrace]
  refine ⟨280541169885037751953957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1496219572720201343754437 280541169885037751953957)
  ·
    refine ⟨52601469353444578491367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280541169885037751953957 52601469353444578491367)
    ·
      refine ⟨78902204030166867737051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52601469353444578491367 78902204030166867737051)
      ·
        refine ⟨118353306045250301605577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78902204030166867737051 118353306045250301605577)
        ·
          refine ⟨88764979533937726204183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118353306045250301605577 88764979533937726204183)
          ·
            refine ⟨133147469300906589306275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88764979533937726204183 133147469300906589306275)
            ·
              refine ⟨199721203951359883959413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133147469300906589306275 199721203951359883959413)
              ·
                refine ⟨18723862870439989121195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199721203951359883959413 18723862870439989121195)
                ·
                  rfl

theorem cell19_61534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_61534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61534 prefixEnd_61534 := by exact prefixLift 61534
  have htrace : WordTrace (prefixWord ++ tailWord_61534) baseStart_61534 baseEnd_61534 := by
    simpa [prefixWord, tailWord_61534, baseEnd_61534] using wordTrace_append hprefix tailTrace_61534
  have hstable : (prefixWord ++ tailWord_61534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61534).length < 2 ^ (prefixWord ++ tailWord_61534).sum := by decide
  have hdescent : baseEnd_61534 < baseStart_61534 := by decide
  rcases family_descends (prefixWord ++ tailWord_61534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61559 : List Nat := [1, 1, 3, 1, 1, 7, 5]
def baseStart_61559 : Nat := 118140960795 + 61559 * 2 ^ 59
def prefixEnd_61559 : Nat := 4983230072969 + 3 ^ 40 * 61559 * 2
def baseEnd_61559 : Nat := 6243823330415779521857

theorem tailTrace_61559 : CollatzResearch.WordTrace tailWord_61559 prefixEnd_61559 6243823330415779521857 := by
  unfold tailWord_61559
  simp only [CollatzResearch.WordTrace]
  refine ⟨2245241183989731285291731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1496827455993154190194487 2245241183989731285291731)
  ·
    refine ⟨3367861775984596927937597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2245241183989731285291731 3367861775984596927937597)
    ·
      refine ⟨1262948165994223847976599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3367861775984596927937597 1262948165994223847976599)
      ·
        refine ⟨1894422248991335771964899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1262948165994223847976599 1894422248991335771964899)
        ·
          refine ⟨2841633373487003657947349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1894422248991335771964899 2841633373487003657947349)
          ·
            refine ⟨66600782191101648233141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2841633373487003657947349 66600782191101648233141)
            ·
              refine ⟨6243823330415779521857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66600782191101648233141 6243823330415779521857)
              ·
                rfl

theorem cell19_61559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_61559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61559 prefixEnd_61559 := by exact prefixLift 61559
  have htrace : WordTrace (prefixWord ++ tailWord_61559) baseStart_61559 baseEnd_61559 := by
    simpa [prefixWord, tailWord_61559, baseEnd_61559] using wordTrace_append hprefix tailTrace_61559
  have hstable : (prefixWord ++ tailWord_61559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61559).length < 2 ^ (prefixWord ++ tailWord_61559).sum := by decide
  have hdescent : baseEnd_61559 < baseStart_61559 := by decide
  rcases family_descends (prefixWord ++ tailWord_61559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61576 : List Nat := [2, 1, 3, 4, 1, 2, 2, 4]
def baseStart_61576 : Nat := 118140960795 + 61576 * 2 ^ 59
def prefixEnd_61576 : Nat := 4983230072969 + 3 ^ 40 * 61576 * 2
def baseEnd_61576 : Nat := 18736642833396336187747

theorem tailTrace_61576 : CollatzResearch.WordTrace tailWord_61576 prefixEnd_61576 18736642833396336187747 := by
  unfold tailWord_61576
  simp only [CollatzResearch.WordTrace]
  refine ⟨1122930612464071594330291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1497240816618762125773721 1122930612464071594330291)
  ·
    refine ⟨1684395918696107391495437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1122930612464071594330291 1684395918696107391495437)
    ·
      refine ⟨631648469511040271810789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1684395918696107391495437 631648469511040271810789)
      ·
        refine ⟨118434088033320050964523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631648469511040271810789 118434088033320050964523)
        ·
          refine ⟨177651132049980076446785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118434088033320050964523 177651132049980076446785)
          ·
            refine ⟨133238349037485057335089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177651132049980076446785 133238349037485057335089)
            ·
              refine ⟨99928761778113793001317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133238349037485057335089 99928761778113793001317)
              ·
                refine ⟨18736642833396336187747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99928761778113793001317 18736642833396336187747)
                ·
                  rfl

theorem cell19_61576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_61576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61576 prefixEnd_61576 := by exact prefixLift 61576
  have htrace : WordTrace (prefixWord ++ tailWord_61576) baseStart_61576 baseEnd_61576 := by
    simpa [prefixWord, tailWord_61576, baseEnd_61576] using wordTrace_append hprefix tailTrace_61576
  have hstable : (prefixWord ++ tailWord_61576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61576).length < 2 ^ (prefixWord ++ tailWord_61576).sum := by decide
  have hdescent : baseEnd_61576 < baseStart_61576 := by decide
  rcases family_descends (prefixWord ++ tailWord_61576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61578 : List Nat := [3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_61578 : Nat := 118140960795 + 61578 * 2 ^ 59
def prefixEnd_61578 : Nat := 4983230072969 + 3 ^ 40 * 61578 * 2
def baseEnd_61578 : Nat := 18737251403060924143297

theorem tailTrace_61578 : CollatzResearch.WordTrace tailWord_61578 prefixEnd_61578 18737251403060924143297 := by
  unfold tailWord_61578
  simp only [CollatzResearch.WordTrace]
  refine ⟨561483542730224382558347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1497289447280598353488925 561483542730224382558347)
  ·
    refine ⟨842225314095336573837521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 561483542730224382558347 842225314095336573837521)
    ·
      refine ⟨631668985571502430378141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 842225314095336573837521 631668985571502430378141)
      ·
        refine ⟨236875869589313411391803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631668985571502430378141 236875869589313411391803)
        ·
          refine ⟨355313804383970117087705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236875869589313411391803 355313804383970117087705)
          ·
            refine ⟨266485353287977587815779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355313804383970117087705 266485353287977587815779)
            ·
              refine ⟨399728029931966381723669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266485353287977587815779 399728029931966381723669)
              ·
                refine ⟨18737251403060924143297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399728029931966381723669 18737251403060924143297)
                ·
                  rfl

theorem cell19_61578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_61578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61578 prefixEnd_61578 := by exact prefixLift 61578
  have htrace : WordTrace (prefixWord ++ tailWord_61578) baseStart_61578 baseEnd_61578 := by
    simpa [prefixWord, tailWord_61578, baseEnd_61578] using wordTrace_append hprefix tailTrace_61578
  have hstable : (prefixWord ++ tailWord_61578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61578).length < 2 ^ (prefixWord ++ tailWord_61578).sum := by decide
  have hdescent : baseEnd_61578 < baseStart_61578 := by decide
  rcases family_descends (prefixWord ++ tailWord_61578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61597 : List Nat := [1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_61597 : Nat := 118140960795 + 61597 * 2 ^ 59
def prefixEnd_61597 : Nat := 4983230072969 + 3 ^ 40 * 61597 * 2
def baseEnd_61597 : Nat := 18743032814874509721023

theorem tailTrace_61597 : CollatzResearch.WordTrace tailWord_61597 prefixEnd_61597 18743032814874509721023 := by
  unfold tailWord_61597
  simp only [CollatzResearch.WordTrace]
  refine ⟨2246627157852063775175045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1497751438568042516783363 2246627157852063775175045)
  ·
    refine ⟨421242592097261957845321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2246627157852063775175045 421242592097261957845321)
    ·
      refine ⟨315931944072946468383991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421242592097261957845321 315931944072946468383991)
      ·
        refine ⟨473897916109419702575987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315931944072946468383991 473897916109419702575987)
        ·
          refine ⟨710846874164129553863981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473897916109419702575987 710846874164129553863981)
          ·
            refine ⟨266567577811548582698993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710846874164129553863981 266567577811548582698993)
            ·
              refine ⟨199925683358661437024245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266567577811548582698993 199925683358661437024245)
              ·
                refine ⟨18743032814874509721023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199925683358661437024245 18743032814874509721023)
                ·
                  rfl

theorem cell19_61597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_61597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61597 prefixEnd_61597 := by exact prefixLift 61597
  have htrace : WordTrace (prefixWord ++ tailWord_61597) baseStart_61597 baseEnd_61597 := by
    simpa [prefixWord, tailWord_61597, baseEnd_61597] using wordTrace_append hprefix tailTrace_61597
  have hstable : (prefixWord ++ tailWord_61597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61597).length < 2 ^ (prefixWord ++ tailWord_61597).sum := by decide
  have hdescent : baseEnd_61597 < baseStart_61597 := by decide
  rcases family_descends (prefixWord ++ tailWord_61597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61614 : List Nat := [4, 1, 4, 2, 8]
def baseStart_61614 : Nat := 118140960795 + 61614 * 2 ^ 59
def prefixEnd_61614 : Nat := 4983230072969 + 3 ^ 40 * 61614 * 2
def baseEnd_61614 : Nat := 694377987297166938637

theorem tailTrace_61614 : CollatzResearch.WordTrace tailWord_61614 prefixEnd_61614 694377987297166938637 := by
  unfold tailWord_61614
  simp only [CollatzResearch.WordTrace]
  refine ⟨280905899848809459817987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1498164799193650452362597 280905899848809459817987)
  ·
    refine ⟨421358849773214189726981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280905899848809459817987 421358849773214189726981)
    ·
      refine ⟨79004784332477660573809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421358849773214189726981 79004784332477660573809)
      ·
        refine ⟨59253588249358245430357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79004784332477660573809 59253588249358245430357)
        ·
          refine ⟨694377987297166938637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 59253588249358245430357 694377987297166938637)
          ·
            rfl

theorem cell19_61614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 8].length) (baseStart_61614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61614 prefixEnd_61614 := by exact prefixLift 61614
  have htrace : WordTrace (prefixWord ++ tailWord_61614) baseStart_61614 baseEnd_61614 := by
    simpa [prefixWord, tailWord_61614, baseEnd_61614] using wordTrace_append hprefix tailTrace_61614
  have hstable : (prefixWord ++ tailWord_61614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61614).length < 2 ^ (prefixWord ++ tailWord_61614).sum := by decide
  have hdescent : baseEnd_61614 < baseStart_61614 := by decide
  rcases family_descends (prefixWord ++ tailWord_61614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61675 : List Nat := [1, 1, 1, 1, 2, 5, 8]
def baseStart_61675 : Nat := 118140960795 + 61675 * 2 ^ 59
def prefixEnd_61675 : Nat := 4983230072969 + 3 ^ 40 * 61675 * 2
def baseEnd_61675 : Nat := 6255589010597813329159

theorem tailTrace_61675 : CollatzResearch.WordTrace tailWord_61675 prefixEnd_61675 6255589010597813329159 := by
  unfold tailWord_61675
  simp only [CollatzResearch.WordTrace]
  refine ⟨2249472051569483096514479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1499648034379655397676319 2249472051569483096514479)
  ·
    refine ⟨3374208077354224644771719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2249472051569483096514479 3374208077354224644771719)
    ·
      refine ⟨5061312116031336967157579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3374208077354224644771719 5061312116031336967157579)
      ·
        refine ⟨7591968174047005450736369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5061312116031336967157579 7591968174047005450736369)
        ·
          refine ⟨5693976130535254088052277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7591968174047005450736369 5693976130535254088052277)
          ·
            refine ⟨533810262237680070754901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5693976130535254088052277 533810262237680070754901)
            ·
              refine ⟨6255589010597813329159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 533810262237680070754901 6255589010597813329159)
              ·
                rfl

theorem cell19_61675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_61675 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61675 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61675 prefixEnd_61675 := by exact prefixLift 61675
  have htrace : WordTrace (prefixWord ++ tailWord_61675) baseStart_61675 baseEnd_61675 := by
    simpa [prefixWord, tailWord_61675, baseEnd_61675] using wordTrace_append hprefix tailTrace_61675
  have hstable : (prefixWord ++ tailWord_61675).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61675).length < 2 ^ (prefixWord ++ tailWord_61675).sum := by decide
  have hdescent : baseEnd_61675 < baseStart_61675 := by decide
  rcases family_descends (prefixWord ++ tailWord_61675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61726 : List Nat := [4, 3, 2, 1, 1, 3, 5]
def baseStart_61726 : Nat := 118140960795 + 61726 * 2 ^ 59
def prefixEnd_61726 : Nat := 4983230072969 + 3 ^ 40 * 61726 * 2
def baseEnd_61726 : Nat := 6260761852746810951335

theorem tailTrace_61726 : CollatzResearch.WordTrace tailWord_61726 prefixEnd_61726 6260761852746810951335 := by
  unfold tailWord_61726
  simp only [CollatzResearch.WordTrace]
  refine ⟨281416521798089850827629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1500888116256479204414021 281416521798089850827629)
  ·
    refine ⟨105531195674283694060361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 281416521798089850827629 105531195674283694060361)
    ·
      refine ⟨79148396755712770545271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105531195674283694060361 79148396755712770545271)
      ·
        refine ⟨118722595133569155817907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79148396755712770545271 118722595133569155817907)
        ·
          refine ⟨178083892700353733726861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118722595133569155817907 178083892700353733726861)
          ·
            refine ⟨66781459762632650147573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178083892700353733726861 66781459762632650147573)
            ·
              refine ⟨6260761852746810951335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66781459762632650147573 6260761852746810951335)
              ·
                rfl

theorem cell19_61726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_61726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61726 prefixEnd_61726 := by exact prefixLift 61726
  have htrace : WordTrace (prefixWord ++ tailWord_61726) baseStart_61726 baseEnd_61726 := by
    simpa [prefixWord, tailWord_61726, baseEnd_61726] using wordTrace_append hprefix tailTrace_61726
  have hstable : (prefixWord ++ tailWord_61726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61726).length < 2 ^ (prefixWord ++ tailWord_61726).sum := by decide
  have hdescent : baseEnd_61726 < baseStart_61726 := by decide
  rcases family_descends (prefixWord ++ tailWord_61726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61730 : List Nat := [3, 3, 1, 1, 3, 1, 7]
def baseStart_61730 : Nat := 118140960795 + 61730 * 2 ^ 59
def prefixEnd_61730 : Nat := 4983230072969 + 3 ^ 40 * 61730 * 2
def baseEnd_61730 : Nat := 6261167565856536255035

theorem tailTrace_61730 : CollatzResearch.WordTrace tailWord_61730 prefixEnd_61730 6261167565856536255035 := by
  unfold tailWord_61730
  simp only [CollatzResearch.WordTrace]
  refine ⟨562869516592556872441661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1500985377580151659844429 562869516592556872441661)
  ·
    refine ⟨211076068722208827165623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 562869516592556872441661 211076068722208827165623)
    ·
      refine ⟨316614103083313240748435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211076068722208827165623 316614103083313240748435)
      ·
        refine ⟨474921154624969861122653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316614103083313240748435 474921154624969861122653)
        ·
          refine ⟨178095432984363697920995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 474921154624969861122653 178095432984363697920995)
          ·
            refine ⟨267143149476545546881493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178095432984363697920995 267143149476545546881493)
            ·
              refine ⟨6261167565856536255035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267143149476545546881493 6261167565856536255035)
              ·
                rfl

theorem cell19_61730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_61730 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61730 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61730 prefixEnd_61730 := by exact prefixLift 61730
  have htrace : WordTrace (prefixWord ++ tailWord_61730) baseStart_61730 baseEnd_61730 := by
    simpa [prefixWord, tailWord_61730, baseEnd_61730] using wordTrace_append hprefix tailTrace_61730
  have hstable : (prefixWord ++ tailWord_61730).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61730).length < 2 ^ (prefixWord ++ tailWord_61730).sum := by decide
  have hdescent : baseEnd_61730 < baseStart_61730 := by decide
  rcases family_descends (prefixWord ++ tailWord_61730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61749 : List Nat := [1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_61749 : Nat := 118140960795 + 61749 * 2 ^ 59
def prefixEnd_61749 : Nat := 4983230072969 + 3 ^ 40 * 61749 * 2
def baseEnd_61749 : Nat := 18789284109383194342831

theorem tailTrace_61749 : CollatzResearch.WordTrace tailWord_61749 prefixEnd_61749 18789284109383194342831 := by
  unfold tailWord_61749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2252171053301393734708301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1501447368867595823138867 2252171053301393734708301)
  ·
    refine ⟨844564144988022650515613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2252171053301393734708301 844564144988022650515613)
    ·
      refine ⟨316711554370508493943355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 844564144988022650515613 316711554370508493943355)
      ·
        refine ⟨475067331555762740915033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316711554370508493943355 475067331555762740915033)
        ·
          refine ⟨356300498666822055686275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475067331555762740915033 356300498666822055686275)
          ·
            refine ⟨534450748000233083529413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356300498666822055686275 534450748000233083529413)
            ·
              refine ⟨100209515250043703161765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 534450748000233083529413 100209515250043703161765)
              ·
                refine ⟨18789284109383194342831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100209515250043703161765 18789284109383194342831)
                ·
                  rfl

theorem cell19_61749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_61749 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61749 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61749 prefixEnd_61749 := by exact prefixLift 61749
  have htrace : WordTrace (prefixWord ++ tailWord_61749) baseStart_61749 baseEnd_61749 := by
    simpa [prefixWord, tailWord_61749, baseEnd_61749] using wordTrace_append hprefix tailTrace_61749
  have hstable : (prefixWord ++ tailWord_61749).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61749).length < 2 ^ (prefixWord ++ tailWord_61749).sum := by decide
  have hdescent : baseEnd_61749 < baseStart_61749 := by decide
  rcases family_descends (prefixWord ++ tailWord_61749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61804 : List Nat := [2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_61804 : Nat := 118140960795 + 61804 * 2 ^ 59
def prefixEnd_61804 : Nat := 4983230072969 + 3 ^ 40 * 61804 * 2
def baseEnd_61804 : Nat := 18806019775159363120459

theorem tailTrace_61804 : CollatzResearch.WordTrace tailWord_61804 prefixEnd_61804 18806019775159363120459 := by
  unfold tailWord_61804
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127088534051069063980233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1502784712068092085306977 1127088534051069063980233)
  ·
    refine ⟨845316400538301797985175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1127088534051069063980233 845316400538301797985175)
    ·
      refine ⟨1267974600807452696977763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845316400538301797985175 1267974600807452696977763)
      ·
        refine ⟨1901961901211179045466645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267974600807452696977763 1901961901211179045466645)
        ·
          refine ⟨89154464119274017756249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1901961901211179045466645 89154464119274017756249)
          ·
            refine ⟨66865848089455513317187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89154464119274017756249 66865848089455513317187)
            ·
              refine ⟨100298772134183269975781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66865848089455513317187 100298772134183269975781)
              ·
                refine ⟨18806019775159363120459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100298772134183269975781 18806019775159363120459)
                ·
                  rfl

theorem cell19_61804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_61804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61804 prefixEnd_61804 := by exact prefixLift 61804
  have htrace : WordTrace (prefixWord ++ tailWord_61804) baseStart_61804 baseEnd_61804 := by
    simpa [prefixWord, tailWord_61804, baseEnd_61804] using wordTrace_append hprefix tailTrace_61804
  have hstable : (prefixWord ++ tailWord_61804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61804).length < 2 ^ (prefixWord ++ tailWord_61804).sum := by decide
  have hdescent : baseEnd_61804 < baseStart_61804 := by decide
  rcases family_descends (prefixWord ++ tailWord_61804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61994 : List Nat := [3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_61994 : Nat := 118140960795 + 61994 * 2 ^ 59
def prefixEnd_61994 : Nat := 4983230072969 + 3 ^ 40 * 61994 * 2
def baseEnd_61994 : Nat := 18863833893295218897719

theorem tailTrace_61994 : CollatzResearch.WordTrace tailWord_61994 prefixEnd_61994 18863833893295218897719 := by
  unfold tailWord_61994
  simp only [CollatzResearch.WordTrace]
  refine ⟨565276734353450144344259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1507404624942533718251357 565276734353450144344259)
  ·
    refine ⟨847915101530175216516389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 565276734353450144344259 847915101530175216516389)
    ·
      refine ⟨158984081536907853096823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 847915101530175216516389 158984081536907853096823)
      ·
        refine ⟨238476122305361779645235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158984081536907853096823 238476122305361779645235)
        ·
          refine ⟨357714183458042669467853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238476122305361779645235 357714183458042669467853)
          ·
            refine ⟨134142818796766001050445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357714183458042669467853 134142818796766001050445)
            ·
              refine ⟨50303557048787250393917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134142818796766001050445 50303557048787250393917)
              ·
                refine ⟨18863833893295218897719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50303557048787250393917 18863833893295218897719)
                ·
                  rfl

theorem cell19_61994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_61994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_61994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_61994 prefixEnd_61994 := by exact prefixLift 61994
  have htrace : WordTrace (prefixWord ++ tailWord_61994) baseStart_61994 baseEnd_61994 := by
    simpa [prefixWord, tailWord_61994, baseEnd_61994] using wordTrace_append hprefix tailTrace_61994
  have hstable : (prefixWord ++ tailWord_61994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61994).length < 2 ^ (prefixWord ++ tailWord_61994).sum := by decide
  have hdescent : baseEnd_61994 < baseStart_61994 := by decide
  rcases family_descends (prefixWord ++ tailWord_61994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62053 : List Nat := [1, 3, 1, 3, 4, 1, 1, 5]
def baseStart_62053 : Nat := 118140960795 + 62053 * 2 ^ 59
def prefixEnd_62053 : Nat := 4983230072969 + 3 ^ 40 * 62053 * 2
def baseEnd_62053 : Nat := 18881786698400563586447

theorem tailTrace_62053 : CollatzResearch.WordTrace tailWord_62053 prefixEnd_62053 18881786698400563586447 := by
  unfold tailWord_62053
  simp only [CollatzResearch.WordTrace]
  refine ⟨2263258844200053653774813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1508839229466702435849875 2263258844200053653774813)
  ·
    refine ⟨848722066575020120165555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2263258844200053653774813 848722066575020120165555)
    ·
      refine ⟨1273083099862530180248333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848722066575020120165555 1273083099862530180248333)
      ·
        refine ⟨477406162448448817593125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1273083099862530180248333 477406162448448817593125)
        ·
          refine ⟨89513655459084153298711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 477406162448448817593125 89513655459084153298711)
          ·
            refine ⟨134270483188626229948067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89513655459084153298711 134270483188626229948067)
            ·
              refine ⟨201405724782939344922101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134270483188626229948067 201405724782939344922101)
              ·
                refine ⟨18881786698400563586447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201405724782939344922101 18881786698400563586447)
                ·
                  rfl

theorem cell19_62053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_62053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62053 prefixEnd_62053 := by exact prefixLift 62053
  have htrace : WordTrace (prefixWord ++ tailWord_62053) baseStart_62053 baseEnd_62053 := by
    simpa [prefixWord, tailWord_62053, baseEnd_62053] using wordTrace_append hprefix tailTrace_62053
  have hstable : (prefixWord ++ tailWord_62053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62053).length < 2 ^ (prefixWord ++ tailWord_62053).sum := by decide
  have hdescent : baseEnd_62053 < baseStart_62053 := by decide
  rcases family_descends (prefixWord ++ tailWord_62053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62070 : List Nat := [5, 1, 1, 2, 3, 2, 5]
def baseStart_62070 : Nat := 118140960795 + 62070 * 2 ^ 59
def prefixEnd_62070 : Nat := 4983230072969 + 3 ^ 40 * 62070 * 2
def baseEnd_62070 : Nat := 6295653180183187069541

theorem tailTrace_62070 : CollatzResearch.WordTrace tailWord_62070 prefixEnd_62070 6295653180183187069541 := by
  unfold tailWord_62070
  simp only [CollatzResearch.WordTrace]
  refine ⟨141492430321154097321479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1509252590092310371429109 141492430321154097321479)
  ·
    refine ⟨212238645481731145982219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141492430321154097321479 212238645481731145982219)
    ·
      refine ⟨318357968222596718973329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212238645481731145982219 318357968222596718973329)
      ·
        refine ⟨238768476166947539229997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318357968222596718973329 238768476166947539229997)
        ·
          refine ⟨89538178562605327211249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238768476166947539229997 89538178562605327211249)
          ·
            refine ⟨67153633921953995408437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89538178562605327211249 67153633921953995408437)
            ·
              refine ⟨6295653180183187069541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67153633921953995408437 6295653180183187069541)
              ·
                rfl

theorem cell19_62070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_62070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62070 prefixEnd_62070 := by exact prefixLift 62070
  have htrace : WordTrace (prefixWord ++ tailWord_62070) baseStart_62070 baseEnd_62070 := by
    simpa [prefixWord, tailWord_62070, baseEnd_62070] using wordTrace_append hprefix tailTrace_62070
  have hstable : (prefixWord ++ tailWord_62070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62070).length < 2 ^ (prefixWord ++ tailWord_62070).sum := by decide
  have hdescent : baseEnd_62070 < baseStart_62070 := by decide
  rcases family_descends (prefixWord ++ tailWord_62070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62110 : List Nat := [4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_62110 : Nat := 118140960795 + 62110 * 2 ^ 59
def prefixEnd_62110 : Nat := 4983230072969 + 3 ^ 40 * 62110 * 2
def baseEnd_62110 : Nat := 18899130933841320319625

theorem tailTrace_62110 : CollatzResearch.WordTrace tailWord_62110 prefixEnd_62110 18899130933841320319625 := by
  unfold tailWord_62110
  simp only [CollatzResearch.WordTrace]
  refine ⟨283167225624194048574973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1510225203329034925733189 283167225624194048574973)
  ·
    refine ⟨106187709609072768215615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 283167225624194048574973 106187709609072768215615)
    ·
      refine ⟨159281564413609152323423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106187709609072768215615 159281564413609152323423)
      ·
        refine ⟨238922346620413728485135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159281564413609152323423 238922346620413728485135)
        ·
          refine ⟨358383519930620592727703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238922346620413728485135 358383519930620592727703)
          ·
            refine ⟨537575279895930889091555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358383519930620592727703 537575279895930889091555)
            ·
              refine ⟨806362919843896333637333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537575279895930889091555 806362919843896333637333)
              ·
                refine ⟨18899130933841320319625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 806362919843896333637333 18899130933841320319625)
                ·
                  rfl

theorem cell19_62110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_62110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62110 prefixEnd_62110 := by exact prefixLift 62110
  have htrace : WordTrace (prefixWord ++ tailWord_62110) baseStart_62110 baseEnd_62110 := by
    simpa [prefixWord, tailWord_62110, baseEnd_62110] using wordTrace_append hprefix tailTrace_62110
  have hstable : (prefixWord ++ tailWord_62110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62110).length < 2 ^ (prefixWord ++ tailWord_62110).sum := by decide
  have hdescent : baseEnd_62110 < baseStart_62110 := by decide
  rcases family_descends (prefixWord ++ tailWord_62110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62129 : List Nat := [1, 2, 2, 6, 1, 7]
def baseStart_62129 : Nat := 118140960795 + 62129 * 2 ^ 59
def prefixEnd_62129 : Nat := 4983230072969 + 3 ^ 40 * 62129 * 2
def baseEnd_62129 : Nat := 2100545816183878433039

theorem tailTrace_62129 : CollatzResearch.WordTrace tailWord_62129 prefixEnd_62129 2100545816183878433039 := by
  unfold tailWord_62129
  simp only [CollatzResearch.WordTrace]
  refine ⟨2266030791924718633541441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1510687194616479089027627 2266030791924718633541441)
  ·
    refine ⟨1699523093943538975156081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2266030791924718633541441 1699523093943538975156081)
    ·
      refine ⟨1274642320457654231367061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1699523093943538975156081 1274642320457654231367061)
      ·
        refine ⟨59748858771452542095331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1274642320457654231367061 59748858771452542095331)
        ·
          refine ⟨89623288157178813142997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59748858771452542095331 89623288157178813142997)
          ·
            refine ⟨2100545816183878433039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 89623288157178813142997 2100545816183878433039)
            ·
              rfl

theorem cell19_62129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 7].length) (baseStart_62129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62129 prefixEnd_62129 := by exact prefixLift 62129
  have htrace : WordTrace (prefixWord ++ tailWord_62129) baseStart_62129 baseEnd_62129 := by
    simpa [prefixWord, tailWord_62129, baseEnd_62129] using wordTrace_append hprefix tailTrace_62129
  have hstable : (prefixWord ++ tailWord_62129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62129).length < 2 ^ (prefixWord ++ tailWord_62129).sum := by decide
  have hdescent : baseEnd_62129 < baseStart_62129 := by decide
  rcases family_descends (prefixWord ++ tailWord_62129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62148 : List Nat := [2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_62148 : Nat := 118140960795 + 62148 * 2 ^ 59
def prefixEnd_62148 : Nat := 4983230072969 + 3 ^ 40 * 62148 * 2
def baseEnd_62148 : Nat := 18910693757468491475077

theorem tailTrace_62148 : CollatzResearch.WordTrace tailWord_62148 prefixEnd_62148 18910693757468491475077 := by
  unfold tailWord_62148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133361889427942439241549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1511149185903923252322065 1133361889427942439241549)
  ·
    refine ⟨425010708535478414715581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1133361889427942439241549 425010708535478414715581)
    ·
      refine ⟨159379015700804405518343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 425010708535478414715581 159379015700804405518343)
      ·
        refine ⟨239068523551206608277515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159379015700804405518343 239068523551206608277515)
        ·
          refine ⟨358602785326809912416273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 239068523551206608277515 358602785326809912416273)
          ·
            refine ⟨268952088995107434312205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358602785326809912416273 268952088995107434312205)
            ·
              refine ⟨100857033373165287867077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268952088995107434312205 100857033373165287867077)
              ·
                refine ⟨18910693757468491475077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100857033373165287867077 18910693757468491475077)
                ·
                  rfl

theorem cell19_62148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_62148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62148 prefixEnd_62148 := by exact prefixLift 62148
  have htrace : WordTrace (prefixWord ++ tailWord_62148) baseStart_62148 baseEnd_62148 := by
    simpa [prefixWord, tailWord_62148, baseEnd_62148] using wordTrace_append hprefix tailTrace_62148
  have hstable : (prefixWord ++ tailWord_62148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62148).length < 2 ^ (prefixWord ++ tailWord_62148).sum := by decide
  have hdescent : baseEnd_62148 < baseStart_62148 := by decide
  rcases family_descends (prefixWord ++ tailWord_62148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62167 : List Nat := [1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_62167 : Nat := 118140960795 + 62167 * 2 ^ 59
def prefixEnd_62167 : Nat := 4983230072969 + 3 ^ 40 * 62167 * 2
def baseEnd_62167 : Nat := 18916475169282077052803

theorem tailTrace_62167 : CollatzResearch.WordTrace tailWord_62167 prefixEnd_62167 18916475169282077052803 := by
  unfold tailWord_62167
  simp only [CollatzResearch.WordTrace]
  refine ⟨2267416765787051123424755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1511611177191367415616503 2267416765787051123424755)
  ·
    refine ⟨3401125148680576685137133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2267416765787051123424755 3401125148680576685137133)
    ·
      refine ⟨1275421930755216256926425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3401125148680576685137133 1275421930755216256926425)
      ·
        refine ⟨956566448066412192694819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1275421930755216256926425 956566448066412192694819)
        ·
          refine ⟨1434849672099618289042229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956566448066412192694819 1434849672099618289042229)
          ·
            refine ⟨134517156759339214597709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1434849672099618289042229 134517156759339214597709)
            ·
              refine ⟨50443933784752205474141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134517156759339214597709 50443933784752205474141)
              ·
                refine ⟨18916475169282077052803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50443933784752205474141 18916475169282077052803)
                ·
                  rfl

theorem cell19_62167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_62167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62167 prefixEnd_62167 := by exact prefixLift 62167
  have htrace : WordTrace (prefixWord ++ tailWord_62167) baseStart_62167 baseEnd_62167 := by
    simpa [prefixWord, tailWord_62167, baseEnd_62167] using wordTrace_append hprefix tailTrace_62167
  have hstable : (prefixWord ++ tailWord_62167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62167).length < 2 ^ (prefixWord ++ tailWord_62167).sum := by decide
  have hdescent : baseEnd_62167 < baseStart_62167 := by decide
  rcases family_descends (prefixWord ++ tailWord_62167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62260 : List Nat := [2, 5, 1, 1, 3, 1, 2, 4]
def baseStart_62260 : Nat := 118140960795 + 62260 * 2 ^ 59
def prefixEnd_62260 : Nat := 4983230072969 + 3 ^ 40 * 62260 * 2
def baseEnd_62260 : Nat := 18944773658685416985883

theorem tailTrace_62260 : CollatzResearch.WordTrace tailWord_62260 prefixEnd_62260 18944773658685416985883 := by
  unfold tailWord_62260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135404377225064003280117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1513872502966752004373489 1135404377225064003280117)
  ·
    refine ⟨106444160364849750307511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1135404377225064003280117 106444160364849750307511)
    ·
      refine ⟨159666240547274625461267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106444160364849750307511 159666240547274625461267)
      ·
        refine ⟨239499360820911938191901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159666240547274625461267 239499360820911938191901)
        ·
          refine ⟨89812260307841976821963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 239499360820911938191901 89812260307841976821963)
          ·
            refine ⟨134718390461762965232945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89812260307841976821963 134718390461762965232945)
            ·
              refine ⟨101038792846322223924709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134718390461762965232945 101038792846322223924709)
              ·
                refine ⟨18944773658685416985883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101038792846322223924709 18944773658685416985883)
                ·
                  rfl

theorem cell19_62260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_62260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62260 prefixEnd_62260 := by exact prefixLift 62260
  have htrace : WordTrace (prefixWord ++ tailWord_62260) baseStart_62260 baseEnd_62260 := by
    simpa [prefixWord, tailWord_62260, baseEnd_62260] using wordTrace_append hprefix tailTrace_62260
  have hstable : (prefixWord ++ tailWord_62260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62260).length < 2 ^ (prefixWord ++ tailWord_62260).sum := by decide
  have hdescent : baseEnd_62260 < baseStart_62260 := by decide
  rcases family_descends (prefixWord ++ tailWord_62260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62264 : List Nat := [2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_62264 : Nat := 118140960795 + 62264 * 2 ^ 59
def prefixEnd_62264 : Nat := 4983230072969 + 3 ^ 40 * 62264 * 2
def baseEnd_62264 : Nat := 18945990798014592896983

theorem tailTrace_62264 : CollatzResearch.WordTrace tailWord_62264 prefixEnd_62264 18945990798014592896983 := by
  unfold tailWord_62264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135477323217818344852923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1513969764290424459803897 1135477323217818344852923)
  ·
    refine ⟨1703215984826727517279385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135477323217818344852923 1703215984826727517279385)
    ·
      refine ⟨1277411988620045637959539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1703215984826727517279385 1277411988620045637959539)
      ·
        refine ⟨1916117982930068456939309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1277411988620045637959539 1916117982930068456939309)
        ·
          refine ⟨718544243598775671352241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1916117982930068456939309 718544243598775671352241)
          ·
            refine ⟨538908182699081753514181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718544243598775671352241 538908182699081753514181)
            ·
              refine ⟨101045284256077828783909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 538908182699081753514181 101045284256077828783909)
              ·
                refine ⟨18945990798014592896983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101045284256077828783909 18945990798014592896983)
                ·
                  rfl

theorem cell19_62264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_62264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62264 prefixEnd_62264 := by exact prefixLift 62264
  have htrace : WordTrace (prefixWord ++ tailWord_62264) baseStart_62264 baseEnd_62264 := by
    simpa [prefixWord, tailWord_62264, baseEnd_62264] using wordTrace_append hprefix tailTrace_62264
  have hstable : (prefixWord ++ tailWord_62264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62264).length < 2 ^ (prefixWord ++ tailWord_62264).sum := by decide
  have hdescent : baseEnd_62264 < baseStart_62264 := by decide
  rcases family_descends (prefixWord ++ tailWord_62264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62321 : List Nat := [1, 2, 2, 2, 1, 4, 3, 4]
def baseStart_62321 : Nat := 118140960795 + 62321 * 2 ^ 59
def prefixEnd_62321 : Nat := 4983230072969 + 3 ^ 40 * 62321 * 2
def baseEnd_62321 : Nat := 18963335033455349630161

theorem tailTrace_62321 : CollatzResearch.WordTrace tailWord_62321 prefixEnd_62321 18963335033455349630161 := by
  unfold tailWord_62321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2273033607229135424530817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1515355738152756949687211 2273033607229135424530817)
  ·
    refine ⟨1704775205421851568398113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2273033607229135424530817 1704775205421851568398113)
    ·
      refine ⟨1278581404066388676298585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1704775205421851568398113 1278581404066388676298585)
      ·
        refine ⟨958936053049791507223939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1278581404066388676298585 958936053049791507223939)
        ·
          refine ⟨1438404079574687260835909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 958936053049791507223939 1438404079574687260835909)
          ·
            refine ⟨269700764920253861406733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1438404079574687260835909 269700764920253861406733)
            ·
              refine ⟨101137786845095198027525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 269700764920253861406733 101137786845095198027525)
              ·
                refine ⟨18963335033455349630161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101137786845095198027525 18963335033455349630161)
                ·
                  rfl

theorem cell19_62321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_62321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62321 prefixEnd_62321 := by exact prefixLift 62321
  have htrace : WordTrace (prefixWord ++ tailWord_62321) baseStart_62321 baseEnd_62321 := by
    simpa [prefixWord, tailWord_62321, baseEnd_62321] using wordTrace_append hprefix tailTrace_62321
  have hstable : (prefixWord ++ tailWord_62321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62321).length < 2 ^ (prefixWord ++ tailWord_62321).sum := by decide
  have hdescent : baseEnd_62321 < baseStart_62321 := by decide
  rcases family_descends (prefixWord ++ tailWord_62321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62334 : List Nat := [4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_62334 : Nat := 118140960795 + 62334 * 2 ^ 59
def prefixEnd_62334 : Nat := 4983230072969 + 3 ^ 40 * 62334 * 2
def baseEnd_62334 : Nat := 18967290736275171341237

theorem tailTrace_62334 : CollatzResearch.WordTrace tailWord_62334 prefixEnd_62334 18967290736275171341237 := by
  unfold tailWord_62334
  simp only [CollatzResearch.WordTrace]
  refine ⟨284188469522754830594257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1515671837454692429836037 284188469522754830594257)
  ·
    refine ⟨213141352142066122945693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284188469522754830594257 213141352142066122945693)
    ·
      refine ⟨79928007053274796104635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213141352142066122945693 79928007053274796104635)
      ·
        refine ⟨119892010579912194156953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79928007053274796104635 119892010579912194156953)
        ·
          refine ⟨89919007934934145617715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119892010579912194156953 89919007934934145617715)
          ·
            refine ⟨134878511902401218426573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89919007934934145617715 134878511902401218426573)
            ·
              refine ⟨50579441963400456909965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134878511902401218426573 50579441963400456909965)
              ·
                refine ⟨18967290736275171341237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50579441963400456909965 18967290736275171341237)
                ·
                  rfl

theorem cell19_62334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_62334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62334 prefixEnd_62334 := by exact prefixLift 62334
  have htrace : WordTrace (prefixWord ++ tailWord_62334) baseStart_62334 baseEnd_62334 := by
    simpa [prefixWord, tailWord_62334, baseEnd_62334] using wordTrace_append hprefix tailTrace_62334
  have hstable : (prefixWord ++ tailWord_62334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62334).length < 2 ^ (prefixWord ++ tailWord_62334).sum := by decide
  have hdescent : baseEnd_62334 < baseStart_62334 := by decide
  rcases family_descends (prefixWord ++ tailWord_62334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62406 : List Nat := [6, 1, 3, 1, 2, 1, 5]
def baseStart_62406 : Nat := 118140960795 + 62406 * 2 ^ 59
def prefixEnd_62406 : Nat := 4983230072969 + 3 ^ 40 * 62406 * 2
def baseEnd_62406 : Nat := 6329733081400112580347

theorem tailTrace_62406 : CollatzResearch.WordTrace tailWord_62406 prefixEnd_62406 6329733081400112580347 := by
  unfold tailWord_62406
  simp only [CollatzResearch.WordTrace]
  refine ⟨71129181622537341917971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1517422541280796627583381 71129181622537341917971)
  ·
    refine ⟨106693772433806012876957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71129181622537341917971 106693772433806012876957)
    ·
      refine ⟨40010164662677254828859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106693772433806012876957 40010164662677254828859)
      ·
        refine ⟨60015246994015882243289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40010164662677254828859 60015246994015882243289)
        ·
          refine ⟨45011435245511911682467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60015246994015882243289 45011435245511911682467)
          ·
            refine ⟨67517152868267867523701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45011435245511911682467 67517152868267867523701)
            ·
              refine ⟨6329733081400112580347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67517152868267867523701 6329733081400112580347)
              ·
                rfl

theorem cell19_62406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_62406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62406 prefixEnd_62406 := by exact prefixLift 62406
  have htrace : WordTrace (prefixWord ++ tailWord_62406) baseStart_62406 baseEnd_62406 := by
    simpa [prefixWord, tailWord_62406, baseEnd_62406] using wordTrace_append hprefix tailTrace_62406
  have hstable : (prefixWord ++ tailWord_62406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62406).length < 2 ^ (prefixWord ++ tailWord_62406).sum := by decide
  have hdescent : baseEnd_62406 < baseStart_62406 := by decide
  rcases family_descends (prefixWord ++ tailWord_62406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62435 : List Nat := [1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_62435 : Nat := 118140960795 + 62435 * 2 ^ 59
def prefixEnd_62435 : Nat := 4983230072969 + 3 ^ 40 * 62435 * 2
def baseEnd_62435 : Nat := 18998023504336863096517

theorem tailTrace_62435 : CollatzResearch.WordTrace tailWord_62435 prefixEnd_62435 18998023504336863096517 := by
  unfold tailWord_62435
  simp only [CollatzResearch.WordTrace]
  refine ⟨2277191528816132894180759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1518127685877421929453839 2277191528816132894180759)
  ·
    refine ⟨3415787293224199341271139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2277191528816132894180759 3415787293224199341271139)
    ·
      refine ⟨5123680939836299011906709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3415787293224199341271139 5123680939836299011906709)
      ·
        refine ⟨240172544054826516183127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5123680939836299011906709 240172544054826516183127)
        ·
          refine ⟨360258816082239774274691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240172544054826516183127 360258816082239774274691)
          ·
            refine ⟨540388224123359661412037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360258816082239774274691 540388224123359661412037)
            ·
              refine ⟨101322792023129936514757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540388224123359661412037 101322792023129936514757)
              ·
                refine ⟨18998023504336863096517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101322792023129936514757 18998023504336863096517)
                ·
                  rfl

theorem cell19_62435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_62435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62435 prefixEnd_62435 := by exact prefixLift 62435
  have htrace : WordTrace (prefixWord ++ tailWord_62435) baseStart_62435 baseEnd_62435 := by
    simpa [prefixWord, tailWord_62435, baseEnd_62435] using wordTrace_append hprefix tailTrace_62435
  have hstable : (prefixWord ++ tailWord_62435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62435).length < 2 ^ (prefixWord ++ tailWord_62435).sum := by decide
  have hdescent : baseEnd_62435 < baseStart_62435 := by decide
  rcases family_descends (prefixWord ++ tailWord_62435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62475 : List Nat := [1, 1, 1, 1, 6, 9]
def baseStart_62475 : Nat := 118140960795 + 62475 * 2 ^ 59
def prefixEnd_62475 : Nat := 4983230072969 + 3 ^ 40 * 62475 * 2
def baseEnd_62475 : Nat := 2112243877514291356391

theorem tailTrace_62475 : CollatzResearch.WordTrace tailWord_62475 prefixEnd_62475 2112243877514291356391 := by
  unfold tailWord_62475
  simp only [CollatzResearch.WordTrace]
  refine ⟨2278650448671219725636879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1519100299114146483757919 2278650448671219725636879)
  ·
    refine ⟨3417975673006829588455319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2278650448671219725636879 3417975673006829588455319)
    ·
      refine ⟨5126963509510244382682979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3417975673006829588455319 5126963509510244382682979)
      ·
        refine ⟨7690445264265366574024469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5126963509510244382682979 7690445264265366574024469)
        ·
          refine ⟨360489621762439058157397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7690445264265366574024469 360489621762439058157397)
          ·
            refine ⟨2112243877514291356391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 360489621762439058157397 2112243877514291356391)
            ·
              rfl

theorem cell19_62475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_62475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62475 prefixEnd_62475 := by exact prefixLift 62475
  have htrace : WordTrace (prefixWord ++ tailWord_62475) baseStart_62475 baseEnd_62475 := by
    simpa [prefixWord, tailWord_62475, baseEnd_62475] using wordTrace_append hprefix tailTrace_62475
  have hstable : (prefixWord ++ tailWord_62475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62475).length < 2 ^ (prefixWord ++ tailWord_62475).sum := by decide
  have hdescent : baseEnd_62475 < baseStart_62475 := by decide
  rcases family_descends (prefixWord ++ tailWord_62475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62551 : List Nat := [1, 1, 3, 2, 2, 1, 1, 8]
def baseStart_62551 : Nat := 118140960795 + 62551 * 2 ^ 59
def prefixEnd_62551 : Nat := 4983230072969 + 3 ^ 40 * 62551 * 2
def baseEnd_62551 : Nat := 19033320544882964518423

theorem tailTrace_62551 : CollatzResearch.WordTrace tailWord_62551 prefixEnd_62551 19033320544882964518423 := by
  unfold tailWord_62551
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281422396395884705403507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1520948264263923136935671 2281422396395884705403507)
  ·
    refine ⟨3422133594593827058105261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281422396395884705403507 3422133594593827058105261)
    ·
      refine ⟨1283300097972685146789473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3422133594593827058105261 1283300097972685146789473)
      ·
        refine ⟨962475073479513860092105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1283300097972685146789473 962475073479513860092105)
        ·
          refine ⟨721856305109635395069079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 962475073479513860092105 721856305109635395069079)
          ·
            refine ⟨1082784457664453092603619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721856305109635395069079 1082784457664453092603619)
            ·
              refine ⟨1624176686496679638905429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082784457664453092603619 1624176686496679638905429)
              ·
                refine ⟨19033320544882964518423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1624176686496679638905429 19033320544882964518423)
                ·
                  rfl

theorem cell19_62551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_62551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62551 prefixEnd_62551 := by exact prefixLift 62551
  have htrace : WordTrace (prefixWord ++ tailWord_62551) baseStart_62551 baseEnd_62551 := by
    simpa [prefixWord, tailWord_62551, baseEnd_62551] using wordTrace_append hprefix tailTrace_62551
  have hstable : (prefixWord ++ tailWord_62551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62551).length < 2 ^ (prefixWord ++ tailWord_62551).sum := by decide
  have hdescent : baseEnd_62551 < baseStart_62551 := by decide
  rcases family_descends (prefixWord ++ tailWord_62551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62585 : List Nat := [1, 2, 1, 3, 6, 1, 5]
def baseStart_62585 : Nat := 118140960795 + 62585 * 2 ^ 59
def prefixEnd_62585 : Nat := 4983230072969 + 3 ^ 40 * 62585 * 2
def baseEnd_62585 : Nat := 6347888743060319920925

theorem tailTrace_62585 : CollatzResearch.WordTrace tailWord_62585 prefixEnd_62585 6347888743060319920925 := by
  unfold tailWord_62585
  simp only [CollatzResearch.WordTrace]
  refine ⟨2282662478272708512141209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1521774985515139008094139 2282662478272708512141209)
  ·
    refine ⟨1711996858704531384105907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2282662478272708512141209 1711996858704531384105907)
    ·
      refine ⟨2567995288056797076158861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1711996858704531384105907 2567995288056797076158861)
      ·
        refine ⟨962998233021298903559573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2567995288056797076158861 962998233021298903559573)
        ·
          refine ⟨45140542172873386104355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 962998233021298903559573 45140542172873386104355)
          ·
            refine ⟨67710813259310079156533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45140542172873386104355 67710813259310079156533)
            ·
              refine ⟨6347888743060319920925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67710813259310079156533 6347888743060319920925)
              ·
                rfl

theorem cell19_62585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_62585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62585 prefixEnd_62585 := by exact prefixLift 62585
  have htrace : WordTrace (prefixWord ++ tailWord_62585) baseStart_62585 baseEnd_62585 := by
    simpa [prefixWord, tailWord_62585, baseEnd_62585] using wordTrace_append hprefix tailTrace_62585
  have hstable : (prefixWord ++ tailWord_62585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62585).length < 2 ^ (prefixWord ++ tailWord_62585).sum := by decide
  have hdescent : baseEnd_62585 < baseStart_62585 := by decide
  rcases family_descends (prefixWord ++ tailWord_62585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62606 : List Nat := [4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_62606 : Nat := 118140960795 + 62606 * 2 ^ 59
def prefixEnd_62606 : Nat := 4983230072969 + 3 ^ 40 * 62606 * 2
def baseEnd_62606 : Nat := 19050056210659133296051

theorem tailTrace_62606 : CollatzResearch.WordTrace tailWord_62606 prefixEnd_62606 19050056210659133296051 := by
  unfold tailWord_62606
  simp only [CollatzResearch.WordTrace]
  refine ⟨285428551399578637331959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1522285607464419399103781 285428551399578637331959)
  ·
    refine ⟨428142827099367955997939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285428551399578637331959 428142827099367955997939)
    ·
      refine ⟨642214240649051933996909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428142827099367955997939 642214240649051933996909)
      ·
        refine ⟨240830340243394475248841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 642214240649051933996909 240830340243394475248841)
        ·
          refine ⟨180622755182545856436631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240830340243394475248841 180622755182545856436631)
          ·
            refine ⟨270934132773818784654947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180622755182545856436631 270934132773818784654947)
            ·
              refine ⟨406401199160728176982421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270934132773818784654947 406401199160728176982421)
              ·
                refine ⟨19050056210659133296051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 406401199160728176982421 19050056210659133296051)
                ·
                  rfl

theorem cell19_62606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_62606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62606 prefixEnd_62606 := by exact prefixLift 62606
  have htrace : WordTrace (prefixWord ++ tailWord_62606) baseStart_62606 baseEnd_62606 := by
    simpa [prefixWord, tailWord_62606, baseEnd_62606] using wordTrace_append hprefix tailTrace_62606
  have hstable : (prefixWord ++ tailWord_62606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62606).length < 2 ^ (prefixWord ++ tailWord_62606).sum := by decide
  have hdescent : baseEnd_62606 < baseStart_62606 := by decide
  rcases family_descends (prefixWord ++ tailWord_62606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62680 : List Nat := [2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_62680 : Nat := 118140960795 + 62680 * 2 ^ 59
def prefixEnd_62680 : Nat := 4983230072969 + 3 ^ 40 * 62680 * 2
def baseEnd_62680 : Nat := 19072573288248887651405

theorem tailTrace_62680 : CollatzResearch.WordTrace tailWord_62680 prefixEnd_62680 19072573288248887651405 := by
  unfold tailWord_62680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1143063706464269868424747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1524084941952359824566329 1143063706464269868424747)
  ·
    refine ⟨1714595559696404802637121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1143063706464269868424747 1714595559696404802637121)
    ·
      refine ⟨1285946669772303601977841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1714595559696404802637121 1285946669772303601977841)
      ·
        refine ⟨964460002329227701483381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1285946669772303601977841 964460002329227701483381)
        ·
          refine ⟨90418125218365097014067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 964460002329227701483381 90418125218365097014067)
          ·
            refine ⟨135627187827547645521101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90418125218365097014067 135627187827547645521101)
            ·
              refine ⟨50860195435330367070413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135627187827547645521101 50860195435330367070413)
              ·
                refine ⟨19072573288248887651405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50860195435330367070413 19072573288248887651405)
                ·
                  rfl

theorem cell19_62680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_62680 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62680 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62680 prefixEnd_62680 := by exact prefixLift 62680
  have htrace : WordTrace (prefixWord ++ tailWord_62680) baseStart_62680 baseEnd_62680 := by
    simpa [prefixWord, tailWord_62680, baseEnd_62680] using wordTrace_append hprefix tailTrace_62680
  have hstable : (prefixWord ++ tailWord_62680).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62680).length < 2 ^ (prefixWord ++ tailWord_62680).sum := by decide
  have hdescent : baseEnd_62680 < baseStart_62680 := by decide
  rcases family_descends (prefixWord ++ tailWord_62680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62701 : List Nat := [1, 5, 1, 2, 2, 2, 6]
def baseStart_62701 : Nat := 118140960795 + 62701 * 2 ^ 59
def prefixEnd_62701 : Nat := 4983230072969 + 3 ^ 40 * 62701 * 2
def baseEnd_62701 : Nat := 6359654423242353728227

theorem tailTrace_62701 : CollatzResearch.WordTrace tailWord_62701 prefixEnd_62701 6359654423242353728227 := by
  unfold tailWord_62701
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286893345852460323363957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1524595563901640215575971 2286893345852460323363957)
  ·
    refine ⟨214396251173668155315371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2286893345852460323363957 214396251173668155315371)
    ·
      refine ⟨321594376760502232973057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214396251173668155315371 321594376760502232973057)
      ·
        refine ⟨241195782570376674729793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321594376760502232973057 241195782570376674729793)
        ·
          refine ⟨180896836927782506047345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241195782570376674729793 180896836927782506047345)
          ·
            refine ⟨135672627695836879535509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180896836927782506047345 135672627695836879535509)
            ·
              refine ⟨6359654423242353728227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135672627695836879535509 6359654423242353728227)
              ·
                rfl

theorem cell19_62701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_62701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62701 prefixEnd_62701 := by exact prefixLift 62701
  have htrace : WordTrace (prefixWord ++ tailWord_62701) baseStart_62701 baseEnd_62701 := by
    simpa [prefixWord, tailWord_62701, baseEnd_62701] using wordTrace_append hprefix tailTrace_62701
  have hstable : (prefixWord ++ tailWord_62701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62701).length < 2 ^ (prefixWord ++ tailWord_62701).sum := by decide
  have hdescent : baseEnd_62701 < baseStart_62701 := by decide
  rcases family_descends (prefixWord ++ tailWord_62701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62798 : List Nat := [4, 1, 1, 1, 1, 1, 3, 7]
def baseStart_62798 : Nat := 118140960795 + 62798 * 2 ^ 59
def prefixEnd_62798 : Nat := 4983230072969 + 3 ^ 40 * 62798 * 2
def baseEnd_62798 : Nat := 19108478898459577028861

theorem tailTrace_62798 : CollatzResearch.WordTrace tailWord_62798 prefixEnd_62798 19108478898459577028861 := by
  unfold tailWord_62798
  simp only [CollatzResearch.WordTrace]
  refine ⟨286303903312630736205631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1526954151000697259763365 286303903312630736205631)
  ·
    refine ⟨429455854968946104308447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286303903312630736205631 429455854968946104308447)
    ·
      refine ⟨644183782453419156462671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429455854968946104308447 644183782453419156462671)
      ·
        refine ⟨966275673680128734694007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644183782453419156462671 966275673680128734694007)
        ·
          refine ⟨1449413510520193102041011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966275673680128734694007 1449413510520193102041011)
          ·
            refine ⟨2174120265780289653061517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449413510520193102041011 2174120265780289653061517)
            ·
              refine ⟨815295099667608619898069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2174120265780289653061517 815295099667608619898069)
              ·
                refine ⟨19108478898459577028861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 815295099667608619898069 19108478898459577028861)
                ·
                  rfl

theorem cell19_62798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_62798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62798 prefixEnd_62798 := by exact prefixLift 62798
  have htrace : WordTrace (prefixWord ++ tailWord_62798) baseStart_62798 baseEnd_62798 := by
    simpa [prefixWord, tailWord_62798, baseEnd_62798] using wordTrace_append hprefix tailTrace_62798
  have hstable : (prefixWord ++ tailWord_62798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62798).length < 2 ^ (prefixWord ++ tailWord_62798).sum := by decide
  have hdescent : baseEnd_62798 < baseStart_62798 := by decide
  rcases family_descends (prefixWord ++ tailWord_62798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62813 : List Nat := [1, 4, 5, 1, 8]
def baseStart_62813 : Nat := 118140960795 + 62813 * 2 ^ 59
def prefixEnd_62813 : Nat := 4983230072969 + 3 ^ 40 * 62813 * 2
def baseEnd_62813 : Nat := 707890487812740247981

theorem tailTrace_62813 : CollatzResearch.WordTrace tailWord_62813 prefixEnd_62813 707890487812740247981 := by
  unfold tailWord_62813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290978321446703451441093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1527318880964468967627395 2290978321446703451441093)
  ·
    refine ⟨429558435271256897145205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2290978321446703451441093 429558435271256897145205)
    ·
      refine ⟨40271103306680334107363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 429558435271256897145205 40271103306680334107363)
      ·
        refine ⟨60406654960020501161045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40271103306680334107363 60406654960020501161045)
        ·
          refine ⟨707890487812740247981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 60406654960020501161045 707890487812740247981)
          ·
            rfl

theorem cell19_62813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 8].length) (baseStart_62813 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62813 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62813 prefixEnd_62813 := by exact prefixLift 62813
  have htrace : WordTrace (prefixWord ++ tailWord_62813) baseStart_62813 baseEnd_62813 := by
    simpa [prefixWord, tailWord_62813, baseEnd_62813] using wordTrace_append hprefix tailTrace_62813
  have hstable : (prefixWord ++ tailWord_62813).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62813).length < 2 ^ (prefixWord ++ tailWord_62813).sum := by decide
  have hdescent : baseEnd_62813 < baseStart_62813 := by decide
  rcases family_descends (prefixWord ++ tailWord_62813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62830 : List Nat := [4, 1, 2, 4, 1, 2, 1, 4]
def baseStart_62830 : Nat := 118140960795 + 62830 * 2 ^ 59
def prefixEnd_62830 : Nat := 4983230072969 + 3 ^ 40 * 62830 * 2
def baseEnd_62830 : Nat := 19118216013092984317663

theorem tailTrace_62830 : CollatzResearch.WordTrace tailWord_62830 prefixEnd_62830 19118216013092984317663 := by
  unfold tailWord_62830
  simp only [CollatzResearch.WordTrace]
  refine ⟨286449795298139419351243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1527732241590076903206629 286449795298139419351243)
  ·
    refine ⟨429674692947209129026865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286449795298139419351243 429674692947209129026865)
    ·
      refine ⟨322256019710406846770149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429674692947209129026865 322256019710406846770149)
      ·
        refine ⟨60423003695701283769403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 322256019710406846770149 60423003695701283769403)
        ·
          refine ⟨90634505543551925654105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60423003695701283769403 90634505543551925654105)
          ·
            refine ⟨67975879157663944240579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90634505543551925654105 67975879157663944240579)
            ·
              refine ⟨101963818736495916360869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67975879157663944240579 101963818736495916360869)
              ·
                refine ⟨19118216013092984317663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101963818736495916360869 19118216013092984317663)
                ·
                  rfl

theorem cell19_62830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_62830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62830 prefixEnd_62830 := by exact prefixLift 62830
  have htrace : WordTrace (prefixWord ++ tailWord_62830) baseStart_62830 baseEnd_62830 := by
    simpa [prefixWord, tailWord_62830, baseEnd_62830] using wordTrace_append hprefix tailTrace_62830
  have hstable : (prefixWord ++ tailWord_62830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62830).length < 2 ^ (prefixWord ++ tailWord_62830).sum := by decide
  have hdescent : baseEnd_62830 < baseStart_62830 := by decide
  rcases family_descends (prefixWord ++ tailWord_62830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62872 : List Nat := [2, 1, 2, 5, 2, 1, 6]
def baseStart_62872 : Nat := 118140960795 + 62872 * 2 ^ 59
def prefixEnd_62872 : Nat := 4983230072969 + 3 ^ 40 * 62872 * 2
def baseEnd_62872 : Nat := 6376998658683110461405

theorem tailTrace_62872 : CollatzResearch.WordTrace tailWord_62872 prefixEnd_62872 6376998658683110461405 := by
  unfold tailWord_62872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1146565114116478263919435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1528753485488637685225913 1146565114116478263919435)
  ·
    refine ⟨1719847671174717395879153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1146565114116478263919435 1719847671174717395879153)
    ·
      refine ⟨1289885753381038046909365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719847671174717395879153 1289885753381038046909365)
      ·
        refine ⟨120926789379472316897753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1289885753381038046909365 120926789379472316897753)
        ·
          refine ⟨90695092034604237673315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120926789379472316897753 90695092034604237673315)
          ·
            refine ⟨136042638051906356509973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90695092034604237673315 136042638051906356509973)
            ·
              refine ⟨6376998658683110461405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 136042638051906356509973 6376998658683110461405)
              ·
                rfl

theorem cell19_62872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_62872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62872 prefixEnd_62872 := by exact prefixLift 62872
  have htrace : WordTrace (prefixWord ++ tailWord_62872) baseStart_62872 baseEnd_62872 := by
    simpa [prefixWord, tailWord_62872, baseEnd_62872] using wordTrace_append hprefix tailTrace_62872
  have hstable : (prefixWord ++ tailWord_62872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62872).length < 2 ^ (prefixWord ++ tailWord_62872).sum := by decide
  have hdescent : baseEnd_62872 < baseStart_62872 := by decide
  rcases family_descends (prefixWord ++ tailWord_62872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62874 : List Nat := [3, 1, 1, 4, 1, 1, 8]
def baseStart_62874 : Nat := 118140960795 + 62874 * 2 ^ 59
def prefixEnd_62874 : Nat := 4983230072969 + 3 ^ 40 * 62874 * 2
def baseEnd_62874 : Nat := 6377201515237973113255

theorem tailTrace_62874 : CollatzResearch.WordTrace tailWord_62874 prefixEnd_62874 6377201515237973113255 := by
  unfold tailWord_62874
  simp only [CollatzResearch.WordTrace]
  refine ⟨573300793556427717352919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1528802116150473912941117 573300793556427717352919)
  ·
    refine ⟨859951190334641576029379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573300793556427717352919 859951190334641576029379)
    ·
      refine ⟨1289926785501962364044069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859951190334641576029379 1289926785501962364044069)
      ·
        refine ⟨241861272281617943258263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1289926785501962364044069 241861272281617943258263)
        ·
          refine ⟨362791908422426914887395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241861272281617943258263 362791908422426914887395)
          ·
            refine ⟨544187862633640372331093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362791908422426914887395 544187862633640372331093)
            ·
              refine ⟨6377201515237973113255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 544187862633640372331093 6377201515237973113255)
              ·
                rfl

theorem cell19_62874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_62874 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62874 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62874 prefixEnd_62874 := by exact prefixLift 62874
  have htrace : WordTrace (prefixWord ++ tailWord_62874) baseStart_62874 baseEnd_62874 := by
    simpa [prefixWord, tailWord_62874, baseEnd_62874] using wordTrace_append hprefix tailTrace_62874
  have hstable : (prefixWord ++ tailWord_62874).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62874).length < 2 ^ (prefixWord ++ tailWord_62874).sum := by decide
  have hdescent : baseEnd_62874 < baseStart_62874 := by decide
  rcases family_descends (prefixWord ++ tailWord_62874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62982 : List Nat := [6, 2, 1, 1, 2, 7]
def baseStart_62982 : Nat := 118140960795 + 62982 * 2 ^ 59
def prefixEnd_62982 : Nat := 4983230072969 + 3 ^ 40 * 62982 * 2
def baseEnd_62982 : Nat := 2129385256400185437719

theorem tailTrace_62982 : CollatzResearch.WordTrace tailWord_62982 prefixEnd_62982 2129385256400185437719 := by
  unfold tailWord_62982
  simp only [CollatzResearch.WordTrace]
  refine ⟨71785695557326416073225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1531428171889630209562133 71785695557326416073225)
  ·
    refine ⟨53839271667994812054919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71785695557326416073225 53839271667994812054919)
    ·
      refine ⟨80758907501992218082379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53839271667994812054919 80758907501992218082379)
      ·
        refine ⟨121138361252988327123569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80758907501992218082379 121138361252988327123569)
        ·
          refine ⟨90853770939741245342677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 121138361252988327123569 90853770939741245342677)
          ·
            refine ⟨2129385256400185437719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 90853770939741245342677 2129385256400185437719)
            ·
              rfl

theorem cell19_62982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_62982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62982 prefixEnd_62982 := by exact prefixLift 62982
  have htrace : WordTrace (prefixWord ++ tailWord_62982) baseStart_62982 baseEnd_62982 := by
    simpa [prefixWord, tailWord_62982, baseEnd_62982] using wordTrace_append hprefix tailTrace_62982
  have hstable : (prefixWord ++ tailWord_62982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62982).length < 2 ^ (prefixWord ++ tailWord_62982).sum := by decide
  have hdescent : baseEnd_62982 < baseStart_62982 := by decide
  rcases family_descends (prefixWord ++ tailWord_62982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_62988 : List Nat := [2, 2, 1, 2, 5, 7]
def baseStart_62988 : Nat := 118140960795 + 62988 * 2 ^ 59
def prefixEnd_62988 : Nat := 4983230072969 + 3 ^ 40 * 62988 * 2
def baseEnd_62988 : Nat := 2129588112955048089569

theorem tailTrace_62988 : CollatzResearch.WordTrace tailWord_62988 prefixEnd_62988 2129588112955048089569 := by
  unfold tailWord_62988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148680547906354169530809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1531574063875138892707745 1148680547906354169530809)
  ·
    refine ⟨861510410929765627148107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1148680547906354169530809 861510410929765627148107)
    ·
      refine ⟨1292265616394648440722161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861510410929765627148107 1292265616394648440722161)
      ·
        refine ⟨969199212295986330541621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292265616394648440722161 969199212295986330541621)
        ·
          refine ⟨90862426152748718488277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 969199212295986330541621 90862426152748718488277)
          ·
            refine ⟨2129588112955048089569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 90862426152748718488277 2129588112955048089569)
            ·
              rfl

theorem cell19_62988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_62988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_62988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_62988 prefixEnd_62988 := by exact prefixLift 62988
  have htrace : WordTrace (prefixWord ++ tailWord_62988) baseStart_62988 baseEnd_62988 := by
    simpa [prefixWord, tailWord_62988, baseEnd_62988] using wordTrace_append hprefix tailTrace_62988
  have hstable : (prefixWord ++ tailWord_62988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_62988).length < 2 ^ (prefixWord ++ tailWord_62988).sum := by decide
  have hdescent : baseEnd_62988 < baseStart_62988 := by decide
  rcases family_descends (prefixWord ++ tailWord_62988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63007 : List Nat := [1, 1, 2, 4, 1, 1, 5, 4]
def baseStart_63007 : Nat := 118140960795 + 63007 * 2 ^ 59
def prefixEnd_63007 : Nat := 4983230072969 + 3 ^ 40 * 63007 * 2
def baseEnd_63007 : Nat := 19172074428409018383847

theorem tailTrace_63007 : CollatzResearch.WordTrace tailWord_63007 prefixEnd_63007 19172074428409018383847 := by
  unfold tailWord_63007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298054082743874584003275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1532036055162583056002183 2298054082743874584003275)
  ·
    refine ⟨3447081124115811876004913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2298054082743874584003275 3447081124115811876004913)
    ·
      refine ⟨2585310843086858907003685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3447081124115811876004913 2585310843086858907003685)
      ·
        refine ⟨484745783078786045063191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2585310843086858907003685 484745783078786045063191)
        ·
          refine ⟨727118674618179067594787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484745783078786045063191 727118674618179067594787)
          ·
            refine ⟨1090678011927268601392181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727118674618179067594787 1090678011927268601392181)
            ·
              refine ⟨102251063618181431380517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1090678011927268601392181 102251063618181431380517)
              ·
                refine ⟨19172074428409018383847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102251063618181431380517 19172074428409018383847)
                ·
                  rfl

theorem cell19_63007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_63007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63007 prefixEnd_63007 := by exact prefixLift 63007
  have htrace : WordTrace (prefixWord ++ tailWord_63007) baseStart_63007 baseEnd_63007 := by
    simpa [prefixWord, tailWord_63007, baseEnd_63007] using wordTrace_append hprefix tailTrace_63007
  have hstable : (prefixWord ++ tailWord_63007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63007).length < 2 ^ (prefixWord ++ tailWord_63007).sum := by decide
  have hdescent : baseEnd_63007 < baseStart_63007 := by decide
  rcases family_descends (prefixWord ++ tailWord_63007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63022 : List Nat := [4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_63022 : Nat := 118140960795 + 63022 * 2 ^ 59
def prefixEnd_63022 : Nat := 4983230072969 + 3 ^ 40 * 63022 * 2
def baseEnd_63022 : Nat := 19176638700893428050473

theorem tailTrace_63022 : CollatzResearch.WordTrace tailWord_63022 prefixEnd_63022 19176638700893428050473 := by
  unfold tailWord_63022
  simp only [CollatzResearch.WordTrace]
  refine ⟨287325147211191518224915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1532400785126354763866213 287325147211191518224915)
  ·
    refine ⟨430987720816787277337373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 287325147211191518224915 430987720816787277337373)
    ·
      refine ⟨161620395306295229001515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 430987720816787277337373 161620395306295229001515)
      ·
        refine ⟨242430592959442843502273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 161620395306295229001515 242430592959442843502273)
        ·
          refine ⟨181822944719582132626705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 242430592959442843502273 181822944719582132626705)
          ·
            refine ⟨136367208539686599470029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 181822944719582132626705 136367208539686599470029)
            ·
              refine ⟨51137703202382474801261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 136367208539686599470029 51137703202382474801261)
              ·
                refine ⟨19176638700893428050473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51137703202382474801261 19176638700893428050473)
                ·
                  rfl

theorem cell19_63022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_63022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63022 prefixEnd_63022 := by exact prefixLift 63022
  have htrace : WordTrace (prefixWord ++ tailWord_63022) baseStart_63022 baseEnd_63022 := by
    simpa [prefixWord, tailWord_63022, baseEnd_63022] using wordTrace_append hprefix tailTrace_63022
  have hstable : (prefixWord ++ tailWord_63022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63022).length < 2 ^ (prefixWord ++ tailWord_63022).sum := by decide
  have hdescent : baseEnd_63022 < baseStart_63022 := by decide
  rcases family_descends (prefixWord ++ tailWord_63022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63140 : List Nat := [2, 3, 1, 2, 2, 2, 2, 5]
def baseStart_63140 : Nat := 118140960795 + 63140 * 2 ^ 59
def prefixEnd_63140 : Nat := 4983230072969 + 3 ^ 40 * 63140 * 2
def baseEnd_63140 : Nat := 19212544311104117427929

theorem tailTrace_63140 : CollatzResearch.WordTrace tailWord_63140 prefixEnd_63140 19212544311104117427929 := by
  unfold tailWord_63140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151452495631019149297437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1535269994174692199063249 1151452495631019149297437)
  ·
    refine ⟨431794685861632180986539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1151452495631019149297437 431794685861632180986539)
    ·
      refine ⟨647692028792448271479809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431794685861632180986539 647692028792448271479809)
      ·
        refine ⟨485769021594336203609857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647692028792448271479809 485769021594336203609857)
        ·
          refine ⟨364326766195752152707393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485769021594336203609857 364326766195752152707393)
          ·
            refine ⟨273245074646814114530545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364326766195752152707393 273245074646814114530545)
            ·
              refine ⟨204933805985110585897909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273245074646814114530545 204933805985110585897909)
              ·
                refine ⟨19212544311104117427929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 204933805985110585897909 19212544311104117427929)
                ·
                  rfl

theorem cell19_63140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_63140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63140 prefixEnd_63140 := by exact prefixLift 63140
  have htrace : WordTrace (prefixWord ++ tailWord_63140) baseStart_63140 baseEnd_63140 := by
    simpa [prefixWord, tailWord_63140, baseEnd_63140] using wordTrace_append hprefix tailTrace_63140
  have hstable : (prefixWord ++ tailWord_63140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63140).length < 2 ^ (prefixWord ++ tailWord_63140).sum := by decide
  have hdescent : baseEnd_63140 < baseStart_63140 := by decide
  rcases family_descends (prefixWord ++ tailWord_63140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63157 : List Nat := [1, 3, 3, 3, 3, 6]
def baseStart_63157 : Nat := 118140960795 + 63157 * 2 ^ 59
def prefixEnd_63157 : Nat := 4983230072969 + 3 ^ 40 * 63157 * 2
def baseEnd_63157 : Nat := 2135301905917012783345

theorem tailTrace_63157 : CollatzResearch.WordTrace tailWord_63157 prefixEnd_63157 2135301905917012783345 := by
  unfold tailWord_63157
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303525032200450201963725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1535683354800300134642483 2303525032200450201963725)
  ·
    refine ⟨863821887075168825736397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2303525032200450201963725 863821887075168825736397)
    ·
      refine ⟨323933207653188309651149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 863821887075168825736397 323933207653188309651149)
      ·
        refine ⟨121474952869945616119181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 323933207653188309651149 121474952869945616119181)
        ·
          refine ⟨45553107326229606044693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 121474952869945616119181 45553107326229606044693)
          ·
            refine ⟨2135301905917012783345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45553107326229606044693 2135301905917012783345)
            ·
              rfl

theorem cell19_63157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_63157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63157 prefixEnd_63157 := by exact prefixLift 63157
  have htrace : WordTrace (prefixWord ++ tailWord_63157) baseStart_63157 baseEnd_63157 := by
    simpa [prefixWord, tailWord_63157, baseEnd_63157] using wordTrace_append hprefix tailTrace_63157
  have hstable : (prefixWord ++ tailWord_63157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63157).length < 2 ^ (prefixWord ++ tailWord_63157).sum := by decide
  have hdescent : baseEnd_63157 < baseStart_63157 := by decide
  rcases family_descends (prefixWord ++ tailWord_63157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63170 : List Nat := [3, 5, 1, 2, 1, 2, 1, 4]
def baseStart_63170 : Nat := 118140960795 + 63170 * 2 ^ 59
def prefixEnd_63170 : Nat := 4983230072969 + 3 ^ 40 * 63170 * 2
def baseEnd_63170 : Nat := 19221672856072936761181

theorem tailTrace_63170 : CollatzResearch.WordTrace tailWord_63170 prefixEnd_63170 19221672856072936761181 := by
  unfold tailWord_63170
  simp only [CollatzResearch.WordTrace]
  refine ⟨575999795288338355546741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1535999454102235614791309 575999795288338355546741)
  ·
    refine ⟨53999980808281720832507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 575999795288338355546741 53999980808281720832507)
    ·
      refine ⟨80999971212422581248761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53999980808281720832507 80999971212422581248761)
      ·
        refine ⟨60749978409316935936571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80999971212422581248761 60749978409316935936571)
        ·
          refine ⟨91124967613975403904857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60749978409316935936571 91124967613975403904857)
          ·
            refine ⟨68343725710481552928643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91124967613975403904857 68343725710481552928643)
            ·
              refine ⟨102515588565722329392965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 68343725710481552928643 102515588565722329392965)
              ·
                refine ⟨19221672856072936761181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 102515588565722329392965 19221672856072936761181)
                ·
                  rfl

theorem cell19_63170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_63170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63170 prefixEnd_63170 := by exact prefixLift 63170
  have htrace : WordTrace (prefixWord ++ tailWord_63170) baseStart_63170 baseEnd_63170 := by
    simpa [prefixWord, tailWord_63170, baseEnd_63170] using wordTrace_append hprefix tailTrace_63170
  have hstable : (prefixWord ++ tailWord_63170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63170).length < 2 ^ (prefixWord ++ tailWord_63170).sum := by decide
  have hdescent : baseEnd_63170 < baseStart_63170 := by decide
  rcases family_descends (prefixWord ++ tailWord_63170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63250 : List Nat := [3, 2, 4, 1, 1, 1, 4, 3]
def baseStart_63250 : Nat := 118140960795 + 63250 * 2 ^ 59
def prefixEnd_63250 : Nat := 4983230072969 + 3 ^ 40 * 63250 * 2
def baseEnd_63250 : Nat := 19246015642656454983185

theorem tailTrace_63250 : CollatzResearch.WordTrace tailWord_63250 prefixEnd_63250 19246015642656454983185 := by
  unfold tailWord_63250
  simp only [CollatzResearch.WordTrace]
  refine ⟨576729255215881771274801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1537944680575684723399469 576729255215881771274801)
  ·
    refine ⟨432546941411911328456101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 576729255215881771274801 432546941411911328456101)
    ·
      refine ⟨81102551514733374085519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 432546941411911328456101 81102551514733374085519)
      ·
        refine ⟨121653827272100061128279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 81102551514733374085519 121653827272100061128279)
        ·
          refine ⟨182480740908150091692419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121653827272100061128279 182480740908150091692419)
          ·
            refine ⟨273721111362225137538629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182480740908150091692419 273721111362225137538629)
            ·
              refine ⟨51322708380417213288493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 273721111362225137538629 51322708380417213288493)
              ·
                refine ⟨19246015642656454983185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51322708380417213288493 19246015642656454983185)
                ·
                  rfl

theorem cell19_63250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_63250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63250 prefixEnd_63250 := by exact prefixLift 63250
  have htrace : WordTrace (prefixWord ++ tailWord_63250) baseStart_63250 baseEnd_63250 := by
    simpa [prefixWord, tailWord_63250, baseEnd_63250] using wordTrace_append hprefix tailTrace_63250
  have hstable : (prefixWord ++ tailWord_63250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63250).length < 2 ^ (prefixWord ++ tailWord_63250).sum := by decide
  have hdescent : baseEnd_63250 < baseStart_63250 := by decide
  rcases family_descends (prefixWord ++ tailWord_63250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63309 : List Nat := [1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_63309 : Nat := 118140960795 + 63309 * 2 ^ 59
def prefixEnd_63309 : Nat := 4983230072969 + 3 ^ 40 * 63309 * 2
def baseEnd_63309 : Nat := 19263968447761799671913

theorem tailTrace_63309 : CollatzResearch.WordTrace tailWord_63309 prefixEnd_63309 19263968447761799671913 := by
  unfold tailWord_63309
  simp only [CollatzResearch.WordTrace]
  refine ⟨2309068927649780161496981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1539379285099853440997987 2309068927649780161496981)
  ·
    refine ⟨108237605983583445070171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2309068927649780161496981 108237605983583445070171)
    ·
      refine ⟨162356408975375167605257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 108237605983583445070171 162356408975375167605257)
      ·
        refine ⟨121767306731531375703943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 162356408975375167605257 121767306731531375703943)
        ·
          refine ⟨182650960097297063555915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 121767306731531375703943 182650960097297063555915)
          ·
            refine ⟨273976440145945595333873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182650960097297063555915 273976440145945595333873)
            ·
              refine ⟨205482330109459196500405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273976440145945595333873 205482330109459196500405)
              ·
                refine ⟨19263968447761799671913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 205482330109459196500405 19263968447761799671913)
                ·
                  rfl

theorem cell19_63309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_63309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63309 prefixEnd_63309 := by exact prefixLift 63309
  have htrace : WordTrace (prefixWord ++ tailWord_63309) baseStart_63309 baseEnd_63309 := by
    simpa [prefixWord, tailWord_63309, baseEnd_63309] using wordTrace_append hprefix tailTrace_63309
  have hstable : (prefixWord ++ tailWord_63309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63309).length < 2 ^ (prefixWord ++ tailWord_63309).sum := by decide
  have hdescent : baseEnd_63309 < baseStart_63309 := by decide
  rcases family_descends (prefixWord ++ tailWord_63309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63330 : List Nat := [3, 3, 2, 1, 2, 8]
def baseStart_63330 : Nat := 118140960795 + 63330 * 2 ^ 59
def prefixEnd_63330 : Nat := 4983230072969 + 3 ^ 40 * 63330 * 2
def baseEnd_63330 : Nat := 2141150936582219245021

theorem tailTrace_63330 : CollatzResearch.WordTrace tailWord_63330 prefixEnd_63330 2141150936582219245021 := by
  unfold tailWord_63330
  simp only [CollatzResearch.WordTrace]
  refine ⟨577458715143425187002861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1539889907049133832007629 577458715143425187002861)
  ·
    refine ⟨216547018178784445126073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 577458715143425187002861 216547018178784445126073)
    ·
      refine ⟨162410263634088333844555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216547018178784445126073 162410263634088333844555)
      ·
        refine ⟨243615395451132500766833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162410263634088333844555 243615395451132500766833)
        ·
          refine ⟨182711546588349375575125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 243615395451132500766833 182711546588349375575125)
          ·
            refine ⟨2141150936582219245021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 182711546588349375575125 2141150936582219245021)
            ·
              rfl

theorem cell19_63330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_63330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63330 prefixEnd_63330 := by exact prefixLift 63330
  have htrace : WordTrace (prefixWord ++ tailWord_63330) baseStart_63330 baseEnd_63330 := by
    simpa [prefixWord, tailWord_63330, baseEnd_63330] using wordTrace_append hprefix tailTrace_63330
  have hstable : (prefixWord ++ tailWord_63330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63330).length < 2 ^ (prefixWord ++ tailWord_63330).sum := by decide
  have hdescent : baseEnd_63330 < baseStart_63330 := by decide
  rcases family_descends (prefixWord ++ tailWord_63330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63332 : List Nat := [2, 3, 1, 1, 12]
def baseStart_63332 : Nat := 118140960795 + 63332 * 2 ^ 59
def prefixEnd_63332 : Nat := 4983230072969 + 3 ^ 40 * 63332 * 2
def baseEnd_63332 : Nat := 713739518477946709657

theorem tailTrace_63332 : CollatzResearch.WordTrace tailWord_63332 prefixEnd_63332 713739518477946709657 := by
  unfold tailWord_63332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1154953903283227544792125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1539938537710970059722833 1154953903283227544792125)
  ·
    refine ⟨433107713731210329297047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1154953903283227544792125 433107713731210329297047)
    ·
      refine ⟨649661570596815493945571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433107713731210329297047 649661570596815493945571)
      ·
        refine ⟨974492355895223240918357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649661570596815493945571 974492355895223240918357)
        ·
          refine ⟨713739518477946709657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 974492355895223240918357 713739518477946709657)
          ·
            rfl

theorem cell19_63332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 12].length) (baseStart_63332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63332 prefixEnd_63332 := by exact prefixLift 63332
  have htrace : WordTrace (prefixWord ++ tailWord_63332) baseStart_63332 baseEnd_63332 := by
    simpa [prefixWord, tailWord_63332, baseEnd_63332] using wordTrace_append hprefix tailTrace_63332
  have hstable : (prefixWord ++ tailWord_63332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63332).length < 2 ^ (prefixWord ++ tailWord_63332).sum := by decide
  have hdescent : baseEnd_63332 < baseStart_63332 := by decide
  rcases family_descends (prefixWord ++ tailWord_63332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63442 : List Nat := [3, 2, 2, 3, 2, 2, 5]
def baseStart_63442 : Nat := 118140960795 + 63442 * 2 ^ 59
def prefixEnd_63442 : Nat := 4983230072969 + 3 ^ 40 * 63442 * 2
def baseEnd_63442 : Nat := 6434812776818966238665

theorem tailTrace_63442 : CollatzResearch.WordTrace tailWord_63442 prefixEnd_63442 6434812776818966238665 := by
  unfold tailWord_63442
  simp only [CollatzResearch.WordTrace]
  refine ⟨578479959041985969022145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1542613224111962584059053 578479959041985969022145)
  ·
    refine ⟨433859969281489476766609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 578479959041985969022145 433859969281489476766609)
    ·
      refine ⟨325394976961117107574957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 433859969281489476766609 325394976961117107574957)
      ·
        refine ⟨122023116360418915340609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 325394976961117107574957 122023116360418915340609)
        ·
          refine ⟨91517337270314186505457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 122023116360418915340609 91517337270314186505457)
          ·
            refine ⟨68638002952735639879093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91517337270314186505457 68638002952735639879093)
            ·
              refine ⟨6434812776818966238665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 68638002952735639879093 6434812776818966238665)
              ·
                rfl

theorem cell19_63442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 5].length) (baseStart_63442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63442 prefixEnd_63442 := by exact prefixLift 63442
  have htrace : WordTrace (prefixWord ++ tailWord_63442) baseStart_63442 baseEnd_63442 := by
    simpa [prefixWord, tailWord_63442, baseEnd_63442] using wordTrace_append hprefix tailTrace_63442
  have hstable : (prefixWord ++ tailWord_63442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63442).length < 2 ^ (prefixWord ++ tailWord_63442).sum := by decide
  have hdescent : baseEnd_63442 < baseStart_63442 := by decide
  rcases family_descends (prefixWord ++ tailWord_63442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63484 : List Nat := [2, 2, 2, 1, 2, 2, 1, 7]
def baseStart_63484 : Nat := 118140960795 + 63484 * 2 ^ 59
def prefixEnd_63484 : Nat := 4983230072969 + 3 ^ 40 * 63484 * 2
def baseEnd_63484 : Nat := 19317218293413245782547

theorem tailTrace_63484 : CollatzResearch.WordTrace tailWord_63484 prefixEnd_63484 19317218293413245782547 := by
  unfold tailWord_63484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157725851007892524558753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1543634468010523366078337 1157725851007892524558753)
  ·
    refine ⟨868294388255919393419065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1157725851007892524558753 868294388255919393419065)
    ·
      refine ⟨651220791191939545064299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 868294388255919393419065 651220791191939545064299)
      ·
        refine ⟨976831186787909317596449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651220791191939545064299 976831186787909317596449)
        ·
          refine ⟨732623390090931988197337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 976831186787909317596449 732623390090931988197337)
          ·
            refine ⟨549467542568198991148003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732623390090931988197337 549467542568198991148003)
            ·
              refine ⟨824201313852298486722005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549467542568198991148003 824201313852298486722005)
              ·
                refine ⟨19317218293413245782547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 824201313852298486722005 19317218293413245782547)
                ·
                  rfl

theorem cell19_63484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_63484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63484 prefixEnd_63484 := by exact prefixLift 63484
  have htrace : WordTrace (prefixWord ++ tailWord_63484) baseStart_63484 baseEnd_63484 := by
    simpa [prefixWord, tailWord_63484, baseEnd_63484] using wordTrace_append hprefix tailTrace_63484
  have hstable : (prefixWord ++ tailWord_63484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63484).length < 2 ^ (prefixWord ++ tailWord_63484).sum := by decide
  have hdescent : baseEnd_63484 < baseStart_63484 := by decide
  rcases family_descends (prefixWord ++ tailWord_63484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63541 : List Nat := [1, 3, 3, 1, 1, 1, 2, 7]
def baseStart_63541 : Nat := 118140960795 + 63541 * 2 ^ 59
def prefixEnd_63541 : Nat := 4983230072969 + 3 ^ 40 * 63541 * 2
def baseEnd_63541 : Nat := 19334562528854002515725

theorem tailTrace_63541 : CollatzResearch.WordTrace tailWord_63541 prefixEnd_63541 19334562528854002515725 := by
  unfold tailWord_63541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317530662809283783942477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1545020441872855855961651 2317530662809283783942477)
  ·
    refine ⟨869073998553481418978429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2317530662809283783942477 869073998553481418978429)
    ·
      refine ⟨325902749457555532116911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 869073998553481418978429 325902749457555532116911)
      ·
        refine ⟨488854124186333298175367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325902749457555532116911 488854124186333298175367)
        ·
          refine ⟨733281186279499947263051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488854124186333298175367 733281186279499947263051)
          ·
            refine ⟨1099921779419249920894577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733281186279499947263051 1099921779419249920894577)
            ·
              refine ⟨824941334564437440670933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099921779419249920894577 824941334564437440670933)
              ·
                refine ⟨19334562528854002515725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 824941334564437440670933 19334562528854002515725)
                ·
                  rfl

theorem cell19_63541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_63541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63541 prefixEnd_63541 := by exact prefixLift 63541
  have htrace : WordTrace (prefixWord ++ tailWord_63541) baseStart_63541 baseEnd_63541 := by
    simpa [prefixWord, tailWord_63541, baseEnd_63541] using wordTrace_append hprefix tailTrace_63541
  have hstable : (prefixWord ++ tailWord_63541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63541).length < 2 ^ (prefixWord ++ tailWord_63541).sum := by decide
  have hdescent : baseEnd_63541 < baseStart_63541 := by decide
  rcases family_descends (prefixWord ++ tailWord_63541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63596 : List Nat := [2, 2, 1, 1, 3, 3, 4, 3]
def baseStart_63596 : Nat := 118140960795 + 63596 * 2 ^ 59
def prefixEnd_63596 : Nat := 4983230072969 + 3 ^ 40 * 63596 * 2
def baseEnd_63596 : Nat := 19351298194630171293353

theorem tailTrace_63596 : CollatzResearch.WordTrace tailWord_63596 prefixEnd_63596 19351298194630171293353 := by
  unfold tailWord_63596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1159768338805014088597321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1546357785073352118129761 1159768338805014088597321)
  ·
    refine ⟨869826254103760566447991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1159768338805014088597321 869826254103760566447991)
    ·
      refine ⟨1304739381155640849671987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869826254103760566447991 1304739381155640849671987)
      ·
        refine ⟨1957109071733461274507981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304739381155640849671987 1957109071733461274507981)
        ·
          refine ⟨733915901900047977940493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1957109071733461274507981 733915901900047977940493)
          ·
            refine ⟨275218463212517991727685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733915901900047977940493 275218463212517991727685)
            ·
              refine ⟨51603461852347123448941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275218463212517991727685 51603461852347123448941)
              ·
                refine ⟨19351298194630171293353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51603461852347123448941 19351298194630171293353)
                ·
                  rfl

theorem cell19_63596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 3].length) (baseStart_63596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63596 prefixEnd_63596 := by exact prefixLift 63596
  have htrace : WordTrace (prefixWord ++ tailWord_63596) baseStart_63596 baseEnd_63596 := by
    simpa [prefixWord, tailWord_63596, baseEnd_63596] using wordTrace_append hprefix tailTrace_63596
  have hstable : (prefixWord ++ tailWord_63596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63596).length < 2 ^ (prefixWord ++ tailWord_63596).sum := by decide
  have hdescent : baseEnd_63596 < baseStart_63596 := by decide
  rcases family_descends (prefixWord ++ tailWord_63596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63634 : List Nat := [3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_63634 : Nat := 118140960795 + 63634 * 2 ^ 59
def prefixEnd_63634 : Nat := 4983230072969 + 3 ^ 40 * 63634 * 2
def baseEnd_63634 : Nat := 19362861018257342448805

theorem tailTrace_63634 : CollatzResearch.WordTrace tailWord_63634 prefixEnd_63634 19362861018257342448805 := by
  unfold tailWord_63634
  simp only [CollatzResearch.WordTrace]
  refine ⟨580230662868090166769489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1547281767648240444718637 580230662868090166769489)
  ·
    refine ⟨435172997151067625077117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 580230662868090166769489 435172997151067625077117)
    ·
      refine ⟨163189873931650359403919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 435172997151067625077117 163189873931650359403919)
      ·
        refine ⟨244784810897475539105879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163189873931650359403919 244784810897475539105879)
        ·
          refine ⟨367177216346213308658819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244784810897475539105879 367177216346213308658819)
          ·
            refine ⟨550765824519319962988229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367177216346213308658819 550765824519319962988229)
            ·
              refine ⟨103268592097372493060293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 550765824519319962988229 103268592097372493060293)
              ·
                refine ⟨19362861018257342448805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103268592097372493060293 19362861018257342448805)
                ·
                  rfl

theorem cell19_63634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_63634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63634 prefixEnd_63634 := by exact prefixLift 63634
  have htrace : WordTrace (prefixWord ++ tailWord_63634) baseStart_63634 baseEnd_63634 := by
    simpa [prefixWord, tailWord_63634, baseEnd_63634] using wordTrace_append hprefix tailTrace_63634
  have hstable : (prefixWord ++ tailWord_63634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63634).length < 2 ^ (prefixWord ++ tailWord_63634).sum := by decide
  have hdescent : baseEnd_63634 < baseStart_63634 := by decide
  rcases family_descends (prefixWord ++ tailWord_63634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63668 : List Nat := [2, 5, 3, 1, 1, 7]
def baseStart_63668 : Nat := 118140960795 + 63668 * 2 ^ 59
def prefixEnd_63668 : Nat := 4983230072969 + 3 ^ 40 * 63668 * 2
def baseEnd_63668 : Nat := 2152578522506148632573

theorem tailTrace_63668 : CollatzResearch.WordTrace tailWord_63668 prefixEnd_63668 2152578522506148632573 := by
  unfold tailWord_63668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1161081366674592236907829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1548108488899456315877105 1161081366674592236907829)
  ·
    refine ⟨108851378125743022210109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1161081366674592236907829 108851378125743022210109)
    ·
      refine ⟨40819266797153633328791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 108851378125743022210109 40819266797153633328791)
      ·
        refine ⟨61228900195730449993187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40819266797153633328791 61228900195730449993187)
        ·
          refine ⟨91843350293595674989781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61228900195730449993187 91843350293595674989781)
          ·
            refine ⟨2152578522506148632573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 91843350293595674989781 2152578522506148632573)
            ·
              rfl

theorem cell19_63668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 7].length) (baseStart_63668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63668 prefixEnd_63668 := by exact prefixLift 63668
  have htrace : WordTrace (prefixWord ++ tailWord_63668) baseStart_63668 baseEnd_63668 := by
    simpa [prefixWord, tailWord_63668, baseEnd_63668] using wordTrace_append hprefix tailTrace_63668
  have hstable : (prefixWord ++ tailWord_63668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63668).length < 2 ^ (prefixWord ++ tailWord_63668).sum := by decide
  have hdescent : baseEnd_63668 < baseStart_63668 := by decide
  rcases family_descends (prefixWord ++ tailWord_63668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63767 : List Nat := [1, 1, 3, 4, 1, 2, 4, 3]
def baseStart_63767 : Nat := 118140960795 + 63767 * 2 ^ 59
def prefixEnd_63767 : Nat := 4983230072969 + 3 ^ 40 * 63767 * 2
def baseEnd_63767 : Nat := 19403330900952441492887

theorem tailTrace_63767 : CollatzResearch.WordTrace tailWord_63767 prefixEnd_63767 19403330900952441492887 := by
  unfold tailWord_63767
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325773559990524381669555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1550515706660349587779703 2325773559990524381669555)
  ·
    refine ⟨3488660339985786572504333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2325773559990524381669555 3488660339985786572504333)
    ·
      refine ⟨1308247627494669964689125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3488660339985786572504333 1308247627494669964689125)
      ·
        refine ⟨245296430155250618379211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1308247627494669964689125 245296430155250618379211)
        ·
          refine ⟨367944645232875927568817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245296430155250618379211 367944645232875927568817)
          ·
            refine ⟨275958483924656945676613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 367944645232875927568817 275958483924656945676613)
            ·
              refine ⟨51742215735873177314365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 275958483924656945676613 51742215735873177314365)
              ·
                refine ⟨19403330900952441492887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51742215735873177314365 19403330900952441492887)
                ·
                  rfl

theorem cell19_63767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 3].length) (baseStart_63767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63767 prefixEnd_63767 := by exact prefixLift 63767
  have htrace : WordTrace (prefixWord ++ tailWord_63767) baseStart_63767 baseEnd_63767 := by
    simpa [prefixWord, tailWord_63767, baseEnd_63767] using wordTrace_append hprefix tailTrace_63767
  have hstable : (prefixWord ++ tailWord_63767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63767).length < 2 ^ (prefixWord ++ tailWord_63767).sum := by decide
  have hdescent : baseEnd_63767 < baseStart_63767 := by decide
  rcases family_descends (prefixWord ++ tailWord_63767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63784 : List Nat := [2, 1, 5, 1, 4, 1, 5]
def baseStart_63784 : Nat := 118140960795 + 63784 * 2 ^ 59
def prefixEnd_63784 : Nat := 4983230072969 + 3 ^ 40 * 63784 * 2
def baseEnd_63784 : Nat := 6469501247700479705021

theorem tailTrace_63784 : CollatzResearch.WordTrace tailWord_63784 prefixEnd_63784 6469501247700479705021 := by
  unfold tailWord_63784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1163196800464468142519203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1550929067285957523358937 1163196800464468142519203)
  ·
    refine ⟨1744795200696702213778805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1163196800464468142519203 1744795200696702213778805)
    ·
      refine ⟨163574550065315832541763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1744795200696702213778805 163574550065315832541763)
      ·
        refine ⟨245361825097973748812645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163574550065315832541763 245361825097973748812645)
        ·
          refine ⟨46005342205870077902371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 245361825097973748812645 46005342205870077902371)
          ·
            refine ⟨69008013308805116853557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46005342205870077902371 69008013308805116853557)
            ·
              refine ⟨6469501247700479705021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69008013308805116853557 6469501247700479705021)
              ·
                rfl

theorem cell19_63784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 5].length) (baseStart_63784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63784 prefixEnd_63784 := by exact prefixLift 63784
  have htrace : WordTrace (prefixWord ++ tailWord_63784) baseStart_63784 baseEnd_63784 := by
    simpa [prefixWord, tailWord_63784, baseEnd_63784] using wordTrace_append hprefix tailTrace_63784
  have hstable : (prefixWord ++ tailWord_63784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63784).length < 2 ^ (prefixWord ++ tailWord_63784).sum := by decide
  have hdescent : baseEnd_63784 < baseStart_63784 := by decide
  rcases family_descends (prefixWord ++ tailWord_63784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63807 : List Nat := [1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_63807 : Nat := 118140960795 + 63807 * 2 ^ 59
def prefixEnd_63807 : Nat := 4983230072969 + 3 ^ 40 * 63807 * 2
def baseEnd_63807 : Nat := 19415502294244200603889

theorem tailTrace_63807 : CollatzResearch.WordTrace tailWord_63807 prefixEnd_63807 19415502294244200603889 := by
  unfold tailWord_63807
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327232479845611213125675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1551488319897074142083783 2327232479845611213125675)
  ·
    refine ⟨3490848719768416819688513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327232479845611213125675 3490848719768416819688513)
    ·
      refine ⟨2618136539826312614766385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3490848719768416819688513 2618136539826312614766385)
      ·
        refine ⟨1963602404869734461074789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2618136539826312614766385 1963602404869734461074789)
        ·
          refine ⟨368175450913075211451523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1963602404869734461074789 368175450913075211451523)
          ·
            refine ⟨552263176369612817177285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368175450913075211451523 552263176369612817177285)
            ·
              refine ⟨103549345569302403220741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 552263176369612817177285 103549345569302403220741)
              ·
                refine ⟨19415502294244200603889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103549345569302403220741 19415502294244200603889)
                ·
                  rfl

theorem cell19_63807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_63807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63807 prefixEnd_63807 := by exact prefixLift 63807
  have htrace : WordTrace (prefixWord ++ tailWord_63807) baseStart_63807 baseEnd_63807 := by
    simpa [prefixWord, tailWord_63807, baseEnd_63807] using wordTrace_append hprefix tailTrace_63807
  have hstable : (prefixWord ++ tailWord_63807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63807).length < 2 ^ (prefixWord ++ tailWord_63807).sum := by decide
  have hdescent : baseEnd_63807 < baseStart_63807 := by decide
  rcases family_descends (prefixWord ++ tailWord_63807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63826 : List Nat := [3, 2, 2, 1, 1, 1, 4, 5]
def baseStart_63826 : Nat := 118140960795 + 63826 * 2 ^ 59
def prefixEnd_63826 : Nat := 4983230072969 + 3 ^ 40 * 63826 * 2
def baseEnd_63826 : Nat := 19421283706057786181615

theorem tailTrace_63826 : CollatzResearch.WordTrace tailWord_63826 prefixEnd_63826 19421283706057786181615 := by
  unfold tailWord_63826
  simp only [CollatzResearch.WordTrace]
  refine ⟨581981366694194364516833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1551950311184518305378221 581981366694194364516833)
  ·
    refine ⟨436486025020645773387625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 581981366694194364516833 436486025020645773387625)
    ·
      refine ⟨327364518765484330040719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436486025020645773387625 327364518765484330040719)
      ·
        refine ⟨491046778148226495061079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327364518765484330040719 491046778148226495061079)
        ·
          refine ⟨736570167222339742591619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 491046778148226495061079 736570167222339742591619)
          ·
            refine ⟨1104855250833509613887429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736570167222339742591619 1104855250833509613887429)
            ·
              refine ⟨207160359531283052603893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1104855250833509613887429 207160359531283052603893)
              ·
                refine ⟨19421283706057786181615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 207160359531283052603893 19421283706057786181615)
                ·
                  rfl

theorem cell19_63826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_63826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63826 prefixEnd_63826 := by exact prefixLift 63826
  have htrace : WordTrace (prefixWord ++ tailWord_63826) baseStart_63826 baseEnd_63826 := by
    simpa [prefixWord, tailWord_63826, baseEnd_63826] using wordTrace_append hprefix tailTrace_63826
  have hstable : (prefixWord ++ tailWord_63826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63826).length < 2 ^ (prefixWord ++ tailWord_63826).sum := by decide
  have hdescent : baseEnd_63826 < baseStart_63826 := by decide
  rcases family_descends (prefixWord ++ tailWord_63826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63881 : List Nat := [1, 2, 1, 1, 6, 2, 3, 3]
def baseStart_63881 : Nat := 118140960795 + 63881 * 2 ^ 59
def prefixEnd_63881 : Nat := 4983230072969 + 3 ^ 40 * 63881 * 2
def baseEnd_63881 : Nat := 19438019371833954959243

theorem tailTrace_63881 : CollatzResearch.WordTrace tailWord_63881 prefixEnd_63881 19438019371833954959243 := by
  unfold tailWord_63881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329931481577521851319497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1553287654385014567546331 2329931481577521851319497)
  ·
    refine ⟨1747448611183141388489623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2329931481577521851319497 1747448611183141388489623)
    ·
      refine ⟨2621172916774712082734435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747448611183141388489623 2621172916774712082734435)
      ·
        refine ⟨3931759375162068124101653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621172916774712082734435 3931759375162068124101653)
        ·
          refine ⟨184301220710721943317265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3931759375162068124101653 184301220710721943317265)
          ·
            refine ⟨138225915533041457487949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 184301220710721943317265 138225915533041457487949)
            ·
              refine ⟨51834718324890546557981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 138225915533041457487949 51834718324890546557981)
              ·
                refine ⟨19438019371833954959243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 51834718324890546557981 19438019371833954959243)
                ·
                  rfl

theorem cell19_63881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 3].length) (baseStart_63881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63881 prefixEnd_63881 := by exact prefixLift 63881
  have htrace : WordTrace (prefixWord ++ tailWord_63881) baseStart_63881 baseEnd_63881 := by
    simpa [prefixWord, tailWord_63881, baseEnd_63881] using wordTrace_append hprefix tailTrace_63881
  have hstable : (prefixWord ++ tailWord_63881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63881).length < 2 ^ (prefixWord ++ tailWord_63881).sum := by decide
  have hdescent : baseEnd_63881 < baseStart_63881 := by decide
  rcases family_descends (prefixWord ++ tailWord_63881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63978 : List Nat := [3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_63978 : Nat := 118140960795 + 63978 * 2 ^ 59
def prefixEnd_63978 : Nat := 4983230072969 + 3 ^ 40 * 63978 * 2
def baseEnd_63978 : Nat := 19467535000566470803423

theorem tailTrace_63978 : CollatzResearch.WordTrace tailWord_63978 prefixEnd_63978 19467535000566470803423 := by
  unfold tailWord_63978
  simp only [CollatzResearch.WordTrace]
  refine ⟨583367340556526854400147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1555646241484071611733725 583367340556526854400147)
  ·
    refine ⟨875051010834790281600221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 583367340556526854400147 875051010834790281600221)
    ·
      refine ⟨328144129063046355600083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 875051010834790281600221 328144129063046355600083)
      ·
        refine ⟨492216193594569533400125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328144129063046355600083 492216193594569533400125)
        ·
          refine ⟨184581072597963575025047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 492216193594569533400125 184581072597963575025047)
          ·
            refine ⟨276871608896945362537571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184581072597963575025047 276871608896945362537571)
            ·
              refine ⟨415307413345418043806357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276871608896945362537571 415307413345418043806357)
              ·
                refine ⟨19467535000566470803423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 415307413345418043806357 19467535000566470803423)
                ·
                  rfl

theorem cell19_63978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_63978 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63978 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63978 prefixEnd_63978 := by exact prefixLift 63978
  have htrace : WordTrace (prefixWord ++ tailWord_63978) baseStart_63978 baseEnd_63978 := by
    simpa [prefixWord, tailWord_63978, baseEnd_63978] using wordTrace_append hprefix tailTrace_63978
  have hstable : (prefixWord ++ tailWord_63978).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63978).length < 2 ^ (prefixWord ++ tailWord_63978).sum := by decide
  have hdescent : baseEnd_63978 < baseStart_63978 := by decide
  rcases family_descends (prefixWord ++ tailWord_63978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_63999 : List Nat := [1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_63999 : Nat := 118140960795 + 63999 * 2 ^ 59
def prefixEnd_63999 : Nat := 4983230072969 + 3 ^ 40 * 63999 * 2
def baseEnd_63999 : Nat := 19473924982044644336699

theorem tailTrace_63999 : CollatzResearch.WordTrace tailWord_63999 prefixEnd_63999 19473924982044644336699 := by
  unfold tailWord_63999
  simp only [CollatzResearch.WordTrace]
  refine ⟨2334235295150028004115051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1556156863433352002743367 2334235295150028004115051)
  ·
    refine ⟨3501352942725042006172577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2334235295150028004115051 3501352942725042006172577)
    ·
      refine ⟨2626014707043781504629433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3501352942725042006172577 2626014707043781504629433)
      ·
        refine ⟨1969511030282836128472075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2626014707043781504629433 1969511030282836128472075)
        ·
          refine ⟨2954266545424254192708113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1969511030282836128472075 2954266545424254192708113)
          ·
            refine ⟨2215699909068190644531085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2954266545424254192708113 2215699909068190644531085)
            ·
              refine ⟨830887465900571491699157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2215699909068190644531085 830887465900571491699157)
              ·
                refine ⟨19473924982044644336699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 830887465900571491699157 19473924982044644336699)
                ·
                  rfl

theorem cell19_63999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_63999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_63999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_63999 prefixEnd_63999 := by exact prefixLift 63999
  have htrace : WordTrace (prefixWord ++ tailWord_63999) baseStart_63999 baseEnd_63999 := by
    simpa [prefixWord, tailWord_63999, baseEnd_63999] using wordTrace_append hprefix tailTrace_63999
  have hstable : (prefixWord ++ tailWord_63999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_63999).length < 2 ^ (prefixWord ++ tailWord_63999).sum := by decide
  have hdescent : baseEnd_63999 < baseStart_63999 := by decide
  rcases family_descends (prefixWord ++ tailWord_63999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64018 : List Nat := [3, 2, 14]
def baseStart_64018 : Nat := 118140960795 + 64018 * 2 ^ 59
def prefixEnd_64018 : Nat := 4983230072969 + 3 ^ 40 * 64018 * 2
def baseEnd_64018 : Nat := 80163400797770493475

theorem tailTrace_64018 : CollatzResearch.WordTrace tailWord_64018 prefixEnd_64018 80163400797770493475 := by
  unfold tailWord_64018
  simp only [CollatzResearch.WordTrace]
  refine ⟨583732070520298562264177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1556618854720796166037805 583732070520298562264177)
  ·
    refine ⟨437799052890223921698133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 583732070520298562264177 437799052890223921698133)
    ·
      refine ⟨80163400797770493475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 437799052890223921698133 80163400797770493475)
      ·
        rfl

theorem cell19_64018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 14].length) (baseStart_64018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64018 prefixEnd_64018 := by exact prefixLift 64018
  have htrace : WordTrace (prefixWord ++ tailWord_64018) baseStart_64018 baseEnd_64018 := by
    simpa [prefixWord, tailWord_64018, baseEnd_64018] using wordTrace_append hprefix tailTrace_64018
  have hstable : (prefixWord ++ tailWord_64018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64018).length < 2 ^ (prefixWord ++ tailWord_64018).sum := by decide
  have hdescent : baseEnd_64018 < baseStart_64018 := by decide
  rcases family_descends (prefixWord ++ tailWord_64018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64035 : List Nat := [1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_64035 : Nat := 118140960795 + 64035 * 2 ^ 59
def prefixEnd_64035 : Nat := 4983230072969 + 3 ^ 40 * 64035 * 2
def baseEnd_64035 : Nat := 19484879236007227536601

theorem tailTrace_64035 : CollatzResearch.WordTrace tailWord_64035 prefixEnd_64035 19484879236007227536601 := by
  unfold tailWord_64035
  simp only [CollatzResearch.WordTrace]
  refine ⟨2335548323019606152425559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1557032215346404101617039 2335548323019606152425559)
  ·
    refine ⟨3503322484529409228638339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2335548323019606152425559 3503322484529409228638339)
    ·
      refine ⟨5254983726794113842957509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3503322484529409228638339 5254983726794113842957509)
      ·
        refine ⟨985309448773896345554533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5254983726794113842957509 985309448773896345554533)
        ·
          refine ⟨184745521645105564791475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 985309448773896345554533 184745521645105564791475)
          ·
            refine ⟨277118282467658347187213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184745521645105564791475 277118282467658347187213)
            ·
              refine ⟨103919355925371880195205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277118282467658347187213 103919355925371880195205)
              ·
                refine ⟨19484879236007227536601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 103919355925371880195205 19484879236007227536601)
                ·
                  rfl

theorem cell19_64035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_64035 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64035 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64035 prefixEnd_64035 := by exact prefixLift 64035
  have htrace : WordTrace (prefixWord ++ tailWord_64035) baseStart_64035 baseEnd_64035 := by
    simpa [prefixWord, tailWord_64035, baseEnd_64035] using wordTrace_append hprefix tailTrace_64035
  have hstable : (prefixWord ++ tailWord_64035).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64035).length < 2 ^ (prefixWord ++ tailWord_64035).sum := by decide
  have hdescent : baseEnd_64035 < baseStart_64035 := by decide
  rcases family_descends (prefixWord ++ tailWord_64035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64109 : List Nat := [1, 5, 1, 1, 3, 1, 4, 3]
def baseStart_64109 : Nat := 118140960795 + 64109 * 2 ^ 59
def prefixEnd_64109 : Nat := 4983230072969 + 3 ^ 40 * 64109 * 2
def baseEnd_64109 : Nat := 19507396313596981891955

theorem tailTrace_64109 : CollatzResearch.WordTrace tailWord_64109 prefixEnd_64109 19507396313596981891955 := by
  unfold tailWord_64109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338247324751516790619381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1558831549834344527079587 2338247324751516790619381)
  ·
    refine ⟨219210686695454699120567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2338247324751516790619381 219210686695454699120567)
    ·
      refine ⟨328816030043182048680851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219210686695454699120567 328816030043182048680851)
      ·
        refine ⟨493224045064773073021277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328816030043182048680851 493224045064773073021277)
        ·
          refine ⟨184959016899289902382979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 493224045064773073021277 184959016899289902382979)
          ·
            refine ⟨277438525348934853574469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184959016899289902382979 277438525348934853574469)
            ·
              refine ⟨52019723502925285045213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 277438525348934853574469 52019723502925285045213)
              ·
                refine ⟨19507396313596981891955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52019723502925285045213 19507396313596981891955)
                ·
                  rfl

theorem cell19_64109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 3].length) (baseStart_64109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64109 prefixEnd_64109 := by exact prefixLift 64109
  have htrace : WordTrace (prefixWord ++ tailWord_64109) baseStart_64109 baseEnd_64109 := by
    simpa [prefixWord, tailWord_64109, baseEnd_64109] using wordTrace_append hprefix tailTrace_64109
  have hstable : (prefixWord ++ tailWord_64109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64109).length < 2 ^ (prefixWord ++ tailWord_64109).sum := by decide
  have hdescent : baseEnd_64109 < baseStart_64109 := by decide
  rcases family_descends (prefixWord ++ tailWord_64109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64111 : List Nat := [1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_64111 : Nat := 118140960795 + 64111 * 2 ^ 59
def prefixEnd_64111 : Nat := 4983230072969 + 3 ^ 40 * 64111 * 2
def baseEnd_64111 : Nat := 19508004883261569847505

theorem tailTrace_64111 : CollatzResearch.WordTrace tailWord_64111 prefixEnd_64111 19508004883261569847505 := by
  unfold tailWord_64111
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338320270744271132192187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1558880180496180754794791 2338320270744271132192187)
  ·
    refine ⟨3507480406116406698288281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338320270744271132192187 3507480406116406698288281)
    ·
      refine ⟨2630610304587305023716211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3507480406116406698288281 2630610304587305023716211)
      ·
        refine ⟨3945915456880957535574317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2630610304587305023716211 3945915456880957535574317)
        ·
          refine ⟨1479718296330359075840369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3945915456880957535574317 1479718296330359075840369)
          ·
            refine ⟨1109788722247769306880277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1479718296330359075840369 1109788722247769306880277)
            ·
              refine ⟨52021346355364186260013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1109788722247769306880277 52021346355364186260013)
              ·
                refine ⟨19508004883261569847505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52021346355364186260013 19508004883261569847505)
                ·
                  rfl

theorem cell19_64111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_64111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64111 prefixEnd_64111 := by exact prefixLift 64111
  have htrace : WordTrace (prefixWord ++ tailWord_64111) baseStart_64111 baseEnd_64111 := by
    simpa [prefixWord, tailWord_64111, baseEnd_64111] using wordTrace_append hprefix tailTrace_64111
  have hstable : (prefixWord ++ tailWord_64111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64111).length < 2 ^ (prefixWord ++ tailWord_64111).sum := by decide
  have hdescent : baseEnd_64111 < baseStart_64111 := by decide
  rcases family_descends (prefixWord ++ tailWord_64111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64189 : List Nat := [1, 4, 1, 2, 1, 10]
def baseStart_64189 : Nat := 118140960795 + 64189 * 2 ^ 59
def prefixEnd_64189 : Nat := 4983230072969 + 3 ^ 40 * 64189 * 2
def baseEnd_64189 : Nat := 2170193233353388901551

theorem tailTrace_64189 : CollatzResearch.WordTrace tailWord_64189 prefixEnd_64189 2170193233353388901551 := by
  unfold tailWord_64189
  simp only [CollatzResearch.WordTrace]
  refine ⟨2341165164461690453531621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1560776776307793635687747 2341165164461690453531621)
  ·
    refine ⟨438968468336566960037179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2341165164461690453531621 438968468336566960037179)
    ·
      refine ⟨658452702504850440055769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 438968468336566960037179 658452702504850440055769)
      ·
        refine ⟨493839526878637830041827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 658452702504850440055769 493839526878637830041827)
        ·
          refine ⟨740759290317956745062741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 493839526878637830041827 740759290317956745062741)
          ·
            refine ⟨2170193233353388901551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 740759290317956745062741 2170193233353388901551)
            ·
              rfl

theorem cell19_64189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 10].length) (baseStart_64189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64189 prefixEnd_64189 := by exact prefixLift 64189
  have htrace : WordTrace (prefixWord ++ tailWord_64189) baseStart_64189 baseEnd_64189 := by
    simpa [prefixWord, tailWord_64189, baseEnd_64189] using wordTrace_append hprefix tailTrace_64189
  have hstable : (prefixWord ++ tailWord_64189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64189).length < 2 ^ (prefixWord ++ tailWord_64189).sum := by decide
  have hdescent : baseEnd_64189 < baseStart_64189 := by decide
  rcases family_descends (prefixWord ++ tailWord_64189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64198 : List Nat := [6, 1, 2, 1, 3, 1, 1, 4]
def baseStart_64198 : Nat := 118140960795 + 64198 * 2 ^ 59
def prefixEnd_64198 : Nat := 4983230072969 + 3 ^ 40 * 64198 * 2
def baseEnd_64198 : Nat := 19534477663671145913935

theorem tailTrace_64198 : CollatzResearch.WordTrace tailWord_64198 prefixEnd_64198 19534477663671145913935 := by
  unfold tailWord_64198
  simp only [CollatzResearch.WordTrace]
  refine ⟨73171669419658905956539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1560995614286056660406165 73171669419658905956539)
  ·
    refine ⟨109757504129488358934809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73171669419658905956539 109757504129488358934809)
    ·
      refine ⟨82318128097116269201107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109757504129488358934809 82318128097116269201107)
      ·
        refine ⟨123477192145674403801661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82318128097116269201107 123477192145674403801661)
        ·
          refine ⟨46303947054627901425623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123477192145674403801661 46303947054627901425623)
          ·
            refine ⟨69455920581941852138435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46303947054627901425623 69455920581941852138435)
            ·
              refine ⟨104183880872912778207653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69455920581941852138435 104183880872912778207653)
              ·
                refine ⟨19534477663671145913935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104183880872912778207653 19534477663671145913935)
                ·
                  rfl

theorem cell19_64198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_64198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64198 prefixEnd_64198 := by exact prefixLift 64198
  have htrace : WordTrace (prefixWord ++ tailWord_64198) baseStart_64198 baseEnd_64198 := by
    simpa [prefixWord, tailWord_64198, baseEnd_64198] using wordTrace_append hprefix tailTrace_64198
  have hstable : (prefixWord ++ tailWord_64198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64198).length < 2 ^ (prefixWord ++ tailWord_64198).sum := by decide
  have hdescent : baseEnd_64198 < baseStart_64198 := by decide
  rcases family_descends (prefixWord ++ tailWord_64198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64204 : List Nat := [2, 2, 1, 5, 1, 3, 1, 4]
def baseStart_64204 : Nat := 118140960795 + 64204 * 2 ^ 59
def prefixEnd_64204 : Nat := 4983230072969 + 3 ^ 40 * 64204 * 2
def baseEnd_64204 : Nat := 19536303372664909780585

theorem tailTrace_64204 : CollatzResearch.WordTrace tailWord_64204 prefixEnd_64204 19536303372664909780585 := by
  unfold tailWord_64204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170856129703674007663833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1561141506271565343551777 1170856129703674007663833)
  ·
    refine ⟨878142097277755505747875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1170856129703674007663833 878142097277755505747875)
    ·
      refine ⟨1317213145916633258621813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878142097277755505747875 1317213145916633258621813)
      ·
        refine ⟨123488732429684367995795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1317213145916633258621813 123488732429684367995795)
        ·
          refine ⟨185233098644526551993693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123488732429684367995795 185233098644526551993693)
          ·
            refine ⟨69462411991697456997635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185233098644526551993693 69462411991697456997635)
            ·
              refine ⟨104193617987546185496453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69462411991697456997635 104193617987546185496453)
              ·
                refine ⟨19536303372664909780585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104193617987546185496453 19536303372664909780585)
                ·
                  rfl

theorem cell19_64204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_64204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64204 prefixEnd_64204 := by exact prefixLift 64204
  have htrace : WordTrace (prefixWord ++ tailWord_64204) baseStart_64204 baseEnd_64204 := by
    simpa [prefixWord, tailWord_64204, baseEnd_64204] using wordTrace_append hprefix tailTrace_64204
  have hstable : (prefixWord ++ tailWord_64204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64204).length < 2 ^ (prefixWord ++ tailWord_64204).sum := by decide
  have hdescent : baseEnd_64204 < baseStart_64204 := by decide
  rcases family_descends (prefixWord ++ tailWord_64204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64206 : List Nat := [4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_64206 : Nat := 118140960795 + 64206 * 2 ^ 59
def prefixEnd_64206 : Nat := 4983230072969 + 3 ^ 40 * 64206 * 2
def baseEnd_64206 : Nat := 19536911942329497736135

theorem tailTrace_64206 : CollatzResearch.WordTrace tailWord_64206 prefixEnd_64206 19536911942329497736135 := by
  unfold tailWord_64206
  simp only [CollatzResearch.WordTrace]
  refine ⟨292723150675012794612559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1561190136933401571266981 292723150675012794612559)
  ·
    refine ⟨439084726012519191918839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 292723150675012794612559 439084726012519191918839)
    ·
      refine ⟨658627089018778787878259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439084726012519191918839 658627089018778787878259)
      ·
        refine ⟨987940633528168181817389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 658627089018778787878259 987940633528168181817389)
        ·
          refine ⟨370477737573063068181521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 987940633528168181817389 370477737573063068181521)
          ·
            refine ⟨277858303179797301136141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370477737573063068181521 277858303179797301136141)
            ·
              refine ⟨104196863692423987926053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 277858303179797301136141 104196863692423987926053)
              ·
                refine ⟨19536911942329497736135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104196863692423987926053 19536911942329497736135)
                ·
                  rfl

theorem cell19_64206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_64206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64206 prefixEnd_64206 := by exact prefixLift 64206
  have htrace : WordTrace (prefixWord ++ tailWord_64206) baseStart_64206 baseEnd_64206 := by
    simpa [prefixWord, tailWord_64206, baseEnd_64206] using wordTrace_append hprefix tailTrace_64206
  have hstable : (prefixWord ++ tailWord_64206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64206).length < 2 ^ (prefixWord ++ tailWord_64206).sum := by decide
  have hdescent : baseEnd_64206 < baseStart_64206 := by decide
  rcases family_descends (prefixWord ++ tailWord_64206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64318 : List Nat := [4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_64318 : Nat := 118140960795 + 64318 * 2 ^ 59
def prefixEnd_64318 : Nat := 4983230072969 + 3 ^ 40 * 64318 * 2
def baseEnd_64318 : Nat := 19570991843546423246941

theorem tailTrace_64318 : CollatzResearch.WordTrace tailWord_64318 prefixEnd_64318 19570991843546423246941 := by
  unfold tailWord_64318
  simp only [CollatzResearch.WordTrace]
  refine ⟨293233772624293185622201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1563913453996230323318405 293233772624293185622201)
  ·
    refine ⟨219925329468219889216651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293233772624293185622201 219925329468219889216651)
    ·
      refine ⟨329887994202329833824977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219925329468219889216651 329887994202329833824977)
      ·
        refine ⟨247415995651747375368733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329887994202329833824977 247415995651747375368733)
        ·
          refine ⟨92780998369405265763275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247415995651747375368733 92780998369405265763275)
          ·
            refine ⟨139171497554107898644913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92780998369405265763275 139171497554107898644913)
            ·
              refine ⟨104378623165580923983685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139171497554107898644913 104378623165580923983685)
              ·
                refine ⟨19570991843546423246941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104378623165580923983685 19570991843546423246941)
                ·
                  rfl

theorem cell19_64318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_64318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64318 prefixEnd_64318 := by exact prefixLift 64318
  have htrace : WordTrace (prefixWord ++ tailWord_64318) baseStart_64318 baseEnd_64318 := by
    simpa [prefixWord, tailWord_64318, baseEnd_64318] using wordTrace_append hprefix tailTrace_64318
  have hstable : (prefixWord ++ tailWord_64318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64318).length < 2 ^ (prefixWord ++ tailWord_64318).sum := by decide
  have hdescent : baseEnd_64318 < baseStart_64318 := by decide
  rcases family_descends (prefixWord ++ tailWord_64318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64341 : List Nat := [1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_64341 : Nat := 118140960795 + 64341 * 2 ^ 59
def prefixEnd_64341 : Nat := 4983230072969 + 3 ^ 40 * 64341 * 2
def baseEnd_64341 : Nat := 19577990394689184735767

theorem tailTrace_64341 : CollatzResearch.WordTrace tailWord_64341 prefixEnd_64341 19577990394689184735767 := by
  unfold tailWord_64341
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346709059911020413064877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1564472706607346942043251 2346709059911020413064877)
  ·
    refine ⟨880015897466632654899329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2346709059911020413064877 880015897466632654899329)
    ·
      refine ⟨660011923099974491174497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 880015897466632654899329 660011923099974491174497)
      ·
        refine ⟨495008942324980868380873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660011923099974491174497 495008942324980868380873)
        ·
          refine ⟨371256706743735651285655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495008942324980868380873 371256706743735651285655)
          ·
            refine ⟨556885060115603476928483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371256706743735651285655 556885060115603476928483)
            ·
              refine ⟨835327590173405215392725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556885060115603476928483 835327590173405215392725)
              ·
                refine ⟨19577990394689184735767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 835327590173405215392725 19577990394689184735767)
                ·
                  rfl

theorem cell19_64341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_64341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64341 prefixEnd_64341 := by exact prefixLift 64341
  have htrace : WordTrace (prefixWord ++ tailWord_64341) baseStart_64341 baseEnd_64341 := by
    simpa [prefixWord, tailWord_64341, baseEnd_64341] using wordTrace_append hprefix tailTrace_64341
  have hstable : (prefixWord ++ tailWord_64341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64341).length < 2 ^ (prefixWord ++ tailWord_64341).sum := by decide
  have hdescent : baseEnd_64341 < baseStart_64341 := by decide
  rcases family_descends (prefixWord ++ tailWord_64341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64360 : List Nat := [2, 1, 4, 2, 1, 9]
def baseStart_64360 : Nat := 118140960795 + 64360 * 2 ^ 59
def prefixEnd_64360 : Nat := 4983230072969 + 3 ^ 40 * 64360 * 2
def baseEnd_64360 : Nat := 2175974645166974479277

theorem tailTrace_64360 : CollatzResearch.WordTrace tailWord_64360 prefixEnd_64360 2175974645166974479277 := by
  unfold tailWord_64360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173701023421093329003267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1564934697894791105337689 1173701023421093329003267)
  ·
    refine ⟨1760551535131639993504901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1173701023421093329003267 1760551535131639993504901)
    ·
      refine ⟨330103412837182498782169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1760551535131639993504901 330103412837182498782169)
      ·
        refine ⟨247577559627886874086627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330103412837182498782169 247577559627886874086627)
        ·
          refine ⟨371366339441830311129941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247577559627886874086627 371366339441830311129941)
          ·
            refine ⟨2175974645166974479277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 371366339441830311129941 2175974645166974479277)
            ·
              rfl

theorem cell19_64360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 9].length) (baseStart_64360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64360 prefixEnd_64360 := by exact prefixLift 64360
  have htrace : WordTrace (prefixWord ++ tailWord_64360) baseStart_64360 baseEnd_64360 := by
    simpa [prefixWord, tailWord_64360, baseEnd_64360] using wordTrace_append hprefix tailTrace_64360
  have hstable : (prefixWord ++ tailWord_64360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64360).length < 2 ^ (prefixWord ++ tailWord_64360).sum := by decide
  have hdescent : baseEnd_64360 < baseStart_64360 := by decide
  rcases family_descends (prefixWord ++ tailWord_64360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64377 : List Nat := [1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_64377 : Nat := 118140960795 + 64377 * 2 ^ 59
def prefixEnd_64377 : Nat := 4983230072969 + 3 ^ 40 * 64377 * 2
def baseEnd_64377 : Nat := 19588944648651767935669

theorem tailTrace_64377 : CollatzResearch.WordTrace tailWord_64377 prefixEnd_64377 19588944648651767935669 := by
  unfold tailWord_64377
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348022087780598561375385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1565348058520399040916923 2348022087780598561375385)
  ·
    refine ⟨1761016565835448921031539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2348022087780598561375385 1761016565835448921031539)
    ·
      refine ⟨2641524848753173381547309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1761016565835448921031539 2641524848753173381547309)
      ·
        refine ⟨990571818282440018080241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2641524848753173381547309 990571818282440018080241)
        ·
          refine ⟨742928863711830013560181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990571818282440018080241 742928863711830013560181)
          ·
            refine ⟨69649580972984063771267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 742928863711830013560181 69649580972984063771267)
            ·
              refine ⟨104474371459476095656901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69649580972984063771267 104474371459476095656901)
              ·
                refine ⟨19588944648651767935669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104474371459476095656901 19588944648651767935669)
                ·
                  rfl

theorem cell19_64377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_64377 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64377 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64377 prefixEnd_64377 := by exact prefixLift 64377
  have htrace : WordTrace (prefixWord ++ tailWord_64377) baseStart_64377 baseEnd_64377 := by
    simpa [prefixWord, tailWord_64377, baseEnd_64377] using wordTrace_append hprefix tailTrace_64377
  have hstable : (prefixWord ++ tailWord_64377).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64377).length < 2 ^ (prefixWord ++ tailWord_64377).sum := by decide
  have hdescent : baseEnd_64377 < baseStart_64377 := by decide
  rcases family_descends (prefixWord ++ tailWord_64377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64379 : List Nat := [1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_64379 : Nat := 118140960795 + 64379 * 2 ^ 59
def prefixEnd_64379 : Nat := 4983230072969 + 3 ^ 40 * 64379 * 2
def baseEnd_64379 : Nat := 19589553218316355891219

theorem tailTrace_64379 : CollatzResearch.WordTrace tailWord_64379 prefixEnd_64379 19589553218316355891219 := by
  unfold tailWord_64379
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348095033773352902948191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1565396689182235268632127 2348095033773352902948191)
  ·
    refine ⟨3522142550660029354422287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348095033773352902948191 3522142550660029354422287)
    ·
      refine ⟨5283213825990044031633431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522142550660029354422287 5283213825990044031633431)
      ·
        refine ⟨7924820738985066047450147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283213825990044031633431 7924820738985066047450147)
        ·
          refine ⟨11887231108477599071175221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924820738985066047450147 11887231108477599071175221)
          ·
            refine ⟨1114427916419774912922677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11887231108477599071175221 1114427916419774912922677)
            ·
              refine ⟨104477617164353898086501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1114427916419774912922677 104477617164353898086501)
              ·
                refine ⟨19589553218316355891219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104477617164353898086501 19589553218316355891219)
                ·
                  rfl

theorem cell19_64379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_64379 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64379 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64379 prefixEnd_64379 := by exact prefixLift 64379
  have htrace : WordTrace (prefixWord ++ tailWord_64379) baseStart_64379 baseEnd_64379 := by
    simpa [prefixWord, tailWord_64379, baseEnd_64379] using wordTrace_append hprefix tailTrace_64379
  have hstable : (prefixWord ++ tailWord_64379).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64379).length < 2 ^ (prefixWord ++ tailWord_64379).sum := by decide
  have hdescent : baseEnd_64379 < baseStart_64379 := by decide
  rcases family_descends (prefixWord ++ tailWord_64379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64394 : List Nat := [3, 1, 2, 4, 1, 2, 3, 3]
def baseStart_64394 : Nat := 118140960795 + 64394 * 2 ^ 59
def prefixEnd_64394 : Nat := 4983230072969 + 3 ^ 40 * 64394 * 2
def baseEnd_64394 : Nat := 19594117490800765557845

theorem tailTrace_64394 : CollatzResearch.WordTrace tailWord_64394 prefixEnd_64394 19594117490800765557845 := by
  unfold tailWord_64394
  simp only [CollatzResearch.WordTrace]
  refine ⟨587160532179752616186059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1565761419146006976496157 587160532179752616186059)
  ·
    refine ⟨880740798269628924279089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 587160532179752616186059 880740798269628924279089)
    ·
      refine ⟨660555598702221693209317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 880740798269628924279089 660555598702221693209317)
      ·
        refine ⟨123854174756666567476747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 660555598702221693209317 123854174756666567476747)
        ·
          refine ⟨185781262134999851215121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123854174756666567476747 185781262134999851215121)
          ·
            refine ⟨139335946601249888411341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185781262134999851215121 139335946601249888411341)
            ·
              refine ⟨52250979975468708154253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139335946601249888411341 52250979975468708154253)
              ·
                refine ⟨19594117490800765557845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52250979975468708154253 19594117490800765557845)
                ·
                  rfl

theorem cell19_64394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_64394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64394 prefixEnd_64394 := by exact prefixLift 64394
  have htrace : WordTrace (prefixWord ++ tailWord_64394) baseStart_64394 baseEnd_64394 := by
    simpa [prefixWord, tailWord_64394, baseEnd_64394] using wordTrace_append hprefix tailTrace_64394
  have hstable : (prefixWord ++ tailWord_64394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64394).length < 2 ^ (prefixWord ++ tailWord_64394).sum := by decide
  have hdescent : baseEnd_64394 < baseStart_64394 := by decide
  rcases family_descends (prefixWord ++ tailWord_64394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64470 : List Nat := [5, 2, 1, 1, 2, 3, 5]
def baseStart_64470 : Nat := 118140960795 + 64470 * 2 ^ 59
def prefixEnd_64470 : Nat := 4983230072969 + 3 ^ 40 * 64470 * 2
def baseEnd_64470 : Nat := 6539081046018369289583

theorem tailTrace_64470 : CollatzResearch.WordTrace tailWord_64470 prefixEnd_64470 6539081046018369289583 := by
  unfold tailWord_64470
  simp only [CollatzResearch.WordTrace]
  refine ⟨146963379777729715281929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1567609384295783629673909 146963379777729715281929)
  ·
    refine ⟨110222534833297286461447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146963379777729715281929 110222534833297286461447)
    ·
      refine ⟨165333802249945929692171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110222534833297286461447 165333802249945929692171)
      ·
        refine ⟨248000703374918894538257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165333802249945929692171 248000703374918894538257)
        ·
          refine ⟨186000527531189170903693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248000703374918894538257 186000527531189170903693)
          ·
            refine ⟨69750197824195939088885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186000527531189170903693 69750197824195939088885)
            ·
              refine ⟨6539081046018369289583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69750197824195939088885 6539081046018369289583)
              ·
                rfl

theorem cell19_64470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_64470 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64470 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64470 prefixEnd_64470 := by exact prefixLift 64470
  have htrace : WordTrace (prefixWord ++ tailWord_64470) baseStart_64470 baseEnd_64470 := by
    simpa [prefixWord, tailWord_64470, baseEnd_64470] using wordTrace_append hprefix tailTrace_64470
  have hstable : (prefixWord ++ tailWord_64470).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64470).length < 2 ^ (prefixWord ++ tailWord_64470).sum := by decide
  have hdescent : baseEnd_64470 < baseStart_64470 := by decide
  rcases family_descends (prefixWord ++ tailWord_64470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64474 : List Nat := [3, 1, 1, 2, 4, 1, 7]
def baseStart_64474 : Nat := 118140960795 + 64474 * 2 ^ 59
def prefixEnd_64474 : Nat := 4983230072969 + 3 ^ 40 * 64474 * 2
def baseEnd_64474 : Nat := 6539486759128094593283

theorem tailTrace_64474 : CollatzResearch.WordTrace tailWord_64474 prefixEnd_64474 6539486759128094593283 := by
  unfold tailWord_64474
  simp only [CollatzResearch.WordTrace]
  refine ⟨587889992107296031914119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1567706645619456085104317 587889992107296031914119)
  ·
    refine ⟨881834988160944047871179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 587889992107296031914119 881834988160944047871179)
    ·
      refine ⟨1322752482241416071806769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881834988160944047871179 1322752482241416071806769)
      ·
        refine ⟨992064361681062053855077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322752482241416071806769 992064361681062053855077)
        ·
          refine ⟨186012067815199135097827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 992064361681062053855077 186012067815199135097827)
          ·
            refine ⟨279018101722798702646741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186012067815199135097827 279018101722798702646741)
            ·
              refine ⟨6539486759128094593283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 279018101722798702646741 6539486759128094593283)
              ·
                rfl

theorem cell19_64474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 7].length) (baseStart_64474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64474 prefixEnd_64474 := by exact prefixLift 64474
  have htrace : WordTrace (prefixWord ++ tailWord_64474) baseStart_64474 baseEnd_64474 := by
    simpa [prefixWord, tailWord_64474, baseEnd_64474] using wordTrace_append hprefix tailTrace_64474
  have hstable : (prefixWord ++ tailWord_64474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64474).length < 2 ^ (prefixWord ++ tailWord_64474).sum := by decide
  have hdescent : baseEnd_64474 < baseStart_64474 := by decide
  rcases family_descends (prefixWord ++ tailWord_64474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64544 : List Nat := [2, 1, 1, 7, 2, 1, 1, 4]
def baseStart_64544 : Nat := 118140960795 + 64544 * 2 ^ 59
def prefixEnd_64544 : Nat := 4983230072969 + 3 ^ 40 * 64544 * 2
def baseEnd_64544 : Nat := 19639760215644862224103

theorem tailTrace_64544 : CollatzResearch.WordTrace tailWord_64544 prefixEnd_64544 19639760215644862224103 := by
  unfold tailWord_64544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177056539087793041352343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1569408718783724055136457 1177056539087793041352343)
  ·
    refine ⟨1765584808631689562028515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1177056539087793041352343 1765584808631689562028515)
    ·
      refine ⟨2648377212947534343042773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1765584808631689562028515 2648377212947534343042773)
      ·
        refine ⟨62071340928457836165065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2648377212947534343042773 62071340928457836165065)
        ·
          refine ⟨46553505696343377123799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62071340928457836165065 46553505696343377123799)
          ·
            refine ⟨69830258544515065685699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46553505696343377123799 69830258544515065685699)
            ·
              refine ⟨104745387816772598528549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69830258544515065685699 104745387816772598528549)
              ·
                refine ⟨19639760215644862224103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104745387816772598528549 19639760215644862224103)
                ·
                  rfl

theorem cell19_64544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_64544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64544 prefixEnd_64544 := by exact prefixLift 64544
  have htrace : WordTrace (prefixWord ++ tailWord_64544) baseStart_64544 baseEnd_64544 := by
    simpa [prefixWord, tailWord_64544, baseEnd_64544] using wordTrace_append hprefix tailTrace_64544
  have hstable : (prefixWord ++ tailWord_64544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64544).length < 2 ^ (prefixWord ++ tailWord_64544).sum := by decide
  have hdescent : baseEnd_64544 < baseStart_64544 := by decide
  rcases family_descends (prefixWord ++ tailWord_64544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64548 : List Nat := [2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_64548 : Nat := 118140960795 + 64548 * 2 ^ 59
def prefixEnd_64548 : Nat := 4983230072969 + 3 ^ 40 * 64548 * 2
def baseEnd_64548 : Nat := 19640977354974038135203

theorem tailTrace_64548 : CollatzResearch.WordTrace tailWord_64548 prefixEnd_64548 19640977354974038135203 := by
  unfold tailWord_64548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177129485080547382925149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1569505980107396510566865 1177129485080547382925149)
  ·
    refine ⟨441423556905205268596931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1177129485080547382925149 441423556905205268596931)
    ·
      refine ⟨662135335357807902895397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441423556905205268596931 662135335357807902895397)
      ·
        refine ⟨124150375379588981792887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 662135335357807902895397 124150375379588981792887)
        ·
          refine ⟨186225563069383472689331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124150375379588981792887 186225563069383472689331)
          ·
            refine ⟨279338344604075209033997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186225563069383472689331 279338344604075209033997)
            ·
              refine ⟨104751879226528203387749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279338344604075209033997 104751879226528203387749)
              ·
                refine ⟨19640977354974038135203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104751879226528203387749 19640977354974038135203)
                ·
                  rfl

theorem cell19_64548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_64548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64548 prefixEnd_64548 := by exact prefixLift 64548
  have htrace : WordTrace (prefixWord ++ tailWord_64548) baseStart_64548 baseEnd_64548 := by
    simpa [prefixWord, tailWord_64548, baseEnd_64548] using wordTrace_append hprefix tailTrace_64548
  have hstable : (prefixWord ++ tailWord_64548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64548).length < 2 ^ (prefixWord ++ tailWord_64548).sum := by decide
  have hdescent : baseEnd_64548 < baseStart_64548 := by decide
  rcases family_descends (prefixWord ++ tailWord_64548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64622 : List Nat := [4, 1, 2, 2, 1, 4, 2, 3]
def baseStart_64622 : Nat := 118140960795 + 64622 * 2 ^ 59
def prefixEnd_64622 : Nat := 4983230072969 + 3 ^ 40 * 64622 * 2
def baseEnd_64622 : Nat := 19663494432563792490557

theorem tailTrace_64622 : CollatzResearch.WordTrace tailWord_64622 prefixEnd_64622 19663494432563792490557 := by
  unfold tailWord_64622
  simp only [CollatzResearch.WordTrace]
  refine ⟨294619746486625675505515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1571305314595336936029413 294619746486625675505515)
  ·
    refine ⟨441929619729938513258273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294619746486625675505515 441929619729938513258273)
    ·
      refine ⟨331447214797453884943705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441929619729938513258273 331447214797453884943705)
      ·
        refine ⟨248585411098090413707779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331447214797453884943705 248585411098090413707779)
        ·
          refine ⟨372878116647135620561669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248585411098090413707779 372878116647135620561669)
          ·
            refine ⟨69914646871337928855313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372878116647135620561669 69914646871337928855313)
            ·
              refine ⟨52435985153503446641485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69914646871337928855313 52435985153503446641485)
              ·
                refine ⟨19663494432563792490557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52435985153503446641485 19663494432563792490557)
                ·
                  rfl

theorem cell19_64622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_64622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64622 prefixEnd_64622 := by exact prefixLift 64622
  have htrace : WordTrace (prefixWord ++ tailWord_64622) baseStart_64622 baseEnd_64622 := by
    simpa [prefixWord, tailWord_64622, baseEnd_64622] using wordTrace_append hprefix tailTrace_64622
  have hstable : (prefixWord ++ tailWord_64622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64622).length < 2 ^ (prefixWord ++ tailWord_64622).sum := by decide
  have hdescent : baseEnd_64622 < baseStart_64622 := by decide
  rcases family_descends (prefixWord ++ tailWord_64622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64626 : List Nat := [3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_64626 : Nat := 118140960795 + 64626 * 2 ^ 59
def prefixEnd_64626 : Nat := 4983230072969 + 3 ^ 40 * 64626 * 2
def baseEnd_64626 : Nat := 19664711571892968401657

theorem tailTrace_64626 : CollatzResearch.WordTrace tailWord_64626 prefixEnd_64626 19664711571892968401657 := by
  unfold tailWord_64626
  simp only [CollatzResearch.WordTrace]
  refine ⟨589275965969628521797433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1571402575919009391459821 589275965969628521797433)
  ·
    refine ⟨441956974477221391348075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 589275965969628521797433 441956974477221391348075)
    ·
      refine ⟨662935461715832087022113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441956974477221391348075 662935461715832087022113)
      ·
        refine ⟨497201596286874065266585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662935461715832087022113 497201596286874065266585)
        ·
          refine ⟨372901197215155548949939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497201596286874065266585 372901197215155548949939)
          ·
            refine ⟨559351795822733323424909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372901197215155548949939 559351795822733323424909)
            ·
              refine ⟨209756923433524996284341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559351795822733323424909 209756923433524996284341)
              ·
                refine ⟨19664711571892968401657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209756923433524996284341 19664711571892968401657)
                ·
                  rfl

theorem cell19_64626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_64626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64626 prefixEnd_64626 := by exact prefixLift 64626
  have htrace : WordTrace (prefixWord ++ tailWord_64626) baseStart_64626 baseEnd_64626 := by
    simpa [prefixWord, tailWord_64626, baseEnd_64626] using wordTrace_append hprefix tailTrace_64626
  have hstable : (prefixWord ++ tailWord_64626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64626).length < 2 ^ (prefixWord ++ tailWord_64626).sum := by decide
  have hdescent : baseEnd_64626 < baseStart_64626 := by decide
  rcases family_descends (prefixWord ++ tailWord_64626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64664 : List Nat := [2, 1, 2, 4, 2, 1, 1, 6]
def baseStart_64664 : Nat := 118140960795 + 64664 * 2 ^ 59
def prefixEnd_64664 : Nat := 4983230072969 + 3 ^ 40 * 64664 * 2
def baseEnd_64664 : Nat := 19676274395520139557109

theorem tailTrace_64664 : CollatzResearch.WordTrace tailWord_64664 prefixEnd_64664 19676274395520139557109 := by
  unfold tailWord_64664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179244918870423288536523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1572326558493897718048697 1179244918870423288536523)
  ·
    refine ⟨1768867378305634932804785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179244918870423288536523 1768867378305634932804785)
    ·
      refine ⟨1326650533729226199603589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768867378305634932804785 1326650533729226199603589)
      ·
        refine ⟨248746975074229912425673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1326650533729226199603589 248746975074229912425673)
        ·
          refine ⟨186560231305672434319255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248746975074229912425673 186560231305672434319255)
          ·
            refine ⟨279840346958508651478883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186560231305672434319255 279840346958508651478883)
            ·
              refine ⟨419760520437762977218325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279840346958508651478883 419760520437762977218325)
              ·
                refine ⟨19676274395520139557109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 419760520437762977218325 19676274395520139557109)
                ·
                  rfl

theorem cell19_64664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_64664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64664 prefixEnd_64664 := by exact prefixLift 64664
  have htrace : WordTrace (prefixWord ++ tailWord_64664) baseStart_64664 baseEnd_64664 := by
    simpa [prefixWord, tailWord_64664, baseEnd_64664] using wordTrace_append hprefix tailTrace_64664
  have hstable : (prefixWord ++ tailWord_64664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64664).length < 2 ^ (prefixWord ++ tailWord_64664).sum := by decide
  have hdescent : baseEnd_64664 < baseStart_64664 := by decide
  rcases family_descends (prefixWord ++ tailWord_64664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64702 : List Nat := [4, 2, 1, 1, 3, 8]
def baseStart_64702 : Nat := 118140960795 + 64702 * 2 ^ 59
def prefixEnd_64702 : Nat := 4983230072969 + 3 ^ 40 * 64702 * 2
def baseEnd_64702 : Nat := 2187537468794145634729

theorem tailTrace_64702 : CollatzResearch.WordTrace tailWord_64702 prefixEnd_64702 2187537468794145634729 := by
  unfold tailWord_64702
  simp only [CollatzResearch.WordTrace]
  refine ⟨294984476450397383369545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1573250541068786044637573 294984476450397383369545)
  ·
    refine ⟨221238357337798037527159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294984476450397383369545 221238357337798037527159)
    ·
      refine ⟨331857536006697056290739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221238357337798037527159 331857536006697056290739)
      ·
        refine ⟨497786304010045584436109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331857536006697056290739 497786304010045584436109)
        ·
          refine ⟨186669864003767094163541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497786304010045584436109 186669864003767094163541)
          ·
            refine ⟨2187537468794145634729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 186669864003767094163541 2187537468794145634729)
            ·
              rfl

theorem cell19_64702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 8].length) (baseStart_64702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64702 prefixEnd_64702 := by exact prefixLift 64702
  have htrace : WordTrace (prefixWord ++ tailWord_64702) baseStart_64702 baseEnd_64702 := by
    simpa [prefixWord, tailWord_64702, baseEnd_64702] using wordTrace_append hprefix tailTrace_64702
  have hstable : (prefixWord ++ tailWord_64702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64702).length < 2 ^ (prefixWord ++ tailWord_64702).sum := by decide
  have hdescent : baseEnd_64702 < baseStart_64702 := by decide
  rcases family_descends (prefixWord ++ tailWord_64702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64704 : List Nat := [2, 1, 1, 2, 13]
def baseStart_64704 : Nat := 118140960795 + 64704 * 2 ^ 59
def prefixEnd_64704 : Nat := 4983230072969 + 3 ^ 40 * 64704 * 2
def baseEnd_64704 : Nat := 729201695881922172893

theorem tailTrace_64704 : CollatzResearch.WordTrace tailWord_64704 prefixEnd_64704 729201695881922172893 := by
  unfold tailWord_64704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1179974378797966704264583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1573299171730622272352777 1179974378797966704264583)
  ·
    refine ⟨1769961568196950056396875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1179974378797966704264583 1769961568196950056396875)
    ·
      refine ⟨2654942352295425084595313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1769961568196950056396875 2654942352295425084595313)
      ·
        refine ⟨1991206764221568813446485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2654942352295425084595313 1991206764221568813446485)
        ·
          refine ⟨729201695881922172893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1991206764221568813446485 729201695881922172893)
          ·
            rfl

theorem cell19_64704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 13].length) (baseStart_64704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64704 prefixEnd_64704 := by exact prefixLift 64704
  have htrace : WordTrace (prefixWord ++ tailWord_64704) baseStart_64704 baseEnd_64704 := by
    simpa [prefixWord, tailWord_64704, baseEnd_64704] using wordTrace_append hprefix tailTrace_64704
  have hstable : (prefixWord ++ tailWord_64704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64704).length < 2 ^ (prefixWord ++ tailWord_64704).sum := by decide
  have hdescent : baseEnd_64704 < baseStart_64704 := by decide
  rcases family_descends (prefixWord ++ tailWord_64704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64761 : List Nat := [1, 2, 1, 3, 1, 1, 10]
def baseStart_64761 : Nat := 118140960795 + 64761 * 2 ^ 59
def prefixEnd_64761 : Nat := 4983230072969 + 3 ^ 40 * 64761 * 2
def baseEnd_64761 : Nat := 6568596674750885133763

theorem tailTrace_64761 : CollatzResearch.WordTrace tailWord_64761 prefixEnd_64761 6568596674750885133763 := by
  unfold tailWord_64761
  simp only [CollatzResearch.WordTrace]
  refine ⟨2362027718389432143354137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1574685145592954762236091 2362027718389432143354137)
  ·
    refine ⟨1771520788792074107515603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2362027718389432143354137 1771520788792074107515603)
    ·
      refine ⟨2657281183188111161273405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771520788792074107515603 2657281183188111161273405)
      ·
        refine ⟨996480443695541685477527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2657281183188111161273405 996480443695541685477527)
        ·
          refine ⟨1494720665543312528216291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 996480443695541685477527 1494720665543312528216291)
          ·
            refine ⟨2242080998314968792324437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494720665543312528216291 2242080998314968792324437)
            ·
              refine ⟨6568596674750885133763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2242080998314968792324437 6568596674750885133763)
              ·
                rfl

theorem cell19_64761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_64761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64761 prefixEnd_64761 := by exact prefixLift 64761
  have htrace : WordTrace (prefixWord ++ tailWord_64761) baseStart_64761 baseEnd_64761 := by
    simpa [prefixWord, tailWord_64761, baseEnd_64761] using wordTrace_append hprefix tailTrace_64761
  have hstable : (prefixWord ++ tailWord_64761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64761).length < 2 ^ (prefixWord ++ tailWord_64761).sum := by decide
  have hdescent : baseEnd_64761 < baseStart_64761 := by decide
  rcases family_descends (prefixWord ++ tailWord_64761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64833 : List Nat := [1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_64833 : Nat := 118140960795 + 64833 * 2 ^ 59
def prefixEnd_64833 : Nat := 4983230072969 + 3 ^ 40 * 64833 * 2
def baseEnd_64833 : Nat := 19727698532177821801093

theorem tailTrace_64833 : CollatzResearch.WordTrace tailWord_64833 prefixEnd_64833 19727698532177821801093 := by
  unfold tailWord_64833
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364653774128588439975153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1576435849419058959983435 2364653774128588439975153)
  ·
    refine ⟨1773490330596441329981365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2364653774128588439975153 1773490330596441329981365)
    ·
      refine ⟨166264718493416374685753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1773490330596441329981365 166264718493416374685753)
      ·
        refine ⟨124698538870062281014315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166264718493416374685753 124698538870062281014315)
        ·
          refine ⟨187047808305093421521473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124698538870062281014315 187047808305093421521473)
          ·
            refine ⟨140285856228820066141105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187047808305093421521473 140285856228820066141105)
            ·
              refine ⟨105214392171615049605829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140285856228820066141105 105214392171615049605829)
              ·
                refine ⟨19727698532177821801093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105214392171615049605829 19727698532177821801093)
                ·
                  rfl

theorem cell19_64833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_64833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64833 prefixEnd_64833 := by exact prefixLift 64833
  have htrace : WordTrace (prefixWord ++ tailWord_64833) baseStart_64833 baseEnd_64833 := by
    simpa [prefixWord, tailWord_64833, baseEnd_64833] using wordTrace_append hprefix tailTrace_64833
  have hstable : (prefixWord ++ tailWord_64833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64833).length < 2 ^ (prefixWord ++ tailWord_64833).sum := by decide
  have hdescent : baseEnd_64833 < baseStart_64833 := by decide
  rcases family_descends (prefixWord ++ tailWord_64833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64856 : List Nat := [2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_64856 : Nat := 118140960795 + 64856 * 2 ^ 59
def prefixEnd_64856 : Nat := 4983230072969 + 3 ^ 40 * 64856 * 2
def baseEnd_64856 : Nat := 19734697083320583289919

theorem tailTrace_64856 : CollatzResearch.WordTrace tailWord_64856 prefixEnd_64856 19734697083320583289919 := by
  unfold tailWord_64856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182746326522631684031211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1576995102030175578708281 1182746326522631684031211)
  ·
    refine ⟨1774119489783947526046817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1182746326522631684031211 1774119489783947526046817)
    ·
      refine ⟨1330589617337960644535113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1774119489783947526046817 1330589617337960644535113)
      ·
        refine ⟨997942213003470483401335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1330589617337960644535113 997942213003470483401335)
        ·
          refine ⟨1496913319505205725102003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997942213003470483401335 1496913319505205725102003)
          ·
            refine ⟨2245369979257808587653005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496913319505205725102003 2245369979257808587653005)
            ·
              refine ⟨842013742221678220369877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2245369979257808587653005 842013742221678220369877)
              ·
                refine ⟨19734697083320583289919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 842013742221678220369877 19734697083320583289919)
                ·
                  rfl

theorem cell19_64856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_64856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64856 prefixEnd_64856 := by exact prefixLift 64856
  have htrace : WordTrace (prefixWord ++ tailWord_64856) baseStart_64856 baseEnd_64856 := by
    simpa [prefixWord, tailWord_64856, baseEnd_64856] using wordTrace_append hprefix tailTrace_64856
  have hstable : (prefixWord ++ tailWord_64856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64856).length < 2 ^ (prefixWord ++ tailWord_64856).sum := by decide
  have hdescent : baseEnd_64856 < baseStart_64856 := by decide
  rcases family_descends (prefixWord ++ tailWord_64856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64930 : List Nat := [3, 3, 1, 2, 1, 3, 6]
def baseStart_64930 : Nat := 118140960795 + 64930 * 2 ^ 59
def prefixEnd_64930 : Nat := 4983230072969 + 3 ^ 40 * 64930 * 2
def baseEnd_64930 : Nat := 6585738053636779215091

theorem tailTrace_64930 : CollatzResearch.WordTrace tailWord_64930 prefixEnd_64930 6585738053636779215091 := by
  unfold tailWord_64930
  simp only [CollatzResearch.WordTrace]
  refine ⟨592047913694293501564061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1578794436518116004170829 592047913694293501564061)
  ·
    refine ⟨222017967635360063086523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 592047913694293501564061 222017967635360063086523)
    ·
      refine ⟨333026951453040094629785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222017967635360063086523 333026951453040094629785)
      ·
        refine ⟨249770213589780070972339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333026951453040094629785 249770213589780070972339)
        ·
          refine ⟨374655320384670106458509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249770213589780070972339 374655320384670106458509)
          ·
            refine ⟨140495745144251289921941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374655320384670106458509 140495745144251289921941)
            ·
              refine ⟨6585738053636779215091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140495745144251289921941 6585738053636779215091)
              ·
                rfl

theorem cell19_64930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_64930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64930 prefixEnd_64930 := by exact prefixLift 64930
  have htrace : WordTrace (prefixWord ++ tailWord_64930) baseStart_64930 baseEnd_64930 := by
    simpa [prefixWord, tailWord_64930, baseEnd_64930] using wordTrace_append hprefix tailTrace_64930
  have hstable : (prefixWord ++ tailWord_64930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64930).length < 2 ^ (prefixWord ++ tailWord_64930).sum := by decide
  have hdescent : baseEnd_64930 < baseStart_64930 := by decide
  rcases family_descends (prefixWord ++ tailWord_64930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64951 : List Nat := [1, 1, 3, 1, 3, 2, 2, 6]
def baseStart_64951 : Nat := 118140960795 + 64951 * 2 ^ 59
def prefixEnd_64951 : Nat := 4983230072969 + 3 ^ 40 * 64951 * 2
def baseEnd_64951 : Nat := 19763604142388511178549

theorem tailTrace_64951 : CollatzResearch.WordTrace tailWord_64951 prefixEnd_64951 19763604142388511178549 := by
  unfold tailWord_64951
  simp only [CollatzResearch.WordTrace]
  refine ⟨2368957587701094592770707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1579305058467396395180471 2368957587701094592770707)
  ·
    refine ⟨3553436381551641889156061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2368957587701094592770707 3553436381551641889156061)
    ·
      refine ⟨1332538643081865708433523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3553436381551641889156061 1332538643081865708433523)
      ·
        refine ⟨1998807964622798562650285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332538643081865708433523 1998807964622798562650285)
        ·
          refine ⟨749552986733549460993857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1998807964622798562650285 749552986733549460993857)
          ·
            refine ⟨562164740050162095745393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 749552986733549460993857 562164740050162095745393)
            ·
              refine ⟨421623555037621571809045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562164740050162095745393 421623555037621571809045)
              ·
                refine ⟨19763604142388511178549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421623555037621571809045 19763604142388511178549)
                ·
                  rfl

theorem cell19_64951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_64951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64951 prefixEnd_64951 := by exact prefixLift 64951
  have htrace : WordTrace (prefixWord ++ tailWord_64951) baseStart_64951 baseEnd_64951 := by
    simpa [prefixWord, tailWord_64951, baseEnd_64951] using wordTrace_append hprefix tailTrace_64951
  have hstable : (prefixWord ++ tailWord_64951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64951).length < 2 ^ (prefixWord ++ tailWord_64951).sum := by decide
  have hdescent : baseEnd_64951 < baseStart_64951 := by decide
  rcases family_descends (prefixWord ++ tailWord_64951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_64964 : List Nat := [2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_64964 : Nat := 118140960795 + 64964 * 2 ^ 59
def prefixEnd_64964 : Nat := 4983230072969 + 3 ^ 40 * 64964 * 2
def baseEnd_64964 : Nat := 19767559845208332889625

theorem tailTrace_64964 : CollatzResearch.WordTrace tailWord_64964 prefixEnd_64964 19767559845208332889625 := by
  unfold tailWord_64964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184715868326998906496973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1579621157769331875329297 1184715868326998906496973)
  ·
    refine ⟨444268450622624589936365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1184715868326998906496973 444268450622624589936365)
    ·
      refine ⟨166600668983484221226137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 444268450622624589936365 166600668983484221226137)
      ·
        refine ⟨124950501737613165919603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166600668983484221226137 124950501737613165919603)
        ·
          refine ⟨187425752606419748879405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124950501737613165919603 187425752606419748879405)
          ·
            refine ⟨70284657227407405829777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187425752606419748879405 70284657227407405829777)
            ·
              refine ⟨52713492920555554372333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70284657227407405829777 52713492920555554372333)
              ·
                refine ⟨19767559845208332889625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52713492920555554372333 19767559845208332889625)
                ·
                  rfl

theorem cell19_64964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_64964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_64964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_64964 prefixEnd_64964 := by exact prefixLift 64964
  have htrace : WordTrace (prefixWord ++ tailWord_64964) baseStart_64964 baseEnd_64964 := by
    simpa [prefixWord, tailWord_64964, baseEnd_64964] using wordTrace_append hprefix tailTrace_64964
  have hstable : (prefixWord ++ tailWord_64964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_64964).length < 2 ^ (prefixWord ++ tailWord_64964).sum := by decide
  have hdescent : baseEnd_64964 < baseStart_64964 := by decide
  rcases family_descends (prefixWord ++ tailWord_64964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65006 : List Nat := [4, 1, 2, 1, 2, 1, 4, 4]
def baseStart_65006 : Nat := 118140960795 + 65006 * 2 ^ 59
def prefixEnd_65006 : Nat := 4983230072969 + 3 ^ 40 * 65006 * 2
def baseEnd_65006 : Nat := 19780339808164679956177

theorem tailTrace_65006 : CollatzResearch.WordTrace tailWord_65006 prefixEnd_65006 19780339808164679956177 := by
  unfold tailWord_65006
  simp only [CollatzResearch.WordTrace]
  refine ⟨296370450312729873252859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1580642401667892657348581 296370450312729873252859)
  ·
    refine ⟨444555675469094809879289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 296370450312729873252859 444555675469094809879289)
    ·
      refine ⟨333416756601821107409467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 444555675469094809879289 333416756601821107409467)
      ·
        refine ⟨500125134902731661114201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333416756601821107409467 500125134902731661114201)
        ·
          refine ⟨375093851177048745835651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 500125134902731661114201 375093851177048745835651)
          ·
            refine ⟨562640776765573118753477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375093851177048745835651 562640776765573118753477)
            ·
              refine ⟨105495145643544959766277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 562640776765573118753477 105495145643544959766277)
              ·
                refine ⟨19780339808164679956177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105495145643544959766277 19780339808164679956177)
                ·
                  rfl

theorem cell19_65006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_65006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65006 prefixEnd_65006 := by exact prefixLift 65006
  have htrace : WordTrace (prefixWord ++ tailWord_65006) baseStart_65006 baseEnd_65006 := by
    simpa [prefixWord, tailWord_65006, baseEnd_65006] using wordTrace_append hprefix tailTrace_65006
  have hstable : (prefixWord ++ tailWord_65006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65006).length < 2 ^ (prefixWord ++ tailWord_65006).sum := by decide
  have hdescent : baseEnd_65006 < baseStart_65006 := by decide
  rcases family_descends (prefixWord ++ tailWord_65006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65008 : List Nat := [2, 1, 1, 1, 3, 4, 1, 6]
def baseStart_65008 : Nat := 118140960795 + 65008 * 2 ^ 59
def prefixEnd_65008 : Nat := 4983230072969 + 3 ^ 40 * 65008 * 2
def baseEnd_65008 : Nat := 19780948377829267911727

theorem tailTrace_65008 : CollatzResearch.WordTrace tailWord_65008 prefixEnd_65008 19780948377829267911727 := by
  unfold tailWord_65008
  simp only [CollatzResearch.WordTrace]
  refine ⟨1185518274247296663797839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1580691032329728885063785 1185518274247296663797839)
  ·
    refine ⟨1778277411370944995696759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1185518274247296663797839 1778277411370944995696759)
    ·
      refine ⟨2667416117056417493545139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1778277411370944995696759 2667416117056417493545139)
      ·
        refine ⟨4001124175584626240317709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2667416117056417493545139 4001124175584626240317709)
        ·
          refine ⟨1500421565844234840119141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4001124175584626240317709 1500421565844234840119141)
          ·
            refine ⟨281329043595794032522339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1500421565844234840119141 281329043595794032522339)
            ·
              refine ⟨421993565393691048783509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281329043595794032522339 421993565393691048783509)
              ·
                refine ⟨19780948377829267911727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 421993565393691048783509 19780948377829267911727)
                ·
                  rfl

theorem cell19_65008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_65008 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65008 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65008 prefixEnd_65008 := by exact prefixLift 65008
  have htrace : WordTrace (prefixWord ++ tailWord_65008) baseStart_65008 baseEnd_65008 := by
    simpa [prefixWord, tailWord_65008, baseEnd_65008] using wordTrace_append hprefix tailTrace_65008
  have hstable : (prefixWord ++ tailWord_65008).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65008).length < 2 ^ (prefixWord ++ tailWord_65008).sum := by decide
  have hdescent : baseEnd_65008 < baseStart_65008 := by decide
  rcases family_descends (prefixWord ++ tailWord_65008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65044 : List Nat := [2, 4, 3, 1, 9]
def baseStart_65044 : Nat := 118140960795 + 65044 * 2 ^ 59
def prefixEnd_65044 : Nat := 4983230072969 + 3 ^ 40 * 65044 * 2
def baseEnd_65044 : Nat := 733033430807105596727

theorem tailTrace_65044 : CollatzResearch.WordTrace tailWord_65044 prefixEnd_65044 733033430807105596727 := by
  unfold tailWord_65044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1186174788182085737953093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1581566384242780983937457 1186174788182085737953093)
  ·
    refine ⟨222407772784141075866205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1186174788182085737953093 222407772784141075866205)
    ·
      refine ⟨83402914794052903449827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222407772784141075866205 83402914794052903449827)
      ·
        refine ⟨125104372191079355174741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83402914794052903449827 125104372191079355174741)
        ·
          refine ⟨733033430807105596727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 125104372191079355174741 733033430807105596727)
          ·
            rfl

theorem cell19_65044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 9].length) (baseStart_65044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65044 prefixEnd_65044 := by exact prefixLift 65044
  have htrace : WordTrace (prefixWord ++ tailWord_65044) baseStart_65044 baseEnd_65044 := by
    simpa [prefixWord, tailWord_65044, baseEnd_65044] using wordTrace_append hprefix tailTrace_65044
  have hstable : (prefixWord ++ tailWord_65044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65044).length < 2 ^ (prefixWord ++ tailWord_65044).sum := by decide
  have hdescent : baseEnd_65044 < baseStart_65044 := by decide
  rcases family_descends (prefixWord ++ tailWord_65044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65078 : List Nat := [5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_65078 : Nat := 118140960795 + 65078 * 2 ^ 59
def prefixEnd_65078 : Nat := 4983230072969 + 3 ^ 40 * 65078 * 2
def baseEnd_65078 : Nat := 19802248316089846355981

theorem tailTrace_65078 : CollatzResearch.WordTrace tailWord_65078 prefixEnd_65078 19802248316089846355981 := by
  unfold tailWord_65078
  simp only [CollatzResearch.WordTrace]
  refine ⟨148349353640062205165243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1582393105493996855095925 148349353640062205165243)
  ·
    refine ⟨222524030460093307747865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148349353640062205165243 222524030460093307747865)
    ·
      refine ⟨166893022845069980810899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222524030460093307747865 166893022845069980810899)
      ·
        refine ⟨250339534267604971216349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166893022845069980810899 250339534267604971216349)
        ·
          refine ⟨93877325350351864206131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250339534267604971216349 93877325350351864206131)
          ·
            refine ⟨140815988025527796309197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93877325350351864206131 140815988025527796309197)
            ·
              refine ⟨52805995509572923615949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140815988025527796309197 52805995509572923615949)
              ·
                refine ⟨19802248316089846355981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52805995509572923615949 19802248316089846355981)
                ·
                  rfl

theorem cell19_65078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_65078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65078 prefixEnd_65078 := by exact prefixLift 65078
  have htrace : WordTrace (prefixWord ++ tailWord_65078) baseStart_65078 baseEnd_65078 := by
    simpa [prefixWord, tailWord_65078, baseEnd_65078] using wordTrace_append hprefix tailTrace_65078
  have hstable : (prefixWord ++ tailWord_65078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65078).length < 2 ^ (prefixWord ++ tailWord_65078).sum := by decide
  have hdescent : baseEnd_65078 < baseStart_65078 := by decide
  rcases family_descends (prefixWord ++ tailWord_65078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65082 : List Nat := [3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_65082 : Nat := 118140960795 + 65082 * 2 ^ 59
def prefixEnd_65082 : Nat := 4983230072969 + 3 ^ 40 * 65082 * 2
def baseEnd_65082 : Nat := 19803465455419022267081

theorem tailTrace_65082 : CollatzResearch.WordTrace tailWord_65082 prefixEnd_65082 19803465455419022267081 := by
  unfold tailWord_65082
  simp only [CollatzResearch.WordTrace]
  refine ⟨593433887556625991447375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1582490366817669310526333 593433887556625991447375)
  ·
    refine ⟨890150831334938987171063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 593433887556625991447375 890150831334938987171063)
    ·
      refine ⟨1335226247002408480756595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 890150831334938987171063 1335226247002408480756595)
      ·
        refine ⟨2002839370503612721134893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1335226247002408480756595 2002839370503612721134893)
        ·
          refine ⟨751064763938854770425585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2002839370503612721134893 751064763938854770425585)
          ·
            refine ⟨563298572954141077819189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 751064763938854770425585 563298572954141077819189)
            ·
              refine ⟨52809241214450726045549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 563298572954141077819189 52809241214450726045549)
              ·
                refine ⟨19803465455419022267081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52809241214450726045549 19803465455419022267081)
                ·
                  rfl

theorem cell19_65082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_65082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65082 prefixEnd_65082 := by exact prefixLift 65082
  have htrace : WordTrace (prefixWord ++ tailWord_65082) baseStart_65082 baseEnd_65082 := by
    simpa [prefixWord, tailWord_65082, baseEnd_65082] using wordTrace_append hprefix tailTrace_65082
  have hstable : (prefixWord ++ tailWord_65082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65082).length < 2 ^ (prefixWord ++ tailWord_65082).sum := by decide
  have hdescent : baseEnd_65082 < baseStart_65082 := by decide
  rcases family_descends (prefixWord ++ tailWord_65082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65156 : List Nat := [2, 3, 2, 1, 5, 1, 5]
def baseStart_65156 : Nat := 118140960795 + 65156 * 2 ^ 59
def prefixEnd_65156 : Nat := 4983230072969 + 3 ^ 40 * 65156 * 2
def baseEnd_65156 : Nat := 6608660844336258874145

theorem tailTrace_65156 : CollatzResearch.WordTrace tailWord_65156 prefixEnd_65156 6608660844336258874145 := by
  unfold tailWord_65156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1188217275979207301991661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1584289701305609735988881 1188217275979207301991661)
  ·
    refine ⟨445581478492202738246873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1188217275979207301991661 445581478492202738246873)
    ·
      refine ⟨334186108869152053685155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 445581478492202738246873 334186108869152053685155)
      ·
        refine ⟨501279163303728080527733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334186108869152053685155 501279163303728080527733)
        ·
          refine ⟨46994921559724507549475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 501279163303728080527733 46994921559724507549475)
          ·
            refine ⟨70492382339586761324213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46994921559724507549475 70492382339586761324213)
            ·
              refine ⟨6608660844336258874145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70492382339586761324213 6608660844336258874145)
              ·
                rfl

theorem cell19_65156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_65156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65156 prefixEnd_65156 := by exact prefixLift 65156
  have htrace : WordTrace (prefixWord ++ tailWord_65156) baseStart_65156 baseEnd_65156 := by
    simpa [prefixWord, tailWord_65156, baseEnd_65156] using wordTrace_append hprefix tailTrace_65156
  have hstable : (prefixWord ++ tailWord_65156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65156).length < 2 ^ (prefixWord ++ tailWord_65156).sum := by decide
  have hdescent : baseEnd_65156 < baseStart_65156 := by decide
  rcases family_descends (prefixWord ++ tailWord_65156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65217 : List Nat := [1, 2, 6, 10]
def baseStart_65217 : Nat := 118140960795 + 65217 * 2 ^ 59
def prefixEnd_65217 : Nat := 4983230072969 + 3 ^ 40 * 65217 * 2
def baseEnd_65217 : Nat := 244994369231835916873

theorem tailTrace_65217 : CollatzResearch.WordTrace tailWord_65217 prefixEnd_65217 244994369231835916873 := by
  unfold tailWord_65217
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378659404737422021953905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1585772936491614681302603 2378659404737422021953905)
  ·
    refine ⟨1783994553553066516465429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2378659404737422021953905 1783994553553066516465429)
    ·
      refine ⟨83624744697799992959317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1783994553553066516465429 83624744697799992959317)
      ·
        refine ⟨244994369231835916873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 83624744697799992959317 244994369231835916873)
        ·
          rfl

theorem cell19_65217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 10].length) (baseStart_65217 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65217 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65217 prefixEnd_65217 := by exact prefixLift 65217
  have htrace : WordTrace (prefixWord ++ tailWord_65217) baseStart_65217 baseEnd_65217 := by
    simpa [prefixWord, tailWord_65217, baseEnd_65217] using wordTrace_append hprefix tailTrace_65217
  have hstable : (prefixWord ++ tailWord_65217).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65217).length < 2 ^ (prefixWord ++ tailWord_65217).sum := by decide
  have hdescent : baseEnd_65217 < baseStart_65217 := by decide
  rcases family_descends (prefixWord ++ tailWord_65217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65234 : List Nat := [3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_65234 : Nat := 118140960795 + 65234 * 2 ^ 59
def prefixEnd_65234 : Nat := 4983230072969 + 3 ^ 40 * 65234 * 2
def baseEnd_65234 : Nat := 19849716749927706888889

theorem tailTrace_65234 : CollatzResearch.WordTrace tailWord_65234 prefixEnd_65234 19849716749927706888889 := by
  unfold tailWord_65234
  simp only [CollatzResearch.WordTrace]
  refine ⟨594819861418958481330689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1586186297117222616881837 594819861418958481330689)
  ·
    refine ⟨446114896064218860998017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 594819861418958481330689 446114896064218860998017)
    ·
      refine ⟨334586172048164145748513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446114896064218860998017 334586172048164145748513)
      ·
        refine ⟨250939629036123109311385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334586172048164145748513 250939629036123109311385)
        ·
          refine ⟨188204721777092331983539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250939629036123109311385 188204721777092331983539)
          ·
            refine ⟨282307082665638497975309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188204721777092331983539 282307082665638497975309)
            ·
              refine ⟨105865155999614436740741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282307082665638497975309 105865155999614436740741)
              ·
                refine ⟨19849716749927706888889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105865155999614436740741 19849716749927706888889)
                ·
                  rfl

theorem cell19_65234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_65234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65234 prefixEnd_65234 := by exact prefixLift 65234
  have htrace : WordTrace (prefixWord ++ tailWord_65234) baseStart_65234 baseEnd_65234 := by
    simpa [prefixWord, tailWord_65234, baseEnd_65234] using wordTrace_append hprefix tailTrace_65234
  have hstable : (prefixWord ++ tailWord_65234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65234).length < 2 ^ (prefixWord ++ tailWord_65234).sum := by decide
  have hdescent : baseEnd_65234 < baseStart_65234 := by decide
  rcases family_descends (prefixWord ++ tailWord_65234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65251 : List Nat := [1, 1, 1, 7, 2, 1, 3, 3]
def baseStart_65251 : Nat := 118140960795 + 65251 * 2 ^ 59
def prefixEnd_65251 : Nat := 4983230072969 + 3 ^ 40 * 65251 * 2
def baseEnd_65251 : Nat := 19854889592076704511065

theorem tailTrace_65251 : CollatzResearch.WordTrace tailWord_65251 prefixEnd_65251 19854889592076704511065 := by
  unfold tailWord_65251
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379899486614245828691607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1586599657742830552461071 2379899486614245828691607)
  ·
    refine ⟨3569849229921368743037411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379899486614245828691607 3569849229921368743037411)
    ·
      refine ⟨5354773844882053114556117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569849229921368743037411 5354773844882053114556117)
      ·
        refine ⟨125502511989423119872409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5354773844882053114556117 125502511989423119872409)
        ·
          refine ⟨94126883992067339904307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125502511989423119872409 94126883992067339904307)
          ·
            refine ⟨141190325988101009856461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94126883992067339904307 141190325988101009856461)
            ·
              refine ⟨52946372245537878696173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141190325988101009856461 52946372245537878696173)
              ·
                refine ⟨19854889592076704511065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52946372245537878696173 19854889592076704511065)
                ·
                  rfl

theorem cell19_65251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 3].length) (baseStart_65251 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65251 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65251 prefixEnd_65251 := by exact prefixLift 65251
  have htrace : WordTrace (prefixWord ++ tailWord_65251) baseStart_65251 baseEnd_65251 := by
    simpa [prefixWord, tailWord_65251, baseEnd_65251] using wordTrace_append hprefix tailTrace_65251
  have hstable : (prefixWord ++ tailWord_65251).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65251).length < 2 ^ (prefixWord ++ tailWord_65251).sum := by decide
  have hdescent : baseEnd_65251 < baseStart_65251 := by decide
  rcases family_descends (prefixWord ++ tailWord_65251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65253 : List Nat := [1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_65253 : Nat := 118140960795 + 65253 * 2 ^ 59
def prefixEnd_65253 : Nat := 4983230072969 + 3 ^ 40 * 65253 * 2
def baseEnd_65253 : Nat := 19855498161741292466615

theorem tailTrace_65253 : CollatzResearch.WordTrace tailWord_65253 prefixEnd_65253 19855498161741292466615 := by
  unfold tailWord_65253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379972432607000170264413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1586648288404666780176275 2379972432607000170264413)
  ·
    refine ⟨892489662227625063849155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2379972432607000170264413 892489662227625063849155)
    ·
      refine ⟨1338734493341437595773733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892489662227625063849155 1338734493341437595773733)
      ·
        refine ⟨251012717501519549207575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1338734493341437595773733 251012717501519549207575)
        ·
          refine ⟨376519076252279323811363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251012717501519549207575 376519076252279323811363)
          ·
            refine ⟨564778614378418985717045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376519076252279323811363 564778614378418985717045)
            ·
              refine ⟨52947995097976779910973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 564778614378418985717045 52947995097976779910973)
              ·
                refine ⟨19855498161741292466615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52947995097976779910973 19855498161741292466615)
                ·
                  rfl

theorem cell19_65253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_65253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65253 prefixEnd_65253 := by exact prefixLift 65253
  have htrace : WordTrace (prefixWord ++ tailWord_65253) baseStart_65253 baseEnd_65253 := by
    simpa [prefixWord, tailWord_65253, baseEnd_65253] using wordTrace_append hprefix tailTrace_65253
  have hstable : (prefixWord ++ tailWord_65253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65253).length < 2 ^ (prefixWord ++ tailWord_65253).sum := by decide
  have hdescent : baseEnd_65253 < baseStart_65253 := by decide
  rcases family_descends (prefixWord ++ tailWord_65253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65312 : List Nat := [2, 1, 1, 5, 1, 1, 3, 5]
def baseStart_65312 : Nat := 118140960795 + 65312 * 2 ^ 59
def prefixEnd_65312 : Nat := 4983230072969 + 3 ^ 40 * 65312 * 2
def baseEnd_65312 : Nat := 19873450966846637155343

theorem tailTrace_65312 : CollatzResearch.WordTrace tailWord_65312 prefixEnd_65312 19873450966846637155343 := by
  unfold tailWord_65312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1191062169696626623331095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1588082892928835497774793 1191062169696626623331095)
  ·
    refine ⟨1786593254544939934996643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1191062169696626623331095 1786593254544939934996643)
    ·
      refine ⟨2679889881817409902494965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786593254544939934996643 2679889881817409902494965)
      ·
        refine ⟨251239676420382178358903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2679889881817409902494965 251239676420382178358903)
        ·
          refine ⟨376859514630573267538355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251239676420382178358903 376859514630573267538355)
          ·
            refine ⟨565289271945859901307533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376859514630573267538355 565289271945859901307533)
            ·
              refine ⟨211983476979697462990325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565289271945859901307533 211983476979697462990325)
              ·
                refine ⟨19873450966846637155343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211983476979697462990325 19873450966846637155343)
                ·
                  rfl

theorem cell19_65312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_65312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65312 prefixEnd_65312 := by exact prefixLift 65312
  have htrace : WordTrace (prefixWord ++ tailWord_65312) baseStart_65312 baseEnd_65312 := by
    simpa [prefixWord, tailWord_65312, baseEnd_65312] using wordTrace_append hprefix tailTrace_65312
  have hstable : (prefixWord ++ tailWord_65312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65312).length < 2 ^ (prefixWord ++ tailWord_65312).sum := by decide
  have hdescent : baseEnd_65312 < baseStart_65312 := by decide
  rcases family_descends (prefixWord ++ tailWord_65312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65386 : List Nat := [3, 1, 3, 4, 1, 7]
def baseStart_65386 : Nat := 118140960795 + 65386 * 2 ^ 59
def prefixEnd_65386 : Nat := 4983230072969 + 3 ^ 40 * 65386 * 2
def baseEnd_65386 : Nat := 2210663116048487945633

theorem tailTrace_65386 : CollatzResearch.WordTrace tailWord_65386 prefixEnd_65386 2210663116048487945633 := by
  unfold tailWord_65386
  simp only [CollatzResearch.WordTrace]
  refine ⟨596205835281290971214003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1589882227416775923237341 596205835281290971214003)
  ·
    refine ⟨894308752921936456821005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596205835281290971214003 894308752921936456821005)
    ·
      refine ⟨335365782345726171307877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 894308752921936456821005 335365782345726171307877)
      ·
        refine ⟨62881084189823657120227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335365782345726171307877 62881084189823657120227)
        ·
          refine ⟨94321626284735485680341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62881084189823657120227 94321626284735485680341)
          ·
            refine ⟨2210663116048487945633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 94321626284735485680341 2210663116048487945633)
            ·
              rfl

theorem cell19_65386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 7].length) (baseStart_65386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65386 prefixEnd_65386 := by exact prefixLift 65386
  have htrace : WordTrace (prefixWord ++ tailWord_65386) baseStart_65386 baseEnd_65386 := by
    simpa [prefixWord, tailWord_65386, baseEnd_65386] using wordTrace_append hprefix tailTrace_65386
  have hstable : (prefixWord ++ tailWord_65386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65386).length < 2 ^ (prefixWord ++ tailWord_65386).sum := by decide
  have hdescent : baseEnd_65386 < baseStart_65386 := by decide
  rcases family_descends (prefixWord ++ tailWord_65386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65517 : List Nat := [1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_65517 : Nat := 118140960795 + 65517 * 2 ^ 59
def prefixEnd_65517 : Nat := 4983230072969 + 3 ^ 40 * 65517 * 2
def baseEnd_65517 : Nat := 19935829357466902599229

theorem tailTrace_65517 : CollatzResearch.WordTrace tailWord_65517 prefixEnd_65517 19935829357466902599229 := by
  unfold tailWord_65517
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389601303650573257874805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1593067535767048838583203 2389601303650573257874805)
  ·
    refine ⟨224025122217241242925763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2389601303650573257874805 224025122217241242925763)
    ·
      refine ⟨336037683325861864388645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224025122217241242925763 336037683325861864388645)
      ·
        refine ⟨63007065623599099572871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 336037683325861864388645 63007065623599099572871)
        ·
          refine ⟨94510598435398649359307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63007065623599099572871 94510598435398649359307)
          ·
            refine ⟨141765897653097974038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94510598435398649359307 141765897653097974038961)
            ·
              refine ⟨106324423239823480529221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141765897653097974038961 106324423239823480529221)
              ·
                refine ⟨19935829357466902599229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106324423239823480529221 19935829357466902599229)
                ·
                  rfl

theorem cell19_65517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_65517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65517 prefixEnd_65517 := by exact prefixLift 65517
  have htrace : WordTrace (prefixWord ++ tailWord_65517) baseStart_65517 baseEnd_65517 := by
    simpa [prefixWord, tailWord_65517, baseEnd_65517] using wordTrace_append hprefix tailTrace_65517
  have hstable : (prefixWord ++ tailWord_65517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65517).length < 2 ^ (prefixWord ++ tailWord_65517).sum := by decide
  have hdescent : baseEnd_65517 < baseStart_65517 := by decide
  rcases family_descends (prefixWord ++ tailWord_65517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65559 : List Nat := [1, 1, 3, 5, 2, 7]
def baseStart_65559 : Nat := 118140960795 + 65559 * 2 ^ 59
def prefixEnd_65559 : Nat := 4983230072969 + 3 ^ 40 * 65559 * 2
def baseEnd_65559 : Nat := 2216512146713694407309

theorem tailTrace_65559 : CollatzResearch.WordTrace tailWord_65559 prefixEnd_65559 2216512146713694407309 := by
  unfold tailWord_65559
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391133169498414430903731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1594088779665609620602487 2391133169498414430903731)
  ·
    refine ⟨3586699754247621646355597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2391133169498414430903731 3586699754247621646355597)
    ·
      refine ⟨1345012407842858117383349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3586699754247621646355597 1345012407842858117383349)
      ·
        refine ⟨126094913235267948504689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1345012407842858117383349 126094913235267948504689)
        ·
          refine ⟨94571184926450961378517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126094913235267948504689 94571184926450961378517)
          ·
            refine ⟨2216512146713694407309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 94571184926450961378517 2216512146713694407309)
            ·
              rfl

theorem cell19_65559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_65559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65559 prefixEnd_65559 := by exact prefixLift 65559
  have htrace : WordTrace (prefixWord ++ tailWord_65559) baseStart_65559 baseEnd_65559 := by
    simpa [prefixWord, tailWord_65559, baseEnd_65559] using wordTrace_append hprefix tailTrace_65559
  have hstable : (prefixWord ++ tailWord_65559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65559).length < 2 ^ (prefixWord ++ tailWord_65559).sum := by decide
  have hdescent : baseEnd_65559 < baseStart_65559 := by decide
  rcases family_descends (prefixWord ++ tailWord_65559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65580 : List Nat := [2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_65580 : Nat := 118140960795 + 65580 * 2 ^ 59
def prefixEnd_65580 : Nat := 4983230072969 + 3 ^ 40 * 65580 * 2
def baseEnd_65580 : Nat := 19954999301901423199057

theorem tailTrace_65580 : CollatzResearch.WordTrace tailWord_65580 prefixEnd_65580 19954999301901423199057 := by
  unfold tailWord_65580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195949551211167508709097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1594599401614890011612129 1195949551211167508709097)
  ·
    refine ⟨896962163408375631531823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1195949551211167508709097 896962163408375631531823)
    ·
      refine ⟨1345443245112563447297735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896962163408375631531823 1345443245112563447297735)
      ·
        refine ⟨2018164867668845170946603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345443245112563447297735 2018164867668845170946603)
        ·
          refine ⟨3027247301503267756419905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2018164867668845170946603 3027247301503267756419905)
          ·
            refine ⟨2270435476127450817314929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3027247301503267756419905 2270435476127450817314929)
            ·
              refine ⟨1702826607095588112986197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270435476127450817314929 1702826607095588112986197)
              ·
                refine ⟨19954999301901423199057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1702826607095588112986197 19954999301901423199057)
                ·
                  rfl

theorem cell19_65580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_65580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65580 prefixEnd_65580 := by exact prefixLift 65580
  have htrace : WordTrace (prefixWord ++ tailWord_65580) baseStart_65580 baseEnd_65580 := by
    simpa [prefixWord, tailWord_65580, baseEnd_65580] using wordTrace_append hprefix tailTrace_65580
  have hstable : (prefixWord ++ tailWord_65580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65580).length < 2 ^ (prefixWord ++ tailWord_65580).sum := by decide
  have hdescent : baseEnd_65580 < baseStart_65580 := by decide
  rcases family_descends (prefixWord ++ tailWord_65580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65599 : List Nat := [1, 1, 2, 2, 3, 1, 2, 7]
def baseStart_65599 : Nat := 118140960795 + 65599 * 2 ^ 59
def prefixEnd_65599 : Nat := 4983230072969 + 3 ^ 40 * 65599 * 2
def baseEnd_65599 : Nat := 19960780713715008776783

theorem tailTrace_65599 : CollatzResearch.WordTrace tailWord_65599 prefixEnd_65599 19960780713715008776783 := by
  unfold tailWord_65599
  simp only [CollatzResearch.WordTrace]
  refine ⟨2392592089353501262359851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1595061392902334174906567 2392592089353501262359851)
  ·
    refine ⟨3588888134030251893539777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2392592089353501262359851 3588888134030251893539777)
    ·
      refine ⟨2691666100522688920154833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3588888134030251893539777 2691666100522688920154833)
      ·
        refine ⟨2018749575392016690116125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2691666100522688920154833 2018749575392016690116125)
        ·
          refine ⟨757031090772006258793547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2018749575392016690116125 757031090772006258793547)
          ·
            refine ⟨1135546636158009388190321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757031090772006258793547 1135546636158009388190321)
            ·
              refine ⟨851659977118507041142741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135546636158009388190321 851659977118507041142741)
              ·
                refine ⟨19960780713715008776783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 851659977118507041142741 19960780713715008776783)
                ·
                  rfl

theorem cell19_65599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 7].length) (baseStart_65599 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65599 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65599 prefixEnd_65599 := by exact prefixLift 65599
  have htrace : WordTrace (prefixWord ++ tailWord_65599) baseStart_65599 baseEnd_65599 := by
    simpa [prefixWord, tailWord_65599, baseEnd_65599] using wordTrace_append hprefix tailTrace_65599
  have hstable : (prefixWord ++ tailWord_65599).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65599).length < 2 ^ (prefixWord ++ tailWord_65599).sum := by decide
  have hdescent : baseEnd_65599 < baseStart_65599 := by decide
  rcases family_descends (prefixWord ++ tailWord_65599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65690 : List Nat := [3, 1, 1, 5, 2, 1, 2, 4]
def baseStart_65690 : Nat := 118140960795 + 65690 * 2 ^ 59
def prefixEnd_65690 : Nat := 4983230072969 + 3 ^ 40 * 65690 * 2
def baseEnd_65690 : Nat := 19988470633453760754313

theorem tailTrace_65690 : CollatzResearch.WordTrace tailWord_65690 prefixEnd_65690 19988470633453760754313 := by
  unfold tailWord_65690
  simp only [CollatzResearch.WordTrace]
  refine ⟨598977783005955950980631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1597274088015882535948349 598977783005955950980631)
  ·
    refine ⟨898466674508933926470947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 598977783005955950980631 898466674508933926470947)
    ·
      refine ⟨1347700011763400889706421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 898466674508933926470947 1347700011763400889706421)
      ·
        refine ⟨126346876102818833409977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1347700011763400889706421 126346876102818833409977)
        ·
          refine ⟨94760157077114125057483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126346876102818833409977 94760157077114125057483)
          ·
            refine ⟨142140235615671187586225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94760157077114125057483 142140235615671187586225)
            ·
              refine ⟨106605176711753390689669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142140235615671187586225 106605176711753390689669)
              ·
                refine ⟨19988470633453760754313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106605176711753390689669 19988470633453760754313)
                ·
                  rfl

theorem cell19_65690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_65690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65690 prefixEnd_65690 := by exact prefixLift 65690
  have htrace : WordTrace (prefixWord ++ tailWord_65690) baseStart_65690 baseEnd_65690 := by
    simpa [prefixWord, tailWord_65690, baseEnd_65690] using wordTrace_append hprefix tailTrace_65690
  have hstable : (prefixWord ++ tailWord_65690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65690).length < 2 ^ (prefixWord ++ tailWord_65690).sum := by decide
  have hdescent : baseEnd_65690 < baseStart_65690 := by decide
  rcases family_descends (prefixWord ++ tailWord_65690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65692 : List Nat := [2, 2, 3, 2, 1, 1, 4, 4]
def baseStart_65692 : Nat := 118140960795 + 65692 * 2 ^ 59
def prefixEnd_65692 : Nat := 4983230072969 + 3 ^ 40 * 65692 * 2
def baseEnd_65692 : Nat := 19989079203118348709863

theorem tailTrace_65692 : CollatzResearch.WordTrace tailWord_65692 prefixEnd_65692 19989079203118348709863 := by
  unfold tailWord_65692
  simp only [CollatzResearch.WordTrace]
  refine ⟨1197992039008289072747665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1597322718677718763663553 1197992039008289072747665)
  ·
    refine ⟨898494029256216804560749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1197992039008289072747665 898494029256216804560749)
    ·
      refine ⟨336935260971081301710281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 898494029256216804560749 336935260971081301710281)
      ·
        refine ⟨252701445728310976282711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336935260971081301710281 252701445728310976282711)
        ·
          refine ⟨379052168592466464424067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252701445728310976282711 379052168592466464424067)
          ·
            refine ⟨568578252888699696636101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379052168592466464424067 568578252888699696636101)
            ·
              refine ⟨106608422416631193119269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 568578252888699696636101 106608422416631193119269)
              ·
                refine ⟨19989079203118348709863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106608422416631193119269 19989079203118348709863)
                ·
                  rfl

theorem cell19_65692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_65692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65692 prefixEnd_65692 := by exact prefixLift 65692
  have htrace : WordTrace (prefixWord ++ tailWord_65692) baseStart_65692 baseEnd_65692 := by
    simpa [prefixWord, tailWord_65692, baseEnd_65692] using wordTrace_append hprefix tailTrace_65692
  have hstable : (prefixWord ++ tailWord_65692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65692).length < 2 ^ (prefixWord ++ tailWord_65692).sum := by decide
  have hdescent : baseEnd_65692 < baseStart_65692 := by decide
  rcases family_descends (prefixWord ++ tailWord_65692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65821 : List Nat := [1, 4, 2, 3, 2, 2, 2, 3]
def baseStart_65821 : Nat := 118140960795 + 65821 * 2 ^ 59
def prefixEnd_65821 : Nat := 4983230072969 + 3 ^ 40 * 65821 * 2
def baseEnd_65821 : Nat := 20028331946484271842845

theorem tailTrace_65821 : CollatzResearch.WordTrace tailWord_65821 prefixEnd_65821 20028331946484271842845 := by
  unfold tailWord_65821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400689094549233176941317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1600459396366155451294211 2400689094549233176941317)
  ·
    refine ⟨450129205227981220676497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2400689094549233176941317 450129205227981220676497)
    ·
      refine ⟨337596903920985915507373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 450129205227981220676497 337596903920985915507373)
      ·
        refine ⟨126598838970369718315265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 337596903920985915507373 126598838970369718315265)
        ·
          refine ⟨94949129227777288736449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126598838970369718315265 94949129227777288736449)
          ·
            refine ⟨71211846920832966552337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94949129227777288736449 71211846920832966552337)
            ·
              refine ⟨53408885190624724914253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71211846920832966552337 53408885190624724914253)
              ·
                refine ⟨20028331946484271842845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53408885190624724914253 20028331946484271842845)
                ·
                  rfl

theorem cell19_65821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 3].length) (baseStart_65821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65821 prefixEnd_65821 := by exact prefixLift 65821
  have htrace : WordTrace (prefixWord ++ tailWord_65821) baseStart_65821 baseEnd_65821 := by
    simpa [prefixWord, tailWord_65821, baseEnd_65821] using wordTrace_append hprefix tailTrace_65821
  have hstable : (prefixWord ++ tailWord_65821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65821).length < 2 ^ (prefixWord ++ tailWord_65821).sum := by decide
  have hdescent : baseEnd_65821 < baseStart_65821 := by decide
  rcases family_descends (prefixWord ++ tailWord_65821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65823 : List Nat := [1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_65823 : Nat := 118140960795 + 65823 * 2 ^ 59
def prefixEnd_65823 : Nat := 4983230072969 + 3 ^ 40 * 65823 * 2
def baseEnd_65823 : Nat := 20028940516148859798395

theorem tailTrace_65823 : CollatzResearch.WordTrace tailWord_65823 prefixEnd_65823 20028940516148859798395 := by
  unfold tailWord_65823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400762040541987518514123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1600508027027991679009415 2400762040541987518514123)
  ·
    refine ⟨3601143060812981277771185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400762040541987518514123 3601143060812981277771185)
    ·
      refine ⟨2700857295609735958328389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3601143060812981277771185 2700857295609735958328389)
      ·
        refine ⟨506410742926825492186573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2700857295609735958328389 506410742926825492186573)
        ·
          refine ⟨189904028597559559569965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 506410742926825492186573 189904028597559559569965)
          ·
            refine ⟨71214010724084834838737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 189904028597559559569965 71214010724084834838737)
            ·
              refine ⟨53410508043063626129053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71214010724084834838737 53410508043063626129053)
              ·
                refine ⟨20028940516148859798395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53410508043063626129053 20028940516148859798395)
                ·
                  rfl

theorem cell19_65823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_65823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65823 prefixEnd_65823 := by exact prefixLift 65823
  have htrace : WordTrace (prefixWord ++ tailWord_65823) baseStart_65823 baseEnd_65823 := by
    simpa [prefixWord, tailWord_65823, baseEnd_65823] using wordTrace_append hprefix tailTrace_65823
  have hstable : (prefixWord ++ tailWord_65823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65823).length < 2 ^ (prefixWord ++ tailWord_65823).sum := by decide
  have hdescent : baseEnd_65823 < baseStart_65823 := by decide
  rcases family_descends (prefixWord ++ tailWord_65823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65825 : List Nat := [1, 2, 3, 2, 1, 1, 6, 3]
def baseStart_65825 : Nat := 118140960795 + 65825 * 2 ^ 59
def prefixEnd_65825 : Nat := 4983230072969 + 3 ^ 40 * 65825 * 2
def baseEnd_65825 : Nat := 20029549085813447753945

theorem tailTrace_65825 : CollatzResearch.WordTrace tailWord_65825 prefixEnd_65825 20029549085813447753945 := by
  unfold tailWord_65825
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400834986534741860086929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1600556657689827906724619 2400834986534741860086929)
  ·
    refine ⟨1800626239901056395065197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2400834986534741860086929 1800626239901056395065197)
    ·
      refine ⟨675234839962896148149449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1800626239901056395065197 675234839962896148149449)
      ·
        refine ⟨506426129972172111112087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 675234839962896148149449 506426129972172111112087)
        ·
          refine ⟨759639194958258166668131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506426129972172111112087 759639194958258166668131)
          ·
            refine ⟨1139458792437387250002197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759639194958258166668131 1139458792437387250002197)
            ·
              refine ⟨53412130895502527343853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1139458792437387250002197 53412130895502527343853)
              ·
                refine ⟨20029549085813447753945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53412130895502527343853 20029549085813447753945)
                ·
                  rfl

theorem cell19_65825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_65825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65825 prefixEnd_65825 := by exact prefixLift 65825
  have htrace : WordTrace (prefixWord ++ tailWord_65825) baseStart_65825 baseEnd_65825 := by
    simpa [prefixWord, tailWord_65825, baseEnd_65825] using wordTrace_append hprefix tailTrace_65825
  have hstable : (prefixWord ++ tailWord_65825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65825).length < 2 ^ (prefixWord ++ tailWord_65825).sum := by decide
  have hdescent : baseEnd_65825 < baseStart_65825 := by decide
  rcases family_descends (prefixWord ++ tailWord_65825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65827 : List Nat := [1, 1, 1, 4, 2, 2, 3, 5]
def baseStart_65827 : Nat := 118140960795 + 65827 * 2 ^ 59
def prefixEnd_65827 : Nat := 4983230072969 + 3 ^ 40 * 65827 * 2
def baseEnd_65827 : Nat := 20030157655478035709495

theorem tailTrace_65827 : CollatzResearch.WordTrace tailWord_65827 prefixEnd_65827 20030157655478035709495 := by
  unfold tailWord_65827
  simp only [CollatzResearch.WordTrace]
  refine ⟨2400907932527496201659735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1600605288351664134439823 2400907932527496201659735)
  ·
    refine ⟨3601361898791244302489603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2400907932527496201659735 3601361898791244302489603)
    ·
      refine ⟨5402042848186866453734405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601361898791244302489603 5402042848186866453734405)
      ·
        refine ⟨1012883034035037460075201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5402042848186866453734405 1012883034035037460075201)
        ·
          refine ⟨759662275526278095056401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012883034035037460075201 759662275526278095056401)
          ·
            refine ⟨569746706644708571292301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759662275526278095056401 569746706644708571292301)
            ·
              refine ⟨213655014991765714234613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569746706644708571292301 213655014991765714234613)
              ·
                refine ⟨20030157655478035709495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 213655014991765714234613 20030157655478035709495)
                ·
                  rfl

theorem cell19_65827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 5].length) (baseStart_65827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65827 prefixEnd_65827 := by exact prefixLift 65827
  have htrace : WordTrace (prefixWord ++ tailWord_65827) baseStart_65827 baseEnd_65827 := by
    simpa [prefixWord, tailWord_65827, baseEnd_65827] using wordTrace_append hprefix tailTrace_65827
  have hstable : (prefixWord ++ tailWord_65827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65827).length < 2 ^ (prefixWord ++ tailWord_65827).sum := by decide
  have hdescent : baseEnd_65827 < baseStart_65827 := by decide
  rcases family_descends (prefixWord ++ tailWord_65827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65842 : List Nat := [3, 2, 1, 1, 6, 1, 5]
def baseStart_65842 : Nat := 118140960795 + 65842 * 2 ^ 59
def prefixEnd_65842 : Nat := 4983230072969 + 3 ^ 40 * 65842 * 2
def baseEnd_65842 : Nat := 6678240642654148458707

theorem tailTrace_65842 : CollatzResearch.WordTrace tailWord_65842 prefixEnd_65842 6678240642654148458707 := by
  unfold tailWord_65842
  simp only [CollatzResearch.WordTrace]
  refine ⟨600363756868288440863945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1600970018315435842303853 600363756868288440863945)
  ·
    refine ⟨450272817651216330647959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 600363756868288440863945 450272817651216330647959)
    ·
      refine ⟨675409226476824495971939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450272817651216330647959 675409226476824495971939)
      ·
        refine ⟨1013113839715236743957909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675409226476824495971939 1013113839715236743957909)
        ·
          refine ⟨47489711236651722373027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1013113839715236743957909 47489711236651722373027)
          ·
            refine ⟨71234566854977583559541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47489711236651722373027 71234566854977583559541)
            ·
              refine ⟨6678240642654148458707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71234566854977583559541 6678240642654148458707)
              ·
                rfl

theorem cell19_65842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 5].length) (baseStart_65842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65842 prefixEnd_65842 := by exact prefixLift 65842
  have htrace : WordTrace (prefixWord ++ tailWord_65842) baseStart_65842 baseEnd_65842 := by
    simpa [prefixWord, tailWord_65842, baseEnd_65842] using wordTrace_append hprefix tailTrace_65842
  have hstable : (prefixWord ++ tailWord_65842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65842).length < 2 ^ (prefixWord ++ tailWord_65842).sum := by decide
  have hdescent : baseEnd_65842 < baseStart_65842 := by decide
  rcases family_descends (prefixWord ++ tailWord_65842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65844 : List Nat := [2, 5, 1, 1, 1, 2, 7]
def baseStart_65844 : Nat := 118140960795 + 65844 * 2 ^ 59
def prefixEnd_65844 : Nat := 4983230072969 + 3 ^ 40 * 65844 * 2
def baseEnd_65844 : Nat := 6678443499209011110557

theorem tailTrace_65844 : CollatzResearch.WordTrace tailWord_65844 prefixEnd_65844 6678443499209011110557 := by
  unfold tailWord_65844
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200763986732954052514293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1601018648977272070019057 1200763986732954052514293)
  ·
    refine ⟨112571623756214442423215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1200763986732954052514293 112571623756214442423215)
    ·
      refine ⟨168857435634321663634823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112571623756214442423215 168857435634321663634823)
      ·
        refine ⟨253286153451482495452235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168857435634321663634823 253286153451482495452235)
        ·
          refine ⟨379929230177223743178353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253286153451482495452235 379929230177223743178353)
          ·
            refine ⟨284946922632917807383765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379929230177223743178353 284946922632917807383765)
            ·
              refine ⟨6678443499209011110557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 284946922632917807383765 6678443499209011110557)
              ·
                rfl

theorem cell19_65844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_65844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65844 prefixEnd_65844 := by exact prefixLift 65844
  have htrace : WordTrace (prefixWord ++ tailWord_65844) baseStart_65844 baseEnd_65844 := by
    simpa [prefixWord, tailWord_65844, baseEnd_65844] using wordTrace_append hprefix tailTrace_65844
  have hstable : (prefixWord ++ tailWord_65844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65844).length < 2 ^ (prefixWord ++ tailWord_65844).sum := by decide
  have hdescent : baseEnd_65844 < baseStart_65844 := by decide
  rcases family_descends (prefixWord ++ tailWord_65844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_65996 : List Nat := [2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_65996 : Nat := 118140960795 + 65996 * 2 ^ 59
def prefixEnd_65996 : Nat := 4983230072969 + 3 ^ 40 * 65996 * 2
def baseEnd_65996 : Nat := 20081581792135717953479

theorem tailTrace_65996 : CollatzResearch.WordTrace tailWord_65996 prefixEnd_65996 20081581792135717953479 := by
  unfold tailWord_65996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203535934457619032280921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1604714579276825376374561 1203535934457619032280921)
  ·
    refine ⟨902651950843214274210691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1203535934457619032280921 902651950843214274210691)
    ·
      refine ⟨1353977926264821411316037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902651950843214274210691 1353977926264821411316037)
      ·
        refine ⟨253870861174654014621757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1353977926264821411316037 253870861174654014621757)
        ·
          refine ⟨95201572940495255483159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 253870861174654014621757 95201572940495255483159)
          ·
            refine ⟨142802359410742883224739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95201572940495255483159 142802359410742883224739)
            ·
              refine ⟨214203539116114324837109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142802359410742883224739 214203539116114324837109)
              ·
                refine ⟨20081581792135717953479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214203539116114324837109 20081581792135717953479)
                ·
                  rfl

theorem cell19_65996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_65996 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_65996 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_65996 prefixEnd_65996 := by exact prefixLift 65996
  have htrace : WordTrace (prefixWord ++ tailWord_65996) baseStart_65996 baseEnd_65996 := by
    simpa [prefixWord, tailWord_65996, baseEnd_65996] using wordTrace_append hprefix tailTrace_65996
  have hstable : (prefixWord ++ tailWord_65996).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_65996).length < 2 ^ (prefixWord ++ tailWord_65996).sum := by decide
  have hdescent : baseEnd_65996 < baseStart_65996 := by decide
  rcases family_descends (prefixWord ++ tailWord_65996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66087 : List Nat := [1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_66087 : Nat := 118140960795 + 66087 * 2 ^ 59
def prefixEnd_66087 : Nat := 4983230072969 + 3 ^ 40 * 66087 * 2
def baseEnd_66087 : Nat := 20109271711874469931009

theorem tailTrace_66087 : CollatzResearch.WordTrace tailWord_66087 prefixEnd_66087 20109271711874469931009 := by
  unfold tailWord_66087
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410390911585560606124515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1606927274390373737416343 2410390911585560606124515)
  ·
    refine ⟨3615586367378340909186773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2410390911585560606124515 3615586367378340909186773)
    ·
      refine ⟨84740305485429865059065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3615586367378340909186773 84740305485429865059065)
      ·
        refine ⟨63555229114072398794299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84740305485429865059065 63555229114072398794299)
        ·
          refine ⟨95332843671108598191449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63555229114072398794299 95332843671108598191449)
          ·
            refine ⟨71499632753331448643587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95332843671108598191449 71499632753331448643587)
            ·
              refine ⟨107249449129997172965381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71499632753331448643587 107249449129997172965381)
              ·
                refine ⟨20109271711874469931009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107249449129997172965381 20109271711874469931009)
                ·
                  rfl

theorem cell19_66087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_66087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66087 prefixEnd_66087 := by exact prefixLift 66087
  have htrace : WordTrace (prefixWord ++ tailWord_66087) baseStart_66087 baseEnd_66087 := by
    simpa [prefixWord, tailWord_66087, baseEnd_66087] using wordTrace_append hprefix tailTrace_66087
  have hstable : (prefixWord ++ tailWord_66087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66087).length < 2 ^ (prefixWord ++ tailWord_66087).sum := by decide
  have hdescent : baseEnd_66087 < baseStart_66087 := by decide
  rcases family_descends (prefixWord ++ tailWord_66087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66169 : List Nat := [1, 2, 1, 3, 3, 3, 1, 5]
def baseStart_66169 : Nat := 118140960795 + 66169 * 2 ^ 59
def prefixEnd_66169 : Nat := 4983230072969 + 3 ^ 40 * 66169 * 2
def baseEnd_66169 : Nat := 20134223068122576108563

theorem tailTrace_66169 : CollatzResearch.WordTrace tailWord_66169 prefixEnd_66169 20134223068122576108563 := by
  unfold tailWord_66169
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413381697288488610609561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1608921131525659073739707 2413381697288488610609561)
  ·
    refine ⟨1810036272966366457957171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2413381697288488610609561 1810036272966366457957171)
    ·
      refine ⟨2715054409449549686935757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1810036272966366457957171 2715054409449549686935757)
      ·
        refine ⟨1018145403543581132600909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2715054409449549686935757 1018145403543581132600909)
        ·
          refine ⟨381804526328842924725341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1018145403543581132600909 381804526328842924725341)
          ·
            refine ⟨143176697373316096772003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 381804526328842924725341 143176697373316096772003)
            ·
              refine ⟨214765046059974145158005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143176697373316096772003 214765046059974145158005)
              ·
                refine ⟨20134223068122576108563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 214765046059974145158005 20134223068122576108563)
                ·
                  rfl

theorem cell19_66169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 5].length) (baseStart_66169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66169 prefixEnd_66169 := by exact prefixLift 66169
  have htrace : WordTrace (prefixWord ++ tailWord_66169) baseStart_66169 baseEnd_66169 := by
    simpa [prefixWord, tailWord_66169, baseEnd_66169] using wordTrace_append hprefix tailTrace_66169
  have hstable : (prefixWord ++ tailWord_66169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66169).length < 2 ^ (prefixWord ++ tailWord_66169).sum := by decide
  have hdescent : baseEnd_66169 < baseStart_66169 := by decide
  rcases family_descends (prefixWord ++ tailWord_66169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66186 : List Nat := [3, 1, 2, 3, 3, 2, 5]
def baseStart_66186 : Nat := 118140960795 + 66186 * 2 ^ 59
def prefixEnd_66186 : Nat := 4983230072969 + 3 ^ 40 * 66186 * 2
def baseEnd_66186 : Nat := 6713131970090524576913

theorem tailTrace_66186 : CollatzResearch.WordTrace tailWord_66186 prefixEnd_66186 6713131970090524576913 := by
  unfold tailWord_66186
  simp only [CollatzResearch.WordTrace]
  refine ⟨603500434556725128494603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1609334492151267009318941 603500434556725128494603)
  ·
    refine ⟨905250651835087692741905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 603500434556725128494603 905250651835087692741905)
    ·
      refine ⟨678937988876315769556429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 905250651835087692741905 678937988876315769556429)
      ·
        refine ⟨254601745828618413583661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 678937988876315769556429 254601745828618413583661)
        ·
          refine ⟨95475654685731905093873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 254601745828618413583661 95475654685731905093873)
          ·
            refine ⟨71606741014298928820405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95475654685731905093873 71606741014298928820405)
            ·
              refine ⟨6713131970090524576913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71606741014298928820405 6713131970090524576913)
              ·
                rfl

theorem cell19_66186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_66186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66186 prefixEnd_66186 := by exact prefixLift 66186
  have htrace : WordTrace (prefixWord ++ tailWord_66186) baseStart_66186 baseEnd_66186 := by
    simpa [prefixWord, tailWord_66186, baseEnd_66186] using wordTrace_append hprefix tailTrace_66186
  have hstable : (prefixWord ++ tailWord_66186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66186).length < 2 ^ (prefixWord ++ tailWord_66186).sum := by decide
  have hdescent : baseEnd_66186 < baseStart_66186 := by decide
  rcases family_descends (prefixWord ++ tailWord_66186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66241 : List Nat := [1, 2, 6, 2, 2, 6]
def baseStart_66241 : Nat := 118140960795 + 66241 * 2 ^ 59
def prefixEnd_66241 : Nat := 4983230072969 + 3 ^ 40 * 66241 * 2
def baseEnd_66241 : Nat := 2239570175116415834263

theorem tailTrace_66241 : CollatzResearch.WordTrace tailWord_66241 prefixEnd_66241 2239570175116415834263 := by
  unfold tailWord_66241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416007753027644907230577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1610671835351763271487051 2416007753027644907230577)
  ·
    refine ⟨1812005814770733680422933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2416007753027644907230577 1812005814770733680422933)
    ·
      refine ⟨84937772567378141269825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1812005814770733680422933 84937772567378141269825)
      ·
        refine ⟨63703329425533605952369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84937772567378141269825 63703329425533605952369)
        ·
          refine ⟨47777497069150204464277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63703329425533605952369 47777497069150204464277)
          ·
            refine ⟨2239570175116415834263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47777497069150204464277 2239570175116415834263)
            ·
              rfl

theorem cell19_66241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 6].length) (baseStart_66241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66241 prefixEnd_66241 := by exact prefixLift 66241
  have htrace : WordTrace (prefixWord ++ tailWord_66241) baseStart_66241 baseEnd_66241 := by
    simpa [prefixWord, tailWord_66241, baseEnd_66241] using wordTrace_append hprefix tailTrace_66241
  have hstable : (prefixWord ++ tailWord_66241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66241).length < 2 ^ (prefixWord ++ tailWord_66241).sum := by decide
  have hdescent : baseEnd_66241 < baseStart_66241 := by decide
  rcases family_descends (prefixWord ++ tailWord_66241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66260 : List Nat := [2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_66260 : Nat := 118140960795 + 66260 * 2 ^ 59
def prefixEnd_66260 : Nat := 4983230072969 + 3 ^ 40 * 66260 * 2
def baseEnd_66260 : Nat := 20161912987861328086093

theorem tailTrace_66260 : CollatzResearch.WordTrace tailWord_66260 prefixEnd_66260 20161912987861328086093 := by
  unfold tailWord_66260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208350369979405576086117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1611133826639207434781489 1208350369979405576086117)
  ·
    refine ⟨226565694371138545516147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1208350369979405576086117 226565694371138545516147)
    ·
      refine ⟨339848541556707818274221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226565694371138545516147 339848541556707818274221)
      ·
        refine ⟨127443203083765431852833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 339848541556707818274221 127443203083765431852833)
        ·
          refine ⟨95582402312824073889625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127443203083765431852833 95582402312824073889625)
          ·
            refine ⟨71686801734618055417219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95582402312824073889625 71686801734618055417219)
            ·
              refine ⟨107530202601927083125829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71686801734618055417219 107530202601927083125829)
              ·
                refine ⟨20161912987861328086093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107530202601927083125829 20161912987861328086093)
                ·
                  rfl

theorem cell19_66260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_66260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66260 prefixEnd_66260 := by exact prefixLift 66260
  have htrace : WordTrace (prefixWord ++ tailWord_66260) baseStart_66260 baseEnd_66260 := by
    simpa [prefixWord, tailWord_66260, baseEnd_66260] using wordTrace_append hprefix tailTrace_66260
  have hstable : (prefixWord ++ tailWord_66260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66260).length < 2 ^ (prefixWord ++ tailWord_66260).sum := by decide
  have hdescent : baseEnd_66260 < baseStart_66260 := by decide
  rcases family_descends (prefixWord ++ tailWord_66260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66264 : List Nat := [2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_66264 : Nat := 118140960795 + 66264 * 2 ^ 59
def prefixEnd_66264 : Nat := 4983230072969 + 3 ^ 40 * 66264 * 2
def baseEnd_66264 : Nat := 20163130127190503997193

theorem tailTrace_66264 : CollatzResearch.WordTrace tailWord_66264 prefixEnd_66264 20163130127190503997193 := by
  unfold tailWord_66264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1208423315972159917658923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1611231087962879890211897 1208423315972159917658923)
  ·
    refine ⟨1812634973958239876488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1208423315972159917658923 1812634973958239876488385)
    ·
      refine ⟨1359476230468679907366289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1812634973958239876488385 1359476230468679907366289)
      ·
        refine ⟨1019607172851509930524717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1359476230468679907366289 1019607172851509930524717)
        ·
          refine ⟨382352689819316223946769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1019607172851509930524717 382352689819316223946769)
          ·
            refine ⟨286764517364487167960077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382352689819316223946769 286764517364487167960077)
            ·
              refine ⟨107536694011682687985029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286764517364487167960077 107536694011682687985029)
              ·
                refine ⟨20163130127190503997193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107536694011682687985029 20163130127190503997193)
                ·
                  rfl

theorem cell19_66264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_66264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66264 prefixEnd_66264 := by exact prefixLift 66264
  have htrace : WordTrace (prefixWord ++ tailWord_66264) baseStart_66264 baseEnd_66264 := by
    simpa [prefixWord, tailWord_66264, baseEnd_66264] using wordTrace_append hprefix tailTrace_66264
  have hstable : (prefixWord ++ tailWord_66264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66264).length < 2 ^ (prefixWord ++ tailWord_66264).sum := by decide
  have hdescent : baseEnd_66264 < baseStart_66264 := by decide
  rcases family_descends (prefixWord ++ tailWord_66264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66323 : List Nat := [1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_66323 : Nat := 118140960795 + 66323 * 2 ^ 59
def prefixEnd_66323 : Nat := 4983230072969 + 3 ^ 40 * 66323 * 2
def baseEnd_66323 : Nat := 20181082932295848685921

theorem tailTrace_66323 : CollatzResearch.WordTrace tailWord_66323 prefixEnd_66323 20181082932295848685921 := by
  unfold tailWord_66323
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418998538730572911715623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1612665692487048607810415 2418998538730572911715623)
  ·
    refine ⟨3628497808095859367573435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418998538730572911715623 3628497808095859367573435)
    ·
      refine ⟨5442746712143789051360153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628497808095859367573435 5442746712143789051360153)
      ·
        refine ⟨4082060034107841788520115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5442746712143789051360153 4082060034107841788520115)
        ·
          refine ⟨6123090051161762682780173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4082060034107841788520115 6123090051161762682780173)
          ·
            refine ⟨2296158769185661006042565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6123090051161762682780173 2296158769185661006042565)
            ·
              refine ⟨430529769222311438632981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2296158769185661006042565 430529769222311438632981)
              ·
                refine ⟨20181082932295848685921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 430529769222311438632981 20181082932295848685921)
                ·
                  rfl

theorem cell19_66323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_66323 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66323 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66323 prefixEnd_66323 := by exact prefixLift 66323
  have htrace : WordTrace (prefixWord ++ tailWord_66323) baseStart_66323 baseEnd_66323 := by
    simpa [prefixWord, tailWord_66323, baseEnd_66323] using wordTrace_append hprefix tailTrace_66323
  have hstable : (prefixWord ++ tailWord_66323).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66323).length < 2 ^ (prefixWord ++ tailWord_66323).sum := by decide
  have hdescent : baseEnd_66323 < baseStart_66323 := by decide
  rcases family_descends (prefixWord ++ tailWord_66323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66338 : List Nat := [3, 3, 1, 1, 2, 2, 4, 3]
def baseStart_66338 : Nat := 118140960795 + 66338 * 2 ^ 59
def prefixEnd_66338 : Nat := 4983230072969 + 3 ^ 40 * 66338 * 2
def baseEnd_66338 : Nat := 20185647204780258352547

theorem tailTrace_66338 : CollatzResearch.WordTrace tailWord_66338 prefixEnd_66338 20185647204780258352547 := by
  unfold tailWord_66338
  simp only [CollatzResearch.WordTrace]
  refine ⟨604886408419057618377917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1613030422450820315674445 604886408419057618377917)
  ·
    refine ⟨226832403157146606891719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 604886408419057618377917 226832403157146606891719)
    ·
      refine ⟨340248604735719910337579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226832403157146606891719 340248604735719910337579)
      ·
        refine ⟨510372907103579865506369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340248604735719910337579 510372907103579865506369)
        ·
          refine ⟨382779680327684899129777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510372907103579865506369 382779680327684899129777)
          ·
            refine ⟨287084760245763674347333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382779680327684899129777 287084760245763674347333)
            ·
              refine ⟨53828392546080688940125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287084760245763674347333 53828392546080688940125)
              ·
                refine ⟨20185647204780258352547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53828392546080688940125 20185647204780258352547)
                ·
                  rfl

theorem cell19_66338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_66338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66338 prefixEnd_66338 := by exact prefixLift 66338
  have htrace : WordTrace (prefixWord ++ tailWord_66338) baseStart_66338 baseEnd_66338 := by
    simpa [prefixWord, tailWord_66338, baseEnd_66338] using wordTrace_append hprefix tailTrace_66338
  have hstable : (prefixWord ++ tailWord_66338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66338).length < 2 ^ (prefixWord ++ tailWord_66338).sum := by decide
  have hdescent : baseEnd_66338 < baseStart_66338 := by decide
  rcases family_descends (prefixWord ++ tailWord_66338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66399 : List Nat := [1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_66399 : Nat := 118140960795 + 66399 * 2 ^ 59
def prefixEnd_66399 : Nat := 4983230072969 + 3 ^ 40 * 66399 * 2
def baseEnd_66399 : Nat := 20204208579550190996825

theorem tailTrace_66399 : CollatzResearch.WordTrace tailWord_66399 prefixEnd_66399 20204208579550190996825 := by
  unfold tailWord_66399
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421770486455237891482251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1614513657636825260988167 2421770486455237891482251)
  ·
    refine ⟨3632655729682856837223377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421770486455237891482251 3632655729682856837223377)
    ·
      refine ⟨2724491797262142627917533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3632655729682856837223377 2724491797262142627917533)
      ·
        refine ⟨1021684423973303485469075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2724491797262142627917533 1021684423973303485469075)
        ·
          refine ⟨1532526635959955228203613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1021684423973303485469075 1532526635959955228203613)
          ·
            refine ⟨574697488484983210576355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1532526635959955228203613 574697488484983210576355)
            ·
              refine ⟨862046232727474815864533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574697488484983210576355 862046232727474815864533)
              ·
                refine ⟨20204208579550190996825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 862046232727474815864533 20204208579550190996825)
                ·
                  rfl

theorem cell19_66399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_66399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66399 prefixEnd_66399 := by exact prefixLift 66399
  have htrace : WordTrace (prefixWord ++ tailWord_66399) baseStart_66399 baseEnd_66399 := by
    simpa [prefixWord, tailWord_66399, baseEnd_66399] using wordTrace_append hprefix tailTrace_66399
  have hstable : (prefixWord ++ tailWord_66399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66399).length < 2 ^ (prefixWord ++ tailWord_66399).sum := by decide
  have hdescent : baseEnd_66399 < baseStart_66399 := by decide
  rcases family_descends (prefixWord ++ tailWord_66399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66414 : List Nat := [4, 1, 2, 3, 3, 6]
def baseStart_66414 : Nat := 118140960795 + 66414 * 2 ^ 59
def prefixEnd_66414 : Nat := 4983230072969 + 3 ^ 40 * 66414 * 2
def baseEnd_66414 : Nat := 2245419205781622295939

theorem tailTrace_66414 : CollatzResearch.WordTrace tailWord_66414 prefixEnd_66414 2245419205781622295939 := by
  unfold tailWord_66414
  simp only [CollatzResearch.WordTrace]
  refine ⟨302789697675111931659787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1614878387600596968852197 302789697675111931659787)
  ·
    refine ⟨454184546512667897489681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302789697675111931659787 454184546512667897489681)
    ·
      refine ⟨340638409884500923117261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454184546512667897489681 340638409884500923117261)
      ·
        refine ⟨127739403706687846168973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340638409884500923117261 127739403706687846168973)
        ·
          refine ⟨47902276390007942313365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127739403706687846168973 47902276390007942313365)
          ·
            refine ⟨2245419205781622295939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47902276390007942313365 2245419205781622295939)
            ·
              rfl

theorem cell19_66414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_66414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66414 prefixEnd_66414 := by exact prefixLift 66414
  have htrace : WordTrace (prefixWord ++ tailWord_66414) baseStart_66414 baseEnd_66414 := by
    simpa [prefixWord, tailWord_66414, baseEnd_66414] using wordTrace_append hprefix tailTrace_66414
  have hstable : (prefixWord ++ tailWord_66414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66414).length < 2 ^ (prefixWord ++ tailWord_66414).sum := by decide
  have hdescent : baseEnd_66414 < baseStart_66414 := by decide
  rcases family_descends (prefixWord ++ tailWord_66414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66450 : List Nat := [3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_66450 : Nat := 118140960795 + 66450 * 2 ^ 59
def prefixEnd_66450 : Nat := 4983230072969 + 3 ^ 40 * 66450 * 2
def baseEnd_66450 : Nat := 20219727105997183863353

theorem tailTrace_66450 : CollatzResearch.WordTrace tailWord_66450 prefixEnd_66450 20219727105997183863353 := by
  unfold tailWord_66450
  simp only [CollatzResearch.WordTrace]
  refine ⟨605907652317618400397201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1615753739513649067725869 605907652317618400397201)
  ·
    refine ⟨454430739238213800297901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 605907652317618400397201 454430739238213800297901)
    ·
      refine ⟨170411527214330175111713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 454430739238213800297901 170411527214330175111713)
      ·
        refine ⟨127808645410747631333785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170411527214330175111713 127808645410747631333785)
        ·
          refine ⟨95856484058060723500339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127808645410747631333785 95856484058060723500339)
          ·
            refine ⟨143784726087091085250509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95856484058060723500339 143784726087091085250509)
            ·
              refine ⟨53919272282659156968941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143784726087091085250509 53919272282659156968941)
              ·
                refine ⟨20219727105997183863353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53919272282659156968941 20219727105997183863353)
                ·
                  rfl

theorem cell19_66450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_66450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66450 prefixEnd_66450 := by exact prefixLift 66450
  have htrace : WordTrace (prefixWord ++ tailWord_66450) baseStart_66450 baseEnd_66450 := by
    simpa [prefixWord, tailWord_66450, baseEnd_66450] using wordTrace_append hprefix tailTrace_66450
  have hstable : (prefixWord ++ tailWord_66450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66450).length < 2 ^ (prefixWord ++ tailWord_66450).sum := by decide
  have hdescent : baseEnd_66450 < baseStart_66450 := by decide
  rcases family_descends (prefixWord ++ tailWord_66450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66452 : List Nat := [2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_66452 : Nat := 118140960795 + 66452 * 2 ^ 59
def prefixEnd_66452 : Nat := 4983230072969 + 3 ^ 40 * 66452 * 2
def baseEnd_66452 : Nat := 20220335675661771818903

theorem tailTrace_66452 : CollatzResearch.WordTrace tailWord_66452 prefixEnd_66452 20220335675661771818903 := by
  unfold tailWord_66452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1211851777631613971580805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1615802370175485295441073 1211851777631613971580805)
  ·
    refine ⟨227222208305927619671401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1211851777631613971580805 227222208305927619671401)
    ·
      refine ⟨170416656229445714753551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227222208305927619671401 170416656229445714753551)
      ·
        refine ⟨255624984344168572130327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170416656229445714753551 255624984344168572130327)
        ·
          refine ⟨383437476516252858195491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255624984344168572130327 383437476516252858195491)
          ·
            refine ⟨575156214774379287293237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383437476516252858195491 575156214774379287293237)
            ·
              refine ⟨53920895135098058183741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 575156214774379287293237 53920895135098058183741)
              ·
                refine ⟨20220335675661771818903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53920895135098058183741 20220335675661771818903)
                ·
                  rfl

theorem cell19_66452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_66452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66452 prefixEnd_66452 := by exact prefixLift 66452
  have htrace : WordTrace (prefixWord ++ tailWord_66452) baseStart_66452 baseEnd_66452 := by
    simpa [prefixWord, tailWord_66452, baseEnd_66452] using wordTrace_append hprefix tailTrace_66452
  have hstable : (prefixWord ++ tailWord_66452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66452).length < 2 ^ (prefixWord ++ tailWord_66452).sum := by decide
  have hdescent : baseEnd_66452 < baseStart_66452 := by decide
  rcases family_descends (prefixWord ++ tailWord_66452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66511 : List Nat := [1, 1, 2, 1, 1, 6, 4, 3]
def baseStart_66511 : Nat := 118140960795 + 66511 * 2 ^ 59
def prefixEnd_66511 : Nat := 4983230072969 + 3 ^ 40 * 66511 * 2
def baseEnd_66511 : Nat := 20238288480767116507631

theorem tailTrace_66511 : CollatzResearch.WordTrace tailWord_66511 prefixEnd_66511 20238288480767116507631 := by
  unfold tailWord_66511
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425855462049481019559387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1617236974699654013039591 2425855462049481019559387)
  ·
    refine ⟨3638783193074221529339081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2425855462049481019559387 3638783193074221529339081)
    ·
      refine ⟨2729087394805666147004311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3638783193074221529339081 2729087394805666147004311)
      ·
        refine ⟨4093631092208499220506467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2729087394805666147004311 4093631092208499220506467)
        ·
          refine ⟨6140446638312748830759701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4093631092208499220506467 6140446638312748830759701)
          ·
            refine ⟨287833436170910101441861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6140446638312748830759701 287833436170910101441861)
            ·
              refine ⟨53968769282045644020349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287833436170910101441861 53968769282045644020349)
              ·
                refine ⟨20238288480767116507631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53968769282045644020349 20238288480767116507631)
                ·
                  rfl

theorem cell19_66511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 3].length) (baseStart_66511 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66511 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66511 prefixEnd_66511 := by exact prefixLift 66511
  have htrace : WordTrace (prefixWord ++ tailWord_66511) baseStart_66511 baseEnd_66511 := by
    simpa [prefixWord, tailWord_66511, baseEnd_66511] using wordTrace_append hprefix tailTrace_66511
  have hstable : (prefixWord ++ tailWord_66511).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66511).length < 2 ^ (prefixWord ++ tailWord_66511).sum := by decide
  have hdescent : baseEnd_66511 < baseStart_66511 := by decide
  rcases family_descends (prefixWord ++ tailWord_66511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66513 : List Nat := [1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_66513 : Nat := 118140960795 + 66513 * 2 ^ 59
def prefixEnd_66513 : Nat := 4983230072969 + 3 ^ 40 * 66513 * 2
def baseEnd_66513 : Nat := 20238897050431704463181

theorem tailTrace_66513 : CollatzResearch.WordTrace tailWord_66513 prefixEnd_66513 20238897050431704463181 := by
  unfold tailWord_66513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2425928408042235361132193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1617285605361490240754795 2425928408042235361132193)
  ·
    refine ⟨1819446306031676520849145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2425928408042235361132193 1819446306031676520849145)
    ·
      refine ⟨1364584729523757390636859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1819446306031676520849145 1364584729523757390636859)
      ·
        refine ⟨2046877094285636085955289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1364584729523757390636859 2046877094285636085955289)
        ·
          refine ⟨1535157820714227064466467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2046877094285636085955289 1535157820714227064466467)
          ·
            refine ⟨2302736731071340596699701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535157820714227064466467 2302736731071340596699701)
            ·
              refine ⟨215881568537938180940597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2302736731071340596699701 215881568537938180940597)
              ·
                refine ⟨20238897050431704463181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215881568537938180940597 20238897050431704463181)
                ·
                  rfl

theorem cell19_66513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_66513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66513 prefixEnd_66513 := by exact prefixLift 66513
  have htrace : WordTrace (prefixWord ++ tailWord_66513) baseStart_66513 baseEnd_66513 := by
    simpa [prefixWord, tailWord_66513, baseEnd_66513] using wordTrace_append hprefix tailTrace_66513
  have hstable : (prefixWord ++ tailWord_66513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66513).length < 2 ^ (prefixWord ++ tailWord_66513).sum := by decide
  have hdescent : baseEnd_66513 < baseStart_66513 := by decide
  rcases family_descends (prefixWord ++ tailWord_66513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66589 : List Nat := [1, 4, 2, 2, 10]
def baseStart_66589 : Nat := 118140960795 + 66589 * 2 ^ 59
def prefixEnd_66589 : Nat := 4983230072969 + 3 ^ 40 * 66589 * 2
def baseEnd_66589 : Nat := 750445285099483213855

theorem tailTrace_66589 : CollatzResearch.WordTrace tailWord_66589 prefixEnd_66589 750445285099483213855 := by
  unfold tailWord_66589
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428700355766900340898821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1619133570511266893932547 2428700355766900340898821)
  ·
    refine ⟨455381316706293813918529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2428700355766900340898821 455381316706293813918529)
    ·
      refine ⟨341535987529720360438897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455381316706293813918529 341535987529720360438897)
      ·
        refine ⟨256151990647290270329173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341535987529720360438897 256151990647290270329173)
        ·
          refine ⟨750445285099483213855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 256151990647290270329173 750445285099483213855)
          ·
            rfl

theorem cell19_66589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 10].length) (baseStart_66589 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66589 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66589 prefixEnd_66589 := by exact prefixLift 66589
  have htrace : WordTrace (prefixWord ++ tailWord_66589) baseStart_66589 baseEnd_66589 := by
    simpa [prefixWord, tailWord_66589, baseEnd_66589] using wordTrace_append hprefix tailTrace_66589
  have hstable : (prefixWord ++ tailWord_66589).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66589).length < 2 ^ (prefixWord ++ tailWord_66589).sum := by decide
  have hdescent : baseEnd_66589 < baseStart_66589 := by decide
  rcases family_descends (prefixWord ++ tailWord_66589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66602 : List Nat := [3, 1, 4, 1, 4, 1, 1, 4]
def baseStart_66602 : Nat := 118140960795 + 66602 * 2 ^ 59
def prefixEnd_66602 : Nat := 4983230072969 + 3 ^ 40 * 66602 * 2
def baseEnd_66602 : Nat := 20265978400505868485161

theorem tailTrace_66602 : CollatzResearch.WordTrace tailWord_66602 prefixEnd_66602 20265978400505868485161 := by
  unfold tailWord_66602
  simp only [CollatzResearch.WordTrace]
  refine ⟨607293626179950890280515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1619449669813202374081373 607293626179950890280515)
  ·
    refine ⟨910940439269926335420773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607293626179950890280515 910940439269926335420773)
    ·
      refine ⟨170801332363111187891395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 910940439269926335420773 170801332363111187891395)
      ·
        refine ⟨256201998544666781837093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170801332363111187891395 256201998544666781837093)
        ·
          refine ⟨48037874727125021594455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256201998544666781837093 48037874727125021594455)
          ·
            refine ⟨72056812090687532391683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48037874727125021594455 72056812090687532391683)
            ·
              refine ⟨108085218136031298587525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72056812090687532391683 108085218136031298587525)
              ·
                refine ⟨20265978400505868485161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108085218136031298587525 20265978400505868485161)
                ·
                  rfl

theorem cell19_66602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_66602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66602 prefixEnd_66602 := by exact prefixLift 66602
  have htrace : WordTrace (prefixWord ++ tailWord_66602) baseStart_66602 baseEnd_66602 := by
    simpa [prefixWord, tailWord_66602, baseEnd_66602] using wordTrace_append hprefix tailTrace_66602
  have hstable : (prefixWord ++ tailWord_66602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66602).length < 2 ^ (prefixWord ++ tailWord_66602).sum := by decide
  have hdescent : baseEnd_66602 < baseStart_66602 := by decide
  rcases family_descends (prefixWord ++ tailWord_66602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66684 : List Nat := [2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_66684 : Nat := 118140960795 + 66684 * 2 ^ 59
def prefixEnd_66684 : Nat := 4983230072969 + 3 ^ 40 * 66684 * 2
def baseEnd_66684 : Nat := 20290929756753974662715

theorem tailTrace_66684 : CollatzResearch.WordTrace tailWord_66684 prefixEnd_66684 20290929756753974662715 := by
  unfold tailWord_66684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216082645211365782803553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1621443526948487710404737 1216082645211365782803553)
  ·
    refine ⟨912061983908524337102665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1216082645211365782803553 912061983908524337102665)
    ·
      refine ⟨684046487931393252826999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 912061983908524337102665 684046487931393252826999)
      ·
        refine ⟨1026069731897089879240499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684046487931393252826999 1026069731897089879240499)
        ·
          refine ⟨1539104597845634818860749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026069731897089879240499 1539104597845634818860749)
          ·
            refine ⟨577164224192113057072781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1539104597845634818860749 577164224192113057072781)
            ·
              refine ⟨216436584072042396402293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577164224192113057072781 216436584072042396402293)
              ·
                refine ⟨20290929756753974662715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216436584072042396402293 20290929756753974662715)
                ·
                  rfl

theorem cell19_66684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_66684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66684 prefixEnd_66684 := by exact prefixLift 66684
  have htrace : WordTrace (prefixWord ++ tailWord_66684) baseStart_66684 baseEnd_66684 := by
    simpa [prefixWord, tailWord_66684, baseEnd_66684] using wordTrace_append hprefix tailTrace_66684
  have hstable : (prefixWord ++ tailWord_66684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66684).length < 2 ^ (prefixWord ++ tailWord_66684).sum := by decide
  have hdescent : baseEnd_66684 < baseStart_66684 := by decide
  rcases family_descends (prefixWord ++ tailWord_66684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66718 : List Nat := [4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_66718 : Nat := 118140960795 + 66718 * 2 ^ 59
def prefixEnd_66718 : Nat := 4983230072969 + 3 ^ 40 * 66718 * 2
def baseEnd_66718 : Nat := 20301275441051969907067

theorem tailTrace_66718 : CollatzResearch.WordTrace tailWord_66718 prefixEnd_66718 20301275441051969907067 := by
  unfold tailWord_66718
  simp only [CollatzResearch.WordTrace]
  refine ⟨304175671537444421543101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1622270248199703581563205 304175671537444421543101)
  ·
    refine ⟨114065876826541658078663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 304175671537444421543101 114065876826541658078663)
    ·
      refine ⟨171098815239812487117995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114065876826541658078663 171098815239812487117995)
      ·
        refine ⟨256648222859718730676993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171098815239812487117995 256648222859718730676993)
        ·
          refine ⟨192486167144789048007745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256648222859718730676993 192486167144789048007745)
          ·
            refine ⟨144364625358591786005809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192486167144789048007745 144364625358591786005809)
            ·
              refine ⟨108273469018943839504357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144364625358591786005809 108273469018943839504357)
              ·
                refine ⟨20301275441051969907067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108273469018943839504357 20301275441051969907067)
                ·
                  rfl

theorem cell19_66718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_66718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66718 prefixEnd_66718 := by exact prefixLift 66718
  have htrace : WordTrace (prefixWord ++ tailWord_66718) baseStart_66718 baseEnd_66718 := by
    simpa [prefixWord, tailWord_66718, baseEnd_66718] using wordTrace_append hprefix tailTrace_66718
  have hstable : (prefixWord ++ tailWord_66718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66718).length < 2 ^ (prefixWord ++ tailWord_66718).sum := by decide
  have hdescent : baseEnd_66718 < baseStart_66718 := by decide
  rcases family_descends (prefixWord ++ tailWord_66718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66754 : List Nat := [3, 5, 1, 1, 3, 6]
def baseStart_66754 : Nat := 118140960795 + 66754 * 2 ^ 59
def prefixEnd_66754 : Nat := 4983230072969 + 3 ^ 40 * 66754 * 2
def baseEnd_66754 : Nat := 2256914410557172567441

theorem tailTrace_66754 : CollatzResearch.WordTrace tailWord_66754 prefixEnd_66754 2256914410557172567441 := by
  unfold tailWord_66754
  simp only [CollatzResearch.WordTrace]
  refine ⟨608679600042283380163829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1623145600112755680436877 608679600042283380163829)
  ·
    refine ⟨57063712503964066890359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 608679600042283380163829 57063712503964066890359)
    ·
      refine ⟨85595568755946100335539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57063712503964066890359 85595568755946100335539)
      ·
        refine ⟨128393353133919150503309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85595568755946100335539 128393353133919150503309)
        ·
          refine ⟨48147507425219681438741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128393353133919150503309 48147507425219681438741)
          ·
            refine ⟨2256914410557172567441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48147507425219681438741 2256914410557172567441)
            ·
              rfl

theorem cell19_66754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 6].length) (baseStart_66754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66754 prefixEnd_66754 := by exact prefixLift 66754
  have htrace : WordTrace (prefixWord ++ tailWord_66754) baseStart_66754 baseEnd_66754 := by
    simpa [prefixWord, tailWord_66754, baseEnd_66754] using wordTrace_append hprefix tailTrace_66754
  have hstable : (prefixWord ++ tailWord_66754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66754).length < 2 ^ (prefixWord ++ tailWord_66754).sum := by decide
  have hdescent : baseEnd_66754 < baseStart_66754 := by decide
  rcases family_descends (prefixWord ++ tailWord_66754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66796 : List Nat := [2, 2, 1, 1, 2, 5, 3, 3]
def baseStart_66796 : Nat := 118140960795 + 66796 * 2 ^ 59
def prefixEnd_66796 : Nat := 4983230072969 + 3 ^ 40 * 66796 * 2
def baseEnd_66796 : Nat := 20325009657970900173521

theorem tailTrace_66796 : CollatzResearch.WordTrace tailWord_66796 prefixEnd_66796 20325009657970900173521 := by
  unfold tailWord_66796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1218125133008487346842121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1624166844011316462456161 1218125133008487346842121)
  ·
    refine ⟨913593849756365510131591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1218125133008487346842121 913593849756365510131591)
    ·
      refine ⟨1370390774634548265197387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 913593849756365510131591 1370390774634548265197387)
      ·
        refine ⟨2055586161951822397796081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1370390774634548265197387 2055586161951822397796081)
        ·
          refine ⟨1541689621463866798347061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2055586161951822397796081 1541689621463866798347061)
          ·
            refine ⟨144533402012237512345037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1541689621463866798347061 144533402012237512345037)
            ·
              refine ⟨54200025754589067129389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144533402012237512345037 54200025754589067129389)
              ·
                refine ⟨20325009657970900173521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54200025754589067129389 20325009657970900173521)
                ·
                  rfl

theorem cell19_66796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_66796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66796 prefixEnd_66796 := by exact prefixLift 66796
  have htrace : WordTrace (prefixWord ++ tailWord_66796) baseStart_66796 baseEnd_66796 := by
    simpa [prefixWord, tailWord_66796, baseEnd_66796] using wordTrace_append hprefix tailTrace_66796
  have hstable : (prefixWord ++ tailWord_66796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66796).length < 2 ^ (prefixWord ++ tailWord_66796).sum := by decide
  have hdescent : baseEnd_66796 < baseStart_66796 := by decide
  rcases family_descends (prefixWord ++ tailWord_66796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66798 : List Nat := [4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_66798 : Nat := 118140960795 + 66798 * 2 ^ 59
def prefixEnd_66798 : Nat := 4983230072969 + 3 ^ 40 * 66798 * 2
def baseEnd_66798 : Nat := 20325618227635488129071

theorem tailTrace_66798 : CollatzResearch.WordTrace tailWord_66798 prefixEnd_66798 20325618227635488129071 := by
  unfold tailWord_66798
  simp only [CollatzResearch.WordTrace]
  refine ⟨304540401501216129407131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1624215474673152690171365 304540401501216129407131)
  ·
    refine ⟨456810602251824194110697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 304540401501216129407131 456810602251824194110697)
    ·
      refine ⟨342607951688868145583023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456810602251824194110697 342607951688868145583023)
      ·
        refine ⟨513911927533302218374535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342607951688868145583023 513911927533302218374535)
        ·
          refine ⟨770867891299953327561803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513911927533302218374535 770867891299953327561803)
          ·
            refine ⟨1156301836949929991342705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770867891299953327561803 1156301836949929991342705)
            ·
              refine ⟨867226377712447493507029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156301836949929991342705 867226377712447493507029)
              ·
                refine ⟨20325618227635488129071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 867226377712447493507029 20325618227635488129071)
                ·
                  rfl

theorem cell19_66798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_66798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66798 prefixEnd_66798 := by exact prefixLift 66798
  have htrace : WordTrace (prefixWord ++ tailWord_66798) baseStart_66798 baseEnd_66798 := by
    simpa [prefixWord, tailWord_66798, baseEnd_66798] using wordTrace_append hprefix tailTrace_66798
  have hstable : (prefixWord ++ tailWord_66798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66798).length < 2 ^ (prefixWord ++ tailWord_66798).sum := by decide
  have hdescent : baseEnd_66798 < baseStart_66798 := by decide
  rcases family_descends (prefixWord ++ tailWord_66798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66817 : List Nat := [1, 2, 4, 1, 1, 4, 6]
def baseStart_66817 : Nat := 118140960795 + 66817 * 2 ^ 59
def prefixEnd_66817 : Nat := 4983230072969 + 3 ^ 40 * 66817 * 2
def baseEnd_66817 : Nat := 6777133213149691235599

theorem tailTrace_66817 : CollatzResearch.WordTrace tailWord_66817 prefixEnd_66817 6777133213149691235599 := by
  unfold tailWord_66817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437016198940895280198705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1624677465960596853465803 2437016198940895280198705)
  ·
    refine ⟨1827762149205671460149029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2437016198940895280198705 1827762149205671460149029)
    ·
      refine ⟨342705402976063398777943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1827762149205671460149029 342705402976063398777943)
      ·
        refine ⟨514058104464095098166915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342705402976063398777943 514058104464095098166915)
        ·
          refine ⟨771087156696142647250373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514058104464095098166915 771087156696142647250373)
          ·
            refine ⟨144578841880526746359445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 771087156696142647250373 144578841880526746359445)
            ·
              refine ⟨6777133213149691235599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 144578841880526746359445 6777133213149691235599)
              ·
                rfl

theorem cell19_66817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 6].length) (baseStart_66817 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66817 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66817 prefixEnd_66817 := by exact prefixLift 66817
  have htrace : WordTrace (prefixWord ++ tailWord_66817) baseStart_66817 baseEnd_66817 := by
    simpa [prefixWord, tailWord_66817, baseEnd_66817] using wordTrace_append hprefix tailTrace_66817
  have hstable : (prefixWord ++ tailWord_66817).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66817).length < 2 ^ (prefixWord ++ tailWord_66817).sum := by decide
  have hdescent : baseEnd_66817 < baseStart_66817 := by decide
  rcases family_descends (prefixWord ++ tailWord_66817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66853 : List Nat := [1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_66853 : Nat := 118140960795 + 66853 * 2 ^ 59
def prefixEnd_66853 : Nat := 4983230072969 + 3 ^ 40 * 66853 * 2
def baseEnd_66853 : Nat := 20342353893411656906699

theorem tailTrace_66853 : CollatzResearch.WordTrace tailWord_66853 prefixEnd_66853 20342353893411656906699 := by
  unfold tailWord_66853
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438329226810473428509213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1625552817873648952339475 2438329226810473428509213)
  ·
    refine ⟨914373460053927535690955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2438329226810473428509213 914373460053927535690955)
    ·
      refine ⟨1371560190080891303536433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 914373460053927535690955 1371560190080891303536433)
      ·
        refine ⟨1028670142560668477652325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371560190080891303536433 1028670142560668477652325)
        ·
          refine ⟨192875651730125339559811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1028670142560668477652325 192875651730125339559811)
          ·
            refine ⟨289313477595188009339717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192875651730125339559811 289313477595188009339717)
            ·
              refine ⟨54246277049097751751197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 289313477595188009339717 54246277049097751751197)
              ·
                refine ⟨20342353893411656906699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54246277049097751751197 20342353893411656906699)
                ·
                  rfl

theorem cell19_66853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_66853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66853 prefixEnd_66853 := by exact prefixLift 66853
  have htrace : WordTrace (prefixWord ++ tailWord_66853) baseStart_66853 baseEnd_66853 := by
    simpa [prefixWord, tailWord_66853, baseEnd_66853] using wordTrace_append hprefix tailTrace_66853
  have hstable : (prefixWord ++ tailWord_66853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66853).length < 2 ^ (prefixWord ++ tailWord_66853).sum := by decide
  have hdescent : baseEnd_66853 < baseStart_66853 := by decide
  rcases family_descends (prefixWord ++ tailWord_66853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66912 : List Nat := [2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_66912 : Nat := 118140960795 + 66912 * 2 ^ 59
def prefixEnd_66912 : Nat := 4983230072969 + 3 ^ 40 * 66912 * 2
def baseEnd_66912 : Nat := 20360306698517001595427

theorem tailTrace_66912 : CollatzResearch.WordTrace tailWord_66912 prefixEnd_66912 20360306698517001595427 := by
  unfold tailWord_66912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220240566798363252453495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1626987422397817669937993 1220240566798363252453495)
  ·
    refine ⟨1830360850197544878680243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1220240566798363252453495 1830360850197544878680243)
    ·
      refine ⟨2745541275296317318020365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1830360850197544878680243 2745541275296317318020365)
      ·
        refine ⟨1029577978236118994257637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2745541275296317318020365 1029577978236118994257637)
        ·
          refine ⟨193045870919272311423307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1029577978236118994257637 193045870919272311423307)
          ·
            refine ⟨289568806378908467134961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193045870919272311423307 289568806378908467134961)
            ·
              refine ⟨217176604784181350351221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289568806378908467134961 217176604784181350351221)
              ·
                refine ⟨20360306698517001595427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217176604784181350351221 20360306698517001595427)
                ·
                  rfl

theorem cell19_66912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_66912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66912 prefixEnd_66912 := by exact prefixLift 66912
  have htrace : WordTrace (prefixWord ++ tailWord_66912) baseStart_66912 baseEnd_66912 := by
    simpa [prefixWord, tailWord_66912, baseEnd_66912] using wordTrace_append hprefix tailTrace_66912
  have hstable : (prefixWord ++ tailWord_66912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66912).length < 2 ^ (prefixWord ++ tailWord_66912).sum := by decide
  have hdescent : baseEnd_66912 < baseStart_66912 := by decide
  rcases family_descends (prefixWord ++ tailWord_66912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66942 : List Nat := [4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_66942 : Nat := 118140960795 + 66942 * 2 ^ 59
def prefixEnd_66942 : Nat := 4983230072969 + 3 ^ 40 * 66942 * 2
def baseEnd_66942 : Nat := 20369435243485820928679

theorem tailTrace_66942 : CollatzResearch.WordTrace tailWord_66942 prefixEnd_66942 20369435243485820928679 := by
  unfold tailWord_66942
  simp only [CollatzResearch.WordTrace]
  refine ⟨305196915436005203562385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1627716882325361085666053 305196915436005203562385)
  ·
    refine ⟨228897686577003902671789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305196915436005203562385 228897686577003902671789)
    ·
      refine ⟨85836632466376463501921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 228897686577003902671789 85836632466376463501921)
      ·
        refine ⟨64377474349782347626441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85836632466376463501921 64377474349782347626441)
        ·
          refine ⟨48283105762336760719831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64377474349782347626441 48283105762336760719831)
          ·
            refine ⟨72424658643505141079747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48283105762336760719831 72424658643505141079747)
            ·
              refine ⟨108636987965257711619621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72424658643505141079747 108636987965257711619621)
              ·
                refine ⟨20369435243485820928679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108636987965257711619621 20369435243485820928679)
                ·
                  rfl

theorem cell19_66942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_66942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66942 prefixEnd_66942 := by exact prefixLift 66942
  have htrace : WordTrace (prefixWord ++ tailWord_66942) baseStart_66942 baseEnd_66942 := by
    simpa [prefixWord, tailWord_66942, baseEnd_66942] using wordTrace_append hprefix tailTrace_66942
  have hstable : (prefixWord ++ tailWord_66942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66942).length < 2 ^ (prefixWord ++ tailWord_66942).sum := by decide
  have hdescent : baseEnd_66942 < baseStart_66942 := by decide
  rcases family_descends (prefixWord ++ tailWord_66942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66946 : List Nat := [3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_66946 : Nat := 118140960795 + 66946 * 2 ^ 59
def prefixEnd_66946 : Nat := 4983230072969 + 3 ^ 40 * 66946 * 2
def baseEnd_66946 : Nat := 20370652382814996839779

theorem tailTrace_66946 : CollatzResearch.WordTrace tailWord_66946 prefixEnd_66946 20370652382814996839779 := by
  unfold tailWord_66946
  simp only [CollatzResearch.WordTrace]
  refine ⟨610430303868387577911173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1627814143649033541096461 610430303868387577911173)
  ·
    refine ⟨114455681975322670858345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 610430303868387577911173 114455681975322670858345)
    ·
      refine ⟨85841761481492003143759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114455681975322670858345 85841761481492003143759)
      ·
        refine ⟨128762642222238004715639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85841761481492003143759 128762642222238004715639)
        ·
          refine ⟨193143963333357007073459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128762642222238004715639 193143963333357007073459)
          ·
            refine ⟨289715945000035510610189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193143963333357007073459 289715945000035510610189)
            ·
              refine ⟨108643479375013316478821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289715945000035510610189 108643479375013316478821)
              ·
                refine ⟨20370652382814996839779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108643479375013316478821 20370652382814996839779)
                ·
                  rfl

theorem cell19_66946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_66946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66946 prefixEnd_66946 := by exact prefixLift 66946
  have htrace : WordTrace (prefixWord ++ tailWord_66946) baseStart_66946 baseEnd_66946 := by
    simpa [prefixWord, tailWord_66946, baseEnd_66946] using wordTrace_append hprefix tailTrace_66946
  have hstable : (prefixWord ++ tailWord_66946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66946).length < 2 ^ (prefixWord ++ tailWord_66946).sum := by decide
  have hdescent : baseEnd_66946 < baseStart_66946 := by decide
  rcases family_descends (prefixWord ++ tailWord_66946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_66948 : List Nat := [2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_66948 : Nat := 118140960795 + 66948 * 2 ^ 59
def prefixEnd_66948 : Nat := 4983230072969 + 3 ^ 40 * 66948 * 2
def baseEnd_66948 : Nat := 20371260952479584795329

theorem tailTrace_66948 : CollatzResearch.WordTrace tailWord_66948 prefixEnd_66948 20371260952479584795329 := by
  unfold tailWord_66948
  simp only [CollatzResearch.WordTrace]
  refine ⟨1220897080733152326608749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1627862774310869768811665 1220897080733152326608749)
  ·
    refine ⟨457836405274932122478281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1220897080733152326608749 457836405274932122478281)
    ·
      refine ⟨343377303956199091858711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 457836405274932122478281 343377303956199091858711)
      ·
        refine ⟨515065955934298637788067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343377303956199091858711 515065955934298637788067)
        ·
          refine ⟨772598933901447956682101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515065955934298637788067 772598933901447956682101)
          ·
            refine ⟨72431150053260745938947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 772598933901447956682101 72431150053260745938947)
            ·
              refine ⟨108646725079891118908421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72431150053260745938947 108646725079891118908421)
              ·
                refine ⟨20371260952479584795329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108646725079891118908421 20371260952479584795329)
                ·
                  rfl

theorem cell19_66948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_66948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_66948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_66948 prefixEnd_66948 := by exact prefixLift 66948
  have htrace : WordTrace (prefixWord ++ tailWord_66948) baseStart_66948 baseEnd_66948 := by
    simpa [prefixWord, tailWord_66948, baseEnd_66948] using wordTrace_append hprefix tailTrace_66948
  have hstable : (prefixWord ++ tailWord_66948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_66948).length < 2 ^ (prefixWord ++ tailWord_66948).sum := by decide
  have hdescent : baseEnd_66948 < baseStart_66948 := by decide
  rcases family_descends (prefixWord ++ tailWord_66948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67045 : List Nat := [1, 3, 1, 5, 1, 1, 7]
def baseStart_67045 : Nat := 118140960795 + 67045 * 2 ^ 59
def prefixEnd_67045 : Nat := 4983230072969 + 3 ^ 40 * 67045 * 2
def baseEnd_67045 : Nat := 6800258860404033546503

theorem tailTrace_67045 : CollatzResearch.WordTrace tailWord_67045 prefixEnd_67045 6800258860404033546503 := by
  unfold tailWord_67045
  simp only [CollatzResearch.WordTrace]
  refine ⟨2445332042114890219498589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1630221361409926812999059 2445332042114890219498589)
  ·
    refine ⟨916999515793083832311971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2445332042114890219498589 916999515793083832311971)
    ·
      refine ⟨1375499273689625748467957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916999515793083832311971 1375499273689625748467957)
      ·
        refine ⟨128953056908402413918871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1375499273689625748467957 128953056908402413918871)
        ·
          refine ⟨193429585362603620878307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128953056908402413918871 193429585362603620878307)
          ·
            refine ⟨290144378043905431317461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193429585362603620878307 290144378043905431317461)
            ·
              refine ⟨6800258860404033546503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 290144378043905431317461 6800258860404033546503)
              ·
                rfl

theorem cell19_67045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_67045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67045 prefixEnd_67045 := by exact prefixLift 67045
  have htrace : WordTrace (prefixWord ++ tailWord_67045) baseStart_67045 baseEnd_67045 := by
    simpa [prefixWord, tailWord_67045, baseEnd_67045] using wordTrace_append hprefix tailTrace_67045
  have hstable : (prefixWord ++ tailWord_67045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67045).length < 2 ^ (prefixWord ++ tailWord_67045).sum := by decide
  have hdescent : baseEnd_67045 < baseStart_67045 := by decide
  rcases family_descends (prefixWord ++ tailWord_67045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67062 : List Nat := [5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_67062 : Nat := 118140960795 + 67062 * 2 ^ 59
def prefixEnd_67062 : Nat := 4983230072969 + 3 ^ 40 * 67062 * 2
def baseEnd_67062 : Nat := 20405949423361098261685

theorem tailTrace_67062 : CollatzResearch.WordTrace tailWord_67062 prefixEnd_67062 20405949423361098261685 := by
  unfold tailWord_67062
  simp only [CollatzResearch.WordTrace]
  refine ⟨152872005190831382679215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1630634722035534748578293 152872005190831382679215)
  ·
    refine ⟨229308007786247074018823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152872005190831382679215 229308007786247074018823)
    ·
      refine ⟨343962011679370611028235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229308007786247074018823 343962011679370611028235)
      ·
        refine ⟨515943017519055916542353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343962011679370611028235 515943017519055916542353)
        ·
          refine ⟨386957263139291937406765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515943017519055916542353 386957263139291937406765)
          ·
            refine ⟨145108973677234476527537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386957263139291937406765 145108973677234476527537)
            ·
              refine ⟨108831730257925857395653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145108973677234476527537 108831730257925857395653)
              ·
                refine ⟨20405949423361098261685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108831730257925857395653 20405949423361098261685)
                ·
                  rfl

theorem cell19_67062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_67062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67062 prefixEnd_67062 := by exact prefixLift 67062
  have htrace : WordTrace (prefixWord ++ tailWord_67062) baseStart_67062 baseEnd_67062 := by
    simpa [prefixWord, tailWord_67062, baseEnd_67062] using wordTrace_append hprefix tailTrace_67062
  have hstable : (prefixWord ++ tailWord_67062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67062).length < 2 ^ (prefixWord ++ tailWord_67062).sum := by decide
  have hdescent : baseEnd_67062 < baseStart_67062 := by decide
  rcases family_descends (prefixWord ++ tailWord_67062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67064 : List Nat := [2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_67064 : Nat := 118140960795 + 67064 * 2 ^ 59
def prefixEnd_67064 : Nat := 4983230072969 + 3 ^ 40 * 67064 * 2
def baseEnd_67064 : Nat := 20406557993025686217235

theorem tailTrace_67064 : CollatzResearch.WordTrace tailWord_67064 prefixEnd_67064 20406557993025686217235 := by
  unfold tailWord_67064
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223012514523028232220123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1630683352697370976293497 1223012514523028232220123)
  ·
    refine ⟨1834518771784542348330185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1223012514523028232220123 1834518771784542348330185)
    ·
      refine ⟨1375889078838406761247639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1834518771784542348330185 1375889078838406761247639)
      ·
        refine ⟨2063833618257610141871459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375889078838406761247639 2063833618257610141871459)
        ·
          refine ⟨3095750427386415212807189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2063833618257610141871459 3095750427386415212807189)
          ·
            refine ⟨145113301283738213100337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3095750427386415212807189 145113301283738213100337)
            ·
              refine ⟨108834975962803659825253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145113301283738213100337 108834975962803659825253)
              ·
                refine ⟨20406557993025686217235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108834975962803659825253 20406557993025686217235)
                ·
                  rfl

theorem cell19_67064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_67064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67064 prefixEnd_67064 := by exact prefixLift 67064
  have htrace : WordTrace (prefixWord ++ tailWord_67064) baseStart_67064 baseEnd_67064 := by
    simpa [prefixWord, tailWord_67064, baseEnd_67064] using wordTrace_append hprefix tailTrace_67064
  have hstable : (prefixWord ++ tailWord_67064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67064).length < 2 ^ (prefixWord ++ tailWord_67064).sum := by decide
  have hdescent : baseEnd_67064 < baseStart_67064 := by decide
  rcases family_descends (prefixWord ++ tailWord_67064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67180 : List Nat := [2, 2, 1, 1, 3, 1, 1, 8]
def baseStart_67180 : Nat := 118140960795 + 67180 * 2 ^ 59
def prefixEnd_67180 : Nat := 4983230072969 + 3 ^ 40 * 67180 * 2
def baseEnd_67180 : Nat := 20441855033571787639141

theorem tailTrace_67180 : CollatzResearch.WordTrace tailWord_67180 prefixEnd_67180 20441855033571787639141 := by
  unfold tailWord_67180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225127948312904137831497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1633503931083872183775329 1225127948312904137831497)
  ·
    refine ⟨918845961234678103373623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1225127948312904137831497 918845961234678103373623)
    ·
      refine ⟨1378268941852017155060435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918845961234678103373623 1378268941852017155060435)
      ·
        refine ⟨2067403412778025732590653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378268941852017155060435 2067403412778025732590653)
        ·
          refine ⟨775276279791759649721495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2067403412778025732590653 775276279791759649721495)
          ·
            refine ⟨1162914419687639474582243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775276279791759649721495 1162914419687639474582243)
            ·
              refine ⟨1744371629531459211873365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162914419687639474582243 1744371629531459211873365)
              ·
                refine ⟨20441855033571787639141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1744371629531459211873365 20441855033571787639141)
                ·
                  rfl

theorem cell19_67180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_67180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67180 prefixEnd_67180 := by exact prefixLift 67180
  have htrace : WordTrace (prefixWord ++ tailWord_67180) baseStart_67180 baseEnd_67180 := by
    simpa [prefixWord, tailWord_67180, baseEnd_67180] using wordTrace_append hprefix tailTrace_67180
  have hstable : (prefixWord ++ tailWord_67180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67180).length < 2 ^ (prefixWord ++ tailWord_67180).sum := by decide
  have hdescent : baseEnd_67180 < baseStart_67180 := by decide
  rcases family_descends (prefixWord ++ tailWord_67180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67197 : List Nat := [1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_67197 : Nat := 118140960795 + 67197 * 2 ^ 59
def prefixEnd_67197 : Nat := 4983230072969 + 3 ^ 40 * 67197 * 2
def baseEnd_67197 : Nat := 20447027875720785261317

theorem tailTrace_67197 : CollatzResearch.WordTrace tailWord_67197 prefixEnd_67197 20447027875720785261317 := by
  unfold tailWord_67197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2450875937564220179031845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1633917291709480119354563 2450875937564220179031845)
  ·
    refine ⟨459539238293291283568471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2450875937564220179031845 459539238293291283568471)
    ·
      refine ⟨689308857439936925352707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 459539238293291283568471 689308857439936925352707)
      ·
        refine ⟨1033963286159905388029061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689308857439936925352707 1033963286159905388029061)
        ·
          refine ⟨193868116154982260255449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1033963286159905388029061 193868116154982260255449)
          ·
            refine ⟨145401087116236695191587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193868116154982260255449 145401087116236695191587)
            ·
              refine ⟨218101630674355042787381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145401087116236695191587 218101630674355042787381)
              ·
                refine ⟨20447027875720785261317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218101630674355042787381 20447027875720785261317)
                ·
                  rfl

theorem cell19_67197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_67197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67197 prefixEnd_67197 := by exact prefixLift 67197
  have htrace : WordTrace (prefixWord ++ tailWord_67197) baseStart_67197 baseEnd_67197 := by
    simpa [prefixWord, tailWord_67197, baseEnd_67197] using wordTrace_append hprefix tailTrace_67197
  have hstable : (prefixWord ++ tailWord_67197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67197).length < 2 ^ (prefixWord ++ tailWord_67197).sum := by decide
  have hdescent : baseEnd_67197 < baseStart_67197 := by decide
  rcases family_descends (prefixWord ++ tailWord_67197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67237 : List Nat := [1, 3, 1, 2, 1, 2, 3, 6]
def baseStart_67237 : Nat := 118140960795 + 67237 * 2 ^ 59
def prefixEnd_67237 : Nat := 4983230072969 + 3 ^ 40 * 67237 * 2
def baseEnd_67237 : Nat := 20459199269012544372319

theorem tailTrace_67237 : CollatzResearch.WordTrace tailWord_67237 prefixEnd_67237 20459199269012544372319 := by
  unfold tailWord_67237
  simp only [CollatzResearch.WordTrace]
  refine ⟨2452334857419307010487965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1634889904946204673658643 2452334857419307010487965)
  ·
    refine ⟨919625571532240128932987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2452334857419307010487965 919625571532240128932987)
    ·
      refine ⟨1379438357298360193399481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 919625571532240128932987 1379438357298360193399481)
      ·
        refine ⟨1034578767973770145049611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379438357298360193399481 1034578767973770145049611)
        ·
          refine ⟨1551868151960655217574417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1034578767973770145049611 1551868151960655217574417)
          ·
            refine ⟨1163901113970491413180813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1551868151960655217574417 1163901113970491413180813)
            ·
              refine ⟨436462917738934279942805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1163901113970491413180813 436462917738934279942805)
              ·
                refine ⟨20459199269012544372319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 436462917738934279942805 20459199269012544372319)
                ·
                  rfl

theorem cell19_67237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6].length) (baseStart_67237 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67237 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67237 prefixEnd_67237 := by exact prefixLift 67237
  have htrace : WordTrace (prefixWord ++ tailWord_67237) baseStart_67237 baseEnd_67237 := by
    simpa [prefixWord, tailWord_67237, baseEnd_67237] using wordTrace_append hprefix tailTrace_67237
  have hstable : (prefixWord ++ tailWord_67237).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67237).length < 2 ^ (prefixWord ++ tailWord_67237).sum := by decide
  have hdescent : baseEnd_67237 < baseStart_67237 := by decide
  rcases family_descends (prefixWord ++ tailWord_67237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67286 : List Nat := [5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_67286 : Nat := 118140960795 + 67286 * 2 ^ 59
def prefixEnd_67286 : Nat := 4983230072969 + 3 ^ 40 * 67286 * 2
def baseEnd_67286 : Nat := 20474109225794949283297

theorem tailTrace_67286 : CollatzResearch.WordTrace tailWord_67286 prefixEnd_67286 20474109225794949283297 := by
  unfold tailWord_67286
  simp only [CollatzResearch.WordTrace]
  refine ⟨153382627140111773688857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1636081356161192252681141 153382627140111773688857)
  ·
    refine ⟨115036970355083830266643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153382627140111773688857 115036970355083830266643)
    ·
      refine ⟨172555455532625745399965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115036970355083830266643 172555455532625745399965)
      ·
        refine ⟨64708295824734654524987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172555455532625745399965 64708295824734654524987)
        ·
          refine ⟨97062443737101981787481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64708295824734654524987 97062443737101981787481)
          ·
            refine ⟨72796832802826486340611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97062443737101981787481 72796832802826486340611)
            ·
              refine ⟨109195249204239729510917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72796832802826486340611 109195249204239729510917)
              ·
                refine ⟨20474109225794949283297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109195249204239729510917 20474109225794949283297)
                ·
                  rfl

theorem cell19_67286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_67286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67286 prefixEnd_67286 := by exact prefixLift 67286
  have htrace : WordTrace (prefixWord ++ tailWord_67286) baseStart_67286 baseEnd_67286 := by
    simpa [prefixWord, tailWord_67286, baseEnd_67286] using wordTrace_append hprefix tailTrace_67286
  have hstable : (prefixWord ++ tailWord_67286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67286).length < 2 ^ (prefixWord ++ tailWord_67286).sum := by decide
  have hdescent : baseEnd_67286 < baseStart_67286 := by decide
  rcases family_descends (prefixWord ++ tailWord_67286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67309 : List Nat := [1, 5, 1, 2, 1, 3, 3, 3]
def baseStart_67309 : Nat := 118140960795 + 67309 * 2 ^ 59
def prefixEnd_67309 : Nat := 4983230072969 + 3 ^ 40 * 67309 * 2
def baseEnd_67309 : Nat := 20481107776937710772123

theorem tailTrace_67309 : CollatzResearch.WordTrace tailWord_67309 prefixEnd_67309 20481107776937710772123 := by
  unfold tailWord_67309
  simp only [CollatzResearch.WordTrace]
  refine ⟨2454960913158463307108981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1636640608772308871405987 2454960913158463307108981)
  ·
    refine ⟨230152585608605935041467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2454960913158463307108981 230152585608605935041467)
    ·
      refine ⟨345228878412908902562201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230152585608605935041467 345228878412908902562201)
      ·
        refine ⟨258921658809681676921651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345228878412908902562201 258921658809681676921651)
        ·
          refine ⟨388382488214522515382477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258921658809681676921651 388382488214522515382477)
          ·
            refine ⟨145643433080445943268429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388382488214522515382477 145643433080445943268429)
            ·
              refine ⟨54616287405167228725661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145643433080445943268429 54616287405167228725661)
              ·
                refine ⟨20481107776937710772123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54616287405167228725661 20481107776937710772123)
                ·
                  rfl

theorem cell19_67309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 3].length) (baseStart_67309 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67309 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67309 prefixEnd_67309 := by exact prefixLift 67309
  have htrace : WordTrace (prefixWord ++ tailWord_67309) baseStart_67309 baseEnd_67309 := by
    simpa [prefixWord, tailWord_67309, baseEnd_67309] using wordTrace_append hprefix tailTrace_67309
  have hstable : (prefixWord ++ tailWord_67309).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67309).length < 2 ^ (prefixWord ++ tailWord_67309).sum := by decide
  have hdescent : baseEnd_67309 < baseStart_67309 := by decide
  rcases family_descends (prefixWord ++ tailWord_67309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67311 : List Nat := [1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_67311 : Nat := 118140960795 + 67311 * 2 ^ 59
def prefixEnd_67311 : Nat := 4983230072969 + 3 ^ 40 * 67311 * 2
def baseEnd_67311 : Nat := 20481716346602298727673

theorem tailTrace_67311 : CollatzResearch.WordTrace tailWord_67311 prefixEnd_67311 20481716346602298727673 := by
  unfold tailWord_67311
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455033859151217648681787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1636689239434145099121191 2455033859151217648681787)
  ·
    refine ⟨3682550788726826473022681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2455033859151217648681787 3682550788726826473022681)
    ·
      refine ⟨2761913091545119854767011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3682550788726826473022681 2761913091545119854767011)
      ·
        refine ⟨4142869637317679782150517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761913091545119854767011 4142869637317679782150517)
        ·
          refine ⟨388394028498532479576611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4142869637317679782150517 388394028498532479576611)
          ·
            refine ⟨582591042747798719364917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388394028498532479576611 582591042747798719364917)
            ·
              refine ⟨54617910257606129940461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 582591042747798719364917 54617910257606129940461)
              ·
                refine ⟨20481716346602298727673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54617910257606129940461 20481716346602298727673)
                ·
                  rfl

theorem cell19_67311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_67311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67311 prefixEnd_67311 := by exact prefixLift 67311
  have htrace : WordTrace (prefixWord ++ tailWord_67311) baseStart_67311 baseEnd_67311 := by
    simpa [prefixWord, tailWord_67311, baseEnd_67311] using wordTrace_append hprefix tailTrace_67311
  have hstable : (prefixWord ++ tailWord_67311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67311).length < 2 ^ (prefixWord ++ tailWord_67311).sum := by decide
  have hdescent : baseEnd_67311 < baseStart_67311 := by decide
  rcases family_descends (prefixWord ++ tailWord_67311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67330 : List Nat := [3, 4, 1, 1, 1, 1, 8]
def baseStart_67330 : Nat := 118140960795 + 67330 * 2 ^ 59
def prefixEnd_67330 : Nat := 4983230072969 + 3 ^ 40 * 67330 * 2
def baseEnd_67330 : Nat := 6829165919471961435133

theorem tailTrace_67330 : CollatzResearch.WordTrace tailWord_67330 prefixEnd_67330 6829165919471961435133 := by
  unfold tailWord_67330
  simp only [CollatzResearch.WordTrace]
  refine ⟨613931711520595973405861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1637151230721589262415629 613931711520595973405861)
  ·
    refine ⟨115112195910111745013599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 613931711520595973405861 115112195910111745013599)
    ·
      refine ⟨172668293865167617520399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115112195910111745013599 172668293865167617520399)
      ·
        refine ⟨259002440797751426280599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172668293865167617520399 259002440797751426280599)
        ·
          refine ⟨388503661196627139420899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259002440797751426280599 388503661196627139420899)
          ·
            refine ⟨582755491794940709131349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388503661196627139420899 582755491794940709131349)
            ·
              refine ⟨6829165919471961435133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 582755491794940709131349 6829165919471961435133)
              ·
                rfl

theorem cell19_67330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 8].length) (baseStart_67330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67330 prefixEnd_67330 := by exact prefixLift 67330
  have htrace : WordTrace (prefixWord ++ tailWord_67330) baseStart_67330 baseEnd_67330 := by
    simpa [prefixWord, tailWord_67330, baseEnd_67330] using wordTrace_append hprefix tailTrace_67330
  have hstable : (prefixWord ++ tailWord_67330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67330).length < 2 ^ (prefixWord ++ tailWord_67330).sum := by decide
  have hdescent : baseEnd_67330 < baseStart_67330 := by decide
  rcases family_descends (prefixWord ++ tailWord_67330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67368 : List Nat := [2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_67368 : Nat := 118140960795 + 67368 * 2 ^ 59
def prefixEnd_67368 : Nat := 4983230072969 + 3 ^ 40 * 67368 * 2
def baseEnd_67368 : Nat := 20499060582043055460851

theorem tailTrace_67368 : CollatzResearch.WordTrace tailWord_67368 prefixEnd_67368 20499060582043055460851 := by
  unfold tailWord_67368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228556409972358191753379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1638075213296477589004505 1228556409972358191753379)
  ·
    refine ⟨1842834614958537287630069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1228556409972358191753379 1842834614958537287630069)
    ·
      refine ⟨172765745152362870715319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1842834614958537287630069 172765745152362870715319)
      ·
        refine ⟨259148617728544306072979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172765745152362870715319 259148617728544306072979)
        ·
          refine ⟨388722926592816459109469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259148617728544306072979 388722926592816459109469)
          ·
            refine ⟨145771097472306172166051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388722926592816459109469 145771097472306172166051)
            ·
              refine ⟨218656646208459258249077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145771097472306172166051 218656646208459258249077)
              ·
                refine ⟨20499060582043055460851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218656646208459258249077 20499060582043055460851)
                ·
                  rfl

theorem cell19_67368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_67368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67368 prefixEnd_67368 := by exact prefixLift 67368
  have htrace : WordTrace (prefixWord ++ tailWord_67368) baseStart_67368 baseEnd_67368 := by
    simpa [prefixWord, tailWord_67368, baseEnd_67368] using wordTrace_append hprefix tailTrace_67368
  have hstable : (prefixWord ++ tailWord_67368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67368).length < 2 ^ (prefixWord ++ tailWord_67368).sum := by decide
  have hdescent : baseEnd_67368 < baseStart_67368 := by decide
  rcases family_descends (prefixWord ++ tailWord_67368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67385 : List Nat := [1, 2, 1, 7, 1, 2, 5]
def baseStart_67385 : Nat := 118140960795 + 67385 * 2 ^ 59
def prefixEnd_67385 : Nat := 4983230072969 + 3 ^ 40 * 67385 * 2
def baseEnd_67385 : Nat := 6834744474730684361009

theorem tailTrace_67385 : CollatzResearch.WordTrace tailWord_67385 prefixEnd_67385 6834744474730684361009 := by
  unfold tailWord_67385
  simp only [CollatzResearch.WordTrace]
  refine ⟨2457732860883128286875609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1638488573922085524583739 2457732860883128286875609)
  ·
    refine ⟨1843299645662346215156707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2457732860883128286875609 1843299645662346215156707)
    ·
      refine ⟨2764949468493519322735061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1843299645662346215156707 2764949468493519322735061)
      ·
        refine ⟨64803503167816859126603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 2764949468493519322735061 64803503167816859126603)
        ·
          refine ⟨97205254751725288689905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64803503167816859126603 97205254751725288689905)
          ·
            refine ⟨72903941063793966517429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97205254751725288689905 72903941063793966517429)
            ·
              refine ⟨6834744474730684361009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72903941063793966517429 6834744474730684361009)
              ·
                rfl

theorem cell19_67385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 5].length) (baseStart_67385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67385 prefixEnd_67385 := by exact prefixLift 67385
  have htrace : WordTrace (prefixWord ++ tailWord_67385) baseStart_67385 baseEnd_67385 := by
    simpa [prefixWord, tailWord_67385, baseEnd_67385] using wordTrace_append hprefix tailTrace_67385
  have hstable : (prefixWord ++ tailWord_67385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67385).length < 2 ^ (prefixWord ++ tailWord_67385).sum := by decide
  have hdescent : baseEnd_67385 < baseStart_67385 := by decide
  rcases family_descends (prefixWord ++ tailWord_67385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67554 : List Nat := [3, 3, 3, 1, 3, 1, 5]
def baseStart_67554 : Nat := 118140960795 + 67554 * 2 ^ 59
def prefixEnd_67554 : Nat := 4983230072969 + 3 ^ 40 * 67554 * 2
def baseEnd_67554 : Nat := 6851885853616578442337

theorem tailTrace_67554 : CollatzResearch.WordTrace tailWord_67554 prefixEnd_67554 6851885853616578442337 := by
  unfold tailWord_67554
  simp only [CollatzResearch.WordTrace]
  refine ⟨615974199317717537444429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1642597864847246766518477 615974199317717537444429)
  ·
    refine ⟨230990324744144076541661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 615974199317717537444429 230990324744144076541661)
    ·
      refine ⟨86621371779054028703123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230990324744144076541661 86621371779054028703123)
      ·
        refine ⟨129932057668581043054685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86621371779054028703123 129932057668581043054685)
        ·
          refine ⟨48724521625717891145507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129932057668581043054685 48724521625717891145507)
          ·
            refine ⟨73086782438576836718261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48724521625717891145507 73086782438576836718261)
            ·
              refine ⟨6851885853616578442337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73086782438576836718261 6851885853616578442337)
              ·
                rfl

theorem cell19_67554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_67554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67554 prefixEnd_67554 := by exact prefixLift 67554
  have htrace : WordTrace (prefixWord ++ tailWord_67554) baseStart_67554 baseEnd_67554 := by
    simpa [prefixWord, tailWord_67554, baseEnd_67554] using wordTrace_append hprefix tailTrace_67554
  have hstable : (prefixWord ++ tailWord_67554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67554).length < 2 ^ (prefixWord ++ tailWord_67554).sum := by decide
  have hdescent : baseEnd_67554 < baseStart_67554 := by decide
  rcases family_descends (prefixWord ++ tailWord_67554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67598 : List Nat := [4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_67598 : Nat := 118140960795 + 67598 * 2 ^ 59
def prefixEnd_67598 : Nat := 4983230072969 + 3 ^ 40 * 67598 * 2
def baseEnd_67598 : Nat := 20569046093470670349113

theorem tailTrace_67598 : CollatzResearch.WordTrace tailWord_67598 prefixEnd_67598 20569046093470670349113 := by
  unfold tailWord_67598
  simp only [CollatzResearch.WordTrace]
  refine ⟨308187701138933208047431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1643667739407643776252965 308187701138933208047431)
  ·
    refine ⟨462281551708399812071147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 308187701138933208047431 462281551708399812071147)
    ·
      refine ⟨693422327562599718106721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462281551708399812071147 693422327562599718106721)
      ·
        refine ⟨520066745671949788580041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693422327562599718106721 520066745671949788580041)
        ·
          refine ⟨390050059253962341435031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520066745671949788580041 390050059253962341435031)
          ·
            refine ⟨585075088880943512152547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390050059253962341435031 585075088880943512152547)
            ·
              refine ⟨877612633321415268228821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585075088880943512152547 877612633321415268228821)
              ·
                refine ⟨20569046093470670349113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 877612633321415268228821 20569046093470670349113)
                ·
                  rfl

theorem cell19_67598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_67598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67598 prefixEnd_67598 := by exact prefixLift 67598
  have htrace : WordTrace (prefixWord ++ tailWord_67598) baseStart_67598 baseEnd_67598 := by
    simpa [prefixWord, tailWord_67598, baseEnd_67598] using wordTrace_append hprefix tailTrace_67598
  have hstable : (prefixWord ++ tailWord_67598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67598).length < 2 ^ (prefixWord ++ tailWord_67598).sum := by decide
  have hdescent : baseEnd_67598 < baseStart_67598 := by decide
  rcases family_descends (prefixWord ++ tailWord_67598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67617 : List Nat := [1, 2, 3, 2, 4, 7]
def baseStart_67617 : Nat := 118140960795 + 67617 * 2 ^ 59
def prefixEnd_67617 : Nat := 4983230072969 + 3 ^ 40 * 67617 * 2
def baseEnd_67617 : Nat := 2286091945031583991871

theorem tailTrace_67617 : CollatzResearch.WordTrace tailWord_67617 prefixEnd_67617 2286091945031583991871 := by
  unfold tailWord_67617
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466194596042631909321105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1644129730695087939547403 2466194596042631909321105)
  ·
    refine ⟨1849645947031973931990829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2466194596042631909321105 1849645947031973931990829)
    ·
      refine ⟨693617230136990224496561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1849645947031973931990829 693617230136990224496561)
      ·
        refine ⟨520212922602742668372421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693617230136990224496561 520212922602742668372421)
        ·
          refine ⟨97539922988014250319829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 520212922602742668372421 97539922988014250319829)
          ·
            refine ⟨2286091945031583991871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 97539922988014250319829 2286091945031583991871)
            ·
              rfl

theorem cell19_67617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_67617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67617 prefixEnd_67617 := by exact prefixLift 67617
  have htrace : WordTrace (prefixWord ++ tailWord_67617) baseStart_67617 baseEnd_67617 := by
    simpa [prefixWord, tailWord_67617, baseEnd_67617] using wordTrace_append hprefix tailTrace_67617
  have hstable : (prefixWord ++ tailWord_67617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67617).length < 2 ^ (prefixWord ++ tailWord_67617).sum := by decide
  have hdescent : baseEnd_67617 < baseStart_67617 := by decide
  rcases family_descends (prefixWord ++ tailWord_67617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67634 : List Nat := [3, 2, 1, 1, 2, 5, 1, 4]
def baseStart_67634 : Nat := 118140960795 + 67634 * 2 ^ 59
def prefixEnd_67634 : Nat := 4983230072969 + 3 ^ 40 * 67634 * 2
def baseEnd_67634 : Nat := 20580000347433253549015

theorem tailTrace_67634 : CollatzResearch.WordTrace tailWord_67634 prefixEnd_67634 20580000347433253549015 := by
  unfold tailWord_67634
  simp only [CollatzResearch.WordTrace]
  refine ⟨616703659245260953172489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1644543091320695875126637 616703659245260953172489)
  ·
    refine ⟨462527744433945714879367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 616703659245260953172489 462527744433945714879367)
    ·
      refine ⟨693791616650918572319051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462527744433945714879367 693791616650918572319051)
      ·
        refine ⟨1040687424976377858478577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693791616650918572319051 1040687424976377858478577)
        ·
          refine ⟨780515568732283393858933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040687424976377858478577 780515568732283393858933)
          ·
            refine ⟨73173334568651568174275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 780515568732283393858933 73173334568651568174275)
            ·
              refine ⟨109760001852977352261413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73173334568651568174275 109760001852977352261413)
              ·
                refine ⟨20580000347433253549015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109760001852977352261413 20580000347433253549015)
                ·
                  rfl

theorem cell19_67634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_67634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67634 prefixEnd_67634 := by exact prefixLift 67634
  have htrace : WordTrace (prefixWord ++ tailWord_67634) baseStart_67634 baseEnd_67634 := by
    simpa [prefixWord, tailWord_67634, baseEnd_67634] using wordTrace_append hprefix tailTrace_67634
  have hstable : (prefixWord ++ tailWord_67634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67634).length < 2 ^ (prefixWord ++ tailWord_67634).sum := by decide
  have hdescent : baseEnd_67634 < baseStart_67634 := by decide
  rcases family_descends (prefixWord ++ tailWord_67634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67670 : List Nat := [5, 2, 2, 1, 1, 2, 6]
def baseStart_67670 : Nat := 118140960795 + 67670 * 2 ^ 59
def prefixEnd_67670 : Nat := 4983230072969 + 3 ^ 40 * 67670 * 2
def baseEnd_67670 : Nat := 6863651533798612249639

theorem tailTrace_67670 : CollatzResearch.WordTrace tailWord_67670 prefixEnd_67670 6863651533798612249639 := by
  unfold tailWord_67670
  simp only [CollatzResearch.WordTrace]
  refine ⟨154257979053163872562529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1645418443233747974000309 154257979053163872562529)
  ·
    refine ⟨115693484289872904421897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154257979053163872562529 115693484289872904421897)
    ·
      refine ⟨86770113217404678316423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115693484289872904421897 86770113217404678316423)
      ·
        refine ⟨130155169826107017474635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86770113217404678316423 130155169826107017474635)
        ·
          refine ⟨195232754739160526211953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130155169826107017474635 195232754739160526211953)
          ·
            refine ⟨146424566054370394658965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195232754739160526211953 146424566054370394658965)
            ·
              refine ⟨6863651533798612249639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146424566054370394658965 6863651533798612249639)
              ·
                rfl

theorem cell19_67670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_67670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67670 prefixEnd_67670 := by exact prefixLift 67670
  have htrace : WordTrace (prefixWord ++ tailWord_67670) baseStart_67670 baseEnd_67670 := by
    simpa [prefixWord, tailWord_67670, baseEnd_67670] using wordTrace_append hprefix tailTrace_67670
  have hstable : (prefixWord ++ tailWord_67670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67670).length < 2 ^ (prefixWord ++ tailWord_67670).sum := by decide
  have hdescent : baseEnd_67670 < baseStart_67670 := by decide
  rcases family_descends (prefixWord ++ tailWord_67670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67693 : List Nat := [1, 5, 1, 1, 2, 1, 2, 6]
def baseStart_67693 : Nat := 118140960795 + 67693 * 2 ^ 59
def prefixEnd_67693 : Nat := 4983230072969 + 3 ^ 40 * 67693 * 2
def baseEnd_67693 : Nat := 20597953152538598237743

theorem tailTrace_67693 : CollatzResearch.WordTrace tailWord_67693 prefixEnd_67693 20597953152538598237743 := by
  unfold tailWord_67693
  simp only [CollatzResearch.WordTrace]
  refine ⟨2468966543767296889087733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1645977695844864592725155 2468966543767296889087733)
  ·
    refine ⟨231465613478184083351975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2468966543767296889087733 231465613478184083351975)
    ·
      refine ⟨347198420217276125027963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231465613478184083351975 347198420217276125027963)
      ·
        refine ⟨520797630325914187541945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347198420217276125027963 520797630325914187541945)
        ·
          refine ⟨390598222744435640656459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520797630325914187541945 390598222744435640656459)
          ·
            refine ⟨585897334116653460984689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390598222744435640656459 585897334116653460984689)
            ·
              refine ⟨439423000587490095738517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585897334116653460984689 439423000587490095738517)
              ·
                refine ⟨20597953152538598237743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 439423000587490095738517 20597953152538598237743)
                ·
                  rfl

theorem cell19_67693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_67693 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67693 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67693 prefixEnd_67693 := by exact prefixLift 67693
  have htrace : WordTrace (prefixWord ++ tailWord_67693) baseStart_67693 baseEnd_67693 := by
    simpa [prefixWord, tailWord_67693, baseEnd_67693] using wordTrace_append hprefix tailTrace_67693
  have hstable : (prefixWord ++ tailWord_67693).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67693).length < 2 ^ (prefixWord ++ tailWord_67693).sum := by decide
  have hdescent : baseEnd_67693 < baseStart_67693 := by decide
  rcases family_descends (prefixWord ++ tailWord_67693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67748 : List Nat := [2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_67748 : Nat := 118140960795 + 67748 * 2 ^ 59
def prefixEnd_67748 : Nat := 4983230072969 + 3 ^ 40 * 67748 * 2
def baseEnd_67748 : Nat := 20614688818314767015371

theorem tailTrace_67748 : CollatzResearch.WordTrace tailWord_67748 prefixEnd_67748 20614688818314767015371 := by
  unfold tailWord_67748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1235486279284020641169949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1647315039045360854893265 1235486279284020641169949)
  ·
    refine ⟨463307354731507740438731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1235486279284020641169949 463307354731507740438731)
    ·
      refine ⟨694961032097261610658097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463307354731507740438731 694961032097261610658097)
      ·
        refine ⟨521220774072946207993573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 694961032097261610658097 521220774072946207993573)
        ·
          refine ⟨97728895138677413998795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 521220774072946207993573 97728895138677413998795)
          ·
            refine ⟨146593342708016120998193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97728895138677413998795 146593342708016120998193)
            ·
              refine ⟨109945007031012090748645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146593342708016120998193 109945007031012090748645)
              ·
                refine ⟨20614688818314767015371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109945007031012090748645 20614688818314767015371)
                ·
                  rfl

theorem cell19_67748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_67748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67748 prefixEnd_67748 := by exact prefixLift 67748
  have htrace : WordTrace (prefixWord ++ tailWord_67748) baseStart_67748 baseEnd_67748 := by
    simpa [prefixWord, tailWord_67748, baseEnd_67748] using wordTrace_append hprefix tailTrace_67748
  have hstable : (prefixWord ++ tailWord_67748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67748).length < 2 ^ (prefixWord ++ tailWord_67748).sum := by decide
  have hdescent : baseEnd_67748 < baseStart_67748 := by decide
  rcases family_descends (prefixWord ++ tailWord_67748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67771 : List Nat := [1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_67771 : Nat := 118140960795 + 67771 * 2 ^ 59
def prefixEnd_67771 : Nat := 4983230072969 + 3 ^ 40 * 67771 * 2
def baseEnd_67771 : Nat := 20621687369457528504197

theorem tailTrace_67771 : CollatzResearch.WordTrace tailWord_67771 prefixEnd_67771 20621687369457528504197 := by
  unfold tailWord_67771
  simp only [CollatzResearch.WordTrace]
  refine ⟨2471811437484716210427167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1647874291656477473618111 2471811437484716210427167)
  ·
    refine ⟨3707717156227074315640751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2471811437484716210427167 3707717156227074315640751)
    ·
      refine ⟨5561575734340611473461127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3707717156227074315640751 5561575734340611473461127)
      ·
        refine ⟨8342363601510917210191691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5561575734340611473461127 8342363601510917210191691)
        ·
          refine ⟨12513545402266375815287537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342363601510917210191691 12513545402266375815287537)
          ·
            refine ⟨9385159051699781861465653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12513545402266375815287537 9385159051699781861465653)
            ·
              refine ⟨879858661096854549512405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9385159051699781861465653 879858661096854549512405)
              ·
                refine ⟨20621687369457528504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 879858661096854549512405 20621687369457528504197)
                ·
                  rfl

theorem cell19_67771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_67771 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67771 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67771 prefixEnd_67771 := by exact prefixLift 67771
  have htrace : WordTrace (prefixWord ++ tailWord_67771) baseStart_67771 baseEnd_67771 := by
    simpa [prefixWord, tailWord_67771, baseEnd_67771] using wordTrace_append hprefix tailTrace_67771
  have hstable : (prefixWord ++ tailWord_67771).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67771).length < 2 ^ (prefixWord ++ tailWord_67771).sum := by decide
  have hdescent : baseEnd_67771 < baseStart_67771 := by decide
  rcases family_descends (prefixWord ++ tailWord_67771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67788 : List Nat := [2, 2, 1, 6, 8]
def baseStart_67788 : Nat := 118140960795 + 67788 * 2 ^ 59
def prefixEnd_67788 : Nat := 4983230072969 + 3 ^ 40 * 67788 * 2
def baseEnd_67788 : Nat := 763957785615056523199

theorem tailTrace_67788 : CollatzResearch.WordTrace tailWord_67788 prefixEnd_67788 763957785615056523199 := by
  unfold tailWord_67788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236215739211564056898009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1648287652282085409197345 1236215739211564056898009)
  ·
    refine ⟨927161804408673042673507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1236215739211564056898009 927161804408673042673507)
    ·
      refine ⟨1390742706613009564010261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 927161804408673042673507 1390742706613009564010261)
      ·
        refine ⟨65191064372484823312981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1390742706613009564010261 65191064372484823312981)
        ·
          refine ⟨763957785615056523199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 65191064372484823312981 763957785615056523199)
          ·
            rfl

theorem cell19_67788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 8].length) (baseStart_67788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67788 prefixEnd_67788 := by exact prefixLift 67788
  have htrace : WordTrace (prefixWord ++ tailWord_67788) baseStart_67788 baseEnd_67788 := by
    simpa [prefixWord, tailWord_67788, baseEnd_67788] using wordTrace_append hprefix tailTrace_67788
  have hstable : (prefixWord ++ tailWord_67788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67788).length < 2 ^ (prefixWord ++ tailWord_67788).sum := by decide
  have hdescent : baseEnd_67788 < baseStart_67788 := by decide
  rcases family_descends (prefixWord ++ tailWord_67788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67805 : List Nat := [1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_67805 : Nat := 118140960795 + 67805 * 2 ^ 59
def prefixEnd_67805 : Nat := 4983230072969 + 3 ^ 40 * 67805 * 2
def baseEnd_67805 : Nat := 20632033053755523748549

theorem tailTrace_67805 : CollatzResearch.WordTrace tailWord_67805 prefixEnd_67805 20632033053755523748549 := by
  unfold tailWord_67805
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473051519361540017164869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1648701012907693344776579 2473051519361540017164869)
  ·
    refine ⟨463697159880288753218413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2473051519361540017164869 463697159880288753218413)
    ·
      refine ⟨173886434955108282456905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 463697159880288753218413 173886434955108282456905)
      ·
        refine ⟨130414826216331211842679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173886434955108282456905 130414826216331211842679)
        ·
          refine ⟨195622239324496817764019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130414826216331211842679 195622239324496817764019)
          ·
            refine ⟨293433358986745226646029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195622239324496817764019 293433358986745226646029)
            ·
              refine ⟨110037509620029459992261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293433358986745226646029 110037509620029459992261)
              ·
                refine ⟨20632033053755523748549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110037509620029459992261 20632033053755523748549)
                ·
                  rfl

theorem cell19_67805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_67805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67805 prefixEnd_67805 := by exact prefixLift 67805
  have htrace : WordTrace (prefixWord ++ tailWord_67805) baseStart_67805 baseEnd_67805 := by
    simpa [prefixWord, tailWord_67805, baseEnd_67805] using wordTrace_append hprefix tailTrace_67805
  have hstable : (prefixWord ++ tailWord_67805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67805).length < 2 ^ (prefixWord ++ tailWord_67805).sum := by decide
  have hdescent : baseEnd_67805 < baseStart_67805 := by decide
  rcases family_descends (prefixWord ++ tailWord_67805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67902 : List Nat := [4, 2, 1, 2, 1, 2, 7]
def baseStart_67902 : Nat := 118140960795 + 67902 * 2 ^ 59
def prefixEnd_67902 : Nat := 4983230072969 + 3 ^ 40 * 67902 * 2
def baseEnd_67902 : Nat := 6887182894162679864243

theorem tailTrace_67902 : CollatzResearch.WordTrace tailWord_67902 prefixEnd_67902 6887182894162679864243 := by
  unfold tailWord_67902
  simp only [CollatzResearch.WordTrace]
  refine ⟨309573675001265697930745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1651059600006750388963973 309573675001265697930745)
  ·
    refine ⟨232180256250949273448059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 309573675001265697930745 232180256250949273448059)
    ·
      refine ⟨348270384376423910172089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232180256250949273448059 348270384376423910172089)
      ·
        refine ⟨261202788282317932629067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 348270384376423910172089 261202788282317932629067)
        ·
          refine ⟨391804182423476898943601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261202788282317932629067 391804182423476898943601)
          ·
            refine ⟨293853136817607674207701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391804182423476898943601 293853136817607674207701)
            ·
              refine ⟨6887182894162679864243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 293853136817607674207701 6887182894162679864243)
              ·
                rfl

theorem cell19_67902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_67902 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67902 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67902 prefixEnd_67902 := by exact prefixLift 67902
  have htrace : WordTrace (prefixWord ++ tailWord_67902) baseStart_67902 baseEnd_67902 := by
    simpa [prefixWord, tailWord_67902, baseEnd_67902] using wordTrace_append hprefix tailTrace_67902
  have hstable : (prefixWord ++ tailWord_67902).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67902).length < 2 ^ (prefixWord ++ tailWord_67902).sum := by decide
  have hdescent : baseEnd_67902 < baseStart_67902 := by decide
  rcases family_descends (prefixWord ++ tailWord_67902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_67921 : List Nat := [1, 2, 2, 1, 4, 3, 2, 4]
def baseStart_67921 : Nat := 118140960795 + 67921 * 2 ^ 59
def prefixEnd_67921 : Nat := 4983230072969 + 3 ^ 40 * 67921 * 2
def baseEnd_67921 : Nat := 20667330094301625170455

theorem tailTrace_67921 : CollatzResearch.WordTrace tailWord_67921 prefixEnd_67921 20667330094301625170455 := by
  unfold tailWord_67921
  simp only [CollatzResearch.WordTrace]
  refine ⟨2477282386941291828387617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1651521591294194552258411 2477282386941291828387617)
  ·
    refine ⟨1857961790205968871290713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2477282386941291828387617 1857961790205968871290713)
    ·
      refine ⟨1393471342654476653468035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1857961790205968871290713 1393471342654476653468035)
      ·
        refine ⟨2090207013981714980202053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393471342654476653468035 2090207013981714980202053)
        ·
          refine ⟨391913815121571558787885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2090207013981714980202053 391913815121571558787885)
          ·
            refine ⟨146967680670589334545457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391913815121571558787885 146967680670589334545457)
            ·
              refine ⟨110225760502942000909093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146967680670589334545457 110225760502942000909093)
              ·
                refine ⟨20667330094301625170455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110225760502942000909093 20667330094301625170455)
                ·
                  rfl

theorem cell19_67921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4].length) (baseStart_67921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_67921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_67921 prefixEnd_67921 := by exact prefixLift 67921
  have htrace : WordTrace (prefixWord ++ tailWord_67921) baseStart_67921 baseEnd_67921 := by
    simpa [prefixWord, tailWord_67921, baseEnd_67921] using wordTrace_append hprefix tailTrace_67921
  have hstable : (prefixWord ++ tailWord_67921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_67921).length < 2 ^ (prefixWord ++ tailWord_67921).sum := by decide
  have hdescent : baseEnd_67921 < baseStart_67921 := by decide
  rcases family_descends (prefixWord ++ tailWord_67921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68018 : List Nat := [3, 2, 1, 1, 1, 1, 10]
def baseStart_68018 : Nat := 118140960795 + 68018 * 2 ^ 59
def prefixEnd_68018 : Nat := 4983230072969 + 3 ^ 40 * 68018 * 2
def baseEnd_68018 : Nat := 6898948574344713671545

theorem tailTrace_68018 : CollatzResearch.WordTrace tailWord_68018 prefixEnd_68018 6898948574344713671545 := by
  unfold tailWord_68018
  simp only [CollatzResearch.WordTrace]
  refine ⟨620205066897469348667177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1653880178393251596445805 620205066897469348667177)
  ·
    refine ⟨465153800173102011500383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 620205066897469348667177 465153800173102011500383)
    ·
      refine ⟨697730700259653017250575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465153800173102011500383 697730700259653017250575)
      ·
        refine ⟨1046596050389479525875863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697730700259653017250575 1046596050389479525875863)
        ·
          refine ⟨1569894075584219288813795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046596050389479525875863 1569894075584219288813795)
          ·
            refine ⟨2354841113376328933220693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569894075584219288813795 2354841113376328933220693)
            ·
              refine ⟨6898948574344713671545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2354841113376328933220693 6898948574344713671545)
              ·
                rfl

theorem cell19_68018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_68018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68018 prefixEnd_68018 := by exact prefixLift 68018
  have htrace : WordTrace (prefixWord ++ tailWord_68018) baseStart_68018 baseEnd_68018 := by
    simpa [prefixWord, tailWord_68018, baseEnd_68018] using wordTrace_append hprefix tailTrace_68018
  have hstable : (prefixWord ++ tailWord_68018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68018).length < 2 ^ (prefixWord ++ tailWord_68018).sum := by decide
  have hdescent : baseEnd_68018 < baseStart_68018 := by decide
  rcases family_descends (prefixWord ++ tailWord_68018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68052 : List Nat := [2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_68052 : Nat := 118140960795 + 68052 * 2 ^ 59
def prefixEnd_68052 : Nat := 4983230072969 + 3 ^ 40 * 68052 * 2
def baseEnd_68052 : Nat := 20707191407332136258987

theorem tailTrace_68052 : CollatzResearch.WordTrace tailWord_68052 prefixEnd_68052 20707191407332136258987 := by
  unfold tailWord_68052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241030174733350600703205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1654706899644467467604273 1241030174733350600703205)
  ·
    refine ⟨232693157762503237631851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1241030174733350600703205 232693157762503237631851)
    ·
      refine ⟨349039736643754856447777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232693157762503237631851 349039736643754856447777)
      ·
        refine ⟨261779802482816142335833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 349039736643754856447777 261779802482816142335833)
        ·
          refine ⟨196334851862112106751875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 261779802482816142335833 196334851862112106751875)
          ·
            refine ⟨294502277793168160127813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196334851862112106751875 294502277793168160127813)
            ·
              refine ⟨55219177086219030023965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 294502277793168160127813 55219177086219030023965)
              ·
                refine ⟨20707191407332136258987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55219177086219030023965 20707191407332136258987)
                ·
                  rfl

theorem cell19_68052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_68052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68052 prefixEnd_68052 := by exact prefixLift 68052
  have htrace : WordTrace (prefixWord ++ tailWord_68052) baseStart_68052 baseEnd_68052 := by
    simpa [prefixWord, tailWord_68052, baseEnd_68052] using wordTrace_append hprefix tailTrace_68052
  have hstable : (prefixWord ++ tailWord_68052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68052).length < 2 ^ (prefixWord ++ tailWord_68052).sum := by decide
  have hdescent : baseEnd_68052 < baseStart_68052 := by decide
  rcases family_descends (prefixWord ++ tailWord_68052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68141 : List Nat := [1, 5, 4, 1, 2, 1, 1, 4]
def baseStart_68141 : Nat := 118140960795 + 68141 * 2 ^ 59
def prefixEnd_68141 : Nat := 4983230072969 + 3 ^ 40 * 68141 * 2
def baseEnd_68141 : Nat := 20734272757406300280967

theorem tailTrace_68141 : CollatzResearch.WordTrace tailWord_68141 prefixEnd_68141 20734272757406300280967 := by
  unfold tailWord_68141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485306446144269401396277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1656870964096179600930851 2485306446144269401396277)
  ·
    refine ⟨232997479326025256380901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2485306446144269401396277 232997479326025256380901)
    ·
      refine ⟨43687027373629735571419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 232997479326025256380901 43687027373629735571419)
      ·
        refine ⟨65530541060444603357129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43687027373629735571419 65530541060444603357129)
        ·
          refine ⟨49147905795333452517847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65530541060444603357129 49147905795333452517847)
          ·
            refine ⟨73721858693000178776771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49147905795333452517847 73721858693000178776771)
            ·
              refine ⟨110582788039500268165157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73721858693000178776771 110582788039500268165157)
              ·
                refine ⟨20734272757406300280967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110582788039500268165157 20734272757406300280967)
                ·
                  rfl

theorem cell19_68141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_68141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68141 prefixEnd_68141 := by exact prefixLift 68141
  have htrace : WordTrace (prefixWord ++ tailWord_68141) baseStart_68141 baseEnd_68141 := by
    simpa [prefixWord, tailWord_68141, baseEnd_68141] using wordTrace_append hprefix tailTrace_68141
  have hstable : (prefixWord ++ tailWord_68141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68141).length < 2 ^ (prefixWord ++ tailWord_68141).sum := by decide
  have hdescent : baseEnd_68141 < baseStart_68141 := by decide
  rcases family_descends (prefixWord ++ tailWord_68141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68221 : List Nat := [1, 4, 1, 1, 6, 1, 2, 3]
def baseStart_68221 : Nat := 118140960795 + 68221 * 2 ^ 59
def prefixEnd_68221 : Nat := 4983230072969 + 3 ^ 40 * 68221 * 2
def baseEnd_68221 : Nat := 20758615543989818502971

theorem tailTrace_68221 : CollatzResearch.WordTrace tailWord_68221 prefixEnd_68221 20758615543989818502971 := by
  unfold tailWord_68221
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488224285854443064308517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1658816190569628709539011 2488224285854443064308517)
  ·
    refine ⟨466542053597708074557847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2488224285854443064308517 466542053597708074557847)
    ·
      refine ⟨699813080396562111836771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466542053597708074557847 699813080396562111836771)
      ·
        refine ⟨1049719620594843167755157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699813080396562111836771 1049719620594843167755157)
        ·
          refine ⟨49205607215383273488523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1049719620594843167755157 49205607215383273488523)
          ·
            refine ⟨73808410823074910232785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49205607215383273488523 73808410823074910232785)
            ·
              refine ⟨55356308117306182674589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73808410823074910232785 55356308117306182674589)
              ·
                refine ⟨20758615543989818502971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55356308117306182674589 20758615543989818502971)
                ·
                  rfl

theorem cell19_68221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_68221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68221 prefixEnd_68221 := by exact prefixLift 68221
  have htrace : WordTrace (prefixWord ++ tailWord_68221) baseStart_68221 baseEnd_68221 := by
    simpa [prefixWord, tailWord_68221, baseEnd_68221] using wordTrace_append hprefix tailTrace_68221
  have hstable : (prefixWord ++ tailWord_68221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68221).length < 2 ^ (prefixWord ++ tailWord_68221).sum := by decide
  have hdescent : baseEnd_68221 < baseStart_68221 := by decide
  rcases family_descends (prefixWord ++ tailWord_68221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68244 : List Nat := [2, 4, 2, 2, 1, 1, 7]
def baseStart_68244 : Nat := 118140960795 + 68244 * 2 ^ 59
def prefixEnd_68244 : Nat := 4983230072969 + 3 ^ 40 * 68244 * 2
def baseEnd_68244 : Nat := 6921871365044193330599

theorem tailTrace_68244 : CollatzResearch.WordTrace tailWord_68244 prefixEnd_68244 6921871365044193330599 := by
  unfold tailWord_68244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1244531582385558996197893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1659375443180745328263857 1244531582385558996197893)
  ·
    refine ⟨233349671697292311787105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1244531582385558996197893 233349671697292311787105)
    ·
      refine ⟨175012253772969233840329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 233349671697292311787105 175012253772969233840329)
      ·
        refine ⟨131259190329726925380247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175012253772969233840329 131259190329726925380247)
        ·
          refine ⟨196888785494590388070371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131259190329726925380247 196888785494590388070371)
          ·
            refine ⟨295333178241885582105557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196888785494590388070371 295333178241885582105557)
            ·
              refine ⟨6921871365044193330599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 295333178241885582105557 6921871365044193330599)
              ·
                rfl

theorem cell19_68244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_68244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68244 prefixEnd_68244 := by exact prefixLift 68244
  have htrace : WordTrace (prefixWord ++ tailWord_68244) baseStart_68244 baseEnd_68244 := by
    simpa [prefixWord, tailWord_68244, baseEnd_68244] using wordTrace_append hprefix tailTrace_68244
  have hstable : (prefixWord ++ tailWord_68244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68244).length < 2 ^ (prefixWord ++ tailWord_68244).sum := by decide
  have hdescent : baseEnd_68244 < baseStart_68244 := by decide
  rcases family_descends (prefixWord ++ tailWord_68244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68284 : List Nat := [2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_68284 : Nat := 118140960795 + 68284 * 2 ^ 59
def prefixEnd_68284 : Nat := 4983230072969 + 3 ^ 40 * 68284 * 2
def baseEnd_68284 : Nat := 20777785488424339102799

theorem tailTrace_68284 : CollatzResearch.WordTrace tailWord_68284 prefixEnd_68284 20777785488424339102799 := by
  unfold tailWord_68284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245261042313102411925953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1660348056417469882567937 1245261042313102411925953)
  ·
    refine ⟨933945781734826808944465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1245261042313102411925953 933945781734826808944465)
    ·
      refine ⟨700459336301120106708349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 933945781734826808944465 700459336301120106708349)
      ·
        refine ⟨262672251112920040015631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 700459336301120106708349 262672251112920040015631)
        ·
          refine ⟨394008376669380060023447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262672251112920040015631 394008376669380060023447)
          ·
            refine ⟨591012565004070090035171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394008376669380060023447 591012565004070090035171)
            ·
              refine ⟨886518847506105135052757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591012565004070090035171 886518847506105135052757)
              ·
                refine ⟨20777785488424339102799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 886518847506105135052757 20777785488424339102799)
                ·
                  rfl

theorem cell19_68284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_68284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68284 prefixEnd_68284 := by exact prefixLift 68284
  have htrace : WordTrace (prefixWord ++ tailWord_68284) baseStart_68284 baseEnd_68284 := by
    simpa [prefixWord, tailWord_68284, baseEnd_68284] using wordTrace_append hprefix tailTrace_68284
  have hstable : (prefixWord ++ tailWord_68284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68284).length < 2 ^ (prefixWord ++ tailWord_68284).sum := by decide
  have hdescent : baseEnd_68284 < baseStart_68284 := by decide
  rcases family_descends (prefixWord ++ tailWord_68284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68301 : List Nat := [1, 6, 2, 1, 9]
def baseStart_68301 : Nat := 118140960795 + 68301 * 2 ^ 59
def prefixEnd_68301 : Nat := 4983230072969 + 3 ^ 40 * 68301 * 2
def baseEnd_68301 : Nat := 769739197428642100925

theorem tailTrace_68301 : CollatzResearch.WordTrace tailWord_68301 prefixEnd_68301 769739197428642100925 := by
  unfold tailWord_68301
  simp only [CollatzResearch.WordTrace]
  refine ⟨2491142125564616727220757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1660761417043077818147171 2491142125564616727220757)
  ·
    refine ⟨116772287135841409088473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2491142125564616727220757 116772287135841409088473)
    ·
      refine ⟨87579215351881056816355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 116772287135841409088473 87579215351881056816355)
      ·
        refine ⟨131368823027821585224533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87579215351881056816355 131368823027821585224533)
        ·
          refine ⟨769739197428642100925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 131368823027821585224533 769739197428642100925)
          ·
            rfl

theorem cell19_68301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 9].length) (baseStart_68301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68301 prefixEnd_68301 := by exact prefixLift 68301
  have htrace : WordTrace (prefixWord ++ tailWord_68301) baseStart_68301 baseEnd_68301 := by
    simpa [prefixWord, tailWord_68301, baseEnd_68301] using wordTrace_append hprefix tailTrace_68301
  have hstable : (prefixWord ++ tailWord_68301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68301).length < 2 ^ (prefixWord ++ tailWord_68301).sum := by decide
  have hdescent : baseEnd_68301 < baseStart_68301 := by decide
  rcases family_descends (prefixWord ++ tailWord_68301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68360 : List Nat := [2, 1, 3, 2, 2, 3, 6]
def baseStart_68360 : Nat := 118140960795 + 68360 * 2 ^ 59
def prefixEnd_68360 : Nat := 4983230072969 + 3 ^ 40 * 68360 * 2
def baseEnd_68360 : Nat := 6933637045226227137901

theorem tailTrace_68360 : CollatzResearch.WordTrace tailWord_68360 prefixEnd_68360 6933637045226227137901 := by
  unfold tailWord_68360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246647016175434901809267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1662196021567246535745689 1246647016175434901809267)
  ·
    refine ⟨1869970524263152352713901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246647016175434901809267 1869970524263152352713901)
    ·
      refine ⟨701238946598682132267713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1869970524263152352713901 701238946598682132267713)
      ·
        refine ⟨525929209949011599200785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701238946598682132267713 525929209949011599200785)
        ·
          refine ⟨394446907461758699400589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525929209949011599200785 394446907461758699400589)
          ·
            refine ⟨147917590298159512275221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394446907461758699400589 147917590298159512275221)
            ·
              refine ⟨6933637045226227137901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 147917590298159512275221 6933637045226227137901)
              ·
                rfl

theorem cell19_68360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_68360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68360 prefixEnd_68360 := by exact prefixLift 68360
  have htrace : WordTrace (prefixWord ++ tailWord_68360) baseStart_68360 baseEnd_68360 := by
    simpa [prefixWord, tailWord_68360, baseEnd_68360] using wordTrace_append hprefix tailTrace_68360
  have hstable : (prefixWord ++ tailWord_68360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68360).length < 2 ^ (prefixWord ++ tailWord_68360).sum := by decide
  have hdescent : baseEnd_68360 < baseStart_68360 := by decide
  rcases family_descends (prefixWord ++ tailWord_68360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68394 : List Nat := [3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_68394 : Nat := 118140960795 + 68394 * 2 ^ 59
def prefixEnd_68394 : Nat := 4983230072969 + 3 ^ 40 * 68394 * 2
def baseEnd_68394 : Nat := 20811256819976676658055

theorem tailTrace_68394 : CollatzResearch.WordTrace tailWord_68394 prefixEnd_68394 20811256819976676658055 := by
  unfold tailWord_68394
  simp only [CollatzResearch.WordTrace]
  refine ⟨623633528556923402589059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1663022742818462406904157 623633528556923402589059)
  ·
    refine ⟨935450292835385103883589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623633528556923402589059 935450292835385103883589)
    ·
      refine ⟨175396929906634706978173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 935450292835385103883589 175396929906634706978173)
      ·
        refine ⟨65773848714988015116815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 175396929906634706978173 65773848714988015116815)
        ·
          refine ⟨98660773072482022675223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65773848714988015116815 98660773072482022675223)
          ·
            refine ⟨147991159608723034012835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98660773072482022675223 147991159608723034012835)
            ·
              refine ⟨221986739413084551019253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147991159608723034012835 221986739413084551019253)
              ·
                refine ⟨20811256819976676658055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 221986739413084551019253 20811256819976676658055)
                ·
                  rfl

theorem cell19_68394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_68394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68394 prefixEnd_68394 := by exact prefixLift 68394
  have htrace : WordTrace (prefixWord ++ tailWord_68394) baseStart_68394 baseEnd_68394 := by
    simpa [prefixWord, tailWord_68394, baseEnd_68394] using wordTrace_append hprefix tailTrace_68394
  have hstable : (prefixWord ++ tailWord_68394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68394).length < 2 ^ (prefixWord ++ tailWord_68394).sum := by decide
  have hdescent : baseEnd_68394 < baseStart_68394 := by decide
  rcases family_descends (prefixWord ++ tailWord_68394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68413 : List Nat := [1, 4, 1, 4, 3, 1, 5]
def baseStart_68413 : Nat := 118140960795 + 68413 * 2 ^ 59
def prefixEnd_68413 : Nat := 4983230072969 + 3 ^ 40 * 68413 * 2
def baseEnd_68413 : Nat := 6939012743930087411927

theorem tailTrace_68413 : CollatzResearch.WordTrace tailWord_68413 prefixEnd_68413 6939012743930087411927 := by
  unfold tailWord_68413
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495227101158859855297893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1663484734105906570198595 2495227101158859855297893)
  ·
    refine ⟨467855081467286222868355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2495227101158859855297893 467855081467286222868355)
    ·
      refine ⟨701782622200929334302533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467855081467286222868355 701782622200929334302533)
      ·
        refine ⟨131584241662674250181725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 701782622200929334302533 131584241662674250181725)
        ·
          refine ⟨49344090623502843818147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 131584241662674250181725 49344090623502843818147)
          ·
            refine ⟨74016135935254265727221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49344090623502843818147 74016135935254265727221)
            ·
              refine ⟨6939012743930087411927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74016135935254265727221 6939012743930087411927)
              ·
                rfl

theorem cell19_68413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_68413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68413 prefixEnd_68413 := by exact prefixLift 68413
  have htrace : WordTrace (prefixWord ++ tailWord_68413) baseStart_68413 baseEnd_68413 := by
    simpa [prefixWord, tailWord_68413, baseEnd_68413] using wordTrace_append hprefix tailTrace_68413
  have hstable : (prefixWord ++ tailWord_68413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68413).length < 2 ^ (prefixWord ++ tailWord_68413).sum := by decide
  have hdescent : baseEnd_68413 < baseStart_68413 := by decide
  rcases family_descends (prefixWord ++ tailWord_68413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68455 : List Nat := [1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_68455 : Nat := 118140960795 + 68455 * 2 ^ 59
def prefixEnd_68455 : Nat := 4983230072969 + 3 ^ 40 * 68455 * 2
def baseEnd_68455 : Nat := 20829818194746609302333

theorem tailTrace_68455 : CollatzResearch.WordTrace tailWord_68455 prefixEnd_68455 20829818194746609302333 := by
  unfold tailWord_68455
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496758967006701028326819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1664505978004467352217879 2496758967006701028326819)
  ·
    refine ⟨3745138450510051542490229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496758967006701028326819 3745138450510051542490229)
    ·
      refine ⟨351106729735317332108459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3745138450510051542490229 351106729735317332108459)
      ·
        refine ⟨526660094602975998162689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351106729735317332108459 526660094602975998162689)
        ·
          refine ⟨394995070952231998622017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526660094602975998162689 394995070952231998622017)
          ·
            refine ⟨296246303214173998966513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394995070952231998622017 296246303214173998966513)
            ·
              refine ⟨222184727410630499224885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296246303214173998966513 222184727410630499224885)
              ·
                refine ⟨20829818194746609302333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222184727410630499224885 20829818194746609302333)
                ·
                  rfl

theorem cell19_68455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_68455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68455 prefixEnd_68455 := by exact prefixLift 68455
  have htrace : WordTrace (prefixWord ++ tailWord_68455) baseStart_68455 baseEnd_68455 := by
    simpa [prefixWord, tailWord_68455, baseEnd_68455] using wordTrace_append hprefix tailTrace_68455
  have hstable : (prefixWord ++ tailWord_68455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68455).length < 2 ^ (prefixWord ++ tailWord_68455).sum := by decide
  have hdescent : baseEnd_68455 < baseStart_68455 := by decide
  rcases family_descends (prefixWord ++ tailWord_68455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68508 : List Nat := [2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_68508 : Nat := 118140960795 + 68508 * 2 ^ 59
def prefixEnd_68508 : Nat := 4983230072969 + 3 ^ 40 * 68508 * 2
def baseEnd_68508 : Nat := 20845945290858190124411

theorem tailTrace_68508 : CollatzResearch.WordTrace tailWord_68508 prefixEnd_68508 20845945290858190124411 := by
  unfold tailWord_68508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249346017907345540003089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1665794690543127386670785 1249346017907345540003089)
  ·
    refine ⟨937009513430509155002317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1249346017907345540003089 937009513430509155002317)
    ·
      refine ⟨351378567536440933125869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 937009513430509155002317 351378567536440933125869)
      ·
        refine ⟨131766962826165349922201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 351378567536440933125869 131766962826165349922201)
        ·
          refine ⟨98825222119624012441651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131766962826165349922201 98825222119624012441651)
          ·
            refine ⟨148237833179436018662477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98825222119624012441651 148237833179436018662477)
            ·
              refine ⟨55589187442288506998429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148237833179436018662477 55589187442288506998429)
              ·
                refine ⟨20845945290858190124411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55589187442288506998429 20845945290858190124411)
                ·
                  rfl

theorem cell19_68508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_68508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68508 prefixEnd_68508 := by exact prefixLift 68508
  have htrace : WordTrace (prefixWord ++ tailWord_68508) baseStart_68508 baseEnd_68508 := by
    simpa [prefixWord, tailWord_68508, baseEnd_68508] using wordTrace_append hprefix tailTrace_68508
  have hstable : (prefixWord ++ tailWord_68508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68508).length < 2 ^ (prefixWord ++ tailWord_68508).sum := by decide
  have hdescent : baseEnd_68508 < baseStart_68508 := by decide
  rcases family_descends (prefixWord ++ tailWord_68508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68565 : List Nat := [1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_68565 : Nat := 118140960795 + 68565 * 2 ^ 59
def prefixEnd_68565 : Nat := 4983230072969 + 3 ^ 40 * 68565 * 2
def baseEnd_68565 : Nat := 20863289526298946857589

theorem tailTrace_68565 : CollatzResearch.WordTrace tailWord_68565 prefixEnd_68565 20863289526298946857589 := by
  unfold tailWord_68565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500770996608189814831149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1667180664405459876554099 2500770996608189814831149)
  ·
    refine ⟨937789123728071180561681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2500770996608189814831149 937789123728071180561681)
    ·
      refine ⟨703341842796053385421261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 937789123728071180561681 703341842796053385421261)
      ·
        refine ⟨263753191048520019532973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 703341842796053385421261 263753191048520019532973)
        ·
          refine ⟨98907446643195007324865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 263753191048520019532973 98907446643195007324865)
          ·
            refine ⟨74180584982396255493649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 98907446643195007324865 74180584982396255493649)
            ·
              refine ⟨55635438736797191620237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74180584982396255493649 55635438736797191620237)
              ·
                refine ⟨20863289526298946857589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55635438736797191620237 20863289526298946857589)
                ·
                  rfl

theorem cell19_68565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_68565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68565 prefixEnd_68565 := by exact prefixLift 68565
  have htrace : WordTrace (prefixWord ++ tailWord_68565) baseStart_68565 baseEnd_68565 := by
    simpa [prefixWord, tailWord_68565, baseEnd_68565] using wordTrace_append hprefix tailTrace_68565
  have hstable : (prefixWord ++ tailWord_68565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68565).length < 2 ^ (prefixWord ++ tailWord_68565).sum := by decide
  have hdescent : baseEnd_68565 < baseStart_68565 := by decide
  rcases family_descends (prefixWord ++ tailWord_68565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68569 : List Nat := [1, 2, 1, 2, 5, 2, 1, 5]
def baseStart_68569 : Nat := 118140960795 + 68569 * 2 ^ 59
def prefixEnd_68569 : Nat := 4983230072969 + 3 ^ 40 * 68569 * 2
def baseEnd_68569 : Nat := 20864506665628122768689

theorem tailTrace_68569 : CollatzResearch.WordTrace tailWord_68569 prefixEnd_68569 20864506665628122768689 := by
  unfold tailWord_68569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500916888593698497976761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1667277925729132331984507 2500916888593698497976761)
  ·
    refine ⟨1875687666445273873482571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2500916888593698497976761 1875687666445273873482571)
    ·
      refine ⟨2813531499667910810223857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875687666445273873482571 2813531499667910810223857)
      ·
        refine ⟨2110148624750933107667893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813531499667910810223857 2110148624750933107667893)
        ·
          refine ⟨197826433570399978843865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2110148624750933107667893 197826433570399978843865)
          ·
            refine ⟨148369825177799984132899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197826433570399978843865 148369825177799984132899)
            ·
              refine ⟨222554737766699976199349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148369825177799984132899 222554737766699976199349)
              ·
                refine ⟨20864506665628122768689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222554737766699976199349 20864506665628122768689)
                ·
                  rfl

theorem cell19_68569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 5].length) (baseStart_68569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68569 prefixEnd_68569 := by exact prefixLift 68569
  have htrace : WordTrace (prefixWord ++ tailWord_68569) baseStart_68569 baseEnd_68569 := by
    simpa [prefixWord, tailWord_68569, baseEnd_68569] using wordTrace_append hprefix tailTrace_68569
  have hstable : (prefixWord ++ tailWord_68569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68569).length < 2 ^ (prefixWord ++ tailWord_68569).sum := by decide
  have hdescent : baseEnd_68569 < baseStart_68569 := by decide
  rcases family_descends (prefixWord ++ tailWord_68569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68660 : List Nat := [2, 5, 1, 2, 1, 3, 1, 4]
def baseStart_68660 : Nat := 118140960795 + 68660 * 2 ^ 59
def prefixEnd_68660 : Nat := 4983230072969 + 3 ^ 40 * 68660 * 2
def baseEnd_68660 : Nat := 20892196585366874746219

theorem tailTrace_68660 : CollatzResearch.WordTrace tailWord_68660 prefixEnd_68660 20892196585366874746219 := by
  unfold tailWord_68660
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252117965632010519769717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1669490620842680693026289 1252117965632010519769717)
  ·
    refine ⟨117386059278000986228411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1252117965632010519769717 117386059278000986228411)
    ·
      refine ⟨176079088917001479342617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117386059278000986228411 176079088917001479342617)
      ·
        refine ⟨132059316687751109506963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176079088917001479342617 132059316687751109506963)
        ·
          refine ⟨198088975031626664260445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132059316687751109506963 198088975031626664260445)
          ·
            refine ⟨74283365636859999097667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198088975031626664260445 74283365636859999097667)
            ·
              refine ⟨111425048455289998646501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74283365636859999097667 111425048455289998646501)
              ·
                refine ⟨20892196585366874746219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111425048455289998646501 20892196585366874746219)
                ·
                  rfl

theorem cell19_68660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_68660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68660 prefixEnd_68660 := by exact prefixLift 68660
  have htrace : WordTrace (prefixWord ++ tailWord_68660) baseStart_68660 baseEnd_68660 := by
    simpa [prefixWord, tailWord_68660, baseEnd_68660] using wordTrace_append hprefix tailTrace_68660
  have hstable : (prefixWord ++ tailWord_68660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68660).length < 2 ^ (prefixWord ++ tailWord_68660).sum := by decide
  have hdescent : baseEnd_68660 < baseStart_68660 := by decide
  rcases family_descends (prefixWord ++ tailWord_68660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68662 : List Nat := [5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_68662 : Nat := 118140960795 + 68662 * 2 ^ 59
def prefixEnd_68662 : Nat := 4983230072969 + 3 ^ 40 * 68662 * 2
def baseEnd_68662 : Nat := 20892805155031462701769

theorem tailTrace_68662 : CollatzResearch.WordTrace tailWord_68662 prefixEnd_68662 20892805155031462701769 := by
  unfold tailWord_68662
  simp only [CollatzResearch.WordTrace]
  refine ⟨156519304828548461319515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1669539251504516920741493 156519304828548461319515)
  ·
    refine ⟨234778957242822691979273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156519304828548461319515 234778957242822691979273)
    ·
      refine ⟨176084217932117018984455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234778957242822691979273 176084217932117018984455)
      ·
        refine ⟨264126326898175528476683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176084217932117018984455 264126326898175528476683)
        ·
          refine ⟨396189490347263292715025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264126326898175528476683 396189490347263292715025)
          ·
            refine ⟨297142117760447469536269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396189490347263292715025 297142117760447469536269)
            ·
              refine ⟨111428294160167801076101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297142117760447469536269 111428294160167801076101)
              ·
                refine ⟨20892805155031462701769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111428294160167801076101 20892805155031462701769)
                ·
                  rfl

theorem cell19_68662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_68662 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68662 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68662 prefixEnd_68662 := by exact prefixLift 68662
  have htrace : WordTrace (prefixWord ++ tailWord_68662) baseStart_68662 baseEnd_68662 := by
    simpa [prefixWord, tailWord_68662, baseEnd_68662] using wordTrace_append hprefix tailTrace_68662
  have hstable : (prefixWord ++ tailWord_68662).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68662).length < 2 ^ (prefixWord ++ tailWord_68662).sum := by decide
  have hdescent : baseEnd_68662 < baseStart_68662 := by decide
  rcases family_descends (prefixWord ++ tailWord_68662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68664 : List Nat := [2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_68664 : Nat := 118140960795 + 68664 * 2 ^ 59
def prefixEnd_68664 : Nat := 4983230072969 + 3 ^ 40 * 68664 * 2
def baseEnd_68664 : Nat := 20893413724696050657319

theorem tailTrace_68664 : CollatzResearch.WordTrace tailWord_68664 prefixEnd_68664 20893413724696050657319 := by
  unfold tailWord_68664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252190911624764861342523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1669587882166353148456697 1252190911624764861342523)
  ·
    refine ⟨1878286367437147292013785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1252190911624764861342523 1878286367437147292013785)
    ·
      refine ⟨1408714775577860469010339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1878286367437147292013785 1408714775577860469010339)
      ·
        refine ⟨2113072163366790703515509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408714775577860469010339 2113072163366790703515509)
        ·
          refine ⟨198100515315636628454579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2113072163366790703515509 198100515315636628454579)
          ·
            refine ⟨297150772973454942681869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198100515315636628454579 297150772973454942681869)
            ·
              refine ⟨111431539865045603505701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297150772973454942681869 111431539865045603505701)
              ·
                refine ⟨20893413724696050657319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111431539865045603505701 20893413724696050657319)
                ·
                  rfl

theorem cell19_68664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_68664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68664 prefixEnd_68664 := by exact prefixLift 68664
  have htrace : WordTrace (prefixWord ++ tailWord_68664) baseStart_68664 baseEnd_68664 := by
    simpa [prefixWord, tailWord_68664, baseEnd_68664] using wordTrace_append hprefix tailTrace_68664
  have hstable : (prefixWord ++ tailWord_68664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68664).length < 2 ^ (prefixWord ++ tailWord_68664).sum := by decide
  have hdescent : baseEnd_68664 < baseStart_68664 := by decide
  rcases family_descends (prefixWord ++ tailWord_68664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68704 : List Nat := [2, 1, 1, 3, 2, 2, 8]
def baseStart_68704 : Nat := 118140960795 + 68704 * 2 ^ 59
def prefixEnd_68704 : Nat := 4983230072969 + 3 ^ 40 * 68704 * 2
def baseEnd_68704 : Nat := 6968528372662603256107

theorem tailTrace_68704 : CollatzResearch.WordTrace tailWord_68704 prefixEnd_68704 6968528372662603256107 := by
  unfold tailWord_68704
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252920371552308277070583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1670560495403077702760777 1252920371552308277070583)
  ·
    refine ⟨1879380557328462415605875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1252920371552308277070583 1879380557328462415605875)
    ·
      refine ⟨2819070835992693623408813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879380557328462415605875 2819070835992693623408813)
      ·
        refine ⟨1057151563497260108778305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2819070835992693623408813 1057151563497260108778305)
        ·
          refine ⟨792863672622945081583729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057151563497260108778305 792863672622945081583729)
          ·
            refine ⟨594647754467208811187797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 792863672622945081583729 594647754467208811187797)
            ·
              refine ⟨6968528372662603256107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 594647754467208811187797 6968528372662603256107)
              ·
                rfl

theorem cell19_68704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_68704 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68704 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68704 prefixEnd_68704 := by exact prefixLift 68704
  have htrace : WordTrace (prefixWord ++ tailWord_68704) baseStart_68704 baseEnd_68704 := by
    simpa [prefixWord, tailWord_68704, baseEnd_68704] using wordTrace_append hprefix tailTrace_68704
  have hstable : (prefixWord ++ tailWord_68704).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68704).length < 2 ^ (prefixWord ++ tailWord_68704).sum := by decide
  have hdescent : baseEnd_68704 < baseStart_68704 := by decide
  rcases family_descends (prefixWord ++ tailWord_68704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68734 : List Nat := [4, 2, 4, 1, 1, 1, 1, 5]
def baseStart_68734 : Nat := 118140960795 + 68734 * 2 ^ 59
def prefixEnd_68734 : Nat := 4983230072969 + 3 ^ 40 * 68734 * 2
def baseEnd_68734 : Nat := 20914713662956629101573

theorem tailTrace_68734 : CollatzResearch.WordTrace tailWord_68734 prefixEnd_68734 20914713662956629101573 := by
  unfold tailWord_68734
  simp only [CollatzResearch.WordTrace]
  refine ⟨313366866624491459716657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1671289955330621118488837 313366866624491459716657)
  ·
    refine ⟨235025149968368594787493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 313366866624491459716657 235025149968368594787493)
    ·
      refine ⟨44067215619069111522655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235025149968368594787493 44067215619069111522655)
      ·
        refine ⟨66100823428603667283983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44067215619069111522655 66100823428603667283983)
        ·
          refine ⟨99151235142905500925975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66100823428603667283983 99151235142905500925975)
          ·
            refine ⟨148726852714358251388963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99151235142905500925975 148726852714358251388963)
            ·
              refine ⟨223090279071537377083445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148726852714358251388963 223090279071537377083445)
              ·
                refine ⟨20914713662956629101573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223090279071537377083445 20914713662956629101573)
                ·
                  rfl

theorem cell19_68734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_68734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68734 prefixEnd_68734 := by exact prefixLift 68734
  have htrace : WordTrace (prefixWord ++ tailWord_68734) baseStart_68734 baseEnd_68734 := by
    simpa [prefixWord, tailWord_68734, baseEnd_68734] using wordTrace_append hprefix tailTrace_68734
  have hstable : (prefixWord ++ tailWord_68734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68734).length < 2 ^ (prefixWord ++ tailWord_68734).sum := by decide
  have hdescent : baseEnd_68734 < baseStart_68734 := by decide
  rcases family_descends (prefixWord ++ tailWord_68734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68740 : List Nat := [2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_68740 : Nat := 118140960795 + 68740 * 2 ^ 59
def prefixEnd_68740 : Nat := 4983230072969 + 3 ^ 40 * 68740 * 2
def baseEnd_68740 : Nat := 20916539371950392968223

theorem tailTrace_68740 : CollatzResearch.WordTrace tailWord_68740 prefixEnd_68740 20916539371950392968223 := by
  unfold tailWord_68740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253576885487097351225837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1671435847316129801634449 1253576885487097351225837)
  ·
    refine ⟨470091332057661506709689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1253576885487097351225837 470091332057661506709689)
    ·
      refine ⟨352568499043246130032267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 470091332057661506709689 352568499043246130032267)
      ·
        refine ⟨528852748564869195048401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352568499043246130032267 528852748564869195048401)
        ·
          refine ⟨396639561423651896286301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528852748564869195048401 396639561423651896286301)
          ·
            refine ⟨148739835533869461107363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396639561423651896286301 148739835533869461107363)
            ·
              refine ⟨223109753300804191661045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148739835533869461107363 223109753300804191661045)
              ·
                refine ⟨20916539371950392968223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223109753300804191661045 20916539371950392968223)
                ·
                  rfl

theorem cell19_68740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_68740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68740 prefixEnd_68740 := by exact prefixLift 68740
  have htrace : WordTrace (prefixWord ++ tailWord_68740) baseStart_68740 baseEnd_68740 := by
    simpa [prefixWord, tailWord_68740, baseEnd_68740] using wordTrace_append hprefix tailTrace_68740
  have hstable : (prefixWord ++ tailWord_68740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68740).length < 2 ^ (prefixWord ++ tailWord_68740).sum := by decide
  have hdescent : baseEnd_68740 < baseStart_68740 := by decide
  rcases family_descends (prefixWord ++ tailWord_68740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68759 : List Nat := [1, 1, 3, 3, 3, 3, 5]
def baseStart_68759 : Nat := 118140960795 + 68759 * 2 ^ 59
def prefixEnd_68759 : Nat := 4983230072969 + 3 ^ 40 * 68759 * 2
def baseEnd_68759 : Nat := 6974106927921326181983

theorem tailTrace_68759 : CollatzResearch.WordTrace tailWord_68759 prefixEnd_68759 6974106927921326181983 := by
  unfold tailWord_68759
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507846757905360947393331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1671897838603573964928887 2507846757905360947393331)
  ·
    refine ⟨3761770136858041421089997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2507846757905360947393331 3761770136858041421089997)
    ·
      refine ⟨1410663801321765532908749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3761770136858041421089997 1410663801321765532908749)
      ·
        refine ⟨528998925495662074840781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1410663801321765532908749 528998925495662074840781)
        ·
          refine ⟨198374597060873278065293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528998925495662074840781 198374597060873278065293)
          ·
            refine ⟨74390473897827479274485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198374597060873278065293 74390473897827479274485)
            ·
              refine ⟨6974106927921326181983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74390473897827479274485 6974106927921326181983)
              ·
                rfl

theorem cell19_68759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 5].length) (baseStart_68759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68759 prefixEnd_68759 := by exact prefixLift 68759
  have htrace : WordTrace (prefixWord ++ tailWord_68759) baseStart_68759 baseEnd_68759 := by
    simpa [prefixWord, tailWord_68759, baseEnd_68759] using wordTrace_append hprefix tailTrace_68759
  have hstable : (prefixWord ++ tailWord_68759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68759).length < 2 ^ (prefixWord ++ tailWord_68759).sum := by decide
  have hdescent : baseEnd_68759 < baseStart_68759 := by decide
  rcases family_descends (prefixWord ++ tailWord_68759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68799 : List Nat := [1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_68799 : Nat := 118140960795 + 68799 * 2 ^ 59
def prefixEnd_68799 : Nat := 4983230072969 + 3 ^ 40 * 68799 * 2
def baseEnd_68799 : Nat := 20934492177055737656951

theorem tailTrace_68799 : CollatzResearch.WordTrace tailWord_68799 prefixEnd_68799 20934492177055737656951 := by
  unfold tailWord_68799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509305677760447778849451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1672870451840298519232967 2509305677760447778849451)
  ·
    refine ⟨3763958516640671668274177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2509305677760447778849451 3763958516640671668274177)
    ·
      refine ⟨2822968887480503751205633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3763958516640671668274177 2822968887480503751205633)
      ·
        refine ⟨2117226665610377813404225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2822968887480503751205633 2117226665610377813404225)
        ·
          refine ⟨1587919999207783360053169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117226665610377813404225 1587919999207783360053169)
          ·
            refine ⟨1190939999405837520039877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1587919999207783360053169 1190939999405837520039877)
            ·
              refine ⟨223301249888594535007477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1190939999405837520039877 223301249888594535007477)
              ·
                refine ⟨20934492177055737656951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223301249888594535007477 20934492177055737656951)
                ·
                  rfl

theorem cell19_68799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_68799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68799 prefixEnd_68799 := by exact prefixLift 68799
  have htrace : WordTrace (prefixWord ++ tailWord_68799) baseStart_68799 baseEnd_68799 := by
    simpa [prefixWord, tailWord_68799, baseEnd_68799] using wordTrace_append hprefix tailTrace_68799
  have hstable : (prefixWord ++ tailWord_68799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68799).length < 2 ^ (prefixWord ++ tailWord_68799).sum := by decide
  have hdescent : baseEnd_68799 < baseStart_68799 := by decide
  rcases family_descends (prefixWord ++ tailWord_68799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68875 : List Nat := [1, 1, 1, 1, 5, 4, 6]
def baseStart_68875 : Nat := 118140960795 + 68875 * 2 ^ 59
def prefixEnd_68875 : Nat := 4983230072969 + 3 ^ 40 * 68875 * 2
def baseEnd_68875 : Nat := 6985872608103359989285

theorem tailTrace_68875 : CollatzResearch.WordTrace tailWord_68875 prefixEnd_68875 6985872608103359989285 := by
  unfold tailWord_68875
  simp only [CollatzResearch.WordTrace]
  refine ⟨2512077625485112758616079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1674718416990075172410719 2512077625485112758616079)
  ·
    refine ⟨3768116438227669137924119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2512077625485112758616079 3768116438227669137924119)
    ·
      refine ⟨5652174657341503706886179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3768116438227669137924119 5652174657341503706886179)
      ·
        refine ⟨8478261986012255560329269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5652174657341503706886179 8478261986012255560329269)
        ·
          refine ⟨794837061188648958780869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8478261986012255560329269 794837061188648958780869)
          ·
            refine ⟨149031948972871679771413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 794837061188648958780869 149031948972871679771413)
            ·
              refine ⟨6985872608103359989285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149031948972871679771413 6985872608103359989285)
              ·
                rfl

theorem cell19_68875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_68875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68875 prefixEnd_68875 := by exact prefixLift 68875
  have htrace : WordTrace (prefixWord ++ tailWord_68875) baseStart_68875 baseEnd_68875 := by
    simpa [prefixWord, tailWord_68875, baseEnd_68875] using wordTrace_append hprefix tailTrace_68875
  have hstable : (prefixWord ++ tailWord_68875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68875).length < 2 ^ (prefixWord ++ tailWord_68875).sum := by decide
  have hdescent : baseEnd_68875 < baseStart_68875 := by decide
  rcases family_descends (prefixWord ++ tailWord_68875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68909 : List Nat := [1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_68909 : Nat := 118140960795 + 68909 * 2 ^ 59
def prefixEnd_68909 : Nat := 4983230072969 + 3 ^ 40 * 68909 * 2
def baseEnd_68909 : Nat := 20967963508608075212207

theorem tailTrace_68909 : CollatzResearch.WordTrace tailWord_68909 prefixEnd_68909 20967963508608075212207 := by
  unfold tailWord_68909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513317707361936565353781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1675545138241291043569187 2513317707361936565353781)
  ·
    refine ⟨235623535065181553001917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2513317707361936565353781 235623535065181553001917)
    ·
      refine ⟨88358825649443082375719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235623535065181553001917 88358825649443082375719)
      ·
        refine ⟨132538238474164623563579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88358825649443082375719 132538238474164623563579)
        ·
          refine ⟨198807357711246935345369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132538238474164623563579 198807357711246935345369)
          ·
            refine ⟨149105518283435201509027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198807357711246935345369 149105518283435201509027)
            ·
              refine ⟨223658277425152802263541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149105518283435201509027 223658277425152802263541)
              ·
                refine ⟨20967963508608075212207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223658277425152802263541 20967963508608075212207)
                ·
                  rfl

theorem cell19_68909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_68909 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68909 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68909 prefixEnd_68909 := by exact prefixLift 68909
  have htrace : WordTrace (prefixWord ++ tailWord_68909) baseStart_68909 baseEnd_68909 := by
    simpa [prefixWord, tailWord_68909, baseEnd_68909] using wordTrace_append hprefix tailTrace_68909
  have hstable : (prefixWord ++ tailWord_68909).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68909).length < 2 ^ (prefixWord ++ tailWord_68909).sum := by decide
  have hdescent : baseEnd_68909 < baseStart_68909 := by decide
  rcases family_descends (prefixWord ++ tailWord_68909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68949 : List Nat := [1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_68949 : Nat := 118140960795 + 68949 * 2 ^ 59
def prefixEnd_68949 : Nat := 4983230072969 + 3 ^ 40 * 68949 * 2
def baseEnd_68949 : Nat := 20980134901899834323209

theorem tailTrace_68949 : CollatzResearch.WordTrace tailWord_68949 prefixEnd_68949 20980134901899834323209 := by
  unfold tailWord_68949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514776627217023396809901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1676517751478015597873267 2514776627217023396809901)
  ·
    refine ⟨943041235206383773803713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2514776627217023396809901 943041235206383773803713)
    ·
      refine ⟨707280926404787830352785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 943041235206383773803713 707280926404787830352785)
      ·
        refine ⟨530460694803590872764589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 707280926404787830352785 530460694803590872764589)
        ·
          refine ⟨198922760551346577286721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 530460694803590872764589 198922760551346577286721)
          ·
            refine ⟨149192070413509932965041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198922760551346577286721 149192070413509932965041)
            ·
              refine ⟨111894052810132449723781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149192070413509932965041 111894052810132449723781)
              ·
                refine ⟨20980134901899834323209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111894052810132449723781 20980134901899834323209)
                ·
                  rfl

theorem cell19_68949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_68949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68949 prefixEnd_68949 := by exact prefixLift 68949
  have htrace : WordTrace (prefixWord ++ tailWord_68949) baseStart_68949 baseEnd_68949 := by
    simpa [prefixWord, tailWord_68949, baseEnd_68949] using wordTrace_append hprefix tailTrace_68949
  have hstable : (prefixWord ++ tailWord_68949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68949).length < 2 ^ (prefixWord ++ tailWord_68949).sum := by decide
  have hdescent : baseEnd_68949 < baseStart_68949 := by decide
  rcases family_descends (prefixWord ++ tailWord_68949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_68951 : List Nat := [1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_68951 : Nat := 118140960795 + 68951 * 2 ^ 59
def prefixEnd_68951 : Nat := 4983230072969 + 3 ^ 40 * 68951 * 2
def baseEnd_68951 : Nat := 20980743471564422278759

theorem tailTrace_68951 : CollatzResearch.WordTrace tailWord_68951 prefixEnd_68951 20980743471564422278759 := by
  unfold tailWord_68951
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514849573209777738382707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1676566382139851825588471 2514849573209777738382707)
  ·
    refine ⟨3772274359814666607574061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2514849573209777738382707 3772274359814666607574061)
    ·
      refine ⟨1414602884930499977840273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3772274359814666607574061 1414602884930499977840273)
      ·
        refine ⟨1060952163697874983380205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414602884930499977840273 1060952163697874983380205)
        ·
          refine ⟨397857061386703118767577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1060952163697874983380205 397857061386703118767577)
          ·
            refine ⟨298392796040027339075683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397857061386703118767577 298392796040027339075683)
            ·
              refine ⟨447589194060041008613525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298392796040027339075683 447589194060041008613525)
              ·
                refine ⟨20980743471564422278759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 447589194060041008613525 20980743471564422278759)
                ·
                  rfl

theorem cell19_68951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_68951 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_68951 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_68951 prefixEnd_68951 := by exact prefixLift 68951
  have htrace : WordTrace (prefixWord ++ tailWord_68951) baseStart_68951 baseEnd_68951 := by
    simpa [prefixWord, tailWord_68951, baseEnd_68951] using wordTrace_append hprefix tailTrace_68951
  have hstable : (prefixWord ++ tailWord_68951).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_68951).length < 2 ^ (prefixWord ++ tailWord_68951).sum := by decide
  have hdescent : baseEnd_68951 < baseStart_68951 := by decide
  rcases family_descends (prefixWord ++ tailWord_68951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69078 : List Nat := [5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_69078 : Nat := 118140960795 + 69078 * 2 ^ 59
def prefixEnd_69078 : Nat := 4983230072969 + 3 ^ 40 * 69078 * 2
def baseEnd_69078 : Nat := 21019387645265757456191

theorem tailTrace_69078 : CollatzResearch.WordTrace tailWord_69078 prefixEnd_69078 21019387645265757456191 := by
  unfold tailWord_69078
  simp only [CollatzResearch.WordTrace]
  refine ⟨157467602734354901765993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1679654429166452285503925 157467602734354901765993)
  ·
    refine ⟨118100702050766176324495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157467602734354901765993 118100702050766176324495)
    ·
      refine ⟨177151053076149264486743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118100702050766176324495 177151053076149264486743)
      ·
        refine ⟨265726579614223896730115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177151053076149264486743 265726579614223896730115)
        ·
          refine ⟨398589869421335845095173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265726579614223896730115 398589869421335845095173)
          ·
            refine ⟨74735600516500470955345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398589869421335845095173 74735600516500470955345)
            ·
              refine ⟨56051700387375353216509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74735600516500470955345 56051700387375353216509)
              ·
                refine ⟨21019387645265757456191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56051700387375353216509 21019387645265757456191)
                ·
                  rfl

theorem cell19_69078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_69078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69078 prefixEnd_69078 := by exact prefixLift 69078
  have htrace : WordTrace (prefixWord ++ tailWord_69078) baseStart_69078 baseEnd_69078 := by
    simpa [prefixWord, tailWord_69078, baseEnd_69078] using wordTrace_append hprefix tailTrace_69078
  have hstable : (prefixWord ++ tailWord_69078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69078).length < 2 ^ (prefixWord ++ tailWord_69078).sum := by decide
  have hdescent : baseEnd_69078 < baseStart_69078 := by decide
  rcases family_descends (prefixWord ++ tailWord_69078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69082 : List Nat := [3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_69082 : Nat := 118140960795 + 69082 * 2 ^ 59
def prefixEnd_69082 : Nat := 4983230072969 + 3 ^ 40 * 69082 * 2
def baseEnd_69082 : Nat := 21020604784594933367291

theorem tailTrace_69082 : CollatzResearch.WordTrace tailWord_69082 prefixEnd_69082 21020604784594933367291 := by
  unfold tailWord_69082
  simp only [CollatzResearch.WordTrace]
  refine ⟨629906883933796777850375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1679751690490124740934333 629906883933796777850375)
  ·
    refine ⟨944860325900695166775563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 629906883933796777850375 944860325900695166775563)
    ·
      refine ⟨1417290488851042750163345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944860325900695166775563 1417290488851042750163345)
      ·
        refine ⟨1062967866638282062622509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417290488851042750163345 1062967866638282062622509)
        ·
          refine ⟨398612949989355773483441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1062967866638282062622509 398612949989355773483441)
          ·
            refine ⟨298959712492016830112581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398612949989355773483441 298959712492016830112581)
            ·
              refine ⟨56054946092253155646109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298959712492016830112581 56054946092253155646109)
              ·
                refine ⟨21020604784594933367291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56054946092253155646109 21020604784594933367291)
                ·
                  rfl

theorem cell19_69082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_69082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69082 prefixEnd_69082 := by exact prefixLift 69082
  have htrace : WordTrace (prefixWord ++ tailWord_69082) baseStart_69082 baseEnd_69082 := by
    simpa [prefixWord, tailWord_69082, baseEnd_69082] using wordTrace_append hprefix tailTrace_69082
  have hstable : (prefixWord ++ tailWord_69082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69082).length < 2 ^ (prefixWord ++ tailWord_69082).sum := by decide
  have hdescent : baseEnd_69082 < baseStart_69082 := by decide
  rcases family_descends (prefixWord ++ tailWord_69082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69141 : List Nat := [1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_69141 : Nat := 118140960795 + 69141 * 2 ^ 59
def prefixEnd_69141 : Nat := 4983230072969 + 3 ^ 40 * 69141 * 2
def baseEnd_69141 : Nat := 21038557589700278056019

theorem tailTrace_69141 : CollatzResearch.WordTrace tailWord_69141 prefixEnd_69141 21038557589700278056019 := by
  unfold tailWord_69141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521779442521440187799277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1681186295014293458532851 2521779442521440187799277)
  ·
    refine ⟨945667290945540070424729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2521779442521440187799277 945667290945540070424729)
    ·
      refine ⟨709250468209155052818547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945667290945540070424729 709250468209155052818547)
      ·
        refine ⟨1063875702313732579227821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709250468209155052818547 1063875702313732579227821)
        ·
          refine ⟨398953388367649717210433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1063875702313732579227821 398953388367649717210433)
          ·
            refine ⟨299215041275737287907825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398953388367649717210433 299215041275737287907825)
            ·
              refine ⟨224411280956802965930869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299215041275737287907825 224411280956802965930869)
              ·
                refine ⟨21038557589700278056019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224411280956802965930869 21038557589700278056019)
                ·
                  rfl

theorem cell19_69141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_69141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69141 prefixEnd_69141 := by exact prefixLift 69141
  have htrace : WordTrace (prefixWord ++ tailWord_69141) baseStart_69141 baseEnd_69141 := by
    simpa [prefixWord, tailWord_69141, baseEnd_69141] using wordTrace_append hprefix tailTrace_69141
  have hstable : (prefixWord ++ tailWord_69141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69141).length < 2 ^ (prefixWord ++ tailWord_69141).sum := by decide
  have hdescent : baseEnd_69141 < baseStart_69141 := by decide
  rcases family_descends (prefixWord ++ tailWord_69141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69160 : List Nat := [2, 1, 5, 2, 9]
def baseStart_69160 : Nat := 118140960795 + 69160 * 2 ^ 59
def prefixEnd_69160 : Nat := 4983230072969 + 3 ^ 40 * 69160 * 2
def baseEnd_69160 : Nat := 779419963019031986435

theorem tailTrace_69160 : CollatzResearch.WordTrace tailWord_69160 prefixEnd_69160 779419963019031986435 := by
  unfold tailWord_69160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261236214726303216370467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1681648286301737621827289 1261236214726303216370467)
  ·
    refine ⟨1891854322089454824555701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1261236214726303216370467 1891854322089454824555701)
    ·
      refine ⟨177361342695886389802097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1891854322089454824555701 177361342695886389802097)
      ·
        refine ⟨133021007021914792351573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177361342695886389802097 133021007021914792351573)
        ·
          refine ⟨779419963019031986435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 133021007021914792351573 779419963019031986435)
          ·
            rfl

theorem cell19_69160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 9].length) (baseStart_69160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69160 prefixEnd_69160 := by exact prefixLift 69160
  have htrace : WordTrace (prefixWord ++ tailWord_69160) baseStart_69160 baseEnd_69160 := by
    simpa [prefixWord, tailWord_69160, baseEnd_69160] using wordTrace_append hprefix tailTrace_69160
  have hstable : (prefixWord ++ tailWord_69160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69160).length < 2 ^ (prefixWord ++ tailWord_69160).sum := by decide
  have hdescent : baseEnd_69160 < baseStart_69160 := by decide
  rcases family_descends (prefixWord ++ tailWord_69160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69177 : List Nat := [1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_69177 : Nat := 118140960795 + 69177 * 2 ^ 59
def prefixEnd_69177 : Nat := 4983230072969 + 3 ^ 40 * 69177 * 2
def baseEnd_69177 : Nat := 21049511843662861255921

theorem tailTrace_69177 : CollatzResearch.WordTrace tailWord_69177 prefixEnd_69177 21049511843662861255921 := by
  unfold tailWord_69177
  simp only [CollatzResearch.WordTrace]
  refine ⟨2523092470391018336109785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1682061646927345557406523 2523092470391018336109785)
  ·
    refine ⟨1892319352793263752082339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2523092470391018336109785 1892319352793263752082339)
    ·
      refine ⟨2838479029189895628123509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1892319352793263752082339 2838479029189895628123509)
      ·
        refine ⟨266107408986552715136579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2838479029189895628123509 266107408986552715136579)
        ·
          refine ⟨399161113479829072704869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266107408986552715136579 399161113479829072704869)
          ·
            refine ⟨74842708777467951132163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 399161113479829072704869 74842708777467951132163)
            ·
              refine ⟨112264063166201926698245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74842708777467951132163 112264063166201926698245)
              ·
                refine ⟨21049511843662861255921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112264063166201926698245 21049511843662861255921)
                ·
                  rfl

theorem cell19_69177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_69177 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69177 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69177 prefixEnd_69177 := by exact prefixLift 69177
  have htrace : WordTrace (prefixWord ++ tailWord_69177) baseStart_69177 baseEnd_69177 := by
    simpa [prefixWord, tailWord_69177, baseEnd_69177] using wordTrace_append hprefix tailTrace_69177
  have hstable : (prefixWord ++ tailWord_69177).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69177).length < 2 ^ (prefixWord ++ tailWord_69177).sum := by decide
  have hdescent : baseEnd_69177 < baseStart_69177 := by decide
  rcases family_descends (prefixWord ++ tailWord_69177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69196 : List Nat := [2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_69196 : Nat := 118140960795 + 69196 * 2 ^ 59
def prefixEnd_69196 : Nat := 4983230072969 + 3 ^ 40 * 69196 * 2
def baseEnd_69196 : Nat := 21055293255476446833647

theorem tailTrace_69196 : CollatzResearch.WordTrace tailWord_69196 prefixEnd_69196 21055293255476446833647 := by
  unfold tailWord_69196
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261892728661092290525721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1682523638214789720700961 1261892728661092290525721)
  ·
    refine ⟨946419546495819217894291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1261892728661092290525721 946419546495819217894291)
    ·
      refine ⟨1419629319743728826841437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 946419546495819217894291 1419629319743728826841437)
      ·
        refine ⟨532360994903898310065539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1419629319743728826841437 532360994903898310065539)
        ·
          refine ⟨798541492355847465098309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532360994903898310065539 798541492355847465098309)
          ·
            refine ⟨149726529816721399705933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 798541492355847465098309 149726529816721399705933)
            ·
              refine ⟨56147448681270524889725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149726529816721399705933 56147448681270524889725)
              ·
                refine ⟨21055293255476446833647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56147448681270524889725 21055293255476446833647)
                ·
                  rfl

theorem cell19_69196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_69196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69196 prefixEnd_69196 := by exact prefixLift 69196
  have htrace : WordTrace (prefixWord ++ tailWord_69196) baseStart_69196 baseEnd_69196 := by
    simpa [prefixWord, tailWord_69196, baseEnd_69196] using wordTrace_append hprefix tailTrace_69196
  have hstable : (prefixWord ++ tailWord_69196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69196).length < 2 ^ (prefixWord ++ tailWord_69196).sum := by decide
  have hdescent : baseEnd_69196 < baseStart_69196 := by decide
  rcases family_descends (prefixWord ++ tailWord_69196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69213 : List Nat := [1, 4, 4, 2, 1, 1, 6]
def baseStart_69213 : Nat := 118140960795 + 69213 * 2 ^ 59
def prefixEnd_69213 : Nat := 4983230072969 + 3 ^ 40 * 69213 * 2
def baseEnd_69213 : Nat := 7020155365875148151941

theorem tailTrace_69213 : CollatzResearch.WordTrace tailWord_69213 prefixEnd_69213 7020155365875148151941 := by
  unfold tailWord_69213
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524405498260596484420293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1682936998840397656280195 2524405498260596484420293)
  ·
    refine ⟨473326030923861840828805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2524405498260596484420293 473326030923861840828805)
    ·
      refine ⟨88748630798224095155401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 473326030923861840828805 88748630798224095155401)
      ·
        refine ⟨66561473098668071366551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88748630798224095155401 66561473098668071366551)
        ·
          refine ⟨99842209648002107049827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66561473098668071366551 99842209648002107049827)
          ·
            refine ⟨149763314472003160574741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99842209648002107049827 149763314472003160574741)
            ·
              refine ⟨7020155365875148151941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149763314472003160574741 7020155365875148151941)
              ·
                rfl

theorem cell19_69213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_69213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69213 prefixEnd_69213 := by exact prefixLift 69213
  have htrace : WordTrace (prefixWord ++ tailWord_69213) baseStart_69213 baseEnd_69213 := by
    simpa [prefixWord, tailWord_69213, baseEnd_69213] using wordTrace_append hprefix tailTrace_69213
  have hstable : (prefixWord ++ tailWord_69213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69213).length < 2 ^ (prefixWord ++ tailWord_69213).sum := by decide
  have hdescent : baseEnd_69213 < baseStart_69213 := by decide
  rcases family_descends (prefixWord ++ tailWord_69213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69255 : List Nat := [1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_69255 : Nat := 118140960795 + 69255 * 2 ^ 59
def prefixEnd_69255 : Nat := 4983230072969 + 3 ^ 40 * 69255 * 2
def baseEnd_69255 : Nat := 21073246060581791522375

theorem tailTrace_69255 : CollatzResearch.WordTrace tailWord_69255 prefixEnd_69255 21073246060581791522375 := by
  unfold tailWord_69255
  simp only [CollatzResearch.WordTrace]
  refine ⟨2525937364108437657449219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1683958242738958438299479 2525937364108437657449219)
  ·
    refine ⟨3788906046162656486173829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2525937364108437657449219 3788906046162656486173829)
    ·
      refine ⟨710419883655498091157593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3788906046162656486173829 710419883655498091157593)
      ·
        refine ⟨532814912741623568368195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710419883655498091157593 532814912741623568368195)
        ·
          refine ⟨799222369112435352552293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532814912741623568368195 799222369112435352552293)
          ·
            refine ⟨149854194208581628603555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 799222369112435352552293 149854194208581628603555)
            ·
              refine ⟨224781291312872442905333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149854194208581628603555 224781291312872442905333)
              ·
                refine ⟨21073246060581791522375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224781291312872442905333 21073246060581791522375)
                ·
                  rfl

theorem cell19_69255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_69255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69255 prefixEnd_69255 := by exact prefixLift 69255
  have htrace : WordTrace (prefixWord ++ tailWord_69255) baseStart_69255 baseEnd_69255 := by
    simpa [prefixWord, tailWord_69255, baseEnd_69255] using wordTrace_append hprefix tailTrace_69255
  have hstable : (prefixWord ++ tailWord_69255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69255).length < 2 ^ (prefixWord ++ tailWord_69255).sum := by decide
  have hdescent : baseEnd_69255 < baseStart_69255 := by decide
  rcases family_descends (prefixWord ++ tailWord_69255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69333 : List Nat := [1, 3, 2, 13]
def baseStart_69333 : Nat := 118140960795 + 69333 * 2 ^ 59
def prefixEnd_69333 : Nat := 4983230072969 + 3 ^ 40 * 69333 * 2
def baseEnd_69333 : Nat := 260456546635811380109

theorem tailTrace_69333 : CollatzResearch.WordTrace tailWord_69333 prefixEnd_69333 260456546635811380109 := by
  unfold tailWord_69333
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528782257825856978788653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1685854838550571319192435 2528782257825856978788653)
  ·
    refine ⟨948293346684696367045745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2528782257825856978788653 948293346684696367045745)
    ·
      refine ⟨711220010013522275284309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948293346684696367045745 711220010013522275284309)
      ·
        refine ⟨260456546635811380109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 711220010013522275284309 260456546635811380109)
        ·
          rfl

theorem cell19_69333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 13].length) (baseStart_69333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69333 prefixEnd_69333 := by exact prefixLift 69333
  have htrace : WordTrace (prefixWord ++ tailWord_69333) baseStart_69333 baseEnd_69333 := by
    simpa [prefixWord, tailWord_69333, baseEnd_69333] using wordTrace_append hprefix tailTrace_69333
  have hstable : (prefixWord ++ tailWord_69333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69333).length < 2 ^ (prefixWord ++ tailWord_69333).sum := by decide
  have hdescent : baseEnd_69333 < baseStart_69333 := by decide
  rcases family_descends (prefixWord ++ tailWord_69333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69426 : List Nat := [3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_69426 : Nat := 118140960795 + 69426 * 2 ^ 59
def prefixEnd_69426 : Nat := 4983230072969 + 3 ^ 40 * 69426 * 2
def baseEnd_69426 : Nat := 21125278766904061721909

theorem tailTrace_69426 : CollatzResearch.WordTrace tailWord_69426 prefixEnd_69426 21125278766904061721909 := by
  unfold tailWord_69426
  simp only [CollatzResearch.WordTrace]
  refine ⟨633043561622233465481033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1688116164325955907949421 633043561622233465481033)
  ·
    refine ⟨474782671216675099110775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 633043561622233465481033 474782671216675099110775)
    ·
      refine ⟨712174006825012648666163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474782671216675099110775 712174006825012648666163)
      ·
        refine ⟨1068261010237518972999245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712174006825012648666163 1068261010237518972999245)
        ·
          refine ⟨400597878839069614874717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1068261010237518972999245 400597878839069614874717)
          ·
            refine ⟨150224204564651105578019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400597878839069614874717 150224204564651105578019)
            ·
              refine ⟨225336306846976658367029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150224204564651105578019 225336306846976658367029)
              ·
                refine ⟨21125278766904061721909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 225336306846976658367029 21125278766904061721909)
                ·
                  rfl

theorem cell19_69426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_69426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69426 prefixEnd_69426 := by exact prefixLift 69426
  have htrace : WordTrace (prefixWord ++ tailWord_69426) baseStart_69426 baseEnd_69426 := by
    simpa [prefixWord, tailWord_69426, baseEnd_69426] using wordTrace_append hprefix tailTrace_69426
  have hstable : (prefixWord ++ tailWord_69426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69426).length < 2 ^ (prefixWord ++ tailWord_69426).sum := by decide
  have hdescent : baseEnd_69426 < baseStart_69426 := by decide
  rcases family_descends (prefixWord ++ tailWord_69426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69447 : List Nat := [1, 1, 4, 1, 2, 1, 9]
def baseStart_69447 : Nat := 118140960795 + 69447 * 2 ^ 59
def prefixEnd_69447 : Nat := 4983230072969 + 3 ^ 40 * 69447 * 2
def baseEnd_69447 : Nat := 7043889582794078418395

theorem tailTrace_69447 : CollatzResearch.WordTrace tailWord_69447 prefixEnd_69447 7043889582794078418395 := by
  unfold tailWord_69447
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532940179412854448438595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1688626786275236298959063 2532940179412854448438595)
  ·
    refine ⟨3799410269119281672657893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2532940179412854448438595 3799410269119281672657893)
    ·
      refine ⟨712389425459865313623355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3799410269119281672657893 712389425459865313623355)
      ·
        refine ⟨1068584138189797970435033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712389425459865313623355 1068584138189797970435033)
        ·
          refine ⟨801438103642348477826275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068584138189797970435033 801438103642348477826275)
          ·
            refine ⟨1202157155463522716739413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801438103642348477826275 1202157155463522716739413)
            ·
              refine ⟨7043889582794078418395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1202157155463522716739413 7043889582794078418395)
              ·
                rfl

theorem cell19_69447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_69447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69447 prefixEnd_69447 := by exact prefixLift 69447
  have htrace : WordTrace (prefixWord ++ tailWord_69447) baseStart_69447 baseEnd_69447 := by
    simpa [prefixWord, tailWord_69447, baseEnd_69447] using wordTrace_append hprefix tailTrace_69447
  have hstable : (prefixWord ++ tailWord_69447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69447).length < 2 ^ (prefixWord ++ tailWord_69447).sum := by decide
  have hdescent : baseEnd_69447 < baseStart_69447 := by decide
  rcases family_descends (prefixWord ++ tailWord_69447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69534 : List Nat := [4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_69534 : Nat := 118140960795 + 69534 * 2 ^ 59
def prefixEnd_69534 : Nat := 4983230072969 + 3 ^ 40 * 69534 * 2
def baseEnd_69534 : Nat := 21158141528791811321615

theorem tailTrace_69534 : CollatzResearch.WordTrace tailWord_69534 prefixEnd_69534 21158141528791811321615 := by
  unfold tailWord_69534
  simp only [CollatzResearch.WordTrace]
  refine ⟨317014166262208538356957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1690742220065112204570437 317014166262208538356957)
  ·
    refine ⟨118880312348328201883859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 317014166262208538356957 118880312348328201883859)
    ·
      refine ⟨178320468522492302825789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118880312348328201883859 178320468522492302825789)
      ·
        refine ⟨66870175695934613559671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 178320468522492302825789 66870175695934613559671)
        ·
          refine ⟨100305263543901920339507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66870175695934613559671 100305263543901920339507)
          ·
            refine ⟨150457895315852880509261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100305263543901920339507 150457895315852880509261)
            ·
              refine ⟨56421710743444830190973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150457895315852880509261 56421710743444830190973)
              ·
                refine ⟨21158141528791811321615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56421710743444830190973 21158141528791811321615)
                ·
                  rfl

theorem cell19_69534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_69534 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69534 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69534 prefixEnd_69534 := by exact prefixLift 69534
  have htrace : WordTrace (prefixWord ++ tailWord_69534) baseStart_69534 baseEnd_69534 := by
    simpa [prefixWord, tailWord_69534, baseEnd_69534] using wordTrace_append hprefix tailTrace_69534
  have hstable : (prefixWord ++ tailWord_69534).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69534).length < 2 ^ (prefixWord ++ tailWord_69534).sum := by decide
  have hdescent : baseEnd_69534 < baseStart_69534 := by decide
  rcases family_descends (prefixWord ++ tailWord_69534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69561 : List Nat := [1, 2, 1, 4, 2, 1, 8]
def baseStart_69561 : Nat := 118140960795 + 69561 * 2 ^ 59
def prefixEnd_69561 : Nat := 4983230072969 + 3 ^ 40 * 69561 * 2
def baseEnd_69561 : Nat := 7055452406421249573847

theorem tailTrace_69561 : CollatzResearch.WordTrace tailWord_69561 prefixEnd_69561 7055452406421249573847 := by
  unfold tailWord_69561
  simp only [CollatzResearch.WordTrace]
  refine ⟨2537098100999851918088537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1691398733999901278725691 2537098100999851918088537)
  ·
    refine ⟨1902823575749888938566403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2537098100999851918088537 1902823575749888938566403)
    ·
      refine ⟨2854235363624833407849605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902823575749888938566403 2854235363624833407849605)
      ·
        refine ⟨535169130679656263971801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2854235363624833407849605 535169130679656263971801)
        ·
          refine ⟨401376848009742197978851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535169130679656263971801 401376848009742197978851)
          ·
            refine ⟨602065272014613296968277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401376848009742197978851 602065272014613296968277)
            ·
              refine ⟨7055452406421249573847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 602065272014613296968277 7055452406421249573847)
              ·
                rfl

theorem cell19_69561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_69561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69561 prefixEnd_69561 := by exact prefixLift 69561
  have htrace : WordTrace (prefixWord ++ tailWord_69561) baseStart_69561 baseEnd_69561 := by
    simpa [prefixWord, tailWord_69561, baseEnd_69561] using wordTrace_append hprefix tailTrace_69561
  have hstable : (prefixWord ++ tailWord_69561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69561).length < 2 ^ (prefixWord ++ tailWord_69561).sum := by decide
  have hdescent : baseEnd_69561 < baseStart_69561 := by decide
  rcases family_descends (prefixWord ++ tailWord_69561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69593 : List Nat := [1, 2, 1, 2, 7, 1, 2, 3]
def baseStart_69593 : Nat := 118140960795 + 69593 * 2 ^ 59
def prefixEnd_69593 : Nat := 4983230072969 + 3 ^ 40 * 69593 * 2
def baseEnd_69593 : Nat := 21176094333897156010343

theorem tailTrace_69593 : CollatzResearch.WordTrace tailWord_69593 prefixEnd_69593 21176094333897156010343 := by
  unfold tailWord_69593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538265236883921383253433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1692176824589280922168955 2538265236883921383253433)
  ·
    refine ⟨1903698927662941037440075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2538265236883921383253433 1903698927662941037440075)
    ·
      refine ⟨2855548391494411556160113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903698927662941037440075 2855548391494411556160113)
      ·
        refine ⟨2141661293620808667120085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855548391494411556160113 2141661293620808667120085)
        ·
          refine ⟨50195186569237703135627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2141661293620808667120085 50195186569237703135627)
          ·
            refine ⟨75292779853856554703441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50195186569237703135627 75292779853856554703441)
            ·
              refine ⟨56469584890392416027581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75292779853856554703441 56469584890392416027581)
              ·
                refine ⟨21176094333897156010343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56469584890392416027581 21176094333897156010343)
                ·
                  rfl

theorem cell19_69593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_69593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69593 prefixEnd_69593 := by exact prefixLift 69593
  have htrace : WordTrace (prefixWord ++ tailWord_69593) baseStart_69593 baseEnd_69593 := by
    simpa [prefixWord, tailWord_69593, baseEnd_69593] using wordTrace_append hprefix tailTrace_69593
  have hstable : (prefixWord ++ tailWord_69593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69593).length < 2 ^ (prefixWord ++ tailWord_69593).sum := by decide
  have hdescent : baseEnd_69593 < baseStart_69593 := by decide
  rcases family_descends (prefixWord ++ tailWord_69593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69637 : List Nat := [1, 3, 1, 1, 2, 4, 1, 6]
def baseStart_69637 : Nat := 118140960795 + 69637 * 2 ^ 59
def prefixEnd_69637 : Nat := 4983230072969 + 3 ^ 40 * 69637 * 2
def baseEnd_69637 : Nat := 21189482866518091032445

theorem tailTrace_69637 : CollatzResearch.WordTrace tailWord_69637 prefixEnd_69637 21189482866518091032445 := by
  unfold tailWord_69637
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539870048724516897855165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1693246699149677931903443 2539870048724516897855165)
  ·
    refine ⟨952451268271693836695687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2539870048724516897855165 952451268271693836695687)
    ·
      refine ⟨1428676902407540755043531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952451268271693836695687 1428676902407540755043531)
      ·
        refine ⟨2143015353611311132565297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428676902407540755043531 2143015353611311132565297)
        ·
          refine ⟨1607261515208483349423973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2143015353611311132565297 1607261515208483349423973)
          ·
            refine ⟨301361534101590628016995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1607261515208483349423973 301361534101590628016995)
            ·
              refine ⟨452042301152385942025493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301361534101590628016995 452042301152385942025493)
              ·
                refine ⟨21189482866518091032445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 452042301152385942025493 21189482866518091032445)
                ·
                  rfl

theorem cell19_69637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_69637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69637 prefixEnd_69637 := by exact prefixLift 69637
  have htrace : WordTrace (prefixWord ++ tailWord_69637) baseStart_69637 baseEnd_69637 := by
    simpa [prefixWord, tailWord_69637, baseEnd_69637] using wordTrace_append hprefix tailTrace_69637
  have hstable : (prefixWord ++ tailWord_69637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69637).length < 2 ^ (prefixWord ++ tailWord_69637).sum := by decide
  have hdescent : baseEnd_69637 < baseStart_69637 := by decide
  rcases family_descends (prefixWord ++ tailWord_69637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69656 : List Nat := [2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_69656 : Nat := 118140960795 + 69656 * 2 ^ 59
def prefixEnd_69656 : Nat := 4983230072969 + 3 ^ 40 * 69656 * 2
def baseEnd_69656 : Nat := 21195264278331676610171

theorem tailTrace_69656 : CollatzResearch.WordTrace tailWord_69656 prefixEnd_69656 21195264278331676610171 := by
  unfold tailWord_69656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270281517827841571398411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1693708690437122095197881 1270281517827841571398411)
  ·
    refine ⟨1905422276741762357097617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1270281517827841571398411 1905422276741762357097617)
    ·
      refine ⟨1429066707556321767823213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1905422276741762357097617 1429066707556321767823213)
      ·
        refine ⟨535900015333620662933705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1429066707556321767823213 535900015333620662933705)
        ·
          refine ⟨401925011500215497200279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 535900015333620662933705 401925011500215497200279)
          ·
            refine ⟨602887517250323245800419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401925011500215497200279 602887517250323245800419)
            ·
              refine ⟨904331275875484868700629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602887517250323245800419 904331275875484868700629)
              ·
                refine ⟨21195264278331676610171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 904331275875484868700629 21195264278331676610171)
                ·
                  rfl

theorem cell19_69656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_69656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69656 prefixEnd_69656 := by exact prefixLift 69656
  have htrace : WordTrace (prefixWord ++ tailWord_69656) baseStart_69656 baseEnd_69656 := by
    simpa [prefixWord, tailWord_69656, baseEnd_69656] using wordTrace_append hprefix tailTrace_69656
  have hstable : (prefixWord ++ tailWord_69656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69656).length < 2 ^ (prefixWord ++ tailWord_69656).sum := by decide
  have hdescent : baseEnd_69656 < baseStart_69656 := by decide
  rcases family_descends (prefixWord ++ tailWord_69656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69671 : List Nat := [1, 1, 7, 1, 3, 6]
def baseStart_69671 : Nat := 118140960795 + 69671 * 2 ^ 59
def prefixEnd_69671 : Nat := 4983230072969 + 3 ^ 40 * 69671 * 2
def baseEnd_69671 : Nat := 2355536505646231808533

theorem tailTrace_69671 : CollatzResearch.WordTrace tailWord_69671 prefixEnd_69671 2355536505646231808533 := by
  unfold tailWord_69671
  simp only [CollatzResearch.WordTrace]
  refine ⟨2541110130601340704592867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694073420400893803061911 2541110130601340704592867)
  ·
    refine ⟨3811665195902011056889301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2541110130601340704592867 3811665195902011056889301)
    ·
      refine ⟨89335903028953384145843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3811665195902011056889301 89335903028953384145843)
      ·
        refine ⟨134003854543430076218765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89335903028953384145843 134003854543430076218765)
        ·
          refine ⟨50251445453786278582037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134003854543430076218765 50251445453786278582037)
          ·
            refine ⟨2355536505646231808533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50251445453786278582037 2355536505646231808533)
            ·
              rfl

theorem cell19_69671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 6].length) (baseStart_69671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69671 prefixEnd_69671 := by exact prefixLift 69671
  have htrace : WordTrace (prefixWord ++ tailWord_69671) baseStart_69671 baseEnd_69671 := by
    simpa [prefixWord, tailWord_69671, baseEnd_69671] using wordTrace_append hprefix tailTrace_69671
  have hstable : (prefixWord ++ tailWord_69671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69671).length < 2 ^ (prefixWord ++ tailWord_69671).sum := by decide
  have hdescent : baseEnd_69671 < baseStart_69671 := by decide
  rcases family_descends (prefixWord ++ tailWord_69671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69709 : List Nat := [1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_69709 : Nat := 118140960795 + 69709 * 2 ^ 59
def prefixEnd_69709 : Nat := 4983230072969 + 3 ^ 40 * 69709 * 2
def baseEnd_69709 : Nat := 21211391374443257432249

theorem tailTrace_69709 : CollatzResearch.WordTrace tailWord_69709 prefixEnd_69709 21211391374443257432249 := by
  unfold tailWord_69709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542496104463673194476181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1694997402975782129650787 2542496104463673194476181)
  ·
    refine ⟨119179504896734680991071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2542496104463673194476181 119179504896734680991071)
    ·
      refine ⟨178769257345102021486607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119179504896734680991071 178769257345102021486607)
      ·
        refine ⟨268153886017653032229911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178769257345102021486607 268153886017653032229911)
        ·
          refine ⟨402230829026479548344867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268153886017653032229911 402230829026479548344867)
          ·
            refine ⟨603346243539719322517301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402230829026479548344867 603346243539719322517301)
            ·
              refine ⟨56563710331848686485997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 603346243539719322517301 56563710331848686485997)
              ·
                refine ⟨21211391374443257432249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56563710331848686485997 21211391374443257432249)
                ·
                  rfl

theorem cell19_69709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_69709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69709 prefixEnd_69709 := by exact prefixLift 69709
  have htrace : WordTrace (prefixWord ++ tailWord_69709) baseStart_69709 baseEnd_69709 := by
    simpa [prefixWord, tailWord_69709, baseEnd_69709] using wordTrace_append hprefix tailTrace_69709
  have hstable : (prefixWord ++ tailWord_69709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69709).length < 2 ^ (prefixWord ++ tailWord_69709).sum := by decide
  have hdescent : baseEnd_69709 < baseStart_69709 := by decide
  rcases family_descends (prefixWord ++ tailWord_69709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69726 : List Nat := [4, 4, 1, 1, 2, 1, 6]
def baseStart_69726 : Nat := 118140960795 + 69726 * 2 ^ 59
def prefixEnd_69726 : Nat := 4983230072969 + 3 ^ 40 * 69726 * 2
def baseEnd_69726 : Nat := 7072188072197418351475

theorem tailTrace_69726 : CollatzResearch.WordTrace tailWord_69726 prefixEnd_69726 7072188072197418351475 := by
  unfold tailWord_69726
  simp only [CollatzResearch.WordTrace]
  refine ⟨317889518175260637230629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1695410763601390065230021 317889518175260637230629)
  ·
    refine ⟨59604284657861369480743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 317889518175260637230629 59604284657861369480743)
    ·
      refine ⟨89406426986792054221115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59604284657861369480743 89406426986792054221115)
      ·
        refine ⟨134109640480188081331673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89406426986792054221115 134109640480188081331673)
        ·
          refine ⟨100582230360141060998755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134109640480188081331673 100582230360141060998755)
          ·
            refine ⟨150873345540211591498133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100582230360141060998755 150873345540211591498133)
            ·
              refine ⟨7072188072197418351475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 150873345540211591498133 7072188072197418351475)
              ·
                rfl

theorem cell19_69726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_69726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69726 prefixEnd_69726 := by exact prefixLift 69726
  have htrace : WordTrace (prefixWord ++ tailWord_69726) baseStart_69726 baseEnd_69726 := by
    simpa [prefixWord, tailWord_69726, baseEnd_69726] using wordTrace_append hprefix tailTrace_69726
  have hstable : (prefixWord ++ tailWord_69726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69726).length < 2 ^ (prefixWord ++ tailWord_69726).sum := by decide
  have hdescent : baseEnd_69726 < baseStart_69726 := by decide
  rcases family_descends (prefixWord ++ tailWord_69726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69768 : List Nat := [2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_69768 : Nat := 118140960795 + 69768 * 2 ^ 59
def prefixEnd_69768 : Nat := 4983230072969 + 3 ^ 40 * 69768 * 2
def baseEnd_69768 : Nat := 21229344179548602120977

theorem tailTrace_69768 : CollatzResearch.WordTrace tailWord_69768 prefixEnd_69768 21229344179548602120977 := by
  unfold tailWord_69768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272324005624963135436979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1696432007499950847249305 1272324005624963135436979)
  ·
    refine ⟨1908486008437444703155469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1272324005624963135436979 1908486008437444703155469)
    ·
      refine ⟨715682253164041763683301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1908486008437444703155469 715682253164041763683301)
      ·
        refine ⟨134190422468257830690619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 715682253164041763683301 134190422468257830690619)
        ·
          refine ⟨201285633702386746035929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134190422468257830690619 201285633702386746035929)
          ·
            refine ⟨150964225276790059526947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201285633702386746035929 150964225276790059526947)
            ·
              refine ⟨226446337915185089290421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150964225276790059526947 226446337915185089290421)
              ·
                refine ⟨21229344179548602120977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 226446337915185089290421 21229344179548602120977)
                ·
                  rfl

theorem cell19_69768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_69768 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69768 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69768 prefixEnd_69768 := by exact prefixLift 69768
  have htrace : WordTrace (prefixWord ++ tailWord_69768) baseStart_69768 baseEnd_69768 := by
    simpa [prefixWord, tailWord_69768, baseEnd_69768] using wordTrace_append hprefix tailTrace_69768
  have hstable : (prefixWord ++ tailWord_69768).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69768).length < 2 ^ (prefixWord ++ tailWord_69768).sum := by decide
  have hdescent : baseEnd_69768 < baseStart_69768 := by decide
  rcases family_descends (prefixWord ++ tailWord_69768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69789 : List Nat := [1, 4, 2, 1, 1, 3, 7]
def baseStart_69789 : Nat := 118140960795 + 69789 * 2 ^ 59
def prefixEnd_69789 : Nat := 4983230072969 + 3 ^ 40 * 69789 * 2
def baseEnd_69789 : Nat := 7078578053675591884751

theorem tailTrace_69789 : CollatzResearch.WordTrace tailWord_69789 prefixEnd_69789 7078578053675591884751 := by
  unfold tailWord_69789
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545413944173846857388421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1696942629449231238258947 2545413944173846857388421)
  ·
    refine ⟨477265114532596285760329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2545413944173846857388421 477265114532596285760329)
    ·
      refine ⟨357948835899447214320247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 477265114532596285760329 357948835899447214320247)
      ·
        refine ⟨536923253849170821480371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 357948835899447214320247 536923253849170821480371)
        ·
          refine ⟨805384880773756232220557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536923253849170821480371 805384880773756232220557)
          ·
            refine ⟨302019330290158587082709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 805384880773756232220557 302019330290158587082709)
            ·
              refine ⟨7078578053675591884751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 302019330290158587082709 7078578053675591884751)
              ·
                rfl

theorem cell19_69789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_69789 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69789 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69789 prefixEnd_69789 := by exact prefixLift 69789
  have htrace : WordTrace (prefixWord ++ tailWord_69789) baseStart_69789 baseEnd_69789 := by
    simpa [prefixWord, tailWord_69789, baseEnd_69789] using wordTrace_append hprefix tailTrace_69789
  have hstable : (prefixWord ++ tailWord_69789).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69789).length < 2 ^ (prefixWord ++ tailWord_69789).sum := by decide
  have hdescent : baseEnd_69789 < baseStart_69789 := by decide
  rcases family_descends (prefixWord ++ tailWord_69789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69859 : List Nat := [1, 1, 1, 8, 2, 1, 1, 4]
def baseStart_69859 : Nat := 118140960795 + 69859 * 2 ^ 59
def prefixEnd_69859 : Nat := 4983230072969 + 3 ^ 40 * 69859 * 2
def baseEnd_69859 : Nat := 21257034099287354098507

theorem tailTrace_69859 : CollatzResearch.WordTrace tailWord_69859 prefixEnd_69859 21257034099287354098507 := by
  unfold tailWord_69859
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547967053920248812436631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1698644702613499208291087 2547967053920248812436631)
  ·
    refine ⟨3821950580880373218654947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547967053920248812436631 3821950580880373218654947)
    ·
      refine ⟨5732925871320559827982421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3821950580880373218654947 5732925871320559827982421)
      ·
        refine ⟨67182725054537810484169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 5732925871320559827982421 67182725054537810484169)
        ·
          refine ⟨50387043790903357863127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67182725054537810484169 50387043790903357863127)
          ·
            refine ⟨75580565686355036794691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50387043790903357863127 75580565686355036794691)
            ·
              refine ⟨113370848529532555192037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75580565686355036794691 113370848529532555192037)
              ·
                refine ⟨21257034099287354098507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113370848529532555192037 21257034099287354098507)
                ·
                  rfl

theorem cell19_69859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 4].length) (baseStart_69859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69859 prefixEnd_69859 := by exact prefixLift 69859
  have htrace : WordTrace (prefixWord ++ tailWord_69859) baseStart_69859 baseEnd_69859 := by
    simpa [prefixWord, tailWord_69859, baseEnd_69859] using wordTrace_append hprefix tailTrace_69859
  have hstable : (prefixWord ++ tailWord_69859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69859).length < 2 ^ (prefixWord ++ tailWord_69859).sum := by decide
  have hdescent : baseEnd_69859 < baseStart_69859 := by decide
  rcases family_descends (prefixWord ++ tailWord_69859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69863 : List Nat := [1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_69863 : Nat := 118140960795 + 69863 * 2 ^ 59
def prefixEnd_69863 : Nat := 4983230072969 + 3 ^ 40 * 69863 * 2
def baseEnd_69863 : Nat := 21258251238616530009607

theorem tailTrace_69863 : CollatzResearch.WordTrace tailWord_69863 prefixEnd_69863 21258251238616530009607 := by
  unfold tailWord_69863
  simp only [CollatzResearch.WordTrace]
  refine ⟨2548112945905757495582243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1698741963937171663721495 2548112945905757495582243)
  ·
    refine ⟨3822169418858636243373365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2548112945905757495582243 3822169418858636243373365)
    ·
      refine ⟨358328383017997147816253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3822169418858636243373365 358328383017997147816253)
      ·
        refine ⟨134373143631748930431095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 358328383017997147816253 134373143631748930431095)
        ·
          refine ⟨201559715447623395646643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134373143631748930431095 201559715447623395646643)
          ·
            refine ⟨302339573171435093469965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201559715447623395646643 302339573171435093469965)
            ·
              refine ⟨113377339939288160051237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302339573171435093469965 113377339939288160051237)
              ·
                refine ⟨21258251238616530009607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113377339939288160051237 21258251238616530009607)
                ·
                  rfl

theorem cell19_69863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_69863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69863 prefixEnd_69863 := by exact prefixLift 69863
  have htrace : WordTrace (prefixWord ++ tailWord_69863) baseStart_69863 baseEnd_69863 := by
    simpa [prefixWord, tailWord_69863, baseEnd_69863] using wordTrace_append hprefix tailTrace_69863
  have hstable : (prefixWord ++ tailWord_69863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69863).length < 2 ^ (prefixWord ++ tailWord_69863).sum := by decide
  have hdescent : baseEnd_69863 < baseStart_69863 := by decide
  rcases family_descends (prefixWord ++ tailWord_69863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69882 : List Nat := [3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_69882 : Nat := 118140960795 + 69882 * 2 ^ 59
def prefixEnd_69882 : Nat := 4983230072969 + 3 ^ 40 * 69882 * 2
def baseEnd_69882 : Nat := 21264032650430115587333

theorem tailTrace_69882 : CollatzResearch.WordTrace tailWord_69882 prefixEnd_69882 21264032650430115587333 := by
  unfold tailWord_69882
  simp only [CollatzResearch.WordTrace]
  refine ⟨637201483209230935130975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1699203955224615827015933 637201483209230935130975)
  ·
    refine ⟨955802224813846402696463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 637201483209230935130975 955802224813846402696463)
    ·
      refine ⟨1433703337220769604044695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955802224813846402696463 1433703337220769604044695)
      ·
        refine ⟨2150555005831154406067043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433703337220769604044695 2150555005831154406067043)
        ·
          refine ⟨3225832508746731609100565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2150555005831154406067043 3225832508746731609100565)
          ·
            refine ⟨151210898847503044176589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3225832508746731609100565 151210898847503044176589)
            ·
              refine ⟨56704087067813641566221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151210898847503044176589 56704087067813641566221)
              ·
                refine ⟨21264032650430115587333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56704087067813641566221 21264032650430115587333)
                ·
                  rfl

theorem cell19_69882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_69882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69882 prefixEnd_69882 := by exact prefixLift 69882
  have htrace : WordTrace (prefixWord ++ tailWord_69882) baseStart_69882 baseEnd_69882 := by
    simpa [prefixWord, tailWord_69882, baseEnd_69882] using wordTrace_append hprefix tailTrace_69882
  have hstable : (prefixWord ++ tailWord_69882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69882).length < 2 ^ (prefixWord ++ tailWord_69882).sum := by decide
  have hdescent : baseEnd_69882 < baseStart_69882 := by decide
  rcases family_descends (prefixWord ++ tailWord_69882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69933 : List Nat := [1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_69933 : Nat := 118140960795 + 69933 * 2 ^ 59
def prefixEnd_69933 : Nat := 4983230072969 + 3 ^ 40 * 69933 * 2
def baseEnd_69933 : Nat := 21279551176877108453861

theorem tailTrace_69933 : CollatzResearch.WordTrace tailWord_69933 prefixEnd_69933 21279551176877108453861 := by
  unfold tailWord_69933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550666055652159450630453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1700444037101439633753635 2550666055652159450630453)
  ·
    refine ⟨239124942717389948496605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2550666055652159450630453 239124942717389948496605)
    ·
      refine ⟨89671853519021230686227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239124942717389948496605 89671853519021230686227)
      ·
        refine ⟨134507780278531846029341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89671853519021230686227 134507780278531846029341)
        ·
          refine ⟨50440417604449442261003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134507780278531846029341 50440417604449442261003)
          ·
            refine ⟨75660626406674163391505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50440417604449442261003 75660626406674163391505)
            ·
              refine ⟨56745469805005622543629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75660626406674163391505 56745469805005622543629)
              ·
                refine ⟨21279551176877108453861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56745469805005622543629 21279551176877108453861)
                ·
                  rfl

theorem cell19_69933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_69933 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69933 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69933 prefixEnd_69933 := by exact prefixLift 69933
  have htrace : WordTrace (prefixWord ++ tailWord_69933) baseStart_69933 baseEnd_69933 := by
    simpa [prefixWord, tailWord_69933, baseEnd_69933] using wordTrace_append hprefix tailTrace_69933
  have hstable : (prefixWord ++ tailWord_69933).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69933).length < 2 ^ (prefixWord ++ tailWord_69933).sum := by decide
  have hdescent : baseEnd_69933 < baseStart_69933 := by decide
  rcases family_descends (prefixWord ++ tailWord_69933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69937 : List Nat := [1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_69937 : Nat := 118140960795 + 69937 * 2 ^ 59
def prefixEnd_69937 : Nat := 4983230072969 + 3 ^ 40 * 69937 * 2
def baseEnd_69937 : Nat := 21280768316206284364961

theorem tailTrace_69937 : CollatzResearch.WordTrace tailWord_69937 prefixEnd_69937 21280768316206284364961 := by
  unfold tailWord_69937
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550811947637668133776065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1700541298425112089184043 2550811947637668133776065)
  ·
    refine ⟨1913108960728251100332049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2550811947637668133776065 1913108960728251100332049)
    ·
      refine ⟨1434831720546188325249037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1913108960728251100332049 1434831720546188325249037)
      ·
        refine ⟨538061895204820621968389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1434831720546188325249037 538061895204820621968389)
        ·
          refine ⟨100886605350903866619073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 538061895204820621968389 100886605350903866619073)
          ·
            refine ⟨75664954013177899964305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100886605350903866619073 75664954013177899964305)
            ·
              refine ⟨56748715509883424973229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75664954013177899964305 56748715509883424973229)
              ·
                refine ⟨21280768316206284364961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56748715509883424973229 21280768316206284364961)
                ·
                  rfl

theorem cell19_69937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_69937 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69937 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69937 prefixEnd_69937 := by exact prefixLift 69937
  have htrace : WordTrace (prefixWord ++ tailWord_69937) baseStart_69937 baseEnd_69937 := by
    simpa [prefixWord, tailWord_69937, baseEnd_69937] using wordTrace_append hprefix tailTrace_69937
  have hstable : (prefixWord ++ tailWord_69937).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69937).length < 2 ^ (prefixWord ++ tailWord_69937).sum := by decide
  have hdescent : baseEnd_69937 < baseStart_69937 := by decide
  rcases family_descends (prefixWord ++ tailWord_69937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69941 : List Nat := [1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_69941 : Nat := 118140960795 + 69941 * 2 ^ 59
def prefixEnd_69941 : Nat := 4983230072969 + 3 ^ 40 * 69941 * 2
def baseEnd_69941 : Nat := 21281985455535460276061

theorem tailTrace_69941 : CollatzResearch.WordTrace tailWord_69941 prefixEnd_69941 21281985455535460276061 := by
  unfold tailWord_69941
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550957839623176816921677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1700638559748784544614451 2550957839623176816921677)
  ·
    refine ⟨956609189858691306345629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2550957839623176816921677 956609189858691306345629)
    ·
      refine ⟨358728446197009239879611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 956609189858691306345629 358728446197009239879611)
      ·
        refine ⟨538092669295513859819417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358728446197009239879611 538092669295513859819417)
        ·
          refine ⟨403569501971635394864563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538092669295513859819417 403569501971635394864563)
          ·
            refine ⟨605354252957453092296845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403569501971635394864563 605354252957453092296845)
            ·
              refine ⟨227007844859044909611317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 605354252957453092296845 227007844859044909611317)
              ·
                refine ⟨21281985455535460276061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227007844859044909611317 21281985455535460276061)
                ·
                  rfl

theorem cell19_69941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_69941 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69941 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69941 prefixEnd_69941 := by exact prefixLift 69941
  have htrace : WordTrace (prefixWord ++ tailWord_69941) baseStart_69941 baseEnd_69941 := by
    simpa [prefixWord, tailWord_69941, baseEnd_69941] using wordTrace_append hprefix tailTrace_69941
  have hstable : (prefixWord ++ tailWord_69941).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69941).length < 2 ^ (prefixWord ++ tailWord_69941).sum := by decide
  have hdescent : baseEnd_69941 < baseStart_69941 := by decide
  rcases family_descends (prefixWord ++ tailWord_69941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_69956 : List Nat := [2, 3, 4, 1, 2, 2, 5]
def baseStart_69956 : Nat := 118140960795 + 69956 * 2 ^ 59
def prefixEnd_69956 : Nat := 4983230072969 + 3 ^ 40 * 69956 * 2
def baseEnd_69956 : Nat := 7095516576006623314229

theorem tailTrace_69956 : CollatzResearch.WordTrace tailWord_69956 prefixEnd_69956 7095516576006623314229 := by
  unfold tailWord_69956
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275752467284417189358861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1701003289712556252478481 1275752467284417189358861)
  ·
    refine ⟨478407175231656446009573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1275752467284417189358861 478407175231656446009573)
    ·
      refine ⟨89701345355935583626795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 478407175231656446009573 89701345355935583626795)
      ·
        refine ⟨134552018033903375440193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89701345355935583626795 134552018033903375440193)
        ·
          refine ⟨100914013525427531580145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134552018033903375440193 100914013525427531580145)
          ·
            refine ⟨75685510144070648685109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100914013525427531580145 75685510144070648685109)
            ·
              refine ⟨7095516576006623314229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75685510144070648685109 7095516576006623314229)
              ·
                rfl

theorem cell19_69956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_69956 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_69956 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_69956 prefixEnd_69956 := by exact prefixLift 69956
  have htrace : WordTrace (prefixWord ++ tailWord_69956) baseStart_69956 baseEnd_69956 := by
    simpa [prefixWord, tailWord_69956, baseEnd_69956] using wordTrace_append hprefix tailTrace_69956
  have hstable : (prefixWord ++ tailWord_69956).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_69956).length < 2 ^ (prefixWord ++ tailWord_69956).sum := by decide
  have hdescent : baseEnd_69956 < baseStart_69956 := by decide
  rcases family_descends (prefixWord ++ tailWord_69956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70017 : List Nat := [1, 2, 4, 3, 1, 8]
def baseStart_70017 : Nat := 118140960795 + 70017 * 2 ^ 59
def prefixEnd_70017 : Nat := 4983230072969 + 3 ^ 40 * 70017 * 2
def baseEnd_70017 : Nat := 2367234566976644731885

theorem tailTrace_70017 : CollatzResearch.WordTrace tailWord_70017 prefixEnd_70017 2367234566976644731885 := by
  unfold tailWord_70017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553729787347841796688305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1702486524898561197792203 2553729787347841796688305)
  ·
    refine ⟨1915297340510881347516229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553729787347841796688305 1915297340510881347516229)
    ·
      refine ⟨359118251345790252659293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1915297340510881347516229 359118251345790252659293)
      ·
        refine ⟨134669344254671344747235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359118251345790252659293 134669344254671344747235)
        ·
          refine ⟨202004016382007017120853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134669344254671344747235 202004016382007017120853)
          ·
            refine ⟨2367234566976644731885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 202004016382007017120853 2367234566976644731885)
            ·
              rfl

theorem cell19_70017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_70017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70017 prefixEnd_70017 := by exact prefixLift 70017
  have htrace : WordTrace (prefixWord ++ tailWord_70017) baseStart_70017 baseEnd_70017 := by
    simpa [prefixWord, tailWord_70017, baseEnd_70017] using wordTrace_append hprefix tailTrace_70017
  have hstable : (prefixWord ++ tailWord_70017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70017).length < 2 ^ (prefixWord ++ tailWord_70017).sum := by decide
  have hdescent : baseEnd_70017 < baseStart_70017 := by decide
  rcases family_descends (prefixWord ++ tailWord_70017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70019 : List Nat := [1, 1, 1, 3, 13]
def baseStart_70019 : Nat := 118140960795 + 70019 * 2 ^ 59
def prefixEnd_70019 : Nat := 4983230072969 + 3 ^ 40 * 70019 * 2
def baseEnd_70019 : Nat := 789100728609421871945

theorem tailTrace_70019 : CollatzResearch.WordTrace tailWord_70019 prefixEnd_70019 789100728609421871945 := by
  unfold tailWord_70019
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553802733340596138261111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1702535155560397425507407 2553802733340596138261111)
  ·
    refine ⟨3830704100010894207391667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2553802733340596138261111 3830704100010894207391667)
    ·
      refine ⟨5746056150016341311087501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3830704100010894207391667 5746056150016341311087501)
      ·
        refine ⟨2154771056256127991657813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5746056150016341311087501 2154771056256127991657813)
        ·
          refine ⟨789100728609421871945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 2154771056256127991657813 789100728609421871945)
          ·
            rfl

theorem cell19_70019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 13].length) (baseStart_70019 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70019 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70019 prefixEnd_70019 := by exact prefixLift 70019
  have htrace : WordTrace (prefixWord ++ tailWord_70019) baseStart_70019 baseEnd_70019 := by
    simpa [prefixWord, tailWord_70019, baseEnd_70019] using wordTrace_append hprefix tailTrace_70019
  have hstable : (prefixWord ++ tailWord_70019).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70019).length < 2 ^ (prefixWord ++ tailWord_70019).sum := by decide
  have hdescent : baseEnd_70019 < baseStart_70019 := by decide
  rcases family_descends (prefixWord ++ tailWord_70019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70057 : List Nat := [1, 2, 1, 1, 1, 1, 3, 9]
def baseStart_70057 : Nat := 118140960795 + 70057 * 2 ^ 59
def prefixEnd_70057 : Nat := 4983230072969 + 3 ^ 40 * 70057 * 2
def baseEnd_70057 : Nat := 21317282496081561697967

theorem tailTrace_70057 : CollatzResearch.WordTrace tailWord_70057 prefixEnd_70057 21317282496081561697967 := by
  unfold tailWord_70057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555188707202928628144425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1703459138135285752096283 2555188707202928628144425)
  ·
    refine ⟨1916391530402196471108319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2555188707202928628144425 1916391530402196471108319)
    ·
      refine ⟨2874587295603294706662479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1916391530402196471108319 2874587295603294706662479)
      ·
        refine ⟨4311880943404942059993719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874587295603294706662479 4311880943404942059993719)
        ·
          refine ⟨6467821415107413089990579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4311880943404942059993719 6467821415107413089990579)
          ·
            refine ⟨9701732122661119634985869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6467821415107413089990579 9701732122661119634985869)
            ·
              refine ⟨3638149545997919863119701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9701732122661119634985869 3638149545997919863119701)
              ·
                refine ⟨21317282496081561697967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3638149545997919863119701 21317282496081561697967)
                ·
                  rfl

theorem cell19_70057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_70057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70057 prefixEnd_70057 := by exact prefixLift 70057
  have htrace : WordTrace (prefixWord ++ tailWord_70057) baseStart_70057 baseEnd_70057 := by
    simpa [prefixWord, tailWord_70057, baseEnd_70057] using wordTrace_append hprefix tailTrace_70057
  have hstable : (prefixWord ++ tailWord_70057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70057).length < 2 ^ (prefixWord ++ tailWord_70057).sum := by decide
  have hdescent : baseEnd_70057 < baseStart_70057 := by decide
  rcases family_descends (prefixWord ++ tailWord_70057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70095 : List Nat := [1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_70095 : Nat := 118140960795 + 70095 * 2 ^ 59
def prefixEnd_70095 : Nat := 4983230072969 + 3 ^ 40 * 70095 * 2
def baseEnd_70095 : Nat := 21328845319708732853419

theorem tailTrace_70095 : CollatzResearch.WordTrace tailWord_70095 prefixEnd_70095 21328845319708732853419 := by
  unfold tailWord_70095
  simp only [CollatzResearch.WordTrace]
  refine ⟨2556574681065261118027739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1704383120710174078685159 2556574681065261118027739)
  ·
    refine ⟨3834862021597891677041609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2556574681065261118027739 3834862021597891677041609)
    ·
      refine ⟨2876146516198418757781207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3834862021597891677041609 2876146516198418757781207)
      ·
        refine ⟨4314219774297628136671811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876146516198418757781207 4314219774297628136671811)
        ·
          refine ⟨6471329661446442205007717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314219774297628136671811 6471329661446442205007717)
          ·
            refine ⟨1213374311521207913438947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6471329661446442205007717 1213374311521207913438947)
            ·
              refine ⟨1820061467281811870158421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1213374311521207913438947 1820061467281811870158421)
              ·
                refine ⟨21328845319708732853419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1820061467281811870158421 21328845319708732853419)
                ·
                  rfl

theorem cell19_70095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_70095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70095 prefixEnd_70095 := by exact prefixLift 70095
  have htrace : WordTrace (prefixWord ++ tailWord_70095) baseStart_70095 baseEnd_70095 := by
    simpa [prefixWord, tailWord_70095, baseEnd_70095] using wordTrace_append hprefix tailTrace_70095
  have hstable : (prefixWord ++ tailWord_70095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70095).length < 2 ^ (prefixWord ++ tailWord_70095).sum := by decide
  have hdescent : baseEnd_70095 < baseStart_70095 := by decide
  rcases family_descends (prefixWord ++ tailWord_70095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70146 : List Nat := [3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_70146 : Nat := 118140960795 + 70146 * 2 ^ 59
def prefixEnd_70146 : Nat := 4983230072969 + 3 ^ 40 * 70146 * 2
def baseEnd_70146 : Nat := 21344363846155725719947

theorem tailTrace_70146 : CollatzResearch.WordTrace tailWord_70146 prefixEnd_70146 21344363846155725719947 := by
  unfold tailWord_70146
  simp only [CollatzResearch.WordTrace]
  refine ⟨639608700970124207033573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1705623202586997885422861 639608700970124207033573)
  ·
    refine ⟨119926631431898288818795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 639608700970124207033573 119926631431898288818795)
    ·
      refine ⟨179889947147847433228193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119926631431898288818795 179889947147847433228193)
      ·
        refine ⟨134917460360885574921145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179889947147847433228193 134917460360885574921145)
        ·
          refine ⟨101188095270664181190859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134917460360885574921145 101188095270664181190859)
          ·
            refine ⟨151782142905996271786289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101188095270664181190859 151782142905996271786289)
            ·
              refine ⟨113836607179497203839717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151782142905996271786289 113836607179497203839717)
              ·
                refine ⟨21344363846155725719947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113836607179497203839717 21344363846155725719947)
                ·
                  rfl

theorem cell19_70146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_70146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70146 prefixEnd_70146 := by exact prefixLift 70146
  have htrace : WordTrace (prefixWord ++ tailWord_70146) baseStart_70146 baseEnd_70146 := by
    simpa [prefixWord, tailWord_70146, baseEnd_70146] using wordTrace_append hprefix tailTrace_70146
  have hstable : (prefixWord ++ tailWord_70146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70146).length < 2 ^ (prefixWord ++ tailWord_70146).sum := by decide
  have hdescent : baseEnd_70146 < baseStart_70146 := by decide
  rcases family_descends (prefixWord ++ tailWord_70146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70148 : List Nat := [2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_70148 : Nat := 118140960795 + 70148 * 2 ^ 59
def prefixEnd_70148 : Nat := 4983230072969 + 3 ^ 40 * 70148 * 2
def baseEnd_70148 : Nat := 21344972415820313675497

theorem tailTrace_70148 : CollatzResearch.WordTrace tailWord_70148 prefixEnd_70148 21344972415820313675497 := by
  unfold tailWord_70148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279253874936625584853549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1705671833248834113138065 1279253874936625584853549)
  ·
    refine ⟨479720203101234594320081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1279253874936625584853549 479720203101234594320081)
    ·
      refine ⟨359790152325925945740061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 479720203101234594320081 359790152325925945740061)
      ·
        refine ⟨134921307122222229652523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359790152325925945740061 134921307122222229652523)
        ·
          refine ⟨202381960683333344478785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134921307122222229652523 202381960683333344478785)
          ·
            refine ⟨151786470512500008359089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202381960683333344478785 151786470512500008359089)
            ·
              refine ⟨113839852884375006269317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151786470512500008359089 113839852884375006269317)
              ·
                refine ⟨21344972415820313675497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113839852884375006269317 21344972415820313675497)
                ·
                  rfl

theorem cell19_70148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_70148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70148 prefixEnd_70148 := by exact prefixLift 70148
  have htrace : WordTrace (prefixWord ++ tailWord_70148) baseStart_70148 baseEnd_70148 := by
    simpa [prefixWord, tailWord_70148, baseEnd_70148] using wordTrace_append hprefix tailTrace_70148
  have hstable : (prefixWord ++ tailWord_70148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70148).length < 2 ^ (prefixWord ++ tailWord_70148).sum := by decide
  have hdescent : baseEnd_70148 < baseStart_70148 := by decide
  rcases family_descends (prefixWord ++ tailWord_70148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70205 : List Nat := [1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_70205 : Nat := 118140960795 + 70205 * 2 ^ 59
def prefixEnd_70205 : Nat := 4983230072969 + 3 ^ 40 * 70205 * 2
def baseEnd_70205 : Nat := 21362316651261070408675

theorem tailTrace_70205 : CollatzResearch.WordTrace tailWord_70205 prefixEnd_70205 21362316651261070408675 := by
  unfold tailWord_70205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560586710666749904532069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1707057807111166603021379 2560586710666749904532069)
  ·
    refine ⟨480110008250015607099763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2560586710666749904532069 480110008250015607099763)
    ·
      refine ⟨720165012375023410649645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480110008250015607099763 720165012375023410649645)
      ·
        refine ⟨270061879640633778993617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 720165012375023410649645 270061879640633778993617)
        ·
          refine ⟨202546409730475334245213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270061879640633778993617 202546409730475334245213)
          ·
            refine ⟨75954903648928250341955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202546409730475334245213 75954903648928250341955)
            ·
              refine ⟨113932355473392375512933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75954903648928250341955 113932355473392375512933)
              ·
                refine ⟨21362316651261070408675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113932355473392375512933 21362316651261070408675)
                ·
                  rfl

theorem cell19_70205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_70205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70205 prefixEnd_70205 := by exact prefixLift 70205
  have htrace : WordTrace (prefixWord ++ tailWord_70205) baseStart_70205 baseEnd_70205 := by
    simpa [prefixWord, tailWord_70205, baseEnd_70205] using wordTrace_append hprefix tailTrace_70205
  have hstable : (prefixWord ++ tailWord_70205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70205).length < 2 ^ (prefixWord ++ tailWord_70205).sum := by decide
  have hdescent : baseEnd_70205 < baseStart_70205 := by decide
  rcases family_descends (prefixWord ++ tailWord_70205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70245 : List Nat := [1, 3, 1, 3, 4, 1, 6]
def baseStart_70245 : Nat := 118140960795 + 70245 * 2 ^ 59
def prefixEnd_70245 : Nat := 4983230072969 + 3 ^ 40 * 70245 * 2
def baseEnd_70245 : Nat := 7124829348184276506559

theorem tailTrace_70245 : CollatzResearch.WordTrace tailWord_70245 prefixEnd_70245 7124829348184276506559 := by
  unfold tailWord_70245
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562045630521836735988189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1708030420347891157325459 2562045630521836735988189)
  ·
    refine ⟨960767111445688775995571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2562045630521836735988189 960767111445688775995571)
    ·
      refine ⟨1441150667168533163993357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960767111445688775995571 1441150667168533163993357)
      ·
        refine ⟨540431500188199936497509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1441150667168533163993357 540431500188199936497509)
        ·
          refine ⟨101330906285287488093283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 540431500188199936497509 101330906285287488093283)
          ·
            refine ⟨151996359427931232139925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101330906285287488093283 151996359427931232139925)
            ·
              refine ⟨7124829348184276506559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 151996359427931232139925 7124829348184276506559)
              ·
                rfl

theorem cell19_70245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_70245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70245 prefixEnd_70245 := by exact prefixLift 70245
  have htrace : WordTrace (prefixWord ++ tailWord_70245) baseStart_70245 baseEnd_70245 := by
    simpa [prefixWord, tailWord_70245, baseEnd_70245] using wordTrace_append hprefix tailTrace_70245
  have hstable : (prefixWord ++ tailWord_70245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70245).length < 2 ^ (prefixWord ++ tailWord_70245).sum := by decide
  have hdescent : baseEnd_70245 < baseStart_70245 := by decide
  rcases family_descends (prefixWord ++ tailWord_70245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70298 : List Nat := [3, 1, 1, 6, 2, 1, 5]
def baseStart_70298 : Nat := 118140960795 + 70298 * 2 ^ 59
def prefixEnd_70298 : Nat := 4983230072969 + 3 ^ 40 * 70298 * 2
def baseEnd_70298 : Nat := 7130205046888136780585

theorem tailTrace_70298 : CollatzResearch.WordTrace tailWord_70298 prefixEnd_70298 7130205046888136780585 := by
  unfold tailWord_70298
  simp only [CollatzResearch.WordTrace]
  refine ⟨640994674832456696916887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1709319132886551191778365 640994674832456696916887)
  ·
    refine ⟨961492012248685045375331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640994674832456696916887 961492012248685045375331)
    ·
      refine ⟨1442238018373027568062997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 961492012248685045375331 1442238018373027568062997)
      ·
        refine ⟨67604907111235667252953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1442238018373027568062997 67604907111235667252953)
        ·
          refine ⟨50703680333426750439715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67604907111235667252953 50703680333426750439715)
          ·
            refine ⟨76055520500140125659573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50703680333426750439715 76055520500140125659573)
            ·
              refine ⟨7130205046888136780585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76055520500140125659573 7130205046888136780585)
              ·
                rfl

theorem cell19_70298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 5].length) (baseStart_70298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70298 prefixEnd_70298 := by exact prefixLift 70298
  have htrace : WordTrace (prefixWord ++ tailWord_70298) baseStart_70298 baseEnd_70298 := by
    simpa [prefixWord, tailWord_70298, baseEnd_70298] using wordTrace_append hprefix tailTrace_70298
  have hstable : (prefixWord ++ tailWord_70298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70298).length < 2 ^ (prefixWord ++ tailWord_70298).sum := by decide
  have hdescent : baseEnd_70298 < baseStart_70298 := by decide
  rcases family_descends (prefixWord ++ tailWord_70298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70323 : List Nat := [1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_70323 : Nat := 118140960795 + 70323 * 2 ^ 59
def prefixEnd_70323 : Nat := 4983230072969 + 3 ^ 40 * 70323 * 2
def baseEnd_70323 : Nat := 21398222261471759786131

theorem tailTrace_70323 : CollatzResearch.WordTrace tailWord_70323 prefixEnd_70323 21398222261471759786131 := by
  unfold tailWord_70323
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564890524239256057327623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1709927016159504038218415 2564890524239256057327623)
  ·
    refine ⟨3847335786358884085991435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2564890524239256057327623 3847335786358884085991435)
    ·
      refine ⟨5771003679538326128987153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3847335786358884085991435 5771003679538326128987153)
      ·
        refine ⟨4328252759653744596740365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5771003679538326128987153 4328252759653744596740365)
        ·
          refine ⟨1623094784870154223777637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4328252759653744596740365 1623094784870154223777637)
          ·
            refine ⟨304330272163153916958307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1623094784870154223777637 304330272163153916958307)
            ·
              refine ⟨456495408244730875437461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304330272163153916958307 456495408244730875437461)
              ·
                refine ⟨21398222261471759786131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 456495408244730875437461 21398222261471759786131)
                ·
                  rfl

theorem cell19_70323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_70323 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70323 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70323 prefixEnd_70323 := by exact prefixLift 70323
  have htrace : WordTrace (prefixWord ++ tailWord_70323) baseStart_70323 baseEnd_70323 := by
    simpa [prefixWord, tailWord_70323, baseEnd_70323] using wordTrace_append hprefix tailTrace_70323
  have hstable : (prefixWord ++ tailWord_70323).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70323).length < 2 ^ (prefixWord ++ tailWord_70323).sum := by decide
  have hdescent : baseEnd_70323 < baseStart_70323 := by decide
  rcases family_descends (prefixWord ++ tailWord_70323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70340 : List Nat := [2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_70340 : Nat := 118140960795 + 70340 * 2 ^ 59
def prefixEnd_70340 : Nat := 4983230072969 + 3 ^ 40 * 70340 * 2
def baseEnd_70340 : Nat := 21403395103620757408307

theorem tailTrace_70340 : CollatzResearch.WordTrace tailWord_70340 prefixEnd_70340 21403395103620757408307 := by
  unfold tailWord_70340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282755282588833980348237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1710340376785111973797649 1282755282588833980348237)
  ·
    refine ⟨481033230970812742630589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1282755282588833980348237 481033230970812742630589)
    ·
      refine ⟨180387461614054778486471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 481033230970812742630589 180387461614054778486471)
      ·
        refine ⟨270581192421082167729707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180387461614054778486471 270581192421082167729707)
        ·
          refine ⟨405871788631623251594561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270581192421082167729707 405871788631623251594561)
          ·
            refine ⟨304403841473717438695921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405871788631623251594561 304403841473717438695921)
            ·
              refine ⟨228302881105288079021941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304403841473717438695921 228302881105288079021941)
              ·
                refine ⟨21403395103620757408307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228302881105288079021941 21403395103620757408307)
                ·
                  rfl

theorem cell19_70340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_70340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70340 prefixEnd_70340 := by exact prefixLift 70340
  have htrace : WordTrace (prefixWord ++ tailWord_70340) baseStart_70340 baseEnd_70340 := by
    simpa [prefixWord, tailWord_70340, baseEnd_70340] using wordTrace_append hprefix tailTrace_70340
  have hstable : (prefixWord ++ tailWord_70340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70340).length < 2 ^ (prefixWord ++ tailWord_70340).sum := by decide
  have hdescent : baseEnd_70340 < baseStart_70340 := by decide
  rcases family_descends (prefixWord ++ tailWord_70340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70357 : List Nat := [1, 3, 2, 5, 2, 6]
def baseStart_70357 : Nat := 118140960795 + 70357 * 2 ^ 59
def prefixEnd_70357 : Nat := 4983230072969 + 3 ^ 40 * 70357 * 2
def baseEnd_70357 : Nat := 2378729771752195003387

theorem tailTrace_70357 : CollatzResearch.WordTrace tailWord_70357 prefixEnd_70357 2378729771752195003387 := by
  unfold tailWord_70357
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566130606116079864065325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1710753737410719909376883 2566130606116079864065325)
  ·
    refine ⟨962298977293529949024497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2566130606116079864065325 962298977293529949024497)
    ·
      refine ⟨721724232970147461768373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 962298977293529949024497 721724232970147461768373)
      ·
        refine ⟨67661646840951324540785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 721724232970147461768373 67661646840951324540785)
        ·
          refine ⟨50746235130713493405589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67661646840951324540785 50746235130713493405589)
          ·
            refine ⟨2378729771752195003387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50746235130713493405589 2378729771752195003387)
            ·
              rfl

theorem cell19_70357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_70357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70357 prefixEnd_70357 := by exact prefixLift 70357
  have htrace : WordTrace (prefixWord ++ tailWord_70357) baseStart_70357 baseEnd_70357 := by
    simpa [prefixWord, tailWord_70357, baseEnd_70357] using wordTrace_append hprefix tailTrace_70357
  have hstable : (prefixWord ++ tailWord_70357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70357).length < 2 ^ (prefixWord ++ tailWord_70357).sum := by decide
  have hdescent : baseEnd_70357 < baseStart_70357 := by decide
  rcases family_descends (prefixWord ++ tailWord_70357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_70376 : List Nat := [2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_70376 : Nat := 118140960795 + 70376 * 2 ^ 59
def prefixEnd_70376 : Nat := 4983230072969 + 3 ^ 40 * 70376 * 2
def baseEnd_70376 : Nat := 21414349357583340608209

theorem tailTrace_70376 : CollatzResearch.WordTrace tailWord_70376 prefixEnd_70376 21414349357583340608209 := by
  unfold tailWord_70376
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283411796523623054503491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1711215728698164072671321 1283411796523623054503491)
  ·
    refine ⟨1925117694785434581755237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1283411796523623054503491 1925117694785434581755237)
    ·
      refine ⟨360959567772268984079107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1925117694785434581755237 360959567772268984079107)
      ·
        refine ⟨541439351658403476118661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360959567772268984079107 541439351658403476118661)
        ·
          refine ⟨101519878435950651772249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 541439351658403476118661 101519878435950651772249)
          ·
            refine ⟨76139908826962988829187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101519878435950651772249 76139908826962988829187)
            ·
              refine ⟨114209863240444483243781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76139908826962988829187 114209863240444483243781)
              ·
                refine ⟨21414349357583340608209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114209863240444483243781 21414349357583340608209)
                ·
                  rfl

theorem cell19_70376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_70376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_70376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_70376 prefixEnd_70376 := by exact prefixLift 70376
  have htrace : WordTrace (prefixWord ++ tailWord_70376) baseStart_70376 baseEnd_70376 := by
    simpa [prefixWord, tailWord_70376, baseEnd_70376] using wordTrace_append hprefix tailTrace_70376
  have hstable : (prefixWord ++ tailWord_70376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_70376).length < 2 ^ (prefixWord ++ tailWord_70376).sum := by decide
  have hdescent : baseEnd_70376 < baseStart_70376 := by decide
  rcases family_descends (prefixWord ++ tailWord_70376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
